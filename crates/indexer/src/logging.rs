//! Bound repeated daemon diagnostics without hiding the first failure.
use std::{
    collections::HashMap,
    fmt,
    hash::{Hash, Hasher},
    sync::{Arc, Mutex},
    time::Duration,
};
use tracing::{Event, Subscriber};
use tracing_subscriber::{
    fmt::{
        format::{Format, Full, Writer},
        time::{FormatTime, SystemTime},
        FmtContext, FormatEvent, FormatFields,
    },
    registry::LookupSpan,
};

const MAX_EVENTS: usize = 1024;
const SUMMARY_INTERVAL: Duration = Duration::from_secs(60);

#[derive(Default)]
struct Counts {
    events: HashMap<u64, (u64, u64)>, // fingerprint -> (last seen sequence, suppressed count)
    sequence: u64,
}

impl Counts {
    fn observe(&mut self, id: u64) -> (bool, Option<(u64, u64)>) {
        self.sequence = self.sequence.wrapping_add(1);
        if let Some((seen, count)) = self.events.get_mut(&id) {
            *seen = self.sequence;
            *count = count.saturating_add(1);
            return (false, None);
        }
        let evicted = if self.events.len() == MAX_EVENTS {
            let oldest = *self
                .events
                .iter()
                .min_by_key(|(_, (seen, _))| *seen)
                .unwrap()
                .0;
            let (_, count) = self.events.remove(&oldest).unwrap();
            Some((oldest, count))
        } else {
            None
        };
        self.events.insert(id, (self.sequence, 0));
        (true, evicted)
    }

    fn drain(&mut self) -> Vec<(u64, u64)> {
        self.events
            .iter_mut()
            .filter_map(|(&id, (_, count))| {
                let repeats = std::mem::take(count);
                (repeats > 0).then_some((id, repeats))
            })
            .collect()
    }
}

#[derive(Clone, Default)]
pub struct RepeatedEvents(Arc<Mutex<Counts>>);

fn summary(out: &mut impl fmt::Write, id: u64, count: u64) -> fmt::Result {
    if count > 0 {
        SystemTime.format_time(&mut Writer::new(out))?;
        writeln!(
            out,
            " event={id:016x} repeated {count} additional times (full message suppressed)"
        )?;
    }
    Ok(())
}

impl<S, N> FormatEvent<S, N> for RepeatedEvents
where
    S: Subscriber + for<'a> LookupSpan<'a>,
    N: for<'a> FormatFields<'a> + 'static,
{
    fn format_event(
        &self,
        ctx: &FmtContext<'_, S, N>,
        mut writer: Writer<'_>,
        event: &Event<'_>,
    ) -> fmt::Result {
        // Exclude timestamps/ANSI from identity, but retain level, target, spans
        // and all fields so changed errors or affected paths remain distinct.
        let mut rendered = String::new();
        let format: Format<Full, ()> = tracing_subscriber::fmt::format()
            .without_time()
            .with_ansi(false);
        format.format_event(ctx, Writer::new(&mut rendered), event)?;
        let mut hash = std::collections::hash_map::DefaultHasher::new();
        rendered.hash(&mut hash);
        let id = hash.finish();
        let mut counts = self.0.lock().unwrap_or_else(|e| e.into_inner());
        let (first, evicted) = counts.observe(id);
        if let Some((old, count)) = evicted {
            summary(&mut writer, old, count)?;
        }
        if first {
            SystemTime.format_time(&mut writer)?;
            write!(writer, " event={id:016x} {rendered}")?;
        }
        Ok(())
    }
}

impl RepeatedEvents {
    fn flush(&self, out: &mut impl fmt::Write) -> fmt::Result {
        let mut counts = self.0.lock().unwrap_or_else(|e| e.into_inner());
        for (id, count) in counts.drain() {
            summary(out, id, count)?;
        }
        Ok(())
    }

    pub fn start_summaries(&self) -> tokio::task::JoinHandle<()> {
        let events = self.clone();
        tokio::spawn(async move {
            loop {
                tokio::time::sleep(SUMMARY_INTERVAL).await;
                events.flush_stderr();
            }
        })
    }

    pub fn flush_stderr(&self) {
        use std::io::Write;
        let mut text = String::new();
        if self.flush(&mut text).is_ok() && !text.is_empty() {
            let _ = std::io::stderr().lock().write_all(text.as_bytes());
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io;

    #[derive(Clone, Default)]
    struct Output(Arc<Mutex<Vec<u8>>>);
    impl io::Write for Output {
        fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
            self.0.lock().unwrap().extend_from_slice(bytes);
            Ok(bytes.len())
        }
        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }
    impl<'a> tracing_subscriber::fmt::MakeWriter<'a> for Output {
        type Writer = Self;
        fn make_writer(&'a self) -> Self {
            self.clone()
        }
    }

    #[test]
    fn storm_logs_first_event_then_compact_counts_and_preserves_changed_errors() {
        let events = RepeatedEvents::default();
        let output = Output::default();
        let subscriber = tracing_subscriber::fmt()
            .with_ansi(false)
            .event_format(events.clone())
            .with_writer(output.clone())
            .finish();
        tracing::subscriber::with_default(subscriber, || {
            for _ in 0..10_000 {
                tracing::error!(path = "one", "database unavailable");
            }
            tracing::error!(path = "two", "database unavailable");
            tracing::warn!(path = "one", "database unavailable");
        });
        let full = String::from_utf8(output.0.lock().unwrap().clone()).unwrap();
        assert_eq!(full.matches("database unavailable").count(), 3);
        let mut summaries = String::new();
        events.flush(&mut summaries).unwrap();
        assert_eq!(summaries.lines().count(), 1);
        assert!(summaries.contains("repeated 9999 additional times"));
        assert!(!summaries.contains("database unavailable"));
        let id = full
            .lines()
            .next()
            .unwrap()
            .split("event=")
            .nth(1)
            .unwrap()
            .split_whitespace()
            .next()
            .unwrap();
        assert!(summaries.contains(id));
        summaries.clear();
        events.flush(&mut summaries).unwrap();
        assert!(summaries.is_empty());
    }

    #[test]
    fn bounded_cache_reports_pending_counts_on_eviction() {
        let mut counts = Counts::default();
        counts.observe(0);
        counts.observe(0);
        for id in 1..MAX_EVENTS as u64 {
            counts.observe(id);
        }
        assert_eq!(counts.observe(MAX_EVENTS as u64), (true, Some((0, 1))));
        assert_eq!(counts.events.len(), MAX_EVENTS);
    }
}
