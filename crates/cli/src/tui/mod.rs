//! Native field/list editor with separate Save and Start confirmations.
mod backend;
pub mod global;
mod model;
#[cfg(test)]
mod tests;
use backend::{Backend, Database};
use console::{Key, Term};
use model::{shell_path, visible, Draft, Field, View};
use muninn_core::{
    config::GlobalConfig,
    db,
    family_policy::{Backend as EmbeddingProvider, PolicyError},
};
use std::{io::IsTerminal, path::Path};

struct Screen(Term);
impl Screen {
    fn enter(term: Term) -> std::io::Result<Self> {
        let guard = Self(term);
        guard.0.write_str("\x1b[?1049h\x1b[?25l")?;
        guard.0.flush()?;
        Ok(guard)
    }
}
impl Drop for Screen {
    fn drop(&mut self) {
        let _ = self.0.write_str("\x1b[?25h\x1b[?1049l");
        let _ = self.0.flush();
    }
}

pub async fn run(path: &Path, add_mode: bool) -> anyhow::Result<()> {
    let term = Term::stdout();
    anyhow::ensure!(
        term.is_term() && std::io::stdin().is_terminal(),
        "Interactive configuration requires a terminal; use --json for automation"
    );
    let config = GlobalConfig::load()
        .map_err(|_| anyhow::anyhow!("Cannot load global Muninn configuration"))?;
    let client = db::connect(&config.database)
        .await
        .map_err(|_| anyhow::anyhow!("Cannot connect using global Muninn configuration"))?;
    let prep_config = config.database.clone();
    let prepare = move || {
        let config = prep_config.clone();
        async move { db::connect_for_preparation(&config).await }
    };
    let mut backend = Database {
        client,
        config,
        path: path.to_owned(),
        add_mode,
        prepare,
    };
    let screen = Screen::enter(term)?;
    #[cfg(unix)]
    let mut terminate = tokio::signal::unix::signal(tokio::signal::unix::SignalKind::terminate())?;
    #[cfg(unix)]
    let result = tokio::select! {
        result=drive(&screen.0,&mut backend,path,add_mode)=>result,
        _=tokio::signal::ctrl_c()=>Err(anyhow::anyhow!("Interrupted; inspect current policy before retrying a save")),
        _=terminate.recv()=>Err(anyhow::anyhow!("Interrupted; inspect current policy before retrying a save")),
    };
    #[cfg(not(unix))]
    let result = tokio::select! {
        result=drive(&screen.0,&mut backend,path,add_mode)=>result,
        _=tokio::signal::ctrl_c()=>Err(anyhow::anyhow!("Interrupted; inspect current policy before retrying a save")),
    };
    drop(screen);
    result
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Axis {
    Exclude,
    Vendor,
}
impl Axis {
    fn label(self) -> &'static str {
        match self {
            Self::Exclude => "Exclusions",
            Self::Vendor => "Vendor rules",
        }
    }
    fn rules(self, draft: &Draft) -> &[String] {
        match self {
            Self::Exclude => &draft.policy.index.exclude,
            Self::Vendor => &draft.policy.index.vendor,
        }
    }
    fn defaults(self, draft: &Draft) -> &[String] {
        match self {
            Self::Exclude => &draft.defaults.index.exclude,
            Self::Vendor => &draft.defaults.index.vendor,
        }
    }
    fn field(self, index: usize) -> Field {
        match self {
            Self::Exclude => Field::Exclude(index),
            Self::Vendor => Field::Vendor(index),
        }
    }
    fn add_field(self) -> Field {
        match self {
            Self::Exclude => Field::AddExclude,
            Self::Vendor => Field::AddVendor,
        }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Action {
    Open(View),
    Edit(Field),
    Advanced,
    EditMore,
    Rules(Axis),
    Defaults(Axis),
    Rule(usize),
    AddRule,
    Check,
    Save,
    Start,
    Close,
    Back,
    RefreshCurrent,
    LoadCurrent,
    KeepDraft,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Confirm {
    Save,
    Discard,
    LoadCurrent,
    KeepDraft,
    RemoveRule(usize),
}
enum Modal {
    Edit(Field, Vec<char>, usize),
    Backend(usize),
    Confirm(Confirm, usize),
    Rule(usize, usize),
    Docs(String, String),
}
struct Ui {
    focus: usize,
    advanced: bool,
    axis: Axis,
    history: Vec<(View, usize, Axis)>,
    modal: Option<Modal>,
    help_return: Option<Box<Modal>>,
    modal_scroll: usize,
    help_scroll: usize,
    follow_focus: bool,
    notice_error: bool,
    saved_session: bool,
    indexing_outcome: Option<(bool, String)>,
    busy: bool,
}
impl Default for Ui {
    fn default() -> Self {
        Self {
            focus: 0,
            advanced: false,
            axis: Axis::Exclude,
            history: Vec::new(),
            modal: None,
            help_return: None,
            modal_scroll: 0,
            help_scroll: 0,
            follow_focus: true,
            notice_error: false,
            saved_session: false,
            indexing_outcome: None,
            busy: false,
        }
    }
}
impl Ui {
    fn open(&mut self, draft: &mut Draft, view: View) {
        self.history.push((draft.view, self.focus, self.axis));
        draft.view = view;
        draft.scroll = 0;
        self.focus = if matches!(view, View::Conflict | View::Help) {
            usize::MAX
        } else {
            0
        };
        self.follow_focus = false;
    }
    fn back(&mut self, draft: &mut Draft) -> bool {
        if let Some((view, focus, axis)) = self.history.pop() {
            draft.view = view;
            draft.scroll = 0;
            self.focus = focus;
            self.axis = axis;
            self.follow_focus = true;
            true
        } else {
            false
        }
    }
    fn confirm(&mut self, confirm: Confirm) {
        self.modal = Some(Modal::Confirm(confirm, 0));
        self.modal_scroll = 0;
    }
    fn failure(&mut self, draft: &mut Draft, error: PolicyError) {
        report_error(draft, error);
        self.notice_error = true;
        draft.view = View::Policy;
        draft.scroll = 0;
        self.history.clear();
        self.focus = usize::MAX;
        self.follow_focus = false;
    }
    fn notice(&mut self, draft: &mut Draft, message: impl Into<String>) {
        draft.status = message.into();
        self.notice_error = false;
    }
    fn select_action(&mut self, draft: &Draft, path: &Path, action: Action) {
        let page = page(draft, self, path);
        if let Some(index) = page.actions().iter().position(|a| *a == action) {
            self.focus = index;
        }
        self.follow_focus = true;
    }
}

async fn drive(
    term: &Term,
    backend: &mut impl Backend,
    path: &Path,
    add_mode: bool,
) -> anyhow::Result<()> {
    term.write_line("Loading configuration and file preview...")?;
    let mut draft = Draft::new(backend.load().await?)?;
    let mut ui = Ui::default();
    if draft.family_id().is_some() && !draft.dirty() && draft.base["indexing_enabled"] == false {
        ui.saved_session = true;
        ui.select_action(&draft, path, recommended_action(&draft));
        ui.follow_focus = false;
    }
    loop {
        draw(term, &mut draft, path, add_mode, &mut ui)?;
        let key = term.read_key_raw()?;
        if key == Key::CtrlC {
            return Ok(());
        }
        if let Some(current) = ui.modal.take() {
            if key == Key::Char('?') && matches!(current, Modal::Backend(..) | Modal::Rule(..)) {
                let field = match current {
                    Modal::Backend(_) => Field::Backend,
                    Modal::Rule(index, _) => ui.axis.field(index),
                    _ => unreachable!(),
                };
                ui.modal = Some(Modal::Docs(
                    field_label(field).into(),
                    field_help(&draft, field, path),
                ));
                ui.help_return = Some(Box::new(current));
                ui.modal_scroll = 0;
                continue;
            }
            let mut accepted = None;
            match current {
                Modal::Docs(label, text) => {
                    match key {
                        Key::Escape | Key::Enter => {
                            ui.modal = ui.help_return.take().map(|modal| *modal);
                            ui.modal_scroll = 0;
                            ui.follow_focus = true;
                            continue;
                        }
                        Key::Char('?') => {
                            ui.help_return = None;
                            ui.open(&mut draft, View::Help);
                            continue;
                        }
                        Key::PageUp => ui.modal_scroll = ui.modal_scroll.saturating_sub(5),
                        Key::PageDown => ui.modal_scroll += 5,
                        _ => {}
                    }
                    ui.modal = Some(Modal::Docs(label, text));
                }
                Modal::Edit(field, mut chars, mut cursor) => {
                    match key {
                        Key::Escape => continue,
                        Key::PageUp => ui.help_scroll = ui.help_scroll.saturating_sub(2),
                        Key::PageDown => ui.help_scroll += 2,
                        Key::Enter => {
                            match draft.edit(field, chars.iter().collect()) {
                                Ok(()) => {
                                    ui.notice_error = false;
                                    ui.saved_session = false;
                                }
                                Err(error) => {
                                    draft.status = error.to_string();
                                    ui.notice_error = true;
                                    ui.modal = Some(Modal::Edit(field, chars, cursor));
                                }
                            }
                            continue;
                        }
                        Key::ArrowLeft => cursor = cursor.saturating_sub(1),
                        Key::ArrowRight => cursor = (cursor + 1).min(chars.len()),
                        Key::Home => cursor = 0,
                        Key::End => cursor = chars.len(),
                        Key::Backspace if cursor > 0 => {
                            cursor -= 1;
                            chars.remove(cursor);
                        }
                        Key::Del if cursor < chars.len() => {
                            chars.remove(cursor);
                        }
                        Key::Char('\u{15}') => {
                            chars.clear();
                            cursor = 0;
                        }
                        Key::Char(c) if !c.is_control() => {
                            chars.insert(cursor, c);
                            cursor += 1;
                        }
                        _ => {}
                    }
                    ui.modal = Some(Modal::Edit(field, chars, cursor));
                }
                Modal::Backend(mut index) => {
                    match key {
                        Key::Escape => continue,
                        Key::ArrowUp | Key::BackTab => {
                            index = index.saturating_sub(1);
                            ui.follow_focus = true;
                        }
                        Key::ArrowDown | Key::Tab => {
                            index = (index + 1).min(2);
                            ui.follow_focus = true;
                        }
                        Key::PageUp => {
                            ui.modal_scroll = ui.modal_scroll.saturating_sub(5);
                            ui.follow_focus = false;
                        }
                        Key::PageDown => {
                            ui.modal_scroll += 5;
                            ui.follow_focus = false;
                        }
                        Key::Enter => {
                            draft.edit(
                                Field::Backend,
                                ["voyage", "openai", "local"][index].into(),
                            )?;
                            ui.notice_error = false;
                            ui.saved_session = false;
                            continue;
                        }
                        _ => {}
                    }
                    ui.modal = Some(Modal::Backend(index));
                }
                Modal::Rule(index, mut choice) => {
                    match key {
                        Key::Escape => continue,
                        Key::ArrowUp | Key::BackTab => {
                            choice = choice.saturating_sub(1);
                            ui.follow_focus = true;
                        }
                        Key::ArrowDown | Key::Tab => {
                            choice = (choice + 1).min(4);
                            ui.follow_focus = true;
                        }
                        Key::PageUp => {
                            ui.modal_scroll = ui.modal_scroll.saturating_sub(5);
                            ui.follow_focus = false;
                        }
                        Key::PageDown => {
                            ui.modal_scroll += 5;
                            ui.follow_focus = false;
                        }
                        Key::Enter => {
                            let field = ui.axis.field(index);
                            draft.selected =
                                draft.fields().iter().position(|f| *f == field).unwrap_or(0);
                            match choice {
                                0 => {
                                    let chars: Vec<_> =
                                        field_value(&draft, field).chars().collect();
                                    let len = chars.len();
                                    ui.help_scroll = 0;
                                    ui.modal = Some(Modal::Edit(field, chars, len));
                                }
                                1 | 2 => {
                                    draft.move_rule(choice == 1);
                                    ui.saved_session = false;
                                    if let Field::Exclude(i) | Field::Vendor(i) = draft.selected() {
                                        ui.select_action(&draft, path, Action::Rule(i));
                                    }
                                }
                                3 => ui.confirm(Confirm::RemoveRule(index)),
                                _ => {}
                            }
                            continue;
                        }
                        _ => {}
                    }
                    ui.modal = Some(Modal::Rule(index, choice));
                }
                Modal::Confirm(confirm, mut choice) => {
                    match key {
                        Key::Escape => continue,
                        Key::Tab | Key::BackTab => choice = 1 - choice,
                        Key::ArrowLeft | Key::ArrowUp => choice = 0,
                        Key::ArrowRight | Key::ArrowDown => choice = 1,
                        Key::PageUp => ui.modal_scroll = ui.modal_scroll.saturating_sub(5),
                        Key::PageDown => ui.modal_scroll += 5,
                        Key::Enter if choice == 0 => continue,
                        Key::Enter => accepted = Some(confirm),
                        _ => {}
                    }
                    if accepted.is_none() {
                        ui.modal = Some(Modal::Confirm(confirm, choice));
                    }
                }
            }
            match accepted {
                Some(Confirm::Discard) => return Ok(()),
                Some(Confirm::RemoveRule(index)) => {
                    draft.selected = draft
                        .fields()
                        .iter()
                        .position(|f| *f == ui.axis.field(index))
                        .unwrap_or(0);
                    draft.remove();
                    ui.saved_session = false;
                    ui.select_action(&draft, path, Action::AddRule);
                }
                Some(Confirm::LoadCurrent) => {
                    if let Some(latest) = draft.latest.take() {
                        draft = Draft::new(latest)?;
                        ui = Ui::default();
                        ui.notice(
                            &mut draft,
                            "Loaded current settings. Previous draft discarded.",
                        );
                    }
                }
                Some(Confirm::KeepDraft) => match draft.keep_draft_on_latest() {
                    Ok(()) => {
                        ui = Ui::default();
                        ui.notice(&mut draft, "Full draft retained against the reviewed revision. Review and save to apply it.");
                    }
                    Err(error) => {
                        draft.status = error.to_string();
                        ui.notice_error = true;
                    }
                },
                Some(Confirm::Save) => {
                    ui.notice(&mut draft, "Saving configuration...");
                    ui.busy = true;
                    draft.scroll = 0;
                    ui.follow_focus = false;
                    draw(term, &mut draft, path, add_mode, &mut ui)?;
                    let saved = backend.save(&draft).await;
                    ui.busy = false;
                    match saved {
                        Ok(data) => {
                            let association_error = data.get("registration_error").cloned();
                            draft = Draft::new(data)?;
                            ui = Ui::default();
                            draft.view = View::Policy;
                            ui.saved_session = true;
                            ui.notice(
                                &mut draft,
                                "Configuration saved. Refreshing the file preview...",
                            );
                            ui.busy = true;
                            draft.scroll = 0;
                            ui.follow_focus = false;
                            draw(term, &mut draft, path, add_mode, &mut ui)?;
                            let checked = backend.check(&draft).await;
                            ui.busy = false;
                            match checked {
                                Ok(data) => {
                                    draft.checked = Some(data);
                                    let message = if draft.base["indexing_enabled"] == true {
                                        "Configuration saved. Indexing is enabled; updates may follow."
                                    } else {
                                        "Configuration saved. Indexing has not started."
                                    };
                                    ui.notice(&mut draft, message);
                                }
                                Err(error) => {
                                    draft.checked = None;
                                    draft.status = format!("Configuration saved, but preview failed: {}. Refresh the preview to retry.", error.message);
                                    ui.notice_error = true;
                                }
                            }
                            if let Some(error) = association_error {
                                draft.status = format!("Settings saved; checkout registration failed: {}. Save configuration again to retry registration.", error["message"].as_str().unwrap_or("see details"));
                                ui.notice_error = true;
                            }
                            // Saving presents the recommendation; a later explicit choice starts work.
                            ui.select_action(&draft, path, recommended_action(&draft));
                            draft.scroll = 0;
                            ui.follow_focus = false;
                        }
                        Err(error) => ui.failure(&mut draft, error),
                    }
                }
                None => {}
            }
            continue;
        }
        // Closing and discard confirmation remain available at every size.
        if key == Key::Escape {
            if !ui.back(&mut draft) {
                if draft.dirty() {
                    ui.confirm(Confirm::Discard);
                } else {
                    return Ok(());
                }
            }
            continue;
        }
        let (height, width) = term.size();
        if height < 14 || width < 52 {
            continue;
        }
        if key == Key::Char('?') {
            let (label, text) = focused_help(&draft, &ui, path);
            ui.modal = Some(Modal::Docs(label, text));
            ui.modal_scroll = 0;
            continue;
        }
        let current_page = page(&draft, &ui, path);
        let actions = current_page.actions();
        ui.focus = ui.focus.min(actions.len().saturating_sub(1));
        match key {
            Key::Tab => {
                ui.focus = (ui.focus + 1) % actions.len();
                ui.follow_focus = true;
            }
            Key::BackTab => {
                ui.focus = (ui.focus + actions.len() - 1) % actions.len();
                ui.follow_focus = true;
            }
            Key::ArrowUp | Key::ArrowDown => {
                ui.focus = if key == Key::ArrowUp {
                    ui.focus.saturating_sub(1)
                } else {
                    (ui.focus + 1).min(actions.len() - 1)
                };
                ui.follow_focus = true;
            }
            Key::PageUp | Key::PageDown => {
                draft.scroll = if key == Key::PageUp {
                    draft.scroll.saturating_sub(6)
                } else {
                    draft.scroll + 6
                };
                ui.follow_focus = false;
            }
            Key::Enter => match actions[ui.focus] {
                Action::Open(view) => ui.open(&mut draft, view),
                Action::Back => {
                    ui.back(&mut draft);
                }
                Action::Close => {
                    if draft.dirty() {
                        ui.confirm(Confirm::Discard);
                    } else {
                        return Ok(());
                    }
                }
                Action::EditMore => {
                    ui.saved_session = false;
                    draft.view = View::Policy;
                    draft.scroll = 0;
                    ui.focus = 0;
                    ui.follow_focus = true;
                }
                Action::Advanced => {
                    ui.advanced = !ui.advanced;
                    ui.follow_focus = true;
                }
                Action::Rules(axis) | Action::Defaults(axis) => {
                    let view = if matches!(actions[ui.focus], Action::Rules(_)) {
                        View::Rules
                    } else {
                        View::Defaults
                    };
                    ui.open(&mut draft, view);
                    ui.axis = axis;
                }
                Action::Rule(index) => {
                    ui.modal = Some(Modal::Rule(index, 0));
                    ui.modal_scroll = 0;
                    ui.follow_focus = true;
                }
                Action::AddRule => {
                    ui.help_scroll = 0;
                    ui.modal = Some(Modal::Edit(ui.axis.add_field(), Vec::new(), 0));
                }
                Action::Edit(field) => {
                    if field == Field::Backend {
                        if draft.family_id().is_some() {
                            ui.notice(
                                &mut draft,
                                "Provider and model are fixed after registration.",
                            );
                        } else {
                            ui.modal =
                                Some(Modal::Backend(match draft.policy.embeddings.backend {
                                    muninn_core::family_policy::Backend::Voyage => 0,
                                    muninn_core::family_policy::Backend::OpenAI => 1,
                                    muninn_core::family_policy::Backend::Local => 2,
                                }));
                        }
                    } else {
                        let chars: Vec<_> = field_value(&draft, field).chars().collect();
                        let len = chars.len();
                        ui.help_scroll = 0;
                        ui.modal = Some(Modal::Edit(field, chars, len));
                    }
                    ui.modal_scroll = 0;
                    ui.follow_focus = true;
                }
                Action::Check | Action::Save | Action::Start => {
                    let action = actions[ui.focus];
                    let had_preview = draft.checked.is_some();
                    let previous_recommendation = recommended_action(&draft);
                    if action == Action::Start && (draft.dirty() || draft.family_id().is_none()) {
                        ui.notice(&mut draft, "Save your draft before starting indexing.");
                        continue;
                    }
                    ui.notice(
                        &mut draft,
                        "Checking configuration and scanning the selected checkout...",
                    );
                    ui.busy = true;
                    draft.scroll = 0;
                    ui.follow_focus = false;
                    draw(term, &mut draft, path, add_mode, &mut ui)?;
                    let checked = backend.check(&draft).await;
                    ui.busy = false;
                    match checked {
                        Ok(data) => {
                            let unsupported = draft.family_id().is_some()
                                && data["candidate"]["validation"]["apply_supported"] == false;
                            draft.checked = Some(data);
                            draft.view = View::Policy;
                            draft.scroll = 0;
                            ui.history.clear();
                            ui.select_action(&draft, path, Action::Check);
                            ui.notice(&mut draft, "Preview refreshed for this draft. Rescan saved nothing and did not start indexing.");
                            if ui.saved_session {
                                ui.select_action(&draft, path, recommended_action(&draft));
                                draft.scroll = 0;
                                ui.follow_focus = false;
                            }
                            match action {
                                Action::Save if unsupported => {
                                    ui.notice(&mut draft, "This provider/model change cannot be saved. Model migration is unavailable.");
                                    ui.notice_error = true;
                                }
                                Action::Save => ui.confirm(Confirm::Save),
                                Action::Start if !key_ready(&draft) => {
                                    ui.notice(&mut draft, "Cannot start: the selected hosted provider has no matching API key. Use muninn config edit --global, then Rescan.");
                                    ui.notice_error = true;
                                }
                                Action::Start if !had_preview => {
                                    ui.notice(&mut draft, "Preview refreshed. Review the recommendation before choosing Start.");
                                    ui.notice_error = true;
                                    ui.select_action(&draft, path, recommended_action(&draft));
                                    draft.scroll = 0;
                                    ui.follow_focus = false;
                                }
                                Action::Start
                                    if previous_recommendation == Action::Start
                                        && recommended_action(&draft) != Action::Start =>
                                {
                                    ui.notice(&mut draft, "The refreshed scan found new concerns. Review them before choosing Start again.");
                                    ui.notice_error = true;
                                    ui.select_action(&draft, path, Action::EditMore);
                                    draft.scroll = 0;
                                    ui.follow_focus = false;
                                }
                                Action::Start => {
                                    run_indexing(term, backend, path, add_mode, &mut draft, &mut ui)
                                        .await?
                                }
                                _ => {}
                            }
                        }
                        Err(error) => ui.failure(&mut draft, error),
                    }
                }
                Action::RefreshCurrent => {
                    ui.notice(&mut draft, "Loading current saved settings for review...");
                    ui.busy = true;
                    draft.scroll = 0;
                    ui.follow_focus = false;
                    draw(term, &mut draft, path, add_mode, &mut ui)?;
                    let loaded = backend.load().await;
                    ui.busy = false;
                    match loaded {
                        Ok(latest) => {
                            ui.history.push((draft.view, ui.focus, ui.axis));
                            draft.receive_latest(latest);
                            ui.focus = usize::MAX;
                            ui.follow_focus = false;
                            ui.notice_error = false;
                        }
                        Err(error) => ui.failure(&mut draft, error),
                    }
                }
                Action::LoadCurrent => ui.confirm(Confirm::LoadCurrent),
                Action::KeepDraft => ui.confirm(Confirm::KeepDraft),
            },
            _ => {}
        }
    }
}
async fn run_indexing(
    term: &Term,
    backend: &mut impl Backend,
    path: &Path,
    add_mode: bool,
    draft: &mut Draft,
    ui: &mut Ui,
) -> anyhow::Result<()> {
    ui.notice(
        draft,
        "Preparing embeddings and scanning files. Completion is reported after the pass finishes.",
    );
    ui.busy = true;
    draft.scroll = 0;
    ui.follow_focus = false;
    draw(term, draft, path, add_mode, ui)?;
    let start_draft = Draft::new(draft.base.clone())?;
    let (progress_tx, mut progress_rx) = tokio::sync::mpsc::unbounded_channel();
    let operation = backend.start_with_progress(&start_draft, move |done, total, file| {
        let _ = progress_tx.send((done, total, file.to_owned()));
    });
    tokio::pin!(operation);
    let mut progress_open = true;
    let mut last_paint = std::time::Instant::now() - std::time::Duration::from_millis(100);
    let started = loop {
        tokio::select! {
            result = &mut operation => break result,
            event = progress_rx.recv(), if progress_open => match event {
                Some((done, total, file)) => {
                    ui.notice(draft, format!("Indexing: {done} of {total} files processed. {}. Waiting for the final indexing result.", file.display()));
                    if last_paint.elapsed() >= std::time::Duration::from_millis(75) {
                        draw(term, draft, path, add_mode, ui)?;
                        last_paint = std::time::Instant::now();
                    }
                }
                None => progress_open = false,
            }
        }
    };
    ui.busy = false;
    match started {
        Ok(data) => {
            draft.base["indexing_enabled"] = serde_json::json!(true);
            let completed = data["indexing_completed"].as_bool().unwrap_or(false);
            ui.notice(
                draft,
                format!(
                    "Indexing enabled. {} Skipped entries: {}.",
                    if completed {
                        "This indexing pass completed."
                    } else {
                        "This indexing pass is incomplete."
                    },
                    count(&data["skipped_checkouts_or_files"])
                ),
            );
            ui.indexing_outcome = Some((completed, draft.status.clone()));
            ui.saved_session = true;
            draft.scroll = 0;
            ui.select_action(draft, path, Action::Close);
            ui.follow_focus = false;
        }
        Err(error) => {
            if error.details["indexing_enabled"] == true {
                draft.base["indexing_enabled"] = serde_json::json!(true);
                ui.indexing_outcome = Some((false, format!("Indexing is enabled, but this pass did not complete: {}. Completed views remain available; retry here or let the daemon retry.", error.message)));
                ui.saved_session = true;
            }
            ui.failure(draft, error);
        }
    }
    Ok(())
}

fn report_error(draft: &mut Draft, error: PolicyError) {
    // A failed indexing pass does not change the checked policy. Keep its last
    // inventory so Retry stays available; Start checks freshness again anyway.
    // Revision, validation and other failures still invalidate the preview.
    if error.code != "indexing_incomplete" || error.details["indexing_enabled"] != true {
        draft.checked = None;
    }
    draft.status = format!(
        "{} Draft retained. Review current saved settings below. ({})",
        error.message, error.code
    );
    if error.details["reservation_persisted"] == true {
        draft.status.push_str(
            " Creation intent was saved; retry add --json without input to finish registration.",
        );
    }
}
fn field_label(field: Field) -> &'static str {
    match field {
        Field::Name => "Name",
        Field::Debounce => "Change delay (ms)",
        Field::Backend => "Embedding provider",
        Field::Batch => "Request size",
        Field::Exclude(_) => "Exclusion rule",
        Field::Vendor(_) => "Vendor rule",
        Field::AddExclude => "New exclusion rule",
        Field::AddVendor => "New vendor rule",
    }
}
fn field_value(draft: &Draft, field: Field) -> String {
    match field {
        Field::Name => draft.policy.name.clone(),
        Field::Debounce => draft.policy.watcher.debounce_ms.to_string(),
        Field::Batch => draft.policy.embeddings.batch_size.to_string(),
        Field::Backend => format!("{:?}", draft.policy.embeddings.backend),
        Field::Exclude(i) => draft.policy.index.exclude[i].clone(),
        Field::Vendor(i) => draft.policy.index.vendor[i].clone(),
        _ => String::new(),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Tone {
    Normal,
    Heading,
    Muted,
    Info,
    Warning,
    Error,
    Success,
    Focus,
}
#[derive(Debug)]
struct RenderLine {
    text: String,
    tone: Tone,
}
impl RenderLine {
    fn new(text: impl Into<String>, tone: Tone) -> Self {
        Self {
            text: text.into(),
            tone,
        }
    }
}
struct Row {
    text: String,
    action: Option<Action>,
    follow: bool,
    tone: Tone,
}
struct Page {
    rows: Vec<Row>,
    footer: Vec<(Action, String)>,
}
impl Page {
    fn new() -> Self {
        Self {
            rows: Vec::new(),
            footer: Vec::new(),
        }
    }
    fn text(&mut self, text: impl Into<String>) {
        self.rows.push(Row {
            text: text.into(),
            action: None,
            follow: false,
            tone: Tone::Normal,
        });
    }
    fn toned(&mut self, text: impl Into<String>, tone: Tone) {
        self.rows.push(Row {
            text: text.into(),
            action: None,
            follow: false,
            tone,
        });
    }
    fn heading(&mut self, text: impl Into<String>) {
        self.toned(text, Tone::Heading);
    }
    fn muted(&mut self, text: impl Into<String>) {
        self.toned(text, Tone::Muted);
    }
    fn warning(&mut self, text: impl Into<String>) {
        self.toned(text, Tone::Warning);
    }
    fn info(&mut self, text: impl Into<String>) {
        self.toned(text, Tone::Info);
    }
    fn control(&mut self, action: Action, text: impl Into<String>) {
        self.rows.push(Row {
            text: text.into(),
            action: Some(action),
            follow: false,
            tone: Tone::Normal,
        });
    }
    fn setting(
        &mut self,
        ui: &Ui,
        action: Action,
        label: impl Into<String>,
        help: impl Into<String>,
    ) {
        let _ = (ui, help);
        self.control(action, label);
    }
    fn button(&mut self, action: Action, text: impl Into<String>) {
        self.footer.push((action, text.into()));
    }
    fn actions(&self) -> Vec<Action> {
        self.rows
            .iter()
            .filter_map(|r| r.action)
            .chain(self.footer.iter().map(|(a, _)| *a))
            .collect()
    }
}
fn bytes(value: &serde_json::Value) -> String {
    match value.as_u64() {
        Some(n) if n >= 1024 * 1024 => format!("{:.1} MiB", n as f64 / (1024.0 * 1024.0)),
        Some(n) if n >= 1024 => format!("{:.1} KiB", n as f64 / 1024.0),
        Some(n) => format!("{n} B"),
        None => "unknown size".into(),
    }
}
fn count(value: &serde_json::Value) -> String {
    value
        .as_u64()
        .map(|n| n.to_string())
        .unwrap_or_else(|| "unknown".into())
}
fn flag(value: &serde_json::Value) -> &'static str {
    match value.as_bool() {
        Some(true) => "Yes",
        Some(false) => "No",
        None => "Not available",
    }
}
fn summary_changes(draft: &Draft) -> Vec<String> {
    let current = &draft.base["policy"];
    let candidate = serde_json::to_value(&draft.policy).unwrap();
    let mut changes = Vec::new();
    for (label, a, b) in [
        ("Name", &current["name"], &candidate["name"]),
        (
            "Change delay (ms)",
            &current["watcher"]["debounce_ms"],
            &candidate["watcher"]["debounce_ms"],
        ),
        (
            "Provider",
            &current["embeddings"]["backend"],
            &candidate["embeddings"]["backend"],
        ),
        (
            "Model",
            &current["embeddings"]["model"],
            &candidate["embeddings"]["model"],
        ),
        (
            "Batch size",
            &current["embeddings"]["batch_size"],
            &candidate["embeddings"]["batch_size"],
        ),
    ] {
        if a != b {
            changes.push(format!(
                "{label}: {} -> {}",
                display_value(a),
                display_value(b)
            ));
        }
    }
    for (key, label) in [("exclude", "Exclusions"), ("vendor", "Vendor rules")] {
        if current["index"][key] != candidate["index"][key] {
            changes.push(format!("{label} (order matters):"));
            changes.push(format!(
                "  Saved: {}",
                display_rules(&current["index"][key])
            ));
            changes.push(format!(
                "  Draft: {}",
                display_rules(&candidate["index"][key])
            ));
        }
    }
    changes
}
fn display_value(value: &serde_json::Value) -> String {
    value.as_str().map(str::to_owned).unwrap_or_else(|| {
        if value.is_null() {
            "None".into()
        } else {
            value.to_string()
        }
    })
}
fn display_rules(value: &serde_json::Value) -> String {
    let rules: Vec<_> = value
        .as_array()
        .into_iter()
        .flatten()
        .enumerate()
        .map(|(i, rule)| format!("{}. {}", i + 1, rule.as_str().unwrap_or("?")))
        .collect();
    if rules.is_empty() {
        "No custom rules".into()
    } else {
        rules.join("; ")
    }
}
fn provider_key(provider: EmbeddingProvider) -> &'static str {
    match provider {
        EmbeddingProvider::Voyage => "voyage",
        EmbeddingProvider::OpenAI => "openai",
        EmbeddingProvider::Local => "local",
    }
}
fn credential_status(draft: &Draft, provider: EmbeddingProvider) -> &str {
    if provider == EmbeddingProvider::Local {
        return "not_required";
    }
    let key = provider_key(provider);
    for data in draft
        .checked
        .as_ref()
        .into_iter()
        .chain(std::iter::once(&draft.base))
    {
        if let Some(value) =
            data["capabilities"]["credential_availability_by_backend"][key].as_str()
        {
            return value;
        }
        if data["candidate"]["policy"]["embeddings"]["backend"] == key
            || data["policy"]["embeddings"]["backend"] == key
        {
            if let Some(value) = data["capabilities"]["credential_availability"].as_str() {
                return value;
            }
        }
    }
    "not_checked"
}
fn credential_label(value: &str) -> &'static str {
    match value {
        "configured_not_verified" | "available" | "present" => {
            "Present in global settings; not verified with provider"
        }
        "not_required" | "not_needed" => "Not needed (local provider)",
        "missing_for_selected_backend" | "missing" => {
            "Missing for this provider; indexing cannot start"
        }
        _ => "Not checked; Rescan to check global settings",
    }
}
fn key_ready(draft: &Draft) -> bool {
    provider_key_ready(draft, draft.policy.embeddings.backend)
}
fn provider_key_ready(draft: &Draft, provider: EmbeddingProvider) -> bool {
    matches!(
        credential_status(draft, provider),
        "configured_not_verified" | "available" | "present" | "not_required" | "not_needed"
    )
}
fn credential_help(provider: EmbeddingProvider) -> Vec<String> {
    if provider == EmbeddingProvider::Local {
        return vec!["Local embeddings run on this computer without a hosted API key. First use may download the model.".into()];
    }
    vec![
        "In another terminal: muninn config edit --global".into(),
        format!("In [embeddings], set backend = \"{}\", model = \"{}\", and api_key in the editor. Then Rescan here.", provider_key(provider), provider.model_identity()),
        "These are existing global settings, shared with knowledge and unbound registrations. Changing them can affect those uses; this form never changes them.".into(),
        "Do not put an API key in a command, rule, or repository file.".into(),
    ]
}
fn global_defaults(draft: &Draft) -> &serde_json::Value {
    if draft.family_id().is_some() {
        if let Some(value) = draft
            .checked
            .as_ref()
            .and_then(|v| v.get("global_defaults"))
        {
            return value;
        }
    }
    &draft.base["global_defaults"]
}
fn global_field(draft: &Draft, field: Field) -> Option<String> {
    let global = global_defaults(draft);
    let value = match field {
        Field::Backend => &global["embeddings"]["backend"],
        Field::Batch => &global["embeddings"]["batch_size"],
        Field::Debounce => &global["watcher"]["debounce_ms"],
        _ => return None,
    };
    (!value.is_null()).then(|| display_value(value))
}
fn saved_field(draft: &Draft, field: Field) -> Option<String> {
    let policy = &draft.base["policy"];
    let value = match field {
        Field::Name => &policy["name"],
        Field::Backend => &policy["embeddings"]["backend"],
        Field::Batch => &policy["embeddings"]["batch_size"],
        Field::Debounce => &policy["watcher"]["debounce_ms"],
        _ => return None,
    };
    (!value.is_null()).then(|| display_value(value))
}
fn provenance(draft: &Draft, field: Field) -> &'static str {
    let current = if field == Field::Backend {
        provider_key(draft.policy.embeddings.backend).into()
    } else {
        field_value(draft, field)
    };
    if draft.family_id().is_some() {
        if field == Field::Backend {
            "saved · fixed"
        } else if saved_field(draft, field).as_deref() == Some(&current) {
            "saved"
        } else {
            "custom draft"
        }
    } else if let Some(global) = global_field(draft, field) {
        if current == global {
            "global default"
        } else {
            "custom"
        }
    } else if saved_field(draft, field).as_deref() == Some(&current) {
        "initial value"
    } else {
        "custom"
    }
}
fn default_reference(draft: &Draft, field: Field) -> String {
    if let Some(value) = global_field(draft, field) {
        format!(
            "{}: {value}.",
            if draft.family_id().is_some() {
                "Global default now"
            } else {
                "Global default copied at creation"
            }
        )
    } else if let Some(value) = saved_field(draft, field) {
        format!(
            "{}: {value}.",
            if draft.family_id().is_some() {
                "Saved value"
            } else {
                "Initial value"
            }
        )
    } else {
        String::new()
    }
}
fn global_rule_count(draft: &Draft, axis: Axis) -> Option<usize> {
    if draft.family_id().is_some() {
        let shipped = muninn_core::family_policy::Defaults::shipped();
        let rules = match axis {
            Axis::Exclude => shipped.index.exclude,
            Axis::Vendor => shipped.index.vendor,
        };
        if (draft.defaults.revision.starts_with("global-snapshot-v1-")
            || draft.defaults.revision == shipped.revision)
            && axis.defaults(draft).starts_with(&rules)
        {
            return Some(axis.defaults(draft).len() - rules.len());
        }
        return None;
    }
    if draft.base["defaults_source"] != "global_snapshot" {
        return None;
    }
    global_defaults(draft)["index"][match axis {
        Axis::Exclude => "exclude",
        Axis::Vendor => "vendor",
    }]
    .as_array()
    .map(Vec::len)
}
fn add_rule_patterns(page: &mut Page, draft: &Draft, axis: Axis, custom: bool) {
    let defaults = axis.defaults(draft);
    let global_count = global_rule_count(draft, axis);
    match global_count {
        Some(count) => {
            page.info(if draft.family_id().is_some() {
                "  Inherited global patterns (saved snapshot):"
            } else {
                "  Inherited global patterns (copied into this draft):"
            });
            if count == 0 {
                page.muted("    (none)");
            }
            for rule in defaults.iter().skip(defaults.len().saturating_sub(count)) {
                page.info(format!("    {rule}"));
            }
            page.muted("  Shipped defaults also remain active; View frozen defaults lists them.");
        }
        None => {
            page.muted(format!(
                "  Saved default patterns (active): {}",
                defaults.join(", ")
            ));
            page.muted("  This older snapshot does not record which patterns originally came from global settings.");
        }
    }
    if draft.family_id().is_some() {
        let key = match axis {
            Axis::Exclude => "exclude",
            Axis::Vendor => "vendor",
        };
        if let Some(rules) = global_defaults(draft)["index"][key].as_array() {
            page.info("  Global patterns now (reference for new repositories):");
            if rules.is_empty() {
                page.muted("    (none)");
            }
            for rule in rules {
                if let Some(rule) = rule.as_str() {
                    page.info(format!("    {rule}"));
                }
            }
            page.muted("  Current global changes do not replace saved defaults.");
        }
    }
    if custom {
        page.text("  Custom patterns (run last):");
        if axis.rules(draft).is_empty() {
            page.muted("    (none)");
        }
        for rule in axis.rules(draft) {
            page.text(format!("    {rule}"));
        }
    }
}

fn rule_source(draft: &Draft, axis: Axis) -> String {
    let total = axis.defaults(draft).len();
    match global_rule_count(draft, axis) {
        Some(global) => format!("{} shipped + {global} global", total.saturating_sub(global)),
        None => format!("{total} frozen defaults"),
    }
}
fn add_preview(page: &mut Page, draft: &Draft, detailed: bool) {
    let partial = draft
        .checked
        .as_ref()
        .is_none_or(|v| v["preflight"]["complete"] != true);
    for (index, line) in preview_lines(draft, detailed).into_iter().enumerate() {
        if index == 0 {
            page.toned(
                line,
                if partial {
                    Tone::Warning
                } else {
                    Tone::Heading
                },
            );
        } else {
            page.text(line);
        }
    }
}
fn add_recommendation(page: &mut Page, draft: &Draft) {
    let ready = recommended_action(draft) == Action::Start;
    for (index, line) in recommendation_lines(draft).into_iter().enumerate() {
        page.toned(
            line,
            if ready {
                Tone::Success
            } else if index == 0 {
                Tone::Warning
            } else {
                Tone::Info
            },
        );
    }
}
fn field_help(draft: &Draft, field: Field, path: &Path) -> String {
    match field {
        Field::Name => {
            let value = draft.base["policy"]["name"].as_str().map(str::to_owned)
                .unwrap_or_else(|| path.file_name().unwrap_or(path.as_os_str()).to_string_lossy().into_owned());
            format!("Display name for this family. {}: {value}.",
                if draft.family_id().is_some() { "Saved value" } else { "Initial value" })
        }
        Field::Backend => format!("Creates vectors for semantic code search. {} {}", default_reference(draft, field),
            if draft.family_id().is_some() { "This saved provider/model is fixed; global changes do not replace it." }
            else { "Global defaults are copied at creation, not inherited live. Provider/model become fixed after Save." }),
        Field::Debounce => format!("Wait after file changes before updating, in milliseconds; 0 means no delay. {} Family setting; later global changes do not replace it.", default_reference(draft, field)),
        Field::Batch => format!("Text chunks per embedding request; must be positive. {} Larger requests need more memory and may exceed provider limits.", default_reference(draft, field)),
        Field::Exclude(_) | Field::AddExclude => "Patterns relative to each checkout. Exclude matches from indexing. Frozen defaults run first; custom rules run afterward, last match wins. ! reverses a rule; reopen an excluded parent before its child.".into(),
        Field::Vendor(_) | Field::AddVendor => "Patterns for files kept in text search without initial embeddings. Frozen defaults run first; last match wins. ! restores primary classification. Exclusions always win.".into(),
    }
}
fn scan_stop(p: &serde_json::Value) -> String {
    match p["stop_reason"].as_str() {
        Some("entry_limit") => format!(
            "the scan reached its {}-entry limit",
            count(&p["entry_limit"])
        ),
        Some("time_limit") => format!(
            "the scan reached its {} ms time limit",
            count(&p["time_budget_ms"])
        ),
        Some("unreadable_entries") => "some files or directories could not be read".into(),
        _ => "the scan did not finish".into(),
    }
}
fn preflight_reason(reason: &str, p: &serde_json::Value) -> String {
    match reason {
        "selected_files_over_10000" => {
            "More than 10,000 files are selected; review whether they are all useful.".into()
        }
        "selected_bytes_over_100_mib" => {
            "Selected files exceed 100 MiB; indexing may take substantial work.".into()
        }
        "file_exceeds_indexer_10_mib_limit" => {
            let file = p["largest_files"].as_array().and_then(|v| v.first());
            file.map(|f| {
                format!(
                    "{} ({}) exceeds the indexer's 10 MiB file limit.",
                    f["path"]["display"].as_str().unwrap_or("A selected file"),
                    bytes(&f["bytes"])
                )
            })
            .unwrap_or_else(|| "A selected file exceeds the indexer's 10 MiB limit.".into())
        }
        "selected_dependency_build_or_environment_directory" => {
            let samples: Vec<_> = p["problem_directory_samples"]
                .as_array()
                .into_iter()
                .flatten()
                .take(3)
                .filter_map(|v| v["display"].as_str())
                .collect();
            if samples.is_empty() {
                "Dependency, build or environment directories are still selected.".into()
            } else {
                format!(
                    "Dependency/build/environment directories are selected: {}.",
                    samples.join(", ")
                )
            }
        }
        "incomplete_inventory" => format!(
            "Partial inventory: {}. Counts are lower bounds.",
            scan_stop(p)
        ),
        "unreadable_entries" => format!(
            "{} entries could not be read; check permissions or exclude them.",
            count(&p["unreadable_entries"])
        ),
        _ => format!("Scan concern: {}.", reason.replace('_', " ")),
    }
}
fn recommended_action(draft: &Draft) -> Action {
    if key_ready(draft)
        && draft.checked.as_ref().is_some_and(|v| {
            v["preflight"]["complete"] == true && v["preflight"]["advice"] == "start"
        })
    {
        Action::Start
    } else {
        Action::EditMore
    }
}
fn recommendation_lines(draft: &Draft) -> Vec<String> {
    let Some(check) = &draft.checked else {
        return Vec::new();
    };
    let p = &check["preflight"];
    if p["advice"] == "start" && p["complete"] == true {
        return vec![if key_ready(draft) {
            "Recommendation: Start. The selected checkout inventory looks suitable.".into()
        } else {
            "Inventory looks suitable. Set up the matching API key before Start.".into()
        }];
    }
    let mut lines = vec!["Recommendation: refine exclusions, yourself or with an agent.".into()];
    let reasons: Vec<_> = p["reasons"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|v| v.as_str())
        .collect();
    if reasons.is_empty() {
        lines.push(format!("The inventory is incomplete: {}.", scan_stop(p)));
    }
    for reason in reasons.iter().take(2) {
        lines.push(format!("- {}", preflight_reason(reason, p)));
    }
    if reasons.len() > 2 {
        lines.push(format!(
            "{} more concerns in Scan details.",
            reasons.len() - 2
        ));
    }
    let suggestions: Vec<_> = p["candidate_exclusions"]
        .as_array()
        .into_iter()
        .flatten()
        .take(3)
        .filter_map(|v| v.as_str())
        .collect();
    if !suggestions.is_empty() {
        lines.push(format!(
            "Suggested exclusions (not applied): {}",
            suggestions.join(", ")
        ));
    }
    lines
}
fn preview_lines(draft: &Draft, detailed: bool) -> Vec<String> {
    let Some(check) = &draft.checked else {
        return vec!["File preview out of date. Save or Rescan will refresh it.".into()];
    };
    let p = &check["preflight"];
    let partial = p["complete"] != true || p["counts_are_lower_bounds"] == true;
    let lower = if partial { "at least " } else { "" };
    let mut lines = vec![format!(
        "{} - selected checkout only",
        if partial {
            "PARTIAL PREVIEW"
        } else {
            "FILE PREVIEW"
        }
    )];
    lines.push(format!(
        "Primary: {lower}{} files / {} · Vendor: {lower}{} files / {}",
        count(&p["tier1"]["files"]),
        bytes(&p["tier1"]["bytes"]),
        count(&p["tier2"]["files"]),
        bytes(&p["tier2"]["bytes"])
    ));
    if partial {
        lines.push(format!(
            "Incomplete: {}. Counts are lower bounds.",
            scan_stop(p)
        ));
    }
    if detailed {
        for reason in p["reasons"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(|v| v.as_str())
        {
            lines.push(preflight_reason(reason, p));
        }
    }
    if detailed {
        lines.push(format!(
            "Checkout: {}",
            p["root"]["display"].as_str().unwrap_or("unavailable")
        ));
        lines.push(format!(
            "Visited files: {} | observed excluded: {}",
            count(&p["visited_regular_files"]),
            count(&p["observed_excluded_files"])
        ));
        lines.push(format!(
            "Pruned directories: {} | unreadable entries: {}",
            count(&p["pruned_directories"]),
            count(&p["unreadable_entries"])
        ));
        lines.push(format!(
            "Skipped symlinks: {}",
            count(&p["skipped_symlinks"])
        ));
        for (key, heading) in [("candidate_exclusions", "SUGGESTED EXCLUSIONS (not applied)")] {
            if let Some(rules) = p[key].as_array().filter(|v| !v.is_empty()) {
                lines.push(String::new());
                lines.push(heading.into());
                for rule in rules {
                    lines.push(rule.as_str().unwrap_or("?").into());
                }
            }
        }
        lines.push(String::new());
        lines.push("LARGEST SELECTED FILES".into());
        for file in p["largest_files"].as_array().into_iter().flatten() {
            lines.push(format!(
                "{}  {}",
                bytes(&file["bytes"]),
                file["path"]["display"].as_str().unwrap_or("?")
            ));
        }
        lines.push(String::new());
        lines.push("LARGEST DIRECTORIES (descendant totals overlap)".into());
        for dir in p["costly_directories"].as_array().into_iter().flatten() {
            lines.push(format!(
                "{} files / {}  {}",
                count(&dir["selected"]["files"]),
                bytes(&dir["selected"]["bytes"]),
                dir["path"]["display"].as_str().unwrap_or("?")
            ));
        }
        lines.push(String::new());
        lines.push("UNREADABLE ENTRIES".into());
        for entry in p["unreadable_samples"].as_array().into_iter().flatten() {
            lines.push(format!(
                "{}: {}",
                entry["operation"].as_str().unwrap_or("Read"),
                entry["path"]["display"].as_str().unwrap_or("?")
            ));
        }
        lines.push("File limit: 10 MiB. Structural parsing limit: 1 MiB.".into());
    }
    if detailed {
        lines.push("Metadata only: parsing and embedding costs are not verified.".into());
    }
    lines
}
fn page(draft: &Draft, ui: &Ui, path: &Path) -> Page {
    let mut page = Page::new();
    match draft.view {
        View::Policy => {
            if ui.busy || ui.notice_error {
                page.toned(
                    if ui.notice_error {
                        "ERROR - ACTION NEEDED"
                    } else {
                        "WORKING"
                    },
                    if ui.notice_error {
                        Tone::Error
                    } else {
                        Tone::Info
                    },
                );
                page.toned(
                    draft.status.clone(),
                    if ui.notice_error {
                        Tone::Error
                    } else {
                        Tone::Info
                    },
                );
                if ui.notice_error {
                    page.control(Action::RefreshCurrent, "[Review current saved settings]");
                }
            }
            if let Some((complete, message)) = &ui.indexing_outcome {
                page.heading("INDEXING RESULT");
                page.toned(
                    message.clone(),
                    if *complete {
                        Tone::Success
                    } else {
                        Tone::Warning
                    },
                );
                page.text("");
            }
            if ui.saved_session {
                page.heading("CONFIGURATION SAVED - choose what happens next");
                page.info(format!(
                    "Indexing runs here using {:?}.",
                    draft.policy.embeddings.backend
                ));
                if draft.policy.embeddings.backend != EmbeddingProvider::Local {
                    page.muted("Hosted embeddings send selected text to that provider.");
                }
                if ui.indexing_outcome.is_none() {
                    add_recommendation(&mut page, draft);
                }
                add_preview(&mut page, draft, false);
                page.text("");
            }
            page.setting(
                ui,
                Action::Edit(Field::Name),
                format!(
                    "Name          {}  [{}]",
                    draft.policy.name,
                    provenance(draft, Field::Name)
                ),
                field_help(draft, Field::Name, path),
            );
            page.text("");
            let provider = draft.policy.embeddings.backend;
            page.setting(
                ui,
                Action::Edit(Field::Backend),
                format!(
                    "Provider      {:?} / {}  [{}]",
                    provider,
                    provider.model_identity(),
                    provenance(draft, Field::Backend)
                ),
                field_help(draft, Field::Backend, path),
            );
            if !ui.saved_session {
                page.muted(if provider == EmbeddingProvider::Local {
                    "  Local; first use may download the model. No hosted API key."
                } else {
                    "  Hosted; selected text is sent to this provider."
                });
            }
            if provider != EmbeddingProvider::Local {
                page.toned(
                    format!(
                        "  API key: {}",
                        credential_label(credential_status(draft, provider))
                    ),
                    if key_ready(draft) {
                        Tone::Muted
                    } else {
                        Tone::Warning
                    },
                );
            }
            if !key_ready(draft) {
                page.warning("  Set up in another terminal: muninn config edit --global");
                page.muted("  Set matching embeddings.backend/model/api_key, then Rescan here.");
            }
            let delay_default = global_field(draft, Field::Debounce)
                .or_else(|| saved_field(draft, Field::Debounce))
                .unwrap_or_else(|| "?".into());
            let request_default = global_field(draft, Field::Batch)
                .or_else(|| saved_field(draft, Field::Batch))
                .unwrap_or_else(|| "?".into());
            page.setting(ui, Action::Advanced,
                format!("{} Advanced   Delay {} ms · Request {} chunks", if ui.advanced { "[-]" } else { "[+]" }, draft.policy.watcher.debounce_ms, draft.policy.embeddings.batch_size),
                "Delay waits for edits to settle; request size controls text chunks per embedding call. Enter to edit these family settings.");
            page.muted(format!(
                "  {}: delay {delay_default} ms · request {request_default}",
                if global_defaults(draft).is_object() {
                    if draft.family_id().is_some() {
                        "Global defaults now"
                    } else {
                        "Global defaults (copied)"
                    }
                } else if draft.family_id().is_some() {
                    "Saved values"
                } else {
                    "Initial values"
                }
            ));
            if ui.advanced {
                page.setting(
                    ui,
                    Action::Edit(Field::Debounce),
                    format!(
                        "Change delay  {} ms  [{}]",
                        draft.policy.watcher.debounce_ms,
                        provenance(draft, Field::Debounce)
                    ),
                    field_help(draft, Field::Debounce, path),
                );
                page.setting(
                    ui,
                    Action::Edit(Field::Batch),
                    format!(
                        "Request size  {} text chunks  [{}]",
                        draft.policy.embeddings.batch_size,
                        provenance(draft, Field::Batch)
                    ),
                    field_help(draft, Field::Batch, path),
                );
            }
            page.text("");
            for axis in [Axis::Exclude, Axis::Vendor] {
                let custom = axis.rules(draft);
                let examples = if custom.is_empty() {
                    "none".into()
                } else {
                    custom
                        .iter()
                        .take(2)
                        .cloned()
                        .collect::<Vec<_>>()
                        .join(", ")
                };
                page.setting(
                    ui,
                    Action::Rules(axis),
                    format!(
                        "{}  {} + {} custom ({examples})",
                        axis.label(),
                        rule_source(draft, axis),
                        custom.len()
                    ),
                    field_help(draft, axis.add_field(), path),
                );
                add_rule_patterns(&mut page, draft, axis, true);
                page.text("");
            }
            page.muted(
                "  Frozen defaults stay active; custom rules run last. .gitignore is not used.",
            );
            if !ui.saved_session {
                page.text("");
                add_preview(&mut page, draft, false);
                add_recommendation(&mut page, draft);
            }
            page.control(Action::Check, "[Rescan files and API-key status]");
            page.control(Action::Open(View::Message), "[Scan details]");
            if draft.base["reconciliation_needed"] == true
                && draft.base["reconciliation_scheduled"] == false
            {
                page.warning("Warning: index reconciliation is needed but has not been scheduled.");
            }
            if ui.saved_session {
                page.button(
                    Action::Start,
                    if !key_ready(draft) {
                        "Start unavailable: API key"
                    } else if draft.checked.is_none() || draft.dirty() {
                        "Start unavailable: Rescan"
                    } else if ui
                        .indexing_outcome
                        .as_ref()
                        .is_some_and(|(completed, _)| *completed)
                    {
                        "Run indexing again"
                    } else if ui
                        .indexing_outcome
                        .as_ref()
                        .is_some_and(|(completed, _)| !*completed)
                    {
                        "Retry indexing"
                    } else if draft.base["indexing_enabled"] == true {
                        "Run indexing"
                    } else {
                        "Start indexing"
                    },
                );
                page.button(Action::EditMore, "Edit more");
                page.button(Action::Open(View::Agent), "Ask an agent");
                page.button(
                    Action::Close,
                    if draft.base["indexing_enabled"] == true {
                        "Leave"
                    } else {
                        "Leave unindexed"
                    },
                );
            } else {
                page.button(Action::Save, "Save configuration...");
                page.button(Action::Close, "Cancel");
            }
        }
        View::Rules => {
            page.text(format!("{} / custom rules", ui.axis.label()));
            add_rule_patterns(&mut page, draft, ui.axis, false);
            page.text("");
            page.heading("Edit custom rules");
            page.text("Frozen default rules run first. These rules run afterward, in this order.");
            page.text("");
            if ui.axis.rules(draft).is_empty() {
                page.text(format!(
                    "No custom rules. {} frozen default rules remain active.",
                    ui.axis.defaults(draft).len()
                ));
            }
            for (i, rule) in ui.axis.rules(draft).iter().enumerate() {
                page.control(Action::Rule(i), format!("{}. {rule}", i + 1));
            }
            page.control(Action::AddRule, "[Add rule...]");
            page.text("");
            page.text("Enter a rule to edit, reorder or remove it. Later matches win.");
            page.text(match ui.axis {
                Axis::Exclude => {
                    "A leading ! reverses an exclusion. Reopen an excluded parent before its child."
                }
                Axis::Vendor => {
                    "A leading ! returns matching files to the primary tier; exclusions still win."
                }
            });
            page.button(Action::Back, "Back");
            page.button(Action::Defaults(ui.axis), "View frozen defaults");
        }
        View::Defaults => {
            page.text(format!(
                "{} / frozen default rules (read only)",
                ui.axis.label()
            ));
            page.text(format!(
                "Frozen rule set: {}. Custom rules run after this list.",
                draft.defaults.revision
            ));
            page.text("These are active even when your custom list is empty.");
            page.text("");
            let global_count = global_rule_count(draft, ui.axis);
            let shipped_count = ui
                .axis
                .defaults(draft)
                .len()
                .saturating_sub(global_count.unwrap_or(0));
            for (i, rule) in ui.axis.defaults(draft).iter().enumerate() {
                let source = match global_count {
                    Some(_) if i >= shipped_count => "global snapshot",
                    Some(_) => "shipped",
                    None => "frozen default",
                };
                page.text(format!("{:>2}. {rule}  [{source}]", i + 1));
            }
            page.button(Action::Back, "Back");
            page.button(Action::Rules(ui.axis), "Edit custom rules");
        }
        View::Message => {
            if !draft.status.is_empty() {
                page.text("LATEST MESSAGE");
                page.text(draft.status.clone());
                page.text("");
            }
            add_preview(&mut page, draft, true);
            page.button(Action::Back, "Back");
            page.button(Action::RefreshCurrent, "Review current settings");
        }
        View::Details => {
            page.text("CONFIGURATION DETAILS");
            for line in summary_changes(draft) {
                page.text(line);
            }
            page.text(format!("Selected checkout: {}", path.display()));
            page.text(format!(
                "Family: {}",
                draft.base["family_id"].as_str().unwrap_or("Not registered")
            ));
            page.text(format!(
                "Saved revision: {}",
                draft
                    .revision()
                    .map(|n| n.to_string())
                    .unwrap_or_else(|| "None".into())
            ));
            page.text(format!("Frozen default rules: {}", draft.defaults.revision));
            page.text(format!(
                "Indexing enabled: {}",
                flag(&draft.base["indexing_enabled"])
            ));
            page.text(format!("Family paused: {}", flag(&draft.base["paused"])));
            page.text(format!(
                "Selected checkout paused: {}",
                flag(&draft.base["checkout"]["paused"])
            ));
            if !draft.status.is_empty() {
                page.text("");
                page.text("LATEST MESSAGE");
                page.text(draft.status.clone());
            }
            page.button(Action::Back, "Back");
            page.button(Action::RefreshCurrent, "Review current settings");
        }
        View::Conflict => {
            page.text("REVIEW CURRENT SAVED SETTINGS");
            page.text("Your draft has not changed. Compare before choosing what to keep.");
            if let Some(latest) = &draft.latest {
                page.text(format!(
                    "Original revision: {} | Current revision: {}",
                    display_value(&draft.base["revision"]),
                    display_value(&latest["revision"])
                ));
                let candidate = serde_json::to_value(&draft.policy).unwrap();
                if latest["family_id"] != draft.base["family_id"] {
                    page.text("Family identity changed. Keeping this draft against it is blocked.");
                }
                let mut differences = false;
                for (label, original, current, ours) in [
                    (
                        "Name",
                        &draft.base["policy"]["name"],
                        &latest["policy"]["name"],
                        &candidate["name"],
                    ),
                    (
                        "Change delay",
                        &draft.base["policy"]["watcher"]["debounce_ms"],
                        &latest["policy"]["watcher"]["debounce_ms"],
                        &candidate["watcher"]["debounce_ms"],
                    ),
                    (
                        "Provider",
                        &draft.base["policy"]["embeddings"]["backend"],
                        &latest["policy"]["embeddings"]["backend"],
                        &candidate["embeddings"]["backend"],
                    ),
                    (
                        "Model",
                        &draft.base["policy"]["embeddings"]["model"],
                        &latest["policy"]["embeddings"]["model"],
                        &candidate["embeddings"]["model"],
                    ),
                    (
                        "Batch size",
                        &draft.base["policy"]["embeddings"]["batch_size"],
                        &latest["policy"]["embeddings"]["batch_size"],
                        &candidate["embeddings"]["batch_size"],
                    ),
                    (
                        "Exclusions",
                        &draft.base["policy"]["index"]["exclude"],
                        &latest["policy"]["index"]["exclude"],
                        &candidate["index"]["exclude"],
                    ),
                    (
                        "Vendor rules",
                        &draft.base["policy"]["index"]["vendor"],
                        &latest["policy"]["index"]["vendor"],
                        &candidate["index"]["vendor"],
                    ),
                ] {
                    if original != current || ours != current {
                        differences = true;
                        page.text("");
                        page.text(label);
                        let display = |v: &serde_json::Value| {
                            if v.is_array() {
                                display_rules(v)
                            } else {
                                display_value(v)
                            }
                        };
                        page.text(format!("  Original: {}", display(original)));
                        page.text(format!("  Current:  {}", display(current)));
                        page.text(format!("  Draft:    {}", display(ours)));
                    }
                }
                if !differences {
                    page.text("No policy differences.");
                }
                page.text("");
                page.text("Keeping your full draft is not a merge. A later save replaces the current policy, including changes made elsewhere.");
                page.control(Action::LoadCurrent, "[Discard draft and load current...]");
                if latest["family_id"] == draft.base["family_id"] && draft.family_id().is_some() {
                    page.control(Action::KeepDraft, "[Keep my full draft against current...]");
                }
            }
            page.button(Action::Back, "Keep editing");
        }
        View::Help => {
            page.text("KEYBOARD");
            page.text(
                "Tab / Shift+Tab: move between controls. Enter: activate the focused control.",
            );
            page.text("Up / Down: move between settings and actions. The main form has no tabs.");
            page.text("Page Up / Page Down: scroll long content. Esc: back or cancel.");
            page.text("At the main screen, Esc closes; unsaved changes require confirmation.");
            page.text("In text fields: arrows, Home/End, Backspace/Delete, Ctrl-U to clear.");
            page.text("Enter accepts a field into the draft, not into saved configuration.");
            page.text("");
            page.text("DEFAULTS AND SCOPE");
            page.text("Family settings apply to this repository and all its worktrees.");
            page.text("The file preview scans only the selected checkout.");
            page.text("New families copy global provider, request-size, delay and file-rule defaults at creation. Later global edits do not replace saved family settings.");
            page.text("Shipped and global exclusion/vendor defaults are captured at creation and frozen for each family. Custom rules follow them; last matching rule wins.");
            page.text(".gitignore does not control selection. Vendor rules keep files in text search without initial embeddings.");
            page.text(
                "After Save, choose Start, Edit more, Ask an agent, or Leave unindexed. Saving an enabled family can cause index updates.",
            );
            page.control(Action::Open(View::Agent), "[Agent help and JSON commands]");
            page.control(
                Action::Open(View::Details),
                "[Configuration details and current saved settings]",
            );
            page.button(Action::Back, "Back");
        }
        View::Agent => {
            let target = shell_path(path);
            page.text("AGENT HELP (nothing runs here)");
            page.text("Ask an agent to review file rules and the largest selected directories.");
            page.text("These commands are for Bash/Zsh. Review every proposed change.");
            page.text(format!("muninn preflight {target} --json"));
            page.text(format!("muninn config {target} --json"));
            page.text(format!(
                "muninn config {target} --check - --json < request.json"
            ));
            page.text(if draft.family_id().is_some() {
                format!("muninn config {target} --apply - --json < request.json")
            } else {
                format!("muninn add {target} --json --input - < request.json")
            });
            page.text("Existing requests require expected_family_id and expected_revision.");
            page.text("New requests require api_version: 1 and a complete policy.");
            page.text(
                "Inspect and check are read only. Saving enabled families can update indexes.",
            );
            page.button(Action::Back, "Back");
        }
    }

    page
}

fn confirmation(
    draft: &Draft,
    ui: &Ui,
    confirm: Confirm,
) -> (String, Vec<String>, &'static str, &'static str) {
    match confirm {
        Confirm::Save => (
            "Save configuration?".into(),
            vec![
                "Settings apply to this repository and all its worktrees.".into(),
                format!(
                    "Embedding profile: {:?} / {}. {}",
                    draft.policy.embeddings.backend,
                    draft.policy.embeddings.backend.model_identity(),
                    if draft.family_id().is_none() {
                        "Provider and model become fixed after this save."
                    } else {
                        "Provider and model remain fixed."
                    }
                ),
                if draft.base["indexing_enabled"] == true {
                    "Indexing is already enabled. Saving can cause indexes to update.".into()
                } else {
                    "This saves configuration only. Indexing will remain off.".into()
                },
                if draft
                    .checked
                    .as_ref()
                    .is_some_and(|v| v["preflight"]["advice"] == "start")
                {
                    "The selected checkout preview suggests starting is suitable.".into()
                } else {
                    "The preview recommends reviewing file rules before indexing.".into()
                },
                "Choose Save configuration to apply these settings.".into(),
            ],
            "Back",
            "Save configuration",
        ),
        Confirm::Discard => (
            "Discard unsaved changes?".into(),
            vec![
                "Your unsaved draft will be discarded and this screen will close.".into(),
                "Saved settings will remain as they are.".into(),
            ],
            "Keep editing",
            "Discard and close",
        ),
        Confirm::LoadCurrent => (
            "Discard draft and load current settings?".into(),
            vec![
                "Your unsaved draft will be discarded.".into(),
                "The reviewed current settings will replace it. Nothing is saved by this action."
                    .into(),
            ],
            "Keep editing",
            "Load current settings",
        ),
        Confirm::KeepDraft => (
            "Keep your full draft against the current revision?".into(),
            vec![
                "This is not a merge. Your entire draft is retained against the reviewed revision."
                    .into(),
                "A later save replaces the whole current policy, including changes made elsewhere."
                    .into(),
                "Nothing is saved yet; review and save explicitly afterward.".into(),
            ],
            "Back",
            "Keep full draft",
        ),
        Confirm::RemoveRule(index) => (
            "Remove this custom rule?".into(),
            vec![
                ui.axis.rules(draft).get(index).cloned().unwrap_or_default(),
                "This changes your draft. Frozen default rules remain active.".into(),
            ],
            "Keep rule",
            "Remove rule",
        ),
    }
}
/// Escape controls and prefer word boundaries, hard-wrapping long paths/globs.
/// Keep boundary whitespace so concatenating the rows preserves the input.
fn wrap_lines(lines: Vec<String>, width: usize) -> Vec<String> {
    let width = width.max(1);
    let mut result = Vec::new();
    for line in lines {
        let mut current = String::new();
        let mut used = 0;
        for c in visible(&line).chars() {
            let size = console::measure_text_width(&c.to_string());
            if used + size > width && !current.is_empty() {
                let boundary = if c.is_whitespace() {
                    None
                } else {
                    current.char_indices().rev().find_map(|(index, ch)| {
                        (ch.is_whitespace()
                            && current[..index]
                                .chars()
                                .any(|before| !before.is_whitespace()))
                        .then_some(index + ch.len_utf8())
                    })
                };
                if let Some(boundary) = boundary {
                    let remainder = current.split_off(boundary);
                    result.push(std::mem::replace(&mut current, remainder));
                    used = console::measure_text_width(&current);
                } else {
                    result.push(std::mem::take(&mut current));
                    used = 0;
                }
                if used + size > width && !current.is_empty() {
                    result.push(std::mem::take(&mut current));
                    used = 0;
                }
            }
            current.push(c);
            used += size;
        }
        result.push(current);
    }
    result
}
fn edit_window(chars: &[char], cursor: usize, width: usize) -> String {
    let mut start = cursor;
    let mut used = 1;
    while start > 0 {
        let size = console::measure_text_width(&visible(&chars[start - 1].to_string()));
        if used + size > width.saturating_sub(4) {
            break;
        }
        start -= 1;
        used += size;
    }
    let text = format!(
        "{}{}|{}",
        if start > 0 { "…" } else { "" },
        chars[start..cursor].iter().collect::<String>(),
        chars[cursor..].iter().collect::<String>()
    );
    clip_line(&visible(&text), width)
}
/// console 0.15 reserves the ellipsis even for text that already fits.
/// Keep complete lines intact, and only add an ellipsis for actual overflow.
fn clip_line(text: &str, width: usize) -> String {
    if width == 0 {
        String::new()
    } else if console::measure_text_width(text) <= width {
        text.to_owned()
    } else {
        console::truncate_str(text, width, "…").into_owned()
    }
}
fn button_frame(buttons: &[(bool, String)], width: usize) -> Vec<RenderLine> {
    let mut lines = Vec::new();
    let mut line = String::new();
    let mut focused_line = false;
    for (focused, label) in buttons {
        let button = format!("{}[{label}]", if *focused { "> " } else { "  " });
        if !line.is_empty()
            && console::measure_text_width(&line)
                + console::measure_text_width(&visible(&button))
                + 2
                > width
        {
            let tone = if focused_line {
                Tone::Focus
            } else {
                Tone::Normal
            };
            lines.extend(
                wrap_lines(vec![std::mem::take(&mut line)], width)
                    .into_iter()
                    .map(|text| RenderLine::new(text, tone)),
            );
            focused_line = false;
        }
        if !line.is_empty() {
            line.push_str("  ");
        }
        line.push_str(&button);
        focused_line |= *focused;
    }
    if !line.is_empty() {
        let tone = if focused_line {
            Tone::Focus
        } else {
            Tone::Normal
        };
        lines.extend(
            wrap_lines(vec![line], width)
                .into_iter()
                .map(|text| RenderLine::new(text, tone)),
        );
    }
    lines
}
fn append_frame(text: &mut Vec<String>, tones: &mut Vec<Tone>, lines: Vec<RenderLine>) {
    for line in lines {
        text.push(line.text);
        tones.push(line.tone);
    }
}
/// Wrap explanatory rows with a hanging indent while retaining all text.
fn wrap_row(text: String, width: usize, indent: usize) -> Vec<String> {
    if indent == 0 {
        return wrap_lines(vec![text], width);
    }
    let prefix = " ".repeat(indent.min(width.saturating_sub(1)));
    let text = text.strip_prefix(&prefix).unwrap_or(&text);
    wrap_lines(
        vec![text.to_owned()],
        width.saturating_sub(prefix.len()).max(1),
    )
    .into_iter()
    .map(|line| format!("{prefix}{line}"))
    .collect()
}
fn state_label(draft: &Draft) -> String {
    if draft.family_id().is_none() {
        if draft.dirty() {
            "New configuration · Unsaved changes".into()
        } else {
            "New configuration · Not saved".into()
        }
    } else if draft.dirty() {
        format!(
            "Unsaved changes · Based on revision {}",
            draft.revision().unwrap()
        )
    } else {
        format!("Saved · Revision {}", draft.revision().unwrap())
    }
}
fn indexing_label(draft: &Draft) -> &'static str {
    if draft.base["paused"] == true {
        "Indexing paused for this family"
    } else if draft.base["checkout"]["paused"] == true {
        "Selected checkout paused"
    } else if draft.base["indexing_enabled"] == true {
        "Indexing enabled"
    } else {
        "Indexing has not started"
    }
}
/// Fixed help region, independent of form scrolling. Overflow is explicit.
fn help_panel(
    label: &str,
    text: &str,
    width: usize,
    rows: usize,
    offset: usize,
    more: &str,
) -> Vec<RenderLine> {
    if rows < 2 {
        return Vec::new();
    }
    let wrapped = wrap_row(text.into(), width, 2);
    let capacity = rows - 1;
    let offset = offset.min(wrapped.len().saturating_sub(capacity));
    let overflow = wrapped.len() > capacity;
    let suffix = if overflow {
        format!(" · {more}")
    } else {
        String::new()
    };
    let label = clip_line(
        &visible(label),
        width.saturating_sub(console::measure_text_width(&suffix) + 9),
    );
    let title = format!("─ About: {label}{suffix}");
    let title = format!(
        "{title} {}",
        "─".repeat(width.saturating_sub(console::measure_text_width(&title) + 1))
    );
    let mut result = vec![RenderLine::new(
        clip_line(&visible(&title), width),
        Tone::Heading,
    )];
    result.extend(
        wrapped
            .into_iter()
            .skip(offset)
            .take(capacity)
            .map(|text| RenderLine::new(text, Tone::Normal)),
    );
    while result.len() < rows {
        result.push(RenderLine::new("", Tone::Normal));
    }
    result
}
fn help_rows(height: usize) -> usize {
    if height >= 29 {
        6
    } else if height >= 23 {
        5
    } else {
        4
    }
}
fn focused_help(draft: &Draft, ui: &Ui, path: &Path) -> (String, String) {
    let actions = page(draft, ui, path).actions();
    let action = actions.get(ui.focus).copied().unwrap_or(Action::Close);
    let field = match action {
        Action::Edit(field) => Some(field),
        Action::Rules(axis) | Action::Defaults(axis) => Some(axis.add_field()),
        Action::Rule(index) => Some(ui.axis.field(index)),
        Action::AddRule => Some(ui.axis.add_field()),
        _ => None,
    };
    if let Some(field) = field {
        return (field_label(field).into(), field_help(draft, field, path));
    }
    let (label,text)=match action {
        Action::Advanced=>("Advanced settings","Show or hide watcher delay and embedding request size. Their values and global reference defaults remain visible."),
        Action::Save=>("Save configuration","Save the repository-family settings. This does not start first indexing; afterward choose Start, Edit more, Ask an agent, or Leave unindexed. Saving an already-enabled family may reconcile its index."),
        Action::Start=>("Start indexing","Explicitly enable indexing for this family and run a foreground pass. Credentials, revision and file inventory are checked again. Hosted providers receive selected text. Completion is reported after publication."),
        Action::Check=>("Rescan","Refresh this checkout's file inventory and global API-key availability without saving settings or starting indexing."),
        Action::Close=>("Cancel","Close this form. Unsaved changes require an explicit discard confirmation."),
        Action::EditMore=>("Edit more","Return to settings while keeping the saved configuration. Indexing remains unstarted until you explicitly choose Start."),
        _=>("Configuration","Settings apply to this repository's worktree family. Saved global defaults are snapshots; custom patterns run afterward. PgUp/PgDn scroll settings; ? opens this explanation in full."),
    };
    (label.into(), text.into())
}

/// Pure terminal layout: useful for checking narrow screens without terminal IO.
fn render_frame(
    draft: &mut Draft,
    ui: &mut Ui,
    path: &Path,
    width: usize,
    height: usize,
) -> Vec<RenderLine> {
    let width = width.saturating_sub(1).max(1);
    let height = height.saturating_sub(1).max(1);
    let narrow = width < 59;
    let title = clip_line(&visible(&format!("Muninn / {}", draft.policy.name)), width);
    let mut header = vec![title.clone()];
    header.extend(wrap_lines(
        vec![format!(
            "{} · {}",
            state_label(draft),
            indexing_label(draft)
        )],
        width,
    ));
    header.push("Settings: all worktrees · Scan: this checkout".into());
    header.push(String::new());
    if height < 18 {
        header = vec![
            title.clone(),
            clip_line(
                &format!("{} · {}", state_label(draft), indexing_label(draft)),
                width,
            ),
        ];
    }
    let mut footer = Vec::new();
    let mut footer_tones = Vec::new();
    let mut content = Vec::new();
    let mut content_tones = Vec::new();
    let mut focused_range = None;
    let small = width < 51 || height < 13;
    if let Some(modal) = &ui.modal {
        // Dialogs remain operable even below the normal editing minimum.
        header.clear();
        match modal {
            Modal::Docs(label, text) => {
                header.push(format!("About: {label}"));
                content.push(text.clone());
                footer.push("PgUp/PgDn: scroll · Enter/Esc: back · ?: controls".into());
            }
            Modal::Edit(field, chars, cursor) => {
                header.extend(wrap_lines(
                    vec![format!("Edit {}", field_label(*field))],
                    width,
                ));
                content.push(edit_window(chars, *cursor, width));

                content.push(String::new());
                if draft.family_id().is_some() {
                    let original = match field {
                        Field::Name => display_value(&draft.base["policy"]["name"]),
                        Field::Debounce => {
                            display_value(&draft.base["policy"]["watcher"]["debounce_ms"])
                        }
                        Field::Batch => {
                            display_value(&draft.base["policy"]["embeddings"]["batch_size"])
                        }
                        _ => String::new(),
                    };
                    if !original.is_empty() {
                        content.push(format!("Saved value: {original}"));
                    }
                }
                content
                    .push("Enter accepts this value into your draft. Nothing is saved yet.".into());
                if matches!(
                    field,
                    Field::Exclude(_) | Field::Vendor(_) | Field::AddExclude | Field::AddVendor
                ) {
                    content.push(
                        "Paths are relative to the checkout. Later matches win; ! reverses a rule."
                            .into(),
                    );
                }
                if ui.notice_error {
                    content.insert(1, format!("Error: {}", draft.status));
                }
                footer.extend(wrap_lines(
                    vec!["Enter: accept · Esc: cancel · Ctrl-U: clear".into()],
                    width,
                ));
            }
            Modal::Backend(index) => {
                header.extend(wrap_lines(
                    vec!["Embedding provider - fixed after Save".into()],
                    width,
                ));
                for (i, provider) in [
                    EmbeddingProvider::Voyage,
                    EmbeddingProvider::OpenAI,
                    EmbeddingProvider::Local,
                ]
                .into_iter()
                .enumerate()
                {
                    let start = content.len();
                    content.push(format!(
                        "{} {:?} / {}{}",
                        if i == *index { ">" } else { " " },
                        provider,
                        provider.model_identity(),
                        if global_field(draft, Field::Backend).as_deref()
                            == Some(provider_key(provider))
                        {
                            " (global default)"
                        } else if global_field(draft, Field::Backend).is_none()
                            && saved_field(draft, Field::Backend).as_deref()
                                == Some(provider_key(provider))
                        {
                            " (initial value)"
                        } else {
                            ""
                        }
                    ));
                    content_tones.resize(content.len() - 1, Tone::Muted);
                    content_tones.push(if i == *index {
                        Tone::Focus
                    } else {
                        Tone::Normal
                    });
                    content.push(if provider == EmbeddingProvider::Local {
                        "  Runs locally; first use may download the model. No API key needed."
                            .into()
                    } else {
                        format!(
                            "  Hosted: sends selected text. API key: {}",
                            credential_label(credential_status(draft, provider))
                        )
                    });
                    content_tones.push(if provider_key_ready(draft, provider) {
                        Tone::Muted
                    } else {
                        Tone::Warning
                    });
                    if i == *index {
                        focused_range = Some(start..content.len());
                        if !provider_key_ready(draft, provider) {
                            for line in credential_help(provider) {
                                content.push(line);
                            }
                        }
                    }
                    content.push(String::new());
                }
                footer.extend(wrap_lines(
                    vec!["Up/Down: choose · Enter: accept · Esc: cancel".into()],
                    width,
                ));
            }
            Modal::Rule(index, choice) => {
                header.push("Custom rule actions".into());
                content.push(
                    ui.axis
                        .rules(draft)
                        .get(*index)
                        .cloned()
                        .unwrap_or_default(),
                );
                for (i, label) in [
                    "Edit rule",
                    "Move up",
                    "Move down",
                    "Remove rule...",
                    "Back",
                ]
                .iter()
                .enumerate()
                {
                    let start = content.len();
                    content.push(format!("{} {label}", if i == *choice { ">" } else { " " }));
                    if i == *choice {
                        focused_range = Some(start..start + 1);
                    }
                }
                footer.extend(wrap_lines(
                    vec!["Up/Down: choose · Enter: open · Esc: back".into()],
                    width,
                ));
            }
            Modal::Confirm(confirm, choice) => {
                let (title, text, cancel, accept) = confirmation(draft, ui, *confirm);
                header.extend(wrap_lines(vec![title], width));
                content = text;
                append_frame(
                    &mut footer,
                    &mut footer_tones,
                    button_frame(
                        &[(*choice == 0, cancel.into()), (*choice == 1, accept.into())],
                        width,
                    ),
                );
                footer.extend(wrap_lines(
                    vec!["Tab: choose · Enter: confirm · Esc: back".into()],
                    width,
                ));
            }
        }
        let raw_focus = focused_range.take();
        content_tones.resize(content.len(), Tone::Muted);
        match ui.modal.as_ref() {
            Some(Modal::Edit(..)) => {
                content_tones[0] = Tone::Focus;
                if ui.notice_error {
                    content_tones[1] = Tone::Error;
                }
            }
            Some(Modal::Rule(..)) => {
                if let Some(range) = &raw_focus {
                    content_tones[range.start] = Tone::Focus;
                }
            }
            _ => {}
        }
        let mut wrapped = Vec::new();
        let mut wrapped_tones = Vec::new();
        for (index, (text, tone)) in content.into_iter().zip(content_tones).enumerate() {
            let start = wrapped.len();
            let lines = wrap_lines(vec![text], width);
            wrapped_tones.extend(std::iter::repeat_n(tone, lines.len()));
            wrapped.extend(lines);
            if raw_focus.as_ref().is_some_and(|r| r.start == index) {
                focused_range = Some(start..wrapped.len());
            }
            if raw_focus.as_ref().is_some_and(|r| r.end == index + 1) {
                if let Some(range) = focused_range.as_mut() {
                    range.end = wrapped.len();
                }
            }
        }
        content_tones = wrapped_tones;
        content = wrapped;
        footer_tones.resize(footer.len(), Tone::Muted);
        if let Modal::Edit(field, chars, cursor) = modal {
            if !content.is_empty() {
                content.remove(0);
                content_tones.remove(0);
            }
            let rows =
                help_rows(height).min(height.saturating_sub(header.len() + footer.len() + 2));
            ui.help_scroll = ui.help_scroll.min(
                wrap_row(field_help(draft, *field, path), width, 2)
                    .len()
                    .saturating_sub(rows.saturating_sub(1)),
            );
            let panel = help_panel(
                field_label(*field),
                &field_help(draft, *field, path),
                width,
                rows,
                ui.help_scroll,
                "PgUp/PgDn: help",
            );
            let mut pinned = vec![RenderLine::new(
                edit_window(chars, *cursor, width),
                Tone::Focus,
            )];
            pinned.extend(panel);
            let old = std::mem::take(&mut footer);
            let tones = std::mem::take(&mut footer_tones);
            append_frame(&mut footer, &mut footer_tones, pinned);
            footer.extend(old);
            footer_tones.extend(tones);
        }
        if let Some(field) = match modal {
            Modal::Backend(_) => Some(Field::Backend),
            Modal::Rule(index, _) => Some(ui.axis.field(*index)),
            _ => None,
        } {
            let rows =
                help_rows(height).min(height.saturating_sub(header.len() + footer.len() + 4));
            let panel = help_panel(
                field_label(field),
                &field_help(draft, field, path),
                width,
                rows,
                0,
                "? more",
            );
            let old = std::mem::take(&mut footer);
            let tones = std::mem::take(&mut footer_tones);
            append_frame(&mut footer, &mut footer_tones, panel);
            footer.extend(old);
            footer_tones.extend(tones);
        }
        // Keep all dialog actions visible. At tiny sizes, scroll the explanation.
        let mut room = height.saturating_sub(header.len() + footer.len()).max(1);
        if content.len() > room {
            footer.insert(0, "PgUp/PgDn: more".into());
            footer_tones.insert(0, Tone::Muted);
            room = height.saturating_sub(header.len() + footer.len()).max(1);
        }
        let max_scroll = content.len().saturating_sub(room);
        ui.modal_scroll = ui.modal_scroll.min(max_scroll);
        if let Some(range) = focused_range.filter(|_| ui.follow_focus) {
            if range.start < ui.modal_scroll {
                ui.modal_scroll = range.start;
            }
            if range.end > ui.modal_scroll + room {
                ui.modal_scroll = range.end.saturating_sub(room);
            }
        }
        ui.follow_focus = false;
        let mut lines: Vec<_> = header
            .into_iter()
            .map(|text| RenderLine::new(text, Tone::Heading))
            .collect();
        lines.extend(
            content
                .into_iter()
                .zip(content_tones)
                .skip(ui.modal_scroll)
                .take(room)
                .map(|(text, tone)| RenderLine::new(text, tone)),
        );
        while lines.len() + footer.len() < height {
            lines.push(RenderLine::new("", Tone::Normal));
        }
        lines.extend(
            footer
                .into_iter()
                .zip(footer_tones)
                .map(|(text, tone)| RenderLine::new(text, tone)),
        );
        if lines.len() > height {
            lines.drain(..lines.len() - height);
        }
        return lines;
    }
    if small {
        return wrap_lines(
            vec![
                "Terminal too small for editing.".into(),
                "Resize to at least 52 x 14.".into(),
                if draft.dirty() {
                    "Unsaved draft retained.".into()
                } else {
                    state_label(draft)
                },
                "Esc: close (asks before discarding changes)".into(),
            ],
            width,
        )
        .into_iter()
        .take(height)
        .map(|text| RenderLine::new(text, Tone::Info))
        .collect();
    }
    let current = page(draft, ui, path);
    let actions = current.actions();
    ui.focus = ui.focus.min(actions.len() - 1);
    let mut control_index = 0;
    for row in current.rows {
        let start = content.len();
        let text = if row.action.is_some() {
            let selected = control_index == ui.focus;
            control_index += 1;
            format!("{} {}", if selected { ">" } else { " " }, row.text)
        } else {
            row.text
        };
        let tone = if row.action.is_some() && control_index - 1 == ui.focus {
            Tone::Focus
        } else {
            row.tone
        };
        let indent = if row.follow
            || matches!(row.tone, Tone::Muted | Tone::Warning) && text.starts_with("  ")
        {
            2
        } else {
            0
        };
        let wrapped = wrap_row(text, width, indent);
        content_tones.extend(std::iter::repeat_n(tone, wrapped.len()));
        content.extend(wrapped);
        if row.action.is_some() && control_index - 1 == ui.focus {
            focused_range = Some(start..content.len());
        } else if row.follow {
            if let Some(range) = focused_range.as_mut() {
                range.end = content.len();
            }
        }
    }
    append_frame(
        &mut footer,
        &mut footer_tones,
        button_frame(
            &current
                .footer
                .iter()
                .enumerate()
                .map(|(i, (_, text))| (ui.focus == control_index + i, text.clone()))
                .collect::<Vec<_>>(),
            width,
        ),
    );
    footer.extend(wrap_lines(
        vec![if narrow {
            "Tab/↑↓: move · Enter: choose · Esc: back · ?: help".into()
        } else {
            "↑/↓ or Tab: move · Enter: edit/choose · Esc: cancel · ?: help".into()
        }],
        width,
    ));
    footer_tones.resize(footer.len(), Tone::Muted);
    let (label, help) = focused_help(draft, ui, path);
    let rows = help_rows(height).min(height.saturating_sub(header.len() + footer.len() + 4));
    let panel = help_panel(&label, &help, width, rows, 0, "? more");
    let old = std::mem::take(&mut footer);
    let tones = std::mem::take(&mut footer_tones);
    append_frame(&mut footer, &mut footer_tones, panel);
    footer.extend(old);
    footer_tones.extend(tones);
    footer_tones.resize(footer.len(), Tone::Muted);
    let room = height
        .saturating_sub(header.len() + footer.len() + 1)
        .max(1);
    draft.scroll = draft.scroll.min(content.len().saturating_sub(room));
    if ui.follow_focus {
        if let Some(range) = focused_range {
            if range.start < draft.scroll {
                draft.scroll = range.start;
            }
            if range.len() > room {
                draft.scroll = range.start;
            } else if range.end > draft.scroll + room {
                draft.scroll = range.end.saturating_sub(room);
            }
        }
    }
    ui.follow_focus = false;
    let total = content.len();
    let mut lines: Vec<_> = header
        .into_iter()
        .enumerate()
        .map(|(index, text)| {
            RenderLine::new(
                text,
                if index == 0 {
                    Tone::Heading
                } else {
                    Tone::Muted
                },
            )
        })
        .collect();
    lines.extend(
        content
            .into_iter()
            .zip(content_tones)
            .skip(draft.scroll)
            .take(room)
            .map(|(text, tone)| RenderLine::new(text, tone)),
    );
    while lines.len() + footer.len() + 1 < height {
        lines.push(RenderLine::new("", Tone::Normal));
    }
    lines.push(RenderLine::new(
        if total > room {
            format!(
                "{}-{} / {} · PgUp/PgDn: scroll",
                draft.scroll + 1,
                (draft.scroll + room).min(total),
                total
            )
        } else {
            "─".repeat(width)
        },
        Tone::Muted,
    ));
    lines.extend(
        footer
            .into_iter()
            .zip(footer_tones)
            .map(|(text, tone)| RenderLine::new(text, tone)),
    );
    lines.into_iter().take(height).collect()
}
#[cfg(test)]
fn render_lines(
    draft: &mut Draft,
    ui: &mut Ui,
    path: &Path,
    width: usize,
    height: usize,
) -> Vec<String> {
    render_frame(draft, ui, path, width, height)
        .into_iter()
        .map(|line| line.text)
        .collect()
}
fn paint_line(line: RenderLine, width: usize) -> String {
    // Escape user text before adding any terminal styling of our own.
    let text = clip_line(&visible(&line.text), width);
    if std::env::var_os("NO_COLOR").is_some() {
        return text;
    }
    match line.tone {
        Tone::Normal => text,
        Tone::Heading => console::style(text).bold().to_string(),
        Tone::Muted => console::style(text).dim().to_string(),
        Tone::Info => console::style(text).blue().to_string(),
        Tone::Warning => console::style(text).yellow().to_string(),
        Tone::Error => console::style(text).red().bold().to_string(),
        Tone::Success => console::style(text).green().to_string(),
        Tone::Focus => console::style(text).cyan().bold().to_string(),
    }
}

fn draw(
    term: &Term,
    draft: &mut Draft,
    path: &Path,
    _add_mode: bool,
    ui: &mut Ui,
) -> std::io::Result<()> {
    let (height, width) = term.size();
    let lines = render_frame(draft, ui, path, width as usize, height as usize);
    let text = lines
        .into_iter()
        .map(|line| paint_line(line, width.saturating_sub(1) as usize))
        .collect::<Vec<_>>()
        .join("\r\n");
    term.write_str(&format!("\x1b[H\x1b[2J{text}"))?;
    term.flush()
}
