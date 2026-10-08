use super::*;
use muninn_core::family_policy::{self as policy, Defaults, Policy};
use serde_json::{json, Value};

fn snapshot(registered: bool) -> Value {
    json!({"family_id":if registered {Some("01234567-89ab-cdef-0123-456789abcdef")}else{None},
        "revision":if registered {Some(1)}else{None}, "policy":Policy::shipped("Fixture".into()),
        "defaults":Defaults::shipped(),"indexing_enabled":false,"paused":false,
        "checkout":{"paused":false},
        "defaults_source":if registered {"stored"}else{"global_snapshot"},
        "global_defaults":{"embeddings":{"backend":"voyage","model":"voyage-code-3","batch_size":64},"watcher":{"debounce_ms":300},"index":{"exclude":[],"vendor":[]}},
        "capabilities":{"credential_availability":"configured_not_verified",
            "credential_availability_by_backend":{"voyage":"configured_not_verified","openai":"missing_for_selected_backend","local":"not_required"},"global_embedding_backend":"voyage"},
        "preflight":{"root":{"display":"/fixture"},"advice":"start","complete":true,
            "counts_are_lower_bounds":false,"stop_reason":null,
            "tier1":{"files":382,"bytes":6710886},"tier2":{"files":38,"bytes":1468006},
            "visited_regular_files":440,"observed_excluded_files":20,"pruned_directories":2,
            "unreadable_entries":0,"skipped_symlinks":0,"reasons":[],
            "candidate_exclusions":[],"largest_files":[],"costly_directories":[],
            "unreadable_samples":[]}})
}
#[test]
fn native_rules_preserve_order_validate_and_invalidate_inventory() {
    let mut draft = Draft::new(snapshot(false)).unwrap();
    draft.edit(Field::AddExclude, "build/".into()).unwrap();
    draft
        .edit(Field::AddExclude, "!build/keep.rs".into())
        .unwrap();
    assert!(draft.checked.is_none());
    draft.selected = draft
        .fields()
        .iter()
        .position(|f| *f == Field::Exclude(1))
        .unwrap();
    draft.move_rule(true);
    assert_eq!(draft.policy.index.exclude, ["!build/keep.rs", "build/"]);
    draft.remove();
    assert_eq!(draft.policy.index.exclude, ["build/"]);
    let before = draft.policy.clone();
    assert!(draft.edit(Field::Debounce, "-1".into()).is_err());
    assert!(draft.edit(Field::Batch, "0".into()).is_err());
    assert!(draft.edit(Field::AddExclude, "[".into()).is_err());
    assert_eq!(draft.policy, before);
    draft.edit(Field::Backend, "local".into()).unwrap();
    assert_eq!(draft.policy.embeddings.model, None);
    let mut existing = Draft::new(snapshot(true)).unwrap();
    assert!(existing.edit(Field::Backend, "local".into()).is_err());
}
#[test]
fn reviewing_conflicts_never_silently_rebases_a_draft() {
    let mut draft = Draft::new(snapshot(true)).unwrap();
    draft.edit(Field::Name, "My draft".into()).unwrap();
    let mut latest = snapshot(true);
    latest["revision"] = json!(2);
    latest["policy"]["name"] = json!("Concurrent edit");
    report_error(
        &mut draft,
        crate::readonly::error("revision_conflict", "stale revision"),
    );
    draft.receive_latest(latest);
    assert_eq!(draft.request()["expected_revision"], 1);
    assert_eq!(draft.policy.name, "My draft");
    draft.keep_draft_on_latest().unwrap();
    assert_eq!(draft.request()["expected_revision"], 2);
    assert_eq!(draft.policy.name, "My draft");
    assert!(draft.checked.is_none());
    let mut replacement = snapshot(true);
    replacement["family_id"] = json!(uuid::Uuid::new_v4());
    draft.receive_latest(replacement);
    assert!(draft.keep_draft_on_latest().is_err());
    assert_eq!(draft.request()["expected_revision"], 2);
}
#[test]
fn long_rules_and_terminal_controls_remain_inspectable() {
    assert_eq!(visible("a\x1b[31m\nb"), "a\\u{1b}[31m\\nb");
    let source = "日本語".repeat(50) + "\x1b";
    let wrapped = wrap_lines(vec![source.clone()], 20);
    assert_eq!(wrapped.concat(), visible(&source));
    assert!(wrapped.iter().all(|s| console::measure_text_width(s) <= 20));
    let chars: Vec<_> = source.chars().collect();
    let window = edit_window(&chars, chars.len(), 30);
    assert!(window.contains('|'));
    assert!(console::measure_text_width(&window) <= 30);
    assert_eq!(shell_path(Path::new("/a'b")), "'/a'\\''b'");
    #[cfg(unix)]
    {
        use std::os::unix::ffi::OsStrExt;
        assert_eq!(
            shell_path(Path::new(std::ffi::OsStr::from_bytes(b"a\xff\n"))),
            "$'\\x61\\xff\\x0a'"
        );
    }
}

#[test]
fn complete_terminal_lines_do_not_lose_their_last_character() {
    for line in [
        "─".repeat(79),
        "日本語".repeat(3),
        "[Discard and close]".into(),
    ] {
        let width = console::measure_text_width(&line);
        assert_eq!(clip_line(&line, width), line);
        let clipped = clip_line(&line, width - 1);
        assert!(console::measure_text_width(&clipped) < width);
        assert!(clipped.ends_with('…'));
    }
    assert_eq!(clip_line("value", 0), "");
}

#[test]
fn file_selection_explains_active_defaults_and_partial_previews() {
    let mut draft = Draft::new(snapshot(false)).unwrap();
    draft.view = View::Policy;
    let ui = Ui::default();
    let content = page(&draft, &ui, Path::new("/fixture"))
        .rows
        .into_iter()
        .map(|row| row.text)
        .collect::<Vec<_>>()
        .join("\n");
    assert!(content.contains("12") && content.contains("0 custom"));
    assert!(content.contains("11") && content.contains("0 custom"));
    assert!(content.contains(".gitignore is not used"));
    assert!(
        field_help(&draft, Field::AddVendor, Path::new("/fixture")).contains("kept in text search")
    );
    let preview = draft.checked.as_mut().unwrap();
    preview["preflight"]["complete"] = json!(false);
    preview["preflight"]["counts_are_lower_bounds"] = json!(true);
    preview["preflight"]["stop_reason"] = json!("entry_limit");
    let content = preview_lines(&draft, false).join("\n");
    assert!(content.contains("PARTIAL PREVIEW"));
    assert!(content.contains("at least 382"));
    assert!(content.contains("entry") && content.contains("limit"));
    assert_eq!(
        credential_status(&draft, policy::Backend::Voyage),
        "configured_not_verified"
    );
    draft.edit(Field::Name, "Changed".into()).unwrap();
    let stale = preview_lines(&draft, false).join("\n");
    assert!(stale.contains("out of date"));
    assert!(!stale.contains("382"));
}

#[test]
fn inventory_guides_the_next_choice_without_applying_suggestions() {
    let mut draft = Draft::new(snapshot(true)).unwrap();
    assert_eq!(recommended_action(&draft), Action::Start);
    let checked = draft.checked.as_mut().unwrap();
    checked["preflight"]["advice"] = json!("refine_configuration_with_or_without_agent");
    checked["preflight"]["reasons"] = json!(["selected_bytes_over_100_mib"]);
    checked["preflight"]["candidate_exclusions"] = json!(["**/node_modules/"]);
    let advice = recommendation_lines(&draft).join("\n");
    assert_eq!(recommended_action(&draft), Action::EditMore);
    assert!(advice.contains("100 MiB"));
    assert!(advice.contains("Suggested exclusions (not applied)"));
    assert!(draft.policy.index.exclude.is_empty());
    let checked = draft.checked.as_mut().unwrap();
    checked["preflight"]["advice"] = json!("start");
    checked["preflight"]["complete"] = json!(false);
    assert_eq!(recommended_action(&draft), Action::EditMore);
    let checked = draft.checked.as_mut().unwrap();
    checked["preflight"]["complete"] = json!(true);
    checked["capabilities"]["credential_availability_by_backend"]["voyage"] =
        json!("missing_for_selected_backend");
    assert_eq!(recommended_action(&draft), Action::EditMore);
    assert!(!key_ready(&draft));
    assert!(recommendation_lines(&draft).join(" ").contains("API key"));
}

#[test]
fn main_form_has_explanations_and_explicit_post_save_choices() {
    let draft = Draft::new(snapshot(false)).unwrap();
    for field in [
        Field::Name,
        Field::Backend,
        Field::Batch,
        Field::Debounce,
        Field::AddExclude,
        Field::AddVendor,
    ] {
        assert!(!field_help(&draft, field, Path::new("/fixture")).is_empty());
    }
    let mut ui = Ui::default();
    let form = page(&draft, &ui, Path::new("/fixture"));
    assert_eq!(
        form.footer
            .iter()
            .map(|(action, _)| *action)
            .collect::<Vec<_>>(),
        [Action::Save, Action::Close]
    );
    let draft = Draft::new(snapshot(true)).unwrap();
    ui.saved_session = true;
    let form = page(&draft, &ui, Path::new("/fixture"));
    assert_eq!(
        form.footer
            .iter()
            .map(|(action, _)| *action)
            .collect::<Vec<_>>(),
        [
            Action::Start,
            Action::EditMore,
            Action::Open(View::Agent),
            Action::Close
        ]
    );
}

#[test]
fn global_snapshot_provenance_stays_stable_while_saved_values_are_explicit() {
    let mut value = snapshot(false);
    value["global_defaults"]["embeddings"]["batch_size"] = json!(16);
    value["policy"]["embeddings"]["batch_size"] = json!(16);
    let mut draft = Draft::new(value).unwrap();
    assert_eq!(provenance(&draft, Field::Batch), "global default");
    draft.edit(Field::Batch, "32".into()).unwrap();
    assert_eq!(provenance(&draft, Field::Batch), "custom");
    let mut current = snapshot(false);
    current["global_defaults"]["embeddings"]["batch_size"] = json!(64);
    draft.checked = Some(current);
    assert_eq!(global_field(&draft, Field::Batch).as_deref(), Some("16"));
    let mut value = snapshot(true);
    value["global_defaults"]["embeddings"]["batch_size"] = json!(16);
    let saved = Draft::new(value).unwrap();
    assert_eq!(provenance(&saved, Field::Batch), "saved");
    assert!(default_reference(&saved, Field::Batch).contains("Global default now: 16"));
    assert_eq!(saved.policy.embeddings.batch_size, 64);
}

#[test]
fn semantic_formatting_keeps_help_indented_and_warnings_distinct() {
    let explanation =
        "  A long explanation of a setting, with enough words to wrap and remain readable.";
    let lines = wrap_row(explanation.into(), 30, 2);
    assert!(lines.len() > 1);
    assert!(lines.iter().all(|line| line.starts_with("  ")));
    assert!(lines
        .iter()
        .all(|line| console::measure_text_width(line) <= 30));
    let mut draft = Draft::new(snapshot(false)).unwrap();
    let mut ui = Ui::default();
    let frame = render_frame(&mut draft, &mut ui, Path::new("/fixture"), 100, 30);
    assert!(frame.iter().any(|line| line.tone == Tone::Focus));
    assert!(frame.iter().any(|line| line.tone == Tone::Muted));
    assert!(frame.iter().any(|line| line.text.is_empty()));
    draft.base["capabilities"]["credential_availability_by_backend"]["voyage"] =
        json!("missing_for_selected_backend");
    draft.checked = None;
    let frame = render_frame(&mut draft, &mut ui, Path::new("/fixture"), 100, 30);
    assert!(frame
        .iter()
        .any(|line| line.tone == Tone::Warning && line.text.contains("API key")));
}

#[test]
fn narrow_screens_keep_confirmations_actionable_and_escape_controls() {
    for (width, height) in [(80, 24), (60, 18), (52, 14), (40, 10)] {
        let mut draft = Draft::new(snapshot(true)).unwrap();
        draft
            .edit(Field::Name, "Long name with 日本語 and \x1b[31m".repeat(3))
            .unwrap();
        let mut ui = Ui::default();
        for view in [View::Policy, View::Rules, View::Message, View::Details] {
            draft.view = view;
            let lines = render_lines(&mut draft, &mut ui, Path::new("/fixture"), width, height);
            assert!(lines.len() < height, "height overflow at {width}x{height}");
            assert!(
                lines
                    .iter()
                    .all(|line| console::measure_text_width(line) < width),
                "width overflow at {width}x{height}: {:?}",
                lines
                    .iter()
                    .map(|line| (console::measure_text_width(line), line))
                    .collect::<Vec<_>>()
            );
            assert!(lines.iter().all(|line| !line.contains('\x1b')));
            if width >= 52 {
                let screen = lines.join("\n");
                assert!(screen.contains("Unsaved changes"), "{screen}");
                let actions = page(&draft, &ui, Path::new("/fixture")).actions();
                ui.focus = actions.len() - 1;
                ui.follow_focus = true;
                let screen =
                    render_lines(&mut draft, &mut ui, Path::new("/fixture"), width, height)
                        .join("\n");
                assert!(screen.contains("> ["), "Focused footer hidden: {screen}");
            }
        }
        ui.confirm(Confirm::Discard);
        let lines = render_lines(&mut draft, &mut ui, Path::new("/fixture"), width, height);
        let screen = lines.join("\n");
        assert!(screen.contains("> [Keep editing]"), "{screen}");
        assert!(screen.contains("Discard and close"), "{screen}");
        assert!(
            lines
                .iter()
                .all(|line| console::measure_text_width(line) < width),
            "{screen}"
        );
        ui.confirm(Confirm::Save);
        let screen =
            render_lines(&mut draft, &mut ui, Path::new("/fixture"), width, height).join("\n");
        assert!(screen.contains("> [Back]"), "{screen}");
        assert!(!screen.contains("> [Save"));
    }
}

#[test]
fn conflict_review_explains_full_replacement_and_blocks_changed_identity() {
    let mut draft = Draft::new(snapshot(true)).unwrap();
    draft.edit(Field::Name, "My draft".into()).unwrap();
    let mut latest = snapshot(true);
    latest["revision"] = json!(2);
    latest["policy"]["watcher"]["debounce_ms"] = json!(777);
    draft.receive_latest(latest.clone());
    let mut ui = Ui::default();
    let conflict = page(&draft, &ui, Path::new("/fixture"));
    let content = conflict
        .rows
        .iter()
        .map(|row| row.text.as_str())
        .collect::<Vec<_>>()
        .join("\n");
    assert!(content.contains("Original: 300"));
    assert!(content.contains("Current:  777"));
    assert!(content.contains("Draft:    300"));
    assert!(content.contains("not a merge"));
    assert!(conflict.actions().contains(&Action::KeepDraft));
    ui.confirm(Confirm::KeepDraft);
    let screen = render_lines(&mut draft, &mut ui, Path::new("/fixture"), 80, 24).join("\n");
    assert!(screen.contains("> [Back]"));
    let readable = screen.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(
        readable.contains("including changes made elsewhere"),
        "{screen}"
    );
    latest["family_id"] = json!(uuid::Uuid::new_v4());
    draft.receive_latest(latest);
    assert!(!page(&draft, &ui, Path::new("/fixture"))
        .actions()
        .contains(&Action::KeepDraft));
    assert_eq!(draft.revision(), Some(1));
    assert_eq!(draft.policy.name, "My draft");
}

struct Fake {
    value: Value,
    saves: usize,
    starts: usize,
    checks: usize,
    scenario: String,
}
impl Backend for Fake {
    async fn start(&mut self, _: &Draft) -> policy::Result<Value> {
        self.starts += 1;
        self.value["indexing_enabled"] = json!(true);
        if self.scenario == "failure" && self.starts == 1 {
            let mut error =
                crate::readonly::error("indexing_incomplete", "The test provider failed.");
            error.details = json!({"indexing_enabled":true,"indexing_completed":false});
            return Err(error);
        }
        let completed = self.scenario != "skipped";
        Ok(
            json!({"indexing_enabled":true,"indexing_completed":completed,
            "skipped_checkouts_or_files":if completed {0} else {1}}),
        )
    }
    async fn start_with_progress(
        &mut self,
        draft: &Draft,
        progress: impl Fn(usize, usize, &Path),
    ) -> policy::Result<Value> {
        progress(1, 2, Path::new("/fixture/first.rs"));
        tokio::time::sleep(std::time::Duration::from_millis(120)).await;
        progress(2, 2, Path::new("/fixture/second.rs"));
        tokio::time::sleep(std::time::Duration::from_millis(120)).await;
        self.start(draft).await
    }
    async fn load(&mut self) -> policy::Result<Value> {
        Ok(self.value.clone())
    }
    async fn check(&mut self, draft: &Draft) -> policy::Result<Value> {
        self.checks += 1;
        if self.scenario == "stale" && self.saves == 1 && self.checks == 2 {
            return Err(crate::readonly::error(
                "preview_unavailable",
                "The inventory could not be read.",
            ));
        }
        if self.scenario == "stale" && self.saves == 1 && self.checks >= 3 {
            self.value["preflight"]["tier2"] = json!({"files":20000,"bytes":210000000});
            self.value["preflight"]["advice"] = json!("refine_configuration_with_or_without_agent");
            self.value["preflight"]["reasons"] = json!(["selected_bytes_over_100_mib"]);
        }
        let mut value = self.value.clone();
        value["policy"] = json!(draft.policy);
        value["candidate"] = json!({"policy":draft.policy,
            "validation":{"apply_supported":true,"impact":"display"}});
        Ok(value)
    }
    async fn save(&mut self, draft: &Draft) -> policy::Result<Value> {
        self.saves += 1;
        self.value["policy"] = json!(draft.policy);
        if self.value["family_id"].is_null() {
            self.value["family_id"] = json!("01234567-89ab-cdef-0123-456789abcdef");
            self.value["revision"] = json!(1);
        } else {
            self.value["revision"] = json!(self.value["revision"].as_u64().unwrap() + 1);
        }
        Ok(self.value.clone())
    }
}

/// Invoked by the real PTY test below, never by the disposable DB runner.
#[tokio::test]
#[ignore]
async fn terminal_session() {
    let scenario = std::env::var("MUNINN_TUI_PTY_CHILD").expect("PTY child only");
    if scenario.starts_with("global-") {
        global::test_session(&scenario);
        return;
    }
    let resize = if scenario == "resize" {
        let trigger = std::path::PathBuf::from(
            std::env::var_os("MUNINN_TUI_RESIZE_TRIGGER").expect("resize trigger required"),
        );
        Some(std::thread::spawn(move || {
            let deadline = std::time::Instant::now() + std::time::Duration::from_secs(10);
            while !trigger.exists() {
                assert!(
                    std::time::Instant::now() < deadline,
                    "resize trigger missing"
                );
                std::thread::sleep(std::time::Duration::from_millis(10));
            }
            assert!(std::process::Command::new("stty")
                .args(["cols", "40", "rows", "10"])
                .stdin(std::process::Stdio::inherit())
                .status()
                .unwrap()
                .success());
            std::fs::write(trigger.with_extension("done"), "resized").unwrap();
        }))
    } else {
        None
    };
    let screen = Screen::enter(Term::stdout()).unwrap();
    let mut value = snapshot(!scenario.starts_with("new-"));
    value["preflight"]["tier1"] = json!({"files":2,"bytes":1916});
    value["preflight"]["tier2"] = json!({"files":0,"bytes":0});
    if scenario == "new-inherited" {
        let mut global = GlobalConfig::default();
        global.embeddings.backend = muninn_core::config::EmbeddingBackend::Local;
        global.embeddings.model = None;
        global.embeddings.batch_size = 16;
        global.watcher.debounce_ms = 450;
        global.index.exclude = vec!["generated/".into()];
        global.index.vendor = vec!["third_party/".into()];
        value["policy"] = json!(policy::policy_from_global("Fixture".into(), &global).unwrap());
        value["defaults"] = json!(policy::defaults_from_global(&global).unwrap());
        crate::readonly::enrich_credentials(&mut value, &global, false).unwrap();
    }

    if scenario == "missing" || scenario == "new-missing" {
        value["capabilities"]["credential_availability"] = json!("missing_for_selected_backend");
        value["capabilities"]["credential_availability_by_backend"]["voyage"] =
            json!("missing_for_selected_backend");
    }
    if scenario == "refine" {
        value["preflight"]["tier2"] = json!({"files":20000,"bytes":210000000});
        value["preflight"]["advice"] = json!("refine_configuration_with_or_without_agent");
        value["preflight"]["reasons"] = json!([
            "selected_bytes_over_100_mib",
            "selected_dependency_build_or_environment_directory"
        ]);
        value["preflight"]["candidate_exclusions"] = json!(["**/node_modules/", "**/target/"]);
    }
    if scenario == "partial" {
        value["preflight"]["complete"] = json!(false);
        value["preflight"]["counts_are_lower_bounds"] = json!(true);
        value["preflight"]["stop_reason"] = json!("entry_limit");
        value["preflight"]["entry_limit"] = json!(100000);
        value["preflight"]["advice"] = json!("refine_configuration_with_or_without_agent");
        value["preflight"]["reasons"] = json!(["incomplete_inventory"]);
    }
    let mut backend = Fake {
        value,
        saves: 0,
        starts: 0,
        checks: 0,
        scenario: scenario.clone(),
    };
    drive(&screen.0, &mut backend, Path::new("/fixture"), false)
        .await
        .unwrap();
    drop(screen);
    if let Some(resize) = resize {
        resize.join().unwrap();
    }
    match scenario.as_str() {
        "new-inherited" => {
            assert_eq!(backend.saves, 1);
            assert_eq!(backend.value["policy"]["embeddings"]["backend"], "local");
            assert_eq!(backend.value["policy"]["embeddings"]["batch_size"], 16);
            assert_eq!(backend.value["policy"]["watcher"]["debounce_ms"], 450);
            assert_eq!(
                backend.value["defaults"]["index"]["exclude"]
                    .as_array()
                    .unwrap()
                    .last()
                    .unwrap(),
                "generated/"
            );
        }
        "save" | "start" | "new-local" | "refine" | "partial" | "missing" | "new-missing"
        | "stale" => {
            assert_eq!(backend.saves, 1);
            assert_eq!(backend.value["policy"]["name"], "Edited");
        }
        "existing-start" | "failure" | "skipped" | "cancel" | "interrupt" | "resize" | "plain" => {
            assert_eq!(backend.saves, 0)
        }
        _ => panic!("unknown scenario"),
    }
    let expected_starts = match scenario.as_str() {
        "failure" => 2,
        "start" | "new-local" | "new-inherited" | "existing-start" | "skipped" => 1,
        _ => 0,
    };
    assert_eq!(backend.starts, expected_starts);
    assert_eq!(backend.value["indexing_enabled"], expected_starts > 0);
    if scenario == "new-local" {
        assert_eq!(backend.value["policy"]["embeddings"]["backend"], "local");
        assert_eq!(backend.value["policy"]["watcher"]["debounce_ms"], 500);
        assert_eq!(backend.value["policy"]["embeddings"]["batch_size"], 16);
    }
    if scenario == "refine" {
        assert_eq!(backend.value["policy"]["index"]["exclude"], json!([]));
    }
}

#[cfg(target_os = "linux")]
struct TerminalSession {
    child: std::process::Child,
    reader: Option<std::thread::JoinHandle<()>>,
    output: std::sync::mpsc::Receiver<Vec<u8>>,
    transcript: Vec<u8>,
}

#[cfg(target_os = "linux")]
impl TerminalSession {
    fn spawn(scenario: &str) -> Self {
        Self::spawn_with_resize(scenario, None)
    }

    fn spawn_with_resize(scenario: &str, resize: Option<&Path>) -> Self {
        use std::{
            io::Read,
            process::{Command, Stdio},
            sync::mpsc,
        };
        let executable = shell_path(&std::env::current_exe().unwrap());
        let command_text = format!("stty cols 80 rows 24; before=$(stty -g); timeout --foreground --kill-after=1s 30s {executable} --exact tui::tests::terminal_session --ignored --nocapture; result=$?; after=$(stty -g); if [ \"$before\" = \"$after\" ]; then echo TERMIOS_RESTORED; else exit 99; fi; exit $result");
        let mut command = Command::new("script");
        command.args(["-q", "-e", "-c", &command_text, "/dev/null"]);
        if let Some(resize) = resize {
            command.env("MUNINN_TUI_RESIZE_TRIGGER", resize);
        }
        if scenario == "plain" || scenario == "global-plain" {
            command.env("NO_COLOR", "1");
        }
        command.env("CLICOLOR_FORCE", "1");
        let mut child = command
            .env("MUNINN_TUI_PTY_CHILD", scenario)
            .env("TERM", "xterm-256color")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .spawn()
            .unwrap();
        let mut stdout = child.stdout.take().unwrap();
        let (tx, output) = mpsc::channel();
        let reader = std::thread::spawn(move || {
            let mut chunk = [0; 4096];
            while let Ok(n) = stdout.read(&mut chunk) {
                if n == 0 || tx.send(chunk[..n].to_vec()).is_err() {
                    break;
                }
            }
        });
        Self {
            child,
            reader: Some(reader),
            output,
            transcript: Vec::new(),
        }
    }

    fn frame(&self) -> String {
        let text = String::from_utf8_lossy(&self.transcript);
        console::strip_ansi_codes(text.rsplit("\x1b[H\x1b[2J").next().unwrap()).replace('\r', "")
    }

    fn wait(&mut self, needle: &str) {
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(8);
        loop {
            if self.frame().contains(needle) {
                // A frame can arrive in several chunks. Let its footer finish.
                while let Ok(part) = self
                    .output
                    .recv_timeout(std::time::Duration::from_millis(60))
                {
                    self.transcript.extend(part);
                }
                if self.frame().contains(needle) {
                    return;
                }
            }
            let part = self
                .output
                .recv_timeout(deadline.saturating_duration_since(std::time::Instant::now()))
                .unwrap_or_else(|error| {
                    panic!(
                        "PTY waiting for {needle:?}: {error}; current frame:\n{}",
                        self.frame()
                    )
                });
            self.transcript.extend(part);
        }
    }

    fn key(&mut self, key: &[u8]) {
        use std::io::Write;
        let before = self.transcript.len();
        self.child.stdin.as_mut().unwrap().write_all(key).unwrap();
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(8);
        loop {
            let part = self
                .output
                .recv_timeout(deadline.saturating_duration_since(std::time::Instant::now()))
                .unwrap_or_else(|error| {
                    panic!("PTY key {key:?}: {error}; current frame:\n{}", self.frame())
                });
            self.transcript.extend(part);
            if self.transcript[before..]
                .windows(4)
                .any(|s| s == b"\x1b[H\x1b")
            {
                while let Ok(part) = self
                    .output
                    .recv_timeout(std::time::Duration::from_millis(60))
                {
                    self.transcript.extend(part);
                }
                return;
            }
        }
    }

    fn send_exit(&mut self, key: &[u8]) {
        use std::io::Write;
        self.child.stdin.as_mut().unwrap().write_all(key).unwrap();
    }

    fn focus(&mut self, label: &str) {
        for _ in 0..32 {
            if self.frame().lines().any(|line| {
                line.split_once("> ").is_some_and(|(_, focused)| {
                    let focused = focused.trim_start();
                    focused
                        .strip_prefix("[+]")
                        .or_else(|| focused.strip_prefix("[-]"))
                        .unwrap_or(focused)
                        .trim_start()
                        .trim_start_matches('[')
                        .starts_with(label)
                })
            }) {
                return;
            }
            self.key(b"\t");
        }
        panic!("No focusable control {label:?}; frame:\n{}", self.frame());
    }

    fn finish(mut self) {
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(5);
        let status = loop {
            if let Some(status) = self.child.try_wait().unwrap() {
                break status;
            }
            assert!(
                std::time::Instant::now() < deadline,
                "PTY did not exit:\n{}",
                self.frame()
            );
            std::thread::sleep(std::time::Duration::from_millis(20));
        };
        self.reader.take().unwrap().join().unwrap();
        for part in self.output.try_iter() {
            self.transcript.extend(part);
        }
        let text = String::from_utf8_lossy(&self.transcript);
        assert!(status.success(), "{text}");
        assert!(text.contains("TERMIOS_RESTORED"));
        assert!(text.contains("\x1b[?1049h"));
        assert!(text.contains("\x1b[?25h\x1b[?1049l"));
    }
}

#[cfg(target_os = "linux")]
impl Drop for TerminalSession {
    fn drop(&mut self) {
        if self.child.try_wait().ok().flatten().is_none() {
            let _ = self.child.kill();
            let _ = self.child.wait();
        }
    }
}

#[test]
#[cfg(target_os = "linux")]
fn pseudoterminal_save_cancel_and_terminal_restoration() {
    for scenario in ["save", "start", "cancel", "interrupt"] {
        let mut terminal = TerminalSession::spawn(scenario);
        terminal.wait("Muninn / Fixture");
        terminal.focus("Name");
        terminal.key(b"\r");
        terminal.wait("Edit Name");
        terminal.key(b"\x15Edited\r");
        terminal.wait("Unsaved changes");
        if scenario == "save" || scenario == "start" {
            terminal.focus("Save configuration");
            terminal.key(b"\r");
            terminal.wait("Save configuration?");
            // Enter on the initial safe choice cancels rather than saving.
            terminal.key(b"\r");
            terminal.wait("Unsaved changes");
            terminal.focus("Save configuration");
            terminal.key(b"\r");
            terminal.focus("Save");
            terminal.key(b"\r");
            terminal.wait("CONFIGURATION SAVED");
            assert!(!terminal.frame().contains("Start indexing?"));
            if scenario == "start" {
                terminal.focus("Start indexing");
                terminal.key(b"\r");
                terminal.wait("Indexing enabled");
                terminal.send_exit(b"\x1b");
            } else {
                // Saving does not start; choosing Leave explicitly keeps the family unindexed.
                terminal.focus("Leave unindexed");
                terminal.send_exit(b"\r");
            }
        } else if scenario == "interrupt" {
            terminal.send_exit(b"\x03");
        } else {
            terminal.key(b"\x1b");
            terminal.wait("Discard");
            terminal.key(b"\r");
            terminal.wait("Unsaved changes");
            terminal.key(b"\x1b");
            terminal.focus("Discard");
            terminal.send_exit(b"\r");
        }
        terminal.finish();
    }
}

#[test]
#[cfg(target_os = "linux")]
fn pseudoterminal_resize_preserves_discard_confirmation() {
    let directory = tempfile::tempdir().unwrap();
    let trigger = directory.path().join("resize");
    let mut terminal = TerminalSession::spawn_with_resize("resize", Some(&trigger));
    terminal.wait("Muninn / Fixture");
    terminal.focus("Name");
    terminal.key(b"\r");
    terminal.key(b"\x15Edited\r");
    terminal.wait("Unsaved changes");
    std::fs::write(&trigger, "resize now").unwrap();
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(3);
    while !trigger.with_extension("done").exists() {
        assert!(
            std::time::Instant::now() < deadline,
            "terminal did not resize"
        );
        std::thread::sleep(std::time::Duration::from_millis(10));
    }
    terminal.key(b"\t");
    terminal.wait("Resize");
    terminal.key(b"\x1b");
    terminal.wait("Discard");
    // The safe choice remains the default at 40x10.
    terminal.key(b"\r");
    terminal.wait("Resize");
    terminal.key(b"\x1b");
    terminal.focus("Discard");
    terminal.send_exit(b"\r");
    terminal.finish();
}

#[test]
#[cfg(target_os = "linux")]
fn pseudoterminal_inventory_credentials_and_completion_flows() {
    for scenario in [
        "new-local",
        "new-missing",
        "missing",
        "refine",
        "partial",
        "existing-start",
        "failure",
        "skipped",
        "stale",
    ] {
        let mut terminal = TerminalSession::spawn(scenario);
        terminal.wait("Muninn / Fixture");
        if scenario == "existing-start" || scenario == "failure" || scenario == "skipped" {
            terminal.wait("CONFIGURATION SAVED");
            terminal.focus("Start indexing");
            terminal.key(b"\r");
        } else {
            terminal.focus("Name");
            terminal.key(b"\r");
            terminal.key(b"\x15Edited\r");
            if scenario == "new-local" {
                terminal.focus("Provider");
                terminal.key(b"\r");
                terminal.focus("Local");
                terminal.key(b"\r");
                terminal.focus("Advanced");
                terminal.key(b"\r");
                terminal.focus("Change delay");
                terminal.key(b"\r");
                terminal.key(b"\x15500\r");
                terminal.focus("Request size");
                terminal.key(b"\r");
                terminal.key(b"\x1516\r");
            }
            terminal.focus("Save configuration");
            terminal.key(b"\r");
            terminal.wait("Save configuration?");
            terminal.focus("Save configuration");
            terminal.key(b"\r");
            terminal.wait("CONFIGURATION SAVED");
            if scenario == "new-local" {
                terminal.wait("Recommendation: Start");
                terminal.focus("Start indexing");
                terminal.key(b"\r");
            }
        }
        match scenario {
            "stale" => {
                terminal.wait("preview failed");
                terminal.focus("Start unavailable");
                terminal.key(b"\r");
                terminal.wait("Review the recommendation before choosing Start");
                assert!(terminal.frame().contains("Recommendation: refine"));
                terminal.focus("Leave unindexed");
                terminal.send_exit(b"\r");
            }
            "missing" | "new-missing" => {
                assert!(terminal.frame().contains("API key"));
                terminal.focus("Start unavailable");
                terminal.key(b"\r");
                terminal.wait("Cannot start");
                terminal.focus("Leave unindexed");
                terminal.send_exit(b"\r");
            }
            "refine" | "partial" => {
                terminal.wait("Recommendation: refine");
                if scenario == "partial" {
                    assert!(terminal.frame().contains("at least"));
                } else {
                    assert!(terminal.frame().contains("100 MiB"));
                }
                terminal.focus("Ask an agent");
                terminal.key(b"\r");
                terminal.wait("muninn preflight");
                terminal.key(b"\x1b");
                terminal.focus("Leave unindexed");
                terminal.send_exit(b"\r");
            }
            "failure" => {
                terminal.wait("this pass did not complete");
                assert!(terminal.frame().contains("Indexing enabled"));
                terminal.focus("Retry indexing");
                terminal.key(b"\r");
                terminal.wait("This indexing pass completed");
                terminal.send_exit(b"\x1b");
            }
            "skipped" => {
                terminal.wait("This indexing pass is incomplete");
                assert!(!terminal.frame().contains("This indexing pass completed"));
                terminal.send_exit(b"\x1b");
            }
            _ => {
                terminal.wait("This indexing pass completed");
                // Real callback data must have been displayed, before the receipt.
                assert!(String::from_utf8_lossy(&terminal.transcript)
                    .contains("Indexing: 1 of 2 files processed"));
                terminal.send_exit(b"\x1b");
            }
        }
        terminal.finish();
    }
}

#[test]
#[cfg(target_os = "linux")]
fn pseudoterminal_monochrome_keeps_explicit_states_without_styles() {
    let mut terminal = TerminalSession::spawn("plain");
    terminal.wait("Muninn / Fixture");
    let raw = String::from_utf8_lossy(&terminal.transcript);
    let raw = raw
        .rsplit("\x1b[H\x1b[2J")
        .next()
        .unwrap()
        .replace('\r', "");
    assert_eq!(raw, terminal.frame());
    assert!(raw.contains("Recommendation: Start"));
    assert!(raw.contains("> [Start indexing]"));
    terminal.send_exit(b"\x1b");
    terminal.finish();
}

#[test]
#[cfg(target_os = "linux")]
fn pseudoterminal_new_repo_uses_visible_global_snapshot_defaults() {
    let mut terminal = TerminalSession::spawn("new-inherited");
    terminal.wait("Muninn / Fixture");
    assert!(terminal.frame().contains("Local"));
    assert!(terminal.frame().contains("global default"));
    assert!(terminal.frame().contains("16") && terminal.frame().contains("450"));
    terminal.focus("Save configuration");
    terminal.key(b"\r");
    terminal.focus("Save configuration");
    terminal.key(b"\r");
    terminal.wait("CONFIGURATION SAVED");
    terminal.focus("Start indexing");
    terminal.key(b"\r");
    terminal.wait("This indexing pass completed");
    terminal.send_exit(b"\x1b");
    terminal.finish();
}

/// Run only through the disposable harness; never loads global configuration.
#[tokio::test]
#[ignore]
async fn persistence() -> anyhow::Result<()> {
    use muninn_core::{family_store::PreparationConnection, store};
    use std::{fs, path::PathBuf, process::Command};
    use tokio_postgres::NoTls;
    let filename = std::env::var_os("MUNINN_PERSISTENCE_TEST_CONFIG")
        .expect("explicit disposable target required");
    let target: Value = serde_json::from_slice(&fs::read(filename)?)?;
    anyhow::ensure!(
        target["host"] == "127.0.0.1"
            && target["port"] == 5451
            && target["database"] == "muninn_persistence_test"
            && target["user"] == "muninn_persistence_test",
        "refusing non-test endpoint"
    );
    let fixture_root = PathBuf::from(target["fixture_root"].as_str().unwrap());
    anyhow::ensure!(
        fixture_root.parent() == Some(Path::new("/tmp"))
            && fixture_root
                .file_name()
                .unwrap()
                .to_string_lossy()
                .starts_with("muninn-persistence-test-")
    );
    let mut connection_config = tokio_postgres::Config::new();
    connection_config
        .host("127.0.0.1")
        .port(5451)
        .dbname("muninn_persistence_test")
        .user("muninn_persistence_test")
        .password(target["password"].as_str().unwrap())
        .connect_timeout(std::time::Duration::from_secs(5))
        .options(
            "-c search_path=public,ag_catalog -c statement_timeout=15000 -c lock_timeout=5000",
        );
    let (client, connection) = connection_config.connect(NoTls).await?;
    tokio::spawn(async move {
        let _ = connection.await;
    });
    let row=client.query_one("SELECT current_database(),current_user,rolsuper,rolcreatedb,rolcreaterole FROM pg_roles WHERE rolname=current_user",&[]).await?;
    anyhow::ensure!(
        row.get::<_, String>(0) == "muninn_persistence_test"
            && row.get::<_, String>(1) == "muninn_persistence_test"
            && !row.get::<_, bool>(2)
            && !row.get::<_, bool>(3)
            && !row.get::<_, bool>(4)
    );
    let run_id = target["run_id"].as_str().unwrap().to_owned();
    anyhow::ensure!(
        client
            .query_one("SELECT run_id FROM public.muninn_persistence_test_run", &[])
            .await?
            .get::<_, String>(0)
            == run_id
    );
    let prepare = move || {
        let config = connection_config.clone();
        let run_id = run_id.clone();
        async move {
            let (client, mut connection) = config.connect(NoTls).await?;
            tokio::select! {
                result=client.query_one("SELECT run_id FROM public.muninn_persistence_test_run",&[])=>anyhow::ensure!(result?.get::<_,String>(0)==run_id),
                result=&mut connection=>{result?;anyhow::bail!("test preparation connection closed");}
            }
            let token = client.cancel_token();
            Ok(PreparationConnection::new(client, connection, async move {
                token.cancel_query(NoTls).await
            }))
        }
    };
    let fixtures = tempfile::tempdir_in(&fixture_root)?;
    let root = fixtures.path().join("repo");
    fs::create_dir(&root)?;
    let git = |args: &[&str]| -> anyhow::Result<()> {
        let output = Command::new("git")
            .arg("-C")
            .arg(&root)
            .args(args)
            .output()?;
        anyhow::ensure!(
            output.status.success(),
            "fixture git failed: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        Ok(())
    };
    git(&["init", "-b", "main"])?;
    git(&[
        "-c",
        "user.name=Fixture",
        "-c",
        "user.email=fixture@example.invalid",
        "commit",
        "--allow-empty",
        "-m",
        "fixture",
    ])?;
    fs::write(root.join("main.rs"), "fn main() {}\n")?;
    fs::create_dir(root.join("bulk"))?;
    fs::write(root.join("bulk/generated.rs"), "generated")?;
    let mut config = GlobalConfig::from_toml_str(GlobalConfig::template_content())?;
    config.database.host = "127.0.0.1".into();
    config.database.port = 5451;
    config.database.dbname = "muninn_persistence_test".into();
    config.database.user = "muninn_persistence_test".into();
    config.database.dsn_override = None;
    let credential_path = PathBuf::from(std::env::var_os("HOME").expect("HOME")).join(".pgpass");
    anyhow::ensure!(
        fs::read(credential_path)? == fs::read(fixture_root.join("client-pgpass"))?,
        "disposable credential mount required"
    );
    let mut backend = Database {
        client,
        config,
        path: root.clone(),
        add_mode: true,
        prepare,
    };
    let count_before: i64 = backend
        .client
        .query_one("SELECT count(*) FROM public.repos", &[])
        .await?
        .get(0);
    let mut draft = Draft::new(backend.load().await?)?;
    assert!(draft.family_id().is_none());
    draft.edit(Field::Name, "TUI fixture".into())?;
    draft.edit(Field::Backend, "local".into())?;
    draft.edit(Field::AddExclude, "bulk/".into())?;
    let check = backend.check(&draft).await?;
    assert_eq!(check["preflight"]["tier1"]["files"], 1);
    assert_eq!(
        backend
            .client
            .query_one("SELECT count(*) FROM public.repos", &[])
            .await?
            .get::<_, i64>(0),
        count_before,
        "opening/editing/checking must not register"
    );
    let saved = backend.save(&draft).await?;
    assert_eq!(saved["policy"]["name"], "TUI fixture");
    assert_eq!(saved["revision"], 1);
    assert_eq!(saved["indexing_enabled"], false);
    draft = Draft::new(saved)?;
    let id = draft.family_id().unwrap();
    let schema = store::repo_schema(id);
    assert_eq!(
        backend
            .client
            .query_one(&format!("SELECT count(*) FROM \"{schema}\".chunks"), &[])
            .await?
            .get::<_, i64>(0),
        0
    );
    // A concurrent JSON edit makes both check and save reject the stale guard.
    backend.add_mode = false;
    let mut concurrent: policy::ApplyRequest = serde_json::from_value(draft.request())?;
    concurrent.policy.name = "Concurrent JSON edit".into();
    policy::apply_path(&mut backend.client, &root, &concurrent).await?;
    draft.edit(Field::Name, "Retained TUI draft".into())?;
    assert_eq!(
        backend.check(&draft).await.unwrap_err().code,
        "revision_conflict"
    );
    let error = backend.save(&draft).await.unwrap_err();
    assert_eq!(error.code, "revision_conflict");
    assert_eq!(
        backend.start(&draft).await.unwrap_err().code,
        "revision_conflict"
    );
    assert!(!backend.client.query_one("SELECT preempt_requested OR indexing_enabled_at IS NOT NULL FROM public.repos WHERE id=$1", &[&id]).await?.get::<_,bool>(0));
    report_error(&mut draft, error);
    assert_eq!(draft.revision(), Some(1));
    assert_eq!(draft.policy.name, "Retained TUI draft");
    draft.receive_latest(backend.load().await?);
    assert_eq!(draft.revision(), Some(1));
    draft.keep_draft_on_latest()?;
    assert_eq!(draft.revision(), Some(2));
    backend.check(&draft).await?;
    draft = Draft::new(backend.save(&draft).await?)?;
    assert_eq!(draft.revision(), Some(3));
    assert_eq!(
        backend.load().await?["policy"]["name"],
        "Retained TUI draft"
    );
    assert_eq!(backend.save(&draft).await?["changed"], false);
    // Add a checkout to the existing family without copying policy or starting.
    let linked = fixtures.path().join("linked");
    git(&["worktree", "add", "-b", "linked", linked.to_str().unwrap()])?;
    backend.path = linked;
    backend.add_mode = true;
    let linked_draft = Draft::new(backend.load().await?)?;
    assert_eq!(linked_draft.family_id(), Some(id));
    assert!(linked_draft.base["checkout_id"].is_null());
    let linked_receipt = backend.save(&linked_draft).await?;
    assert!(!linked_receipt["checkout_id"].is_null());
    assert!(linked_receipt.get("registration_error").is_none());
    assert_eq!(linked_receipt["revision"], 3);
    assert_eq!(linked_receipt["indexing_enabled"], false);
    assert_eq!(
        backend
            .client
            .query_one(&format!("SELECT count(*) FROM \"{schema}\".checkouts"), &[])
            .await?
            .get::<_, i64>(0),
        2
    );
    assert_eq!(
        backend
            .client
            .query_one("SELECT count(*) FROM public.repos", &[])
            .await?
            .get::<_, i64>(0),
        count_before + 1
    );
    let mut start_draft = Draft::new(backend.load().await?)?;
    start_draft.edit(Field::AddExclude, "*".into())?;
    start_draft = Draft::new(backend.save(&start_draft).await?)?;
    assert_eq!(
        backend.check(&start_draft).await?["preflight"]["tier1"]["files"],
        0
    );
    let started = backend.start(&start_draft).await?;
    assert_eq!(started["indexing_enabled"], true);
    assert_eq!(started["indexing_completed"], true);
    assert_eq!(backend.load().await?["indexing_enabled"], true);
    assert_eq!(
        backend
            .client
            .query_one(
                &format!("SELECT count(*) FROM {schema}.checkouts WHERE indexed_at IS NOT NULL"),
                &[]
            )
            .await?
            .get::<_, i64>(0),
        2
    );
    println!("TUI persistence: read-only open/check, registration, CAS conflict/review, no-op save, worktree association, save without indexing, and explicit foreground start verified");
    Ok(())
}

#[test]
fn inherited_patterns_are_visible_with_custom_rules_and_reference_globals() {
    let mut value = snapshot(false);
    value["defaults"]["index"]["exclude"]
        .as_array_mut()
        .unwrap()
        .push(json!("generated/"));
    value["global_defaults"]["index"]["exclude"] = json!(["generated/"]);
    let mut draft = Draft::new(value).unwrap();
    draft.edit(Field::AddExclude, "local-only/".into()).unwrap();
    let content = page(&draft, &Ui::default(), Path::new("/fixture"))
        .rows
        .into_iter()
        .map(|r| r.text)
        .collect::<Vec<_>>()
        .join("\n");
    assert!(content.contains("generated/") && content.contains("local-only/"));
    assert!(content.contains("copied into this draft"));
    let mut saved = snapshot(true);
    saved["global_defaults"]["index"]["vendor"] = json!(["third_party/"]);
    let draft = Draft::new(saved).unwrap();
    let content = page(&draft, &Ui::default(), Path::new("/fixture"))
        .rows
        .into_iter()
        .map(|r| r.text)
        .collect::<Vec<_>>()
        .join("\n");
    assert!(content.contains("third_party/") && content.contains("reference for new repositories"));
}

#[test]
#[cfg(target_os = "linux")]
fn pseudoterminal_global_creation() {
    let mut terminal = TerminalSession::spawn("global-create");
    terminal.wait("Muninn / Global configuration");
    terminal.focus("Provider");
    terminal.key(b"\r");
    terminal.focus("Local");
    terminal.key(b"\r");
    terminal.focus("Exclude defaults");
    terminal.key(b"\r");
    terminal.focus("Add pattern");
    terminal.key(b"\r");
    terminal.key(b"generated/\r");
    terminal.focus("Back");
    terminal.key(b"\r");
    terminal.focus("Save global configuration");
    terminal.key(b"\r");
    terminal.wait("Save global configuration?");
    assert!(terminal.frame().contains("Database:"));
    assert!(terminal.frame().contains("> [Keep editing]"));
    terminal.key(b"\r");
    terminal.focus("Save global configuration");
    terminal.key(b"\r");
    terminal.key(b"\x1b[A");
    terminal.send_exit(b"\r");
    terminal.finish();
}
#[test]
#[cfg(target_os = "linux")]
fn pseudoterminal_global_edit_and_secrets() {
    let mut terminal = TerminalSession::spawn("global-edit");
    terminal.wait("Muninn / Global configuration");
    terminal.focus("API key");
    terminal.key(b"\r");
    assert!(terminal.frame().contains("> [Keep current key]"));
    terminal.key(b"\r");
    terminal.focus("API key");
    terminal.key(b"\r");
    terminal.focus("Replace key");
    terminal.key(b"\r");
    terminal.key(b"replacement-private-key");
    assert!(!terminal.frame().contains("replacement-private-key"));
    assert!(!terminal.frame().contains("canary-original-secret"));
    terminal.key(b"\r");
    terminal.focus("Save global configuration");
    terminal.key(b"\r");
    assert!(
        terminal.frame().contains("Save global configuration?"),
        "{}",
        terminal.frame()
    );
    terminal.key(b"\x1b[A");
    assert!(
        terminal.frame().contains("> [Save]"),
        "{}",
        terminal.frame()
    );
    terminal.send_exit(b"\r");
    terminal.finish();
}
#[test]
#[cfg(target_os = "linux")]
fn pseudoterminal_global_cancel_preserves_file() {
    let mut terminal = TerminalSession::spawn("global-cancel");
    terminal.wait("Muninn / Global configuration");
    terminal.focus("Database host");
    terminal.key(b"\r");
    terminal.key(b"\x15changed-host\r");
    terminal.key(b"\x1b");
    terminal.wait("Discard changes?");
    assert!(terminal.frame().contains("> [Keep editing]"));
    terminal.key(b"\x1b[A");
    terminal.send_exit(b"\r");
    terminal.finish();
}

#[test]
#[cfg(target_os = "linux")]
fn pseudoterminal_global_narrow_confirmations_and_monochrome() {
    let mut terminal = TerminalSession::spawn("global-create-narrow");
    terminal.wait("Muninn / Global configuration");
    terminal.focus("Provider");
    terminal.key(b"\r");
    assert!(terminal.frame().contains("Voyage") && terminal.frame().contains("OpenAI"));
    terminal.focus("Local");
    terminal.key(b"\r");
    terminal.focus("Exclude defaults");
    terminal.key(b"\r");
    terminal.focus("Add pattern");
    terminal.key(b"\r");
    terminal.key(b"generated/\r");
    terminal.focus("Back");
    terminal.key(b"\r");
    terminal.focus("Save global configuration");
    terminal.key(b"\r");
    assert!(terminal.frame().contains("[Save]") && terminal.frame().contains("[Keep editing]"));
    terminal.key(b"\x1b[A");
    terminal.send_exit(b"\r");
    terminal.finish();
    let mut terminal = TerminalSession::spawn("global-plain");
    terminal.wait("Muninn / Global configuration");
    let raw = String::from_utf8_lossy(&terminal.transcript);
    let frame = raw
        .rsplit("\x1b[H\x1b[2J")
        .next()
        .unwrap()
        .replace('\r', "");
    assert_eq!(frame, console::strip_ansi_codes(&frame));
    terminal.send_exit(b"\x1b");
    terminal.finish();
}

#[test]
fn setting_help_stays_in_a_separate_bottom_region_when_form_scrolls() {
    for (width, height) in [(100, 30), (80, 24), (52, 14)] {
        let mut draft = Draft::new(snapshot(false)).unwrap();
        let mut ui = Ui::default();
        let first = render_frame(&mut draft, &mut ui, Path::new("/fixture"), width, height);
        let first_help = first
            .iter()
            .position(|line| line.text.contains("About: Name"))
            .unwrap();
        assert!(first_help > 0);
        assert!(first
            .iter()
            .skip(first_help + 1)
            .any(|line| line.text.contains("Display name")));
        assert!(first
            .iter()
            .skip(first_help + 1)
            .any(|line| line.text.contains("Save configuration")));
        assert!(!first[..first_help]
            .iter()
            .any(|line| line.text.contains("Display name")));
        ui.select_action(&draft, Path::new("/fixture"), Action::Edit(Field::Backend));
        let next = render_frame(&mut draft, &mut ui, Path::new("/fixture"), width, height);
        let next_help = next
            .iter()
            .position(|line| line.text.contains("About: Embedding provider"))
            .unwrap();
        assert_eq!(first_help, next_help);
        draft.scroll = 999;
        ui.follow_focus = false;
        let scrolled = render_frame(&mut draft, &mut ui, Path::new("/fixture"), width, height);
        assert_eq!(
            scrolled
                .iter()
                .position(|line| line.text.contains("About: Embedding provider")),
            Some(next_help)
        );
        assert!(scrolled.len() < height);
    }
}
#[test]
#[cfg(target_os = "linux")]
fn pseudoterminal_global_fixed_help_and_full_explanation() {
    let mut terminal = TerminalSession::spawn("global-cancel");
    terminal.wait("About: Database host");
    let first = terminal
        .frame()
        .lines()
        .position(|line| line.contains("About:"))
        .unwrap();
    terminal.focus("Provider");
    terminal.wait("About: Provider");
    assert_eq!(
        terminal
            .frame()
            .lines()
            .position(|line| line.contains("About:")),
        Some(first)
    );
    terminal.key(b"\x1b[6~");
    terminal.wait("About: Provider");
    assert_eq!(
        terminal
            .frame()
            .lines()
            .position(|line| line.contains("About:")),
        Some(first)
    );
    terminal.key(b"?");
    terminal.wait("About: Provider");
    assert!(terminal
        .frame()
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
        .contains("Changing provider clears"));
    terminal.key(b"\x1b");
    terminal.send_exit(b"\x1b");
    terminal.finish();
}

#[test]
#[cfg(target_os = "linux")]
fn pseudoterminal_repository_help_and_editor_keep_value_visible() {
    let mut terminal = TerminalSession::spawn("cancel");
    terminal.wait("Muninn / Fixture");
    terminal.focus("Advanced");
    terminal.key(b"\r");
    terminal.focus("Request size");
    terminal.wait("About: Request size");
    terminal.key(b"?");
    terminal.wait("About: Request size");
    assert!(terminal.frame().contains("must be positive"));
    terminal.key(b"\x1b");
    terminal.key(b"\r");
    terminal.wait("Edit Request size");
    assert!(terminal.frame().contains("About: Request size"));
    assert!(terminal.frame().contains('|'));
    terminal.key(b"\x1b[6~");
    assert!(terminal.frame().contains('|'));
    terminal.key(b"\x1b");
    terminal.send_exit(b"\x1b");
    terminal.finish();
}
