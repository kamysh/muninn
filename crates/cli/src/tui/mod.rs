//! Native field/list editor with separate Save and Start confirmations.
mod backend;
mod model;
#[cfg(test)]
mod tests;
use backend::{Backend, Database};
use console::{Key, Term};
use model::{shell_path, visible, Draft, Field, View};
use muninn_core::{config::GlobalConfig, db, family_policy::PolicyError};
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

enum Modal {
    Edit(Field, Vec<char>, usize),
    Backend(usize),
    Save,
    Start,
    Discard,
    LoadCurrent,
}

async fn drive(
    term: &Term,
    backend: &mut impl Backend,
    path: &Path,
    add_mode: bool,
) -> anyhow::Result<()> {
    term.write_line("Loading policy and preflight...")?;
    let mut draft = Draft::new(backend.load().await?)?;
    let mut modal = None;
    loop {
        draw(term, &mut draft, path, add_mode, modal.as_ref())?;
        let key = term.read_key_raw()?;
        if key == Key::CtrlC {
            return Ok(());
        }
        let (height, width) = term.size();
        if height < 14 || width < 52 {
            if key == Key::Char('q') {
                return Ok(());
            }
            continue;
        }
        if let Some(current) = modal.take() {
            match current {
                Modal::Edit(field, mut chars, mut cursor) => {
                    match key {
                        Key::Escape => continue,
                        Key::Enter => {
                            match draft.edit(field, chars.iter().collect()) {
                                Ok(()) => {}
                                Err(error) => {
                                    draft.status = error.to_string();
                                    modal = Some(Modal::Edit(field, chars, cursor));
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
                    modal = Some(Modal::Edit(field, chars, cursor));
                }
                Modal::Backend(mut index) => {
                    match key {
                        Key::Escape => continue,
                        Key::ArrowUp => index = index.saturating_sub(1),
                        Key::ArrowDown => index = (index + 1).min(2),
                        Key::Enter => {
                            draft.edit(
                                Field::Backend,
                                ["voyage", "openai", "local"][index].into(),
                            )?;
                            continue;
                        }
                        _ => {}
                    }
                    modal = Some(Modal::Backend(index));
                }
                Modal::Save => {
                    match key {
                        Key::Enter => {
                            draft.status = "Saving configuration...".into();
                            draw(term, &mut draft, path, add_mode, None)?;
                            match backend.save(&draft).await {
                                Ok(data) => {
                                    let association_error = data.get("registration_error").cloned();
                                    draft = Draft::new(data)?;
                                    let saved_revision = draft.revision().unwrap();
                                    match backend.check(&draft).await {
                                        Ok(data) => draft.checked = Some(data),
                                        Err(error) => {
                                            draft.checked = None;
                                            draft.status=format!("Saved revision {saved_revision}. Preflight failed: {}",error.message);
                                        }
                                    }
                                    if draft.checked.is_some() {
                                        draft.status=format!("Saved revision {saved_revision}. I: start indexing | E: edit more | A: ask an agent | Q: leave");
                                    }
                                    if let Some(ref error) = association_error {
                                        draft.status=format!("Policy saved. Checkout association failed: {}. Save again to retry.",error["message"].as_str().unwrap_or("inspect registration"));
                                    }
                                    if association_error.is_none()
                                        && draft.base["indexing_enabled"] == false
                                        && draft.checked.is_some()
                                    {
                                        modal = Some(Modal::Start);
                                    }
                                    draft.view = View::Preflight;
                                    draft.scroll = 0;
                                }
                                Err(error) => report_error(&mut draft, error),
                            }
                        }
                        Key::Escape => {}
                        _ => modal = Some(Modal::Save),
                    }
                }
                Modal::Start => match key {
                    Key::Enter => {
                        draft.status="Indexing in the foreground; interruption retains completed views and enables retries.".into();
                        draw(term, &mut draft, path, add_mode, None)?;
                        match backend.start(&draft).await {
                            Ok(data) => {
                                draft.base["indexing_enabled"] = serde_json::json!(true);
                                draft.status = format!(
                                    "Indexing enabled. Pass completed: {}. Skipped: {}.",
                                    data["indexing_completed"], data["skipped_checkouts_or_files"]
                                );
                            }
                            Err(error) => report_error(&mut draft, error),
                        }
                    }
                    Key::Escape | Key::Char('e') => {
                        draft.view = View::Policy;
                    }
                    Key::Char('a') => {
                        draft.view = View::Agent;
                    }
                    Key::Char('q') => return Ok(()),
                    _ => modal = Some(Modal::Start),
                },
                Modal::Discard => match key {
                    Key::Enter => return Ok(()),
                    Key::Escape => {}
                    _ => modal = Some(Modal::Discard),
                },
                Modal::LoadCurrent => match key {
                    Key::Enter => {
                        if let Some(latest) = draft.latest.take() {
                            draft = Draft::new(latest)?;
                            draft.status =
                                "Loaded current policy; previous draft discarded by request."
                                    .into();
                        }
                    }
                    Key::Escape => {}
                    _ => modal = Some(Modal::LoadCurrent),
                },
            }
            continue;
        }
        match key {
            Key::Char('q') | Key::Escape => {
                if draft.dirty() {
                    modal = Some(Modal::Discard)
                } else {
                    return Ok(());
                }
            }
            Key::Char('1') | Key::Char('e') => {
                draft.view = View::Policy;
                draft.scroll = 0;
            }
            Key::Char('2') | Key::Char('d') => {
                draft.view = View::Defaults;
                draft.scroll = 0;
            }
            Key::Char('3') => {
                draft.view = View::Preflight;
                draft.scroll = 0;
            }
            Key::Char('4') | Key::Char('a') => {
                draft.view = View::Agent;
                draft.scroll = 0;
            }
            Key::Char('m') => {
                draft.view = View::Message;
                draft.scroll = 0;
            }
            Key::Char('5') if draft.latest.is_some() => {
                draft.view = View::Conflict;
                draft.scroll = 0;
            }
            Key::ArrowUp | Key::BackTab => {
                if draft.view == View::Policy {
                    draft.selected = draft.selected.saturating_sub(1);
                } else {
                    draft.scroll = draft.scroll.saturating_sub(1);
                }
            }
            Key::ArrowDown | Key::Tab => {
                if draft.view == View::Policy {
                    draft.selected = (draft.selected + 1).min(draft.fields().len() - 1);
                } else {
                    draft.scroll += 1;
                }
            }
            Key::PageUp => {
                if draft.view == View::Policy {
                    draft.selected = draft.selected.saturating_sub(8);
                } else {
                    draft.scroll = draft.scroll.saturating_sub(8);
                }
            }
            Key::PageDown => {
                if draft.view == View::Policy {
                    draft.selected = (draft.selected + 8).min(draft.fields().len() - 1);
                } else {
                    draft.scroll += 8;
                }
            }
            Key::Enter if draft.view == View::Policy => {
                let field = draft.selected();
                if field == Field::Backend {
                    if draft.family_id().is_some() {
                        draft.status="Embedding profile is fixed for this family; model migration is unavailable.".into();
                    } else {
                        modal = Some(Modal::Backend(match draft.policy.embeddings.backend {
                            muninn_core::family_policy::Backend::Voyage => 0,
                            muninn_core::family_policy::Backend::OpenAI => 1,
                            muninn_core::family_policy::Backend::Local => 2,
                        }));
                    }
                } else {
                    let chars: Vec<_> = field_value(&draft, field).chars().collect();
                    let len = chars.len();
                    modal = Some(Modal::Edit(field, chars, len));
                }
            }
            Key::Char('x') if draft.view == View::Policy => draft.remove(),
            Key::Char('K') if draft.view == View::Policy => draft.move_rule(true),
            Key::Char('J') if draft.view == View::Policy => draft.move_rule(false),
            Key::Char('i') => {
                if draft.dirty() || draft.family_id().is_none() {
                    draft.status = "Save the draft before starting indexing.".into();
                } else {
                    match backend.check(&draft).await {
                        Ok(data) => {
                            draft.checked = Some(data);
                            modal = Some(Modal::Start);
                        }
                        Err(error) => report_error(&mut draft, error),
                    }
                }
            }
            Key::Char('p') | Key::Char('s') => {
                draft.status = "Checking draft and scanning selected checkout...".into();
                draw(term, &mut draft, path, add_mode, None)?;
                match backend.check(&draft).await {
                    Ok(data) => {
                        let unsupported = draft.family_id().is_some()
                            && data["candidate"]["validation"]["apply_supported"] == false;
                        draft.checked = Some(data);
                        draft.view = View::Preflight;
                        draft.scroll = 0;
                        draft.status =
                            "Preflight refreshed for this draft. Advice does not start indexing."
                                .into();
                        if key == Key::Char('s') {
                            if unsupported {
                                draft.status="This policy change requires an unsupported model/dimension migration.".into();
                            } else {
                                modal = Some(Modal::Save);
                            }
                        }
                    }
                    Err(error) => report_error(&mut draft, error),
                }
            }
            Key::Char('r') => {
                draft.status = "Loading current policy for review...".into();
                draw(term, &mut draft, path, add_mode, None)?;
                match backend.load().await {
                    Ok(latest) => draft.receive_latest(latest),
                    Err(error) => report_error(&mut draft, error),
                }
            }
            Key::Char('l') if draft.view == View::Conflict => modal = Some(Modal::LoadCurrent),
            Key::Char('k') if draft.view == View::Conflict => {
                if let Err(error) = draft.keep_draft_on_latest() {
                    draft.status = error.to_string();
                }
            }
            _ => {}
        }
    }
}
fn report_error(draft: &mut Draft, error: PolicyError) {
    draft.checked = None;
    draft.status = format!(
        "{}: {}. Draft retained. R: load current for review.",
        error.code, error.message
    );
    if error.details["reservation_persisted"] == true {
        draft
            .status
            .push_str(" Creation intent was saved; retry add --json without input to finish it.");
    }
}
fn field_label(field: Field) -> String {
    match field {
        Field::Name => "Name".into(),
        Field::Debounce => "Debounce (ms)".into(),
        Field::Backend => "Embedding backend".into(),
        Field::Batch => "Embedding batch size".into(),
        Field::Exclude(i) => format!("Exclude [{}]", i + 1),
        Field::Vendor(i) => format!("Vendor [{}]", i + 1),
        Field::AddExclude => "+ Add exclusion rule".into(),
        Field::AddVendor => "+ Add vendor rule".into(),
    }
}
fn field_value(draft: &Draft, field: Field) -> String {
    match field {
        Field::Name => draft.policy.name.clone(),
        Field::Debounce => draft.policy.watcher.debounce_ms.to_string(),
        Field::Batch => draft.policy.embeddings.batch_size.to_string(),
        Field::Backend => format!(
            "{:?} / {}",
            draft.policy.embeddings.backend,
            draft.policy.embeddings.backend.model_identity()
        ),
        Field::Exclude(i) => draft.policy.index.exclude[i].clone(),
        Field::Vendor(i) => draft.policy.index.vendor[i].clone(),
        _ => String::new(),
    }
}
fn body(draft: &Draft, path: &Path) -> Vec<String> {
    match draft.view {
        View::Message => vec!["FULL STATUS MESSAGE".into(), draft.status.clone()],
        View::Policy => draft
            .fields()
            .into_iter()
            .enumerate()
            .map(|(i, field)| {
                format!(
                    "{} {:24} {}",
                    if i == draft.selected { ">" } else { " " },
                    field_label(field),
                    field_value(draft, field)
                )
            })
            .collect(),
        View::Defaults => {
            let mut lines = vec![
                format!("Frozen defaults: {} (read only)", draft.defaults.revision),
                "Effective ordering: defaults, then family rules; last match wins.".into(),
                "Exclusion wins over vendor. Reopen a pruned parent before its child.".into(),
                String::new(),
                "DEFAULT EXCLUSIONS".into(),
            ];
            lines.extend(
                draft
                    .defaults
                    .index
                    .exclude
                    .iter()
                    .enumerate()
                    .map(|(i, s)| format!("{}: {s}", i + 1)),
            );
            lines.push("FAMILY EXCLUSIONS (editable on Policy)".into());
            lines.extend(draft.policy.index.exclude.clone());
            lines.push("DEFAULT VENDOR RULES".into());
            lines.extend(draft.defaults.index.vendor.clone());
            lines.push("FAMILY VENDOR RULES (editable on Policy)".into());
            lines.extend(draft.policy.index.vendor.clone());
            lines
        }
        View::Preflight => {
            let Some(check) = &draft.checked else {
                return vec![
                    "Preflight is stale or unavailable for this draft. Press P to refresh.".into(),
                ];
            };
            let p = &check["preflight"];
            let mut lines = vec![
                "SELECTED CHECKOUT INVENTORY (policy affects every worktree)".into(),
                format!("Root: {}", p["root"]["display"].as_str().unwrap_or("")),
                format!(
                    "Complete: {} | stop: {} | lower bounds: {}",
                    p["complete"], p["stop_reason"], p["counts_are_lower_bounds"]
                ),
                format!(
                    "Tier 1: {} files / {} bytes",
                    p["tier1"]["files"], p["tier1"]["bytes"]
                ),
                format!(
                    "Tier 2: {} files / {} bytes",
                    p["tier2"]["files"], p["tier2"]["bytes"]
                ),
                format!(
                    "Visited: {} | observed excluded: {} | pruned dirs: {}",
                    p["visited_regular_files"],
                    p["observed_excluded_files"],
                    p["pruned_directories"]
                ),
                format!(
                    "Unreadable: {} | skipped symlinks: {}",
                    p["unreadable_entries"], p["skipped_symlinks"]
                ),
                format!(
                    "Credentials: {}",
                    check["capabilities"]["credential_availability"]
                        .as_str()
                        .unwrap_or("not checked")
                ),
                String::new(),
                if p["advice"] == "start" {
                    "Advice: inventory looks suitable for indexing.".into()
                } else {
                    "Advice: refine exclusions, manually or with an agent, then rescan.".into()
                },
            ];
            if draft.base["reconciliation_needed"] == true
                && draft.base["reconciliation_scheduled"] == false
            {
                lines.push(
                    "Saved policy requires index reconciliation; it has not been scheduled.".into(),
                );
            }
            if let Some(validation) = check
                .get("candidate")
                .filter(|_| draft.family_id().is_some())
                .and_then(|candidate| candidate.get("validation"))
            {
                lines.push(format!(
                    "Draft impact: {} | save supported: {}",
                    validation["impact"], validation["apply_supported"]
                ));
            }
            for reason in p["reasons"].as_array().into_iter().flatten() {
                lines.push(format!("Reason: {}", reason.as_str().unwrap_or("unknown")));
            }
            for rule in p["candidate_exclusions"].as_array().into_iter().flatten() {
                lines.push(format!(
                    "Suggested exclusion (not applied): {}",
                    rule.as_str().unwrap_or("")
                ));
            }
            lines.push("LARGEST SELECTED FILES".into());
            for f in p["largest_files"].as_array().into_iter().flatten() {
                lines.push(format!(
                    "{} bytes  {}",
                    f["bytes"],
                    f["path"]["display"].as_str().unwrap_or("")
                ));
            }
            lines.push("COSTLY DIRECTORIES (descendant totals overlap)".into());
            for d in p["costly_directories"].as_array().into_iter().flatten() {
                lines.push(format!(
                    "{} files / {} bytes  {}",
                    d["selected"]["files"],
                    d["selected"]["bytes"],
                    d["path"]["display"].as_str().unwrap_or("")
                ));
            }
            lines.push("UNREADABLE ENTRIES".into());
            for e in p["unreadable_samples"].as_array().into_iter().flatten() {
                lines.push(format!(
                    "{}: {}",
                    e["operation"],
                    e["path"]["display"].as_str().unwrap_or("")
                ));
            }
            lines.push(
                "Metadata only: file contents, parsing and embedding costs are not verified."
                    .into(),
            );
            lines.push("Current file limit: 10 MiB. Structural parsing limit: 1 MiB.".into());
            lines
        }
        View::Agent => {
            let target = shell_path(path);
            vec![
                "ASK AN AGENT — commands for Bash/Zsh; nothing is executed here".into(),
                "Ask it to review exclusions and costly directories before indexing.".into(),
                format!("muninn preflight {target} --json"),
                format!("muninn config {target} --json"),
                format!("muninn config {target} --check - --json < request.json"),
                if draft.family_id().is_some() {
                    format!("muninn config {target} --apply - --json < request.json")
                } else {
                    format!("muninn add {target} --json --input - < request.json")
                },
                format!(
                    "Current family: {} | revision: {}",
                    draft.base["family_id"], draft.base["revision"]
                ),
                "Existing requests need expected_family_id and expected_revision.".into(),
                "New-family requests contain api_version: 1 and a complete policy.".into(),
                "Inspect/check are read only. Save updates enabled families. I: explicit first start.".into(),
            ]
        }
        View::Conflict => {
            let Some(latest) = &draft.latest else {
                return vec!["Press R to load current policy for review.".into()];
            };
            let mut lines = vec![
                "REVIEW CURRENT POLICY — your draft has not been changed".into(),
                format!(
                    "Original family/revision: {} / {}",
                    draft.base["family_id"], draft.base["revision"]
                ),
                format!(
                    "Current family/revision:  {} / {}",
                    latest["family_id"], latest["revision"]
                ),
                "L: discard draft and load current (confirmation required)".into(),
                "k: retain draft against reviewed revision; save still required".into(),
            ];
            if latest["family_id"] != draft.base["family_id"] {
                lines.push(
                    "FAMILY CHANGED — retaining this draft against that family is blocked.".into(),
                );
            }
            let candidate = serde_json::to_value(&draft.policy).unwrap();
            for key in ["name", "watcher", "embeddings", "index"] {
                if draft.base["policy"][key] != latest["policy"][key]
                    || candidate[key] != latest["policy"][key]
                {
                    lines.push(format!("{key}:"));
                    lines.push(format!("  original: {}", draft.base["policy"][key]));
                    lines.push(format!("  current:  {}", latest["policy"][key]));
                    lines.push(format!("  draft:    {}", candidate[key]));
                }
            }
            lines
        }
    }
}
/// Wrap after escaping controls so long rules and conflict details stay readable.
fn wrap_lines(lines: Vec<String>, width: usize) -> Vec<String> {
    let mut result = Vec::new();
    for line in lines {
        let mut current = String::new();
        let mut used = 0;
        for c in visible(&line).chars() {
            let size = console::measure_text_width(&c.to_string());
            if used + size > width && !current.is_empty() {
                result.push(std::mem::take(&mut current));
                used = 0;
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
    console::truncate_str(&visible(&text), width, "…").into_owned()
}
fn draw(
    term: &Term,
    draft: &mut Draft,
    path: &Path,
    add_mode: bool,
    modal: Option<&Modal>,
) -> std::io::Result<()> {
    let (height, width) = term.size();
    let height = height as usize;
    let width = width as usize;
    let mut lines = vec![
        format!(
            "MUNINN — {} configuration{}",
            if add_mode { "add / family" } else { "family" },
            if draft.dirty() {
                " [unsaved draft]"
            } else {
                ""
            }
        ),
        format!(
            "{} | family {} | revision {}",
            path.display(),
            draft.base["family_id"],
            draft.base["revision"]
        ),
        format!(
            "Indexing enabled: {} | family paused: {} | checkout paused: {}",
            draft.base["indexing_enabled"], draft.base["paused"], draft.base["checkout"]["paused"]
        ),
        "1 Policy | 2 Defaults | 3 Preflight | 4 Agent | 5 Review".into(),
    ];
    let available = height.saturating_sub(8);
    if height < 14 || width < 52 {
        lines = vec!["Resize terminal to at least 52 x 14. Q: close".into()];
    } else if let Some(modal) = modal {
        let content = match modal {
            Modal::Edit(field, chars, cursor) => vec![
                format!("Edit {}", field_label(*field)),
                edit_window(chars, *cursor, width.saturating_sub(1)),
                "Enter: accept | Esc: cancel | Ctrl-U: clear".into(),
            ],
            Modal::Backend(index) => vec![
                "Choose initial embedding backend".into(),
                format!(
                    "{} Voyage / voyage-code-3 / 1024",
                    if *index == 0 { ">" } else { " " }
                ),
                format!(
                    "{} OpenAI / text-embedding-3-small / 1536",
                    if *index == 1 { ">" } else { " " }
                ),
                format!(
                    "{} Local / potion-base-32M / 512",
                    if *index == 2 { ">" } else { " " }
                ),
                "Up/Down: choose | Enter: accept | Esc: cancel".into(),
            ],
            Modal::Save => vec![
                "SAVE CONFIGURATION?".into(),
                "Changes apply to this family and all its worktrees.".into(),
                "First indexing requires Start; enabled families will update.".into(),
                format!(
                    "Inventory advice: {}",
                    draft
                        .checked
                        .as_ref()
                        .map(|d| d["preflight"]["advice"]
                            .as_str()
                            .unwrap_or("review required"))
                        .unwrap_or("unavailable")
                ),
                "Enter: save | Esc: return to draft".into(),
            ],
            Modal::Start => vec![
                "START INDEXING THIS FAMILY?".into(),
                if draft
                    .checked
                    .as_ref()
                    .is_some_and(|d| d["preflight"]["advice"] == "start")
                {
                    "Inventory suggests starting now.".into()
                } else {
                    "Inventory suggests refining exclusions first, manually or with an agent."
                        .into()
                },
                "Runs here; the daemon handles subsequent updates and retries.".into(),
                "Enter: start | E/Esc: edit | A: agent help | Q: leave".into(),
            ],
            Modal::Discard => vec![
                "Discard unsaved draft and close?".into(),
                "Enter: discard | Esc: keep editing".into(),
            ],
            Modal::LoadCurrent => vec![
                "Discard draft and load reviewed current policy?".into(),
                "Enter: load current | Esc: keep draft".into(),
            ],
        };
        lines.extend(content.into_iter().take(available));
    } else {
        let content = if draft.view == View::Policy {
            body(draft, path)
        } else {
            wrap_lines(body(draft, path), width.saturating_sub(1))
        };
        if draft.view == View::Policy {
            if draft.selected < draft.scroll {
                draft.scroll = draft.selected;
            }
            if draft.selected >= draft.scroll + available {
                draft.scroll = draft.selected + 1 - available;
            }
        }
        draft.scroll = draft.scroll.min(content.len().saturating_sub(available));
        lines.extend(content.into_iter().skip(draft.scroll).take(available));
    }
    while lines.len() < height.saturating_sub(4) {
        lines.push(String::new());
    }
    if height >= 14 && width >= 52 {
        lines.push(draft.status.clone());
        lines.push("Enter edit | x delete | J/K reorder | arrows scroll".into());
        lines.push("p check | s save | r review | m status | q leave".into());
    }
    let text = lines
        .into_iter()
        .take(height.saturating_sub(1))
        .map(|line| {
            console::truncate_str(&visible(&line), width.saturating_sub(1), "…").into_owned()
        })
        .collect::<Vec<_>>()
        .join("\r\n");
    term.write_str(&format!("\x1b[H\x1b[2J{text}"))?;
    term.flush()
}
