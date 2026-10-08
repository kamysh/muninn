//! Global bootstrap editor. Edits a draft only; the caller owns persistence.
use super::{edit_window, paint_line, wrap_row, RenderLine, Screen, Tone};
use console::{Key, Term};
use muninn_core::config::{self, GlobalConfig};
use serde_json::Value;
use std::{io::IsTerminal, path::Path};

#[derive(Clone, Copy)]
enum Kind {
    Text,
    Optional,
    Number,
    OptionalNumber,
    Bool,
    Secret,
    Provider,
    Rules,
}
struct Setting {
    key: &'static str,
    label: &'static str,
    help: &'static str,
    kind: Kind,
    advanced: bool,
}
macro_rules! setting {
    ($key:literal,$label:literal,$help:literal,$kind:ident,$advanced:expr) => {
        Setting {
            key: $key,
            label: $label,
            help: $help,
            kind: Kind::$kind,
            advanced: $advanced,
        }
    };
}
const SETTINGS: &[Setting] = &[
    setting!("database.host","Database host","PostgreSQL hostname or Unix-socket directory. Passwords come from ~/.pgpass; this form does not change database users or passwords.",Text,false),
    setting!("database.port","Database port","PostgreSQL port, usually 5432. Must match the matching ~/.pgpass entry.",Number,false),
    setting!("database.dbname","Database name","Existing PostgreSQL database used by Muninn. Saving prepares its Muninn schema; it does not create a database.",Text,false),
    setting!("database.user","Database user","Existing application role. Its password belongs in the matching owner-only ~/.pgpass entry.",Text,false),
    setting!("embeddings.backend","Provider","Local runs on this machine without an API key; first use may download weights. Voyage/OpenAI send selected text to that provider. Changing provider clears the old key and selects its standard model.",Provider,false),
    setting!("embeddings.model","Model","Local uses minishlab/potion-base-32M. Standard new-repository models: Voyage voyage-code-3; OpenAI text-embedding-3-small. Existing repository profiles stay fixed.",Optional,false),
    setting!("embeddings.api_key","API key","Hosted providers require their own key. Stored only in this owner-only global file. Choose Replace or Clear explicitly. An empty replacement keeps the current key; Esc keeps the current key.",Secret,false),
    setting!("embeddings.batch_size","Request size","Chunks per embedding request; must be positive. New repositories copy this default. Larger requests use more memory and may exceed provider limits.",Number,false),
    setting!("watcher.debounce_ms","Change delay (ms)","Milliseconds to wait after file changes before indexing; 0 means no delay. New repositories copy this default.",Number,false),
    setting!("index.exclude","Exclude defaults","Ordered patterns relative to checkout roots. Matching files are omitted. Shipped rules run first, then these global defaults, then custom repository rules. ! reverses a rule; parent directories must remain traversable.",Rules,false),
    setting!("index.vendor","Vendor defaults","Ordered patterns for searchable text without initial embeddings. ! restores primary classification. Exclusions win. These rules are copied into new repository snapshots.",Rules,false),
    setting!("embeddings.cache_dir","Model cache directory","Optional local cache location. Empty uses the application default. This machine-specific path is not copied into repository settings.",Optional,true),
    setting!("database.connect_timeout","Connection timeout (s)","Seconds to wait while connecting. Empty uses the normal driver behavior; family preparation supplies 10 seconds if unset.",OptionalNumber,true),
    setting!("database.application_name","Connection name","Optional name visible in PostgreSQL activity. Some internal connections use their own names.",Optional,true),
    setting!("database.ssl_mode","TLS mode","Optional: disable, allow, prefer, require, verify-ca, verify-full. Current driver can fall back to plaintext; these names do not guarantee TLS-only transport.",Optional,true),
    setting!("database.ssl_root_cert","TLS CA certificate","Optional PEM certificate path added to native TLS trust.",Optional,true),
    setting!("database.ssl_client_cert","TLS client certificate","Optional PEM certificate path for client authentication; pair with the private-key path.",Optional,true),
    setting!("database.ssl_client_key","TLS client key path","Path to the PEM private key, not the private key itself.",Optional,true),
    setting!("mcp.record_usage","Record MCP usage","Record successful tool-call statistics in the database for muninn usage.",Bool,true),
    setting!("mcp.logging.enabled","MCP logging","Write local MCP logs. Logs can include search queries and repository paths.",Bool,true),
    setting!("mcp.logging.dir","MCP log directory","Directory for daily rotating MCP logs.",Text,true),
    setting!("mcp.logging.retention_days","Log retention (days)","Days of local MCP logs to retain.",Number,true),
    setting!("mcp.logging.prune_interval_hours","Log cleanup interval (h)","Hours between checks for expired local MCP logs.",Number,true),
];

struct Draft {
    base: String,
    text: String,
    values: Value,
}
impl Draft {
    fn new(text: &str) -> anyhow::Result<Self> {
        let config = GlobalConfig::from_toml_str(text).map_err(|_| {
            anyhow::anyhow!(
                "Cannot parse global configuration; fix its TOML syntax before opening the form"
            )
        })?;
        Ok(Self {
            base: text.into(),
            text: text.into(),
            values: serde_json::to_value(config)?,
        })
    }
    fn value(&self, key: &str) -> Value {
        let mut value = &self.values;
        for part in key.split('.') {
            value = &value[part];
        }
        value.clone()
    }
    fn apply(&mut self, text: String) -> anyhow::Result<()> {
        let config = GlobalConfig::from_toml_str(&text)
            .map_err(|_| anyhow::anyhow!("Value does not fit this setting's type or range"))?;
        self.values = serde_json::to_value(config)?;
        self.text = text;
        Ok(())
    }
    fn set(&mut self, index: usize, input: &str) -> anyhow::Result<()> {
        let setting = &SETTINGS[index];
        let candidate = match setting.kind {
            Kind::Optional | Kind::OptionalNumber | Kind::Secret if input.is_empty() => {
                config::toml_unset(&self.text, setting.key)
            }
            Kind::Number | Kind::OptionalNumber => {
                let number: u64 = input
                    .parse()
                    .map_err(|_| anyhow::anyhow!("Enter a nonnegative whole number"))?;
                config::toml_set(&self.text, setting.key, &number.to_string())
            }
            _ => config::toml_set(&self.text, setting.key, &serde_json::to_string(input)?),
        }
        .map_err(|_| anyhow::anyhow!("Cannot apply this value"))?;
        GlobalConfig::from_toml_str(&candidate)
            .map_err(|_| anyhow::anyhow!("Value does not fit this setting's type or range"))?;
        self.apply(candidate)
    }
    fn provider(&mut self, provider: &str) -> anyhow::Result<()> {
        if self.value("embeddings.backend") == provider {
            return Ok(());
        }
        let mut candidate = config::toml_set(&self.text, "embeddings.backend", provider)?;
        candidate = config::toml_unset(&candidate, "embeddings.api_key")?;
        candidate = match provider {
            "local" => config::toml_unset(&candidate, "embeddings.model")?,
            "voyage" => config::toml_set(&candidate, "embeddings.model", "voyage-code-3")?,
            _ => config::toml_set(&candidate, "embeddings.model", "text-embedding-3-small")?,
        };
        GlobalConfig::from_toml_str(&candidate)?;
        self.apply(candidate)
    }
    fn rules(&self, index: usize) -> Vec<String> {
        self.value(SETTINGS[index].key)
            .as_array()
            .unwrap()
            .iter()
            .map(|v| v.as_str().unwrap().into())
            .collect()
    }
    fn set_rules(&mut self, index: usize, rules: Vec<String>) -> anyhow::Result<()> {
        let candidate = config::toml_set(
            &self.text,
            SETTINGS[index].key,
            &serde_json::to_string(&rules)?,
        )?;
        let cfg = GlobalConfig::from_toml_str(&candidate)?;
        muninn_core::family_policy::defaults_from_global(&cfg)
            .map_err(|_| anyhow::anyhow!("Invalid glob pattern; changes were not applied"))?;
        self.apply(candidate)
    }
    fn validate(&self) -> anyhow::Result<()> {
        let cfg = GlobalConfig::from_toml_str(&self.text)?;
        cfg.validate()?;
        muninn_core::family_policy::defaults_from_global(&cfg)
            .map_err(|_| anyhow::anyhow!("Invalid file-selection pattern"))?;
        Ok(())
    }
}
#[derive(Clone, Copy, PartialEq)]
enum Action {
    Field(usize),
    Advanced,
    Save,
    Cancel,
    Back,
    Add,
    Rule(usize),
}
enum Modal {
    Edit(usize, Option<usize>, Vec<char>, usize),
    Provider(usize),
    Secret(usize),
    Docs(String, String),
    Confirm(bool, bool),
    Rule(usize, usize),
}
#[derive(Default)]
struct Ui {
    focus: usize,
    scroll: usize,
    advanced: bool,
    rules: Option<usize>,
    modal: Option<Modal>,
    help_return: Option<Box<Modal>>,
    notice: String,
    follow: bool,
}

fn display(draft: &Draft, index: usize) -> String {
    let field = &SETTINGS[index];
    let value = draft.value(field.key);
    if matches!(field.kind, Kind::Secret) {
        let configured = value.as_str().is_some_and(|s| !s.is_empty());
        if draft.value("embeddings.backend") == "local" {
            return if configured {
                "Stored (hidden; unused for Local)"
            } else {
                "Not required (Local)"
            }
            .into();
        }
        return if configured {
            "Configured (hidden)"
        } else {
            "Missing — required for hosted embeddings"
        }
        .into();
    }
    if field.key == "embeddings.model" && draft.value("embeddings.backend") == "local" {
        return "minishlab/potion-base-32M (fixed)".into();
    }
    if value.is_null() {
        "Not set".into()
    } else if let Some(s) = value.as_str() {
        s.into()
    } else if matches!(field.kind, Kind::Rules) {
        format!("{} patterns", draft.rules(index).len())
    } else {
        value.to_string()
    }
}
fn rows(draft: &Draft, ui: &Ui) -> Vec<(String, Tone, Option<Action>)> {
    let mut out = Vec::new();
    let mut add = |text: String, tone, action| out.push((text, tone, action));
    if let Some(index) = ui.rules {
        add(SETTINGS[index].label.into(), Tone::Heading, None);

        add(String::new(), Tone::Normal, None);
        for (i, rule) in draft.rules(index).iter().enumerate() {
            add(
                format!("{}. {}", i + 1, rule),
                Tone::Normal,
                Some(Action::Rule(i)),
            );
        }
        add("[Add pattern]".into(), Tone::Normal, Some(Action::Add));
        add(
            "Enter: edit, move or remove a pattern. Order matters; later matches win.".into(),
            Tone::Muted,
            None,
        );
    } else {
        add("Global settings supply defaults for NEW repositories. Saved repository snapshots stay unchanged.".into(),Tone::Info,None);
        for (i, field) in SETTINGS
            .iter()
            .enumerate()
            .filter(|(_, s)| !s.advanced || ui.advanced)
        {
            if matches!(
                field.key,
                "database.host"
                    | "embeddings.backend"
                    | "watcher.debounce_ms"
                    | "index.exclude"
                    | "embeddings.cache_dir"
            ) {
                add(String::new(), Tone::Normal, None);
            }
            add(
                format!("{}  {}", field.label, display(draft, i)),
                Tone::Normal,
                Some(Action::Field(i)),
            );
            if matches!(field.kind, Kind::Rules) {
                let rules = draft.rules(i);
                if rules.is_empty() {
                    add(
                        "  (no additional global patterns)".into(),
                        Tone::Muted,
                        None,
                    );
                }
                for rule in rules {
                    add(format!("  {rule}"), Tone::Muted, None);
                }
            }
        }
        if draft.value("embeddings.backend") != "local"
            && draft
                .value("embeddings.api_key")
                .as_str()
                .is_none_or(str::is_empty)
        {
            add(
                "API key missing: hosted embeddings cannot run until a matching key is supplied."
                    .into(),
                Tone::Warning,
                None,
            );
        }
        add(String::new(), Tone::Normal, None);
        add(
            format!(
                "[{} Advanced connection, cache and MCP settings]",
                if ui.advanced { "−" } else { "+" }
            ),
            Tone::Normal,
            Some(Action::Advanced),
        );
    }
    out
}
fn actions(draft: &Draft, ui: &Ui) -> Vec<Action> {
    let mut actions: Vec<_> = rows(draft, ui).into_iter().filter_map(|r| r.2).collect();
    actions.extend(if ui.rules.is_some() {
        vec![Action::Back]
    } else {
        vec![Action::Save, Action::Cancel]
    });
    actions
}
fn focus_help(draft: &Draft, ui: &Ui) -> (String, String) {
    let index = match ui.modal.as_ref() {
        Some(Modal::Edit(index, ..)) => Some(*index),
        Some(Modal::Provider(_)) => Some(4),
        Some(Modal::Secret(_)) => Some(6),
        Some(Modal::Rule(..)) => ui.rules,
        _ => match actions(draft, ui).get(ui.focus) {
            Some(Action::Field(index)) => Some(*index),
            Some(Action::Rule(_) | Action::Add) => ui.rules,
            _ => None,
        },
    };
    if let Some(index) = index {
        return (SETTINGS[index].label.into(), SETTINGS[index].help.into());
    }
    let (label,text)=match actions(draft,ui).get(ui.focus) {
        Some(Action::Advanced)=>("Advanced settings","Show optional database connection, local model cache and MCP settings. Existing values remain preserved when collapsed."),
        Some(Action::Save)=>("Save global configuration","Save an owner-only file, then prepare its configured database. Existing repository snapshots stay unchanged. Running daemon and MCP processes need a restart or reconnection for changed global settings."),
        Some(Action::Cancel)=>("Cancel","Leave the global configuration unchanged. If the draft was edited, confirm whether to discard it."),
        _=>("Global defaults","Global settings supply defaults for newly configured repositories. Saved repository settings remain stable. Use ? to read the selected explanation in full."),
    };
    (label.into(), text.into())
}
fn draw(term: &Term, draft: &Draft, ui: &mut Ui, path: &Path) -> anyhow::Result<()> {
    let (height, width) = term.size();
    let width = usize::from(width).saturating_sub(1).max(1);
    let height = usize::from(height).saturating_sub(1).max(1);
    if height < 13 || width < 51 {
        term.write_str("\x1b[H\x1b[2JResize to at least 52 x 14. Draft retained.\nCtrl-C: cancel")?;
        term.flush()?;
        return Ok(());
    }
    let controls = actions(draft, ui);
    ui.focus = ui.focus.min(controls.len() - 1);
    let mut lines = vec![
        RenderLine::new("Muninn / Global configuration", Tone::Heading),
        RenderLine::new(
            super::model::visible(&path.display().to_string()),
            Tone::Muted,
        ),
        RenderLine::new(
            if draft.text == draft.base {
                "Unchanged draft"
            } else {
                "Unsaved changes"
            },
            Tone::Info,
        ),
    ];
    if height < 18 {
        lines = vec![RenderLine::new(
            "Muninn / Global configuration",
            Tone::Heading,
        )];
    }
    if !ui.notice.is_empty() {
        lines.extend(
            wrap_row(ui.notice.clone(), width, 2)
                .into_iter()
                .map(|text| RenderLine::new(text, Tone::Error)),
        );
    }
    let mut body = Vec::new();
    let mut control = 0;
    let mut focused = None;
    for (text, tone, action) in rows(draft, ui) {
        let selected = action.is_some() && control == ui.focus;
        if selected {
            focused = Some(body.len());
        }
        if action.is_some() {
            control += 1;
        }
        let text = if action.is_some() {
            format!("{} {text}", if selected { ">" } else { " " })
        } else {
            text
        };
        for text in wrap_row(text, width, 2) {
            body.push(RenderLine::new(
                text,
                if selected { Tone::Focus } else { tone },
            ));
        }
    }
    let mut footer = vec![];
    for (i, action) in controls.iter().enumerate().skip(control) {
        let label = match action {
            Action::Save => "Save global configuration",
            Action::Cancel => "Cancel",
            _ => "Back",
        };
        footer.push(format!(
            "{} [{label}]",
            if i == ui.focus { ">" } else { " " }
        ));
    }
    if let Some(modal) = &ui.modal {
        focused = None;
        body.clear();
        let texts:Vec<String>=match modal {
            Modal::Docs(label,text)=>vec![format!("About: {label}"),text.clone()],
            Modal::Edit(index,rule,chars,cursor)=>{
                let field=&SETTINGS[*index];
                let _ = (chars,cursor);
                vec![format!("Edit {}{}",field.label,if rule.is_some(){" pattern"}else{""}),"This edits your draft; global Save writes the file.".into()]
            }
            Modal::Secret(selected) => ["Replace key (input hidden)", "Clear key", "Keep current key"].iter().enumerate().map(|(i,s)|format!("{} [{s}]",if i==*selected{">"}else{" "})).collect(),
            Modal::Provider(selected)=>vec!["Choose embedding provider".into(),"Changing provider clears its existing API key.".into(),String::new()].into_iter().chain(["Local — runs here, no API key","Voyage — hosted, Voyage key required","OpenAI — hosted, OpenAI key required"].into_iter().enumerate().map(|(i,s)|format!("{} {s}",if i==*selected{">"}else{" "}))).collect(),
            Modal::Confirm(save,yes)=>vec![if *save{"Save global configuration?"}else{"Discard changes?"}.into(),if *save{"Writes an owner-only global file, then prepares its configured database. Existing repository snapshots remain unchanged. Restart daemon and reconnect MCP clients to apply changed global settings."}else{"Your draft will be discarded; the global file remains unchanged."}.into(),String::new(),format!("{} [{}]",if *yes{">"}else{" "},if *save{"Save"}else{"Discard"}),format!("{} [Keep editing]",if !*yes{">"}else{" "})],
            Modal::Rule(_,selected)=>["Edit pattern","Move earlier","Move later","Remove pattern","Back"].iter().enumerate().map(|(i,s)|format!("{} [{s}]",if i==*selected{">"}else{" "})).collect(),
        };
        let mut texts = texts;
        if matches!(modal, Modal::Confirm(true, _)) {
            let cfg = GlobalConfig::from_toml_str(&draft.text)?;
            texts.insert(
                2,
                format!(
                    "Database: {}@{}:{}/{}",
                    cfg.database.user, cfg.database.host, cfg.database.port, cfg.database.dbname
                ),
            );
            texts.insert(
                3,
                format!(
                    "Provider: {} · API key: {}",
                    display(draft, 4),
                    display(draft, 6)
                ),
            );
            if cfg.database.dsn_override.is_some() {
                texts.insert(4,"Existing DSN override is preserved but not used; the target above uses explicit connection fields.".into());
            }
        }

        let menu_count = match modal {
            Modal::Confirm(_, _) => 2,
            Modal::Provider(_) | Modal::Secret(_) => 3,
            Modal::Rule(_, _) => 5,
            _ => 0,
        };
        let menu = if menu_count > 0 {
            texts.split_off(texts.len().saturating_sub(menu_count))
        } else {
            Vec::new()
        };
        for text in texts {
            for text in wrap_row(text, width, 2) {
                body.push(RenderLine::new(text, Tone::Info));
            }
        }
        footer = menu;
        if let Modal::Edit(index, _, chars, cursor) = modal {
            let masked = if matches!(SETTINGS[*index].kind, Kind::Secret) {
                vec!['•'; chars.len()]
            } else {
                chars.clone()
            };
            footer = vec![
                edit_window(&masked, *cursor, width.saturating_sub(4)),
                "Enter: apply to draft · Esc: keep current".into(),
            ];
        } else if footer.is_empty() {
            footer.push("Enter: apply to draft · Esc: keep current".into());
        }
    }
    let docs = !matches!(ui.modal, Some(Modal::Confirm(..) | Modal::Docs(..)));
    let panel = if docs {
        let (label, text) = focus_help(draft, ui);
        let rows =
            super::help_rows(height).min(height.saturating_sub(lines.len() + footer.len() + 4));
        if matches!(ui.modal, Some(Modal::Edit(..))) {
            ui.scroll = ui.scroll.min(
                wrap_row(text.clone(), width, 2)
                    .len()
                    .saturating_sub(rows.saturating_sub(1)),
            );
        }
        super::help_panel(
            &label,
            &text,
            width,
            rows,
            if matches!(ui.modal, Some(Modal::Edit(..))) {
                ui.scroll
            } else {
                0
            },
            if matches!(ui.modal, Some(Modal::Edit(..))) {
                "PgUp/PgDn: help"
            } else {
                "? more"
            },
        )
    } else {
        Vec::new()
    };
    let input = if matches!(ui.modal, Some(Modal::Edit(..))) && !footer.is_empty() {
        vec![RenderLine::new(footer.remove(0), Tone::Focus)]
    } else {
        Vec::new()
    };
    let capacity = height
        .saturating_sub(lines.len() + footer.len() + input.len() + panel.len() + 2)
        .max(1);

    if ui.follow {
        if let Some(index) = focused {
            if index < ui.scroll {
                ui.scroll = index;
            } else if index >= ui.scroll + capacity {
                ui.scroll = index + 1 - capacity;
            }
        }
        ui.follow = false;
    }
    let body_scroll = if matches!(ui.modal, Some(Modal::Edit(..))) {
        0
    } else {
        ui.scroll.min(body.len().saturating_sub(capacity))
    };
    if !matches!(ui.modal, Some(Modal::Edit(..))) {
        ui.scroll = body_scroll;
    }
    let total = body.len();
    lines.extend(body.into_iter().skip(body_scroll).take(capacity));
    let show_scroll = total > capacity && ui.modal.is_none();
    while lines.len() + footer.len() + input.len() + panel.len() + 1 + usize::from(show_scroll)
        < height
    {
        lines.push(RenderLine::new("", Tone::Normal));
    }
    if show_scroll {
        lines.push(RenderLine::new(
            format!(
                "Settings {}-{}/{} · PgUp/PgDn: scroll",
                body_scroll + 1,
                (body_scroll + capacity).min(total),
                total
            ),
            Tone::Muted,
        ));
    }
    lines.extend(input);
    lines.extend(panel);
    lines.extend(footer.into_iter().map(|s| {
        let tone = if s.starts_with('>') {
            Tone::Focus
        } else {
            Tone::Normal
        };
        RenderLine::new(s, tone)
    }));
    let hint = match ui.modal.as_ref() {
        Some(Modal::Edit(..)) => {
            if width < 59 {
                "←/→: cursor · Enter: apply · Esc: cancel"
            } else {
                "←/→: cursor · Enter: apply · Esc: cancel · Ctrl-U: clear"
            }
        }
        Some(Modal::Docs(..)) => "PgUp/PgDn: scroll · Enter/Esc: back",
        Some(_) => "Tab/↑↓: choose · Enter: accept · Esc: back · ?: help",
        None => {
            if width < 59 {
                "Tab/↑↓: move · Enter: edit · ?: help · Esc: back"
            } else {
                "Tab/↑↓: move · Enter: edit · PgUp/PgDn: scroll · ?: help · Esc: back"
            }
        }
    };
    lines.push(RenderLine::new(hint, Tone::Muted));
    let text = lines
        .into_iter()
        .map(|line| paint_line(line, width))
        .collect::<Vec<_>>()
        .join("\n");
    term.write_str(&format!("\x1b[H\x1b[2J{text}"))?;
    term.flush()?;
    Ok(())
}

pub fn run(content: &str, path: &Path) -> anyhow::Result<Option<String>> {
    let term = Term::stdout();
    anyhow::ensure!(term.is_term()&&std::io::stdin().is_terminal(),"Interactive global configuration requires a terminal; use init key=value or config set --global for automation");
    let mut draft = Draft::new(content)?;
    let mut ui = Ui::default();
    let screen = Screen::enter(term)?;
    loop {
        draw(&screen.0, &draft, &mut ui, path)?;
        let key = screen.0.read_key_raw()?;
        if key == Key::CtrlC {
            return Ok(None);
        }
        if key == Key::Char('?') && !matches!(ui.modal, Some(Modal::Edit(..) | Modal::Docs(..))) {
            let (label, text) = focus_help(&draft, &ui);
            ui.help_return = ui.modal.take().map(Box::new);
            ui.modal = Some(Modal::Docs(label, text));
            ui.scroll = 0;
            continue;
        }
        if ui.modal.is_some() && matches!(key, Key::PageUp | Key::PageDown) {
            ui.scroll = if key == Key::PageUp {
                ui.scroll.saturating_sub(3)
            } else {
                ui.scroll + 3
            };
            continue;
        }
        let (height, width) = screen.0.size();
        if height < 14 || width < 52 {
            continue;
        }
        if let Some(modal) = ui.modal.take() {
            ui.follow = true;
            match modal {
                Modal::Docs(label, text) => {
                    match key {
                        Key::Enter | Key::Escape | Key::Char('?') => {
                            ui.modal = ui.help_return.take().map(|modal| *modal);
                            ui.scroll = 0;
                            continue;
                        }
                        _ => {}
                    }
                    ui.modal = Some(Modal::Docs(label, text));
                }
                Modal::Edit(index, rule, mut chars, mut cursor) => {
                    match key {
                        Key::Escape => {
                            ui.follow = true;
                            ui.notice.clear();
                            continue;
                        }
                        Key::Enter => {
                            let input: String = chars.iter().collect();
                            if matches!(SETTINGS[index].kind, Kind::Secret) && input.is_empty() {
                                ui.notice = "Empty replacement kept the current key. Use Clear key to remove it.".into();
                                continue;
                            }
                            let result = if let Some(row) = rule {
                                let mut list = draft.rules(index);
                                if row < list.len() {
                                    list[row] = input;
                                } else {
                                    list.push(input);
                                }
                                draft.set_rules(index, list)
                            } else {
                                draft.set(index, &input)
                            };
                            match result {
                                Ok(()) => {
                                    ui.notice.clear();
                                    ui.follow = true;
                                    continue;
                                }
                                Err(error) => ui.notice = error.to_string(),
                            }
                        }
                        Key::Char('\u{15}') => {
                            chars.clear();
                            cursor = 0;
                        }
                        Key::Char(c) if !c.is_control() => {
                            chars.insert(cursor, c);
                            cursor += 1;
                        }
                        Key::Backspace if cursor > 0 => {
                            cursor -= 1;
                            chars.remove(cursor);
                        }
                        Key::Del if cursor < chars.len() => {
                            chars.remove(cursor);
                        }
                        Key::ArrowLeft => cursor = cursor.saturating_sub(1),
                        Key::ArrowRight => cursor = (cursor + 1).min(chars.len()),
                        Key::Home => cursor = 0,
                        Key::End => cursor = chars.len(),
                        _ => {}
                    }
                    ui.modal = Some(Modal::Edit(index, rule, chars, cursor));
                }
                Modal::Secret(mut selected) => {
                    match key {
                        Key::Escape => continue,
                        Key::ArrowDown | Key::Tab => selected = (selected + 1) % 3,
                        Key::ArrowUp | Key::BackTab => selected = (selected + 2) % 3,
                        Key::Enter => {
                            match selected {
                                0 => ui.modal = Some(Modal::Edit(6, None, Vec::new(), 0)),
                                1 => draft.set(6, "")?,
                                _ => {}
                            }
                            continue;
                        }
                        _ => {}
                    }
                    ui.modal = Some(Modal::Secret(selected));
                }
                Modal::Provider(mut selected) => {
                    match key {
                        Key::Escape => continue,
                        Key::ArrowDown | Key::Tab => selected = (selected + 1) % 3,
                        Key::ArrowUp | Key::BackTab => selected = (selected + 2) % 3,
                        Key::Enter => {
                            draft.provider(["local", "voyage", "openai"][selected])?;
                            continue;
                        }
                        _ => {}
                    }
                    ui.modal = Some(Modal::Provider(selected));
                }
                Modal::Confirm(save, mut yes) => {
                    match key {
                        Key::Escape => continue,
                        Key::ArrowUp | Key::ArrowDown | Key::Tab | Key::BackTab => yes = !yes,
                        Key::Enter => {
                            if yes {
                                return Ok(if save { Some(draft.text) } else { None });
                            }
                            continue;
                        }
                        _ => {}
                    }
                    ui.modal = Some(Modal::Confirm(save, yes));
                }
                Modal::Rule(index, mut selected) => {
                    match key {
                        Key::Escape => continue,
                        Key::ArrowDown | Key::Tab => selected = (selected + 1) % 5,
                        Key::ArrowUp | Key::BackTab => selected = (selected + 4) % 5,
                        Key::Enter => {
                            let field = ui.rules.unwrap();
                            let mut rules = draft.rules(field);
                            match selected {
                                0 => {
                                    let chars: Vec<_> = rules[index].chars().collect();
                                    let cursor = chars.len();
                                    ui.modal = Some(Modal::Edit(field, Some(index), chars, cursor));
                                }
                                1 if index > 0 => {
                                    rules.swap(index, index - 1);
                                    draft.set_rules(field, rules)?;
                                    ui.focus = index - 1;
                                    ui.follow = true;
                                }
                                2 if index + 1 < rules.len() => {
                                    rules.swap(index, index + 1);
                                    draft.set_rules(field, rules)?;
                                    ui.focus = index + 1;
                                    ui.follow = true;
                                }
                                3 => {
                                    rules.remove(index);
                                    draft.set_rules(field, rules)?;
                                }
                                _ => {}
                            }
                            continue;
                        }
                        _ => {}
                    }
                    ui.modal = Some(Modal::Rule(index, selected));
                }
            }
            continue;
        }
        let controls = actions(&draft, &ui);
        match key {
            Key::ArrowDown | Key::Tab => {
                ui.focus = (ui.focus + 1) % controls.len();
                ui.follow = true;
            }
            Key::ArrowUp | Key::BackTab => {
                ui.focus = (ui.focus + controls.len() - 1) % controls.len();
                ui.follow = true;
            }
            Key::PageDown => {
                ui.scroll += 5;
                ui.follow = false;
            }
            Key::PageUp => {
                ui.scroll = ui.scroll.saturating_sub(5);
                ui.follow = false;
            }
            Key::Escape => {
                if ui.rules.take().is_some() {
                    ui.focus = 0;
                    ui.scroll = 0;
                } else if draft.text != draft.base {
                    ui.scroll = 0;
                    ui.modal = Some(Modal::Confirm(false, false));
                } else {
                    return Ok(None);
                }
            }
            Key::Enter => match controls[ui.focus] {
                Action::Field(index) => {
                    ui.scroll = 0;
                    let field = &SETTINGS[index];
                    match field.kind {
                        Kind::Rules => {
                            ui.rules = Some(index);
                            ui.focus = 0;
                            ui.scroll = 0;
                        }
                        Kind::Bool => {
                            let candidate = config::toml_set(
                                &draft.text,
                                field.key,
                                if draft.value(field.key) == true {
                                    "false"
                                } else {
                                    "true"
                                },
                            )?;
                            draft.apply(candidate)?;
                        }
                        Kind::Secret => ui.modal = Some(Modal::Secret(2)),
                        Kind::Provider => {
                            let selected = match draft.value(field.key).as_str() {
                                Some("local") => 0,
                                Some("voyage") => 1,
                                _ => 2,
                            };
                            ui.modal = Some(Modal::Provider(selected));
                        }
                        _ => {
                            if field.key == "embeddings.model"
                                && draft.value("embeddings.backend") == "local"
                            {
                                ui.notice =
                                    "Local model is fixed; no model setting is required.".into();
                                continue;
                            }
                            let value = if matches!(field.kind, Kind::Secret) {
                                String::new()
                            } else {
                                let value = draft.value(field.key);
                                value.as_str().map(str::to_owned).unwrap_or_else(|| {
                                    if value.is_null() {
                                        String::new()
                                    } else {
                                        value.to_string()
                                    }
                                })
                            };
                            let chars: Vec<_> = value.chars().collect();
                            let cursor = chars.len();
                            ui.modal = Some(Modal::Edit(index, None, chars, cursor));
                        }
                    }
                }
                Action::Advanced => {
                    ui.advanced = !ui.advanced;
                    ui.follow = true;
                }
                Action::Back => {
                    ui.rules = None;
                    ui.focus = 0;
                    ui.scroll = 0;
                }
                Action::Add => {
                    let field = ui.rules.unwrap();
                    ui.modal = Some(Modal::Edit(
                        field,
                        Some(draft.rules(field).len()),
                        Vec::new(),
                        0,
                    ));
                }
                Action::Rule(index) => ui.modal = Some(Modal::Rule(index, 0)),
                Action::Save => match draft.validate() {
                    Ok(()) => {
                        ui.notice.clear();
                        ui.scroll = 0;
                        ui.modal = Some(Modal::Confirm(true, false));
                    }
                    Err(error) => ui.notice = error.to_string(),
                },
                Action::Cancel => {
                    if draft.text != draft.base {
                        ui.scroll = 0;
                        ui.modal = Some(Modal::Confirm(false, false));
                    } else {
                        return Ok(None);
                    }
                }
            },
            _ => {}
        }
    }
}

#[cfg(test)]
pub(super) fn test_session(scenario: &str) {
    let fixture = tempfile::tempdir().unwrap();
    let path = fixture.path().join("config.toml");
    let mut base = crate::global_template().unwrap();
    let creating = scenario.starts_with("global-create");
    if scenario.ends_with("narrow") {
        assert!(std::process::Command::new("stty")
            .args(["cols", "52", "rows", "14"])
            .stdin(std::process::Stdio::inherit())
            .status()
            .unwrap()
            .success());
    }
    if !creating {
        base = config::toml_set(&base, "embeddings.api_key", "canary-original-secret").unwrap();
        base = config::toml_set(&base, "database.application_name", "kept-custom-name").unwrap();
        base = format!("# keep this comment\n{base}");
        std::fs::write(&path, &base).unwrap();
    }
    let result = run(&base, &path).unwrap();
    if let Some(content) = result {
        crate::persist_global(&path, !creating, &base, &content).unwrap();
        let cfg = GlobalConfig::from_toml_str(&content).unwrap();
        cfg.validate().unwrap();
        assert!(content.contains("# keep this comment") || creating);
        if creating {
            assert_eq!(cfg.embeddings.backend, config::EmbeddingBackend::Local);
            assert!(cfg.embeddings.api_key.is_none());
            assert!(cfg.embeddings.cache_dir.is_none());
            assert_eq!(cfg.index.exclude, ["generated/"]);
        } else {
            assert_eq!(
                cfg.embeddings.api_key.as_deref(),
                Some("replacement-private-key")
            );
            assert_eq!(
                cfg.database.application_name.as_deref(),
                Some("kept-custom-name")
            );
        }
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            assert_eq!(
                std::fs::metadata(&path).unwrap().permissions().mode() & 0o777,
                0o600
            );
        }
    } else if scenario == "global-cancel" || scenario == "global-plain" {
        assert_eq!(std::fs::read_to_string(&path).unwrap(), base);
    } else {
        panic!("Expected explicit Save");
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn bootstrap_has_real_defaults_and_secrets_are_never_displayed() {
        let text = crate::global_template().unwrap();
        let cfg = GlobalConfig::from_toml_str(&text).unwrap();
        assert!(cfg.embeddings.api_key.is_none());
        assert!(cfg.embeddings.cache_dir.is_none());
        let text = config::toml_set(&text, "embeddings.api_key", "canary-private-key").unwrap();
        let draft = Draft::new(&text).unwrap();
        assert!(!rows(&draft, &Ui::default())
            .iter()
            .any(|row| row.0.contains("canary-private-key")));
        assert_eq!(display(&draft, 6), "Configured (hidden)");
        let mut local = draft;
        local.provider("local").unwrap();
        assert_eq!(display(&local, 6), "Not required (Local)");
    }
    #[test]
    fn edits_keep_comments_optional_settings_and_clear_key_on_provider_change() {
        let mut text = crate::global_template().unwrap();
        text = config::toml_set(&text, "embeddings.api_key", "private-key").unwrap();
        text = config::toml_set(&text, "database.dsn_override", "kept-unused-setting").unwrap();
        let mut draft = Draft::new(&format!("# preserve me\n{text}")).unwrap();
        draft.set(8, "450").unwrap();
        draft
            .set_rules(10, vec!["third_party/".into(), "!third_party/core/".into()])
            .unwrap();
        draft.provider("local").unwrap();
        draft.validate().unwrap();
        assert!(draft.text.contains("# preserve me"));
        assert_eq!(draft.value("database.dsn_override"), "kept-unused-setting");
        assert!(draft.value("embeddings.api_key").is_null());
        assert_eq!(draft.value("watcher.debounce_ms"), 450);
        let before = draft.text.clone();
        assert!(draft.set_rules(9, vec!["[".into()]).is_err());
        assert_eq!(draft.text, before);
    }
    #[test]
    fn atomic_save_rejects_concurrent_changes_and_creates_owner_only_file() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("config.toml");
        let base = crate::global_template().unwrap();
        crate::persist_global(&path, false, "", &base).unwrap();
        std::fs::write(&path, "changed concurrently").unwrap();
        assert!(crate::persist_global(&path, true, &base, &base).is_err());
        assert_eq!(
            std::fs::read_to_string(path).unwrap(),
            "changed concurrently"
        );
    }
}
