//! Bounded metadata inventory. Never reads file contents or consults Git ignores.
use super::{CompiledRules, Defaults, Policy, PolicyError, Result};
use crate::pipeline::Decision;
use serde::Serialize;
use std::{
    collections::HashMap,
    fs,
    path::{Path, PathBuf},
    time::{Duration, Instant},
};

const SAMPLE_LIMIT: usize = 20;
const MIB: u64 = 1024 * 1024;

/// Display is informational; encoding + hex is the lossless locator.
#[derive(Debug, Clone, Serialize)]
pub struct ReportPath {
    pub display: String,
    pub encoding: &'static str,
    pub hex: String,
}
impl ReportPath {
    pub fn new(path: &Path) -> Self {
        #[cfg(unix)]
        let (encoding, bytes) = {
            use std::os::unix::ffi::OsStrExt;
            ("unix-bytes", path.as_os_str().as_bytes().to_vec())
        };
        #[cfg(windows)]
        let (encoding, bytes) = {
            use std::os::windows::ffi::OsStrExt;
            (
                "windows-utf16le",
                path.as_os_str()
                    .encode_wide()
                    .flat_map(u16::to_le_bytes)
                    .collect::<Vec<_>>(),
            )
        };
        Self {
            display: path.to_string_lossy().into_owned(),
            encoding,
            hex: bytes.iter().map(|b| format!("{b:02x}")).collect(),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Budget {
    pub duration: Duration,
    pub entries: u64,
}
impl Default for Budget {
    fn default() -> Self {
        Self {
            duration: Duration::from_secs(2),
            entries: 100_000,
        }
    }
}
#[derive(Debug, Default, Clone, Serialize)]
pub struct Totals {
    pub files: u64,
    pub bytes: u64,
}
#[derive(Debug, Serialize)]
pub struct FileSize {
    pub path: ReportPath,
    pub bytes: u64,
}
#[derive(Debug, Serialize)]
pub struct DirectoryCost {
    pub path: ReportPath,
    pub selected: Totals,
    pub dependency_build_or_environment: bool,
}
#[derive(Debug, Serialize)]
pub struct Unreadable {
    pub path: ReportPath,
    pub operation: &'static str,
}
#[derive(Debug, Serialize)]
pub struct Report {
    pub scope: &'static str,
    pub root: ReportPath,
    pub complete: bool,
    pub counts_are_lower_bounds: bool,
    pub stop_reason: Option<&'static str>,
    pub entry_limit: u64,
    pub time_budget_ms: u128,
    pub elapsed_ms: u128,
    pub visited_entries: u64,
    pub visited_regular_files: u64,
    pub tier1: Totals,
    pub tier2: Totals,
    pub observed_excluded_files: u64,
    pub pruned_directories: u64,
    pub pruned_directory_samples: Vec<ReportPath>,
    pub excluded_descendant_count: Option<u64>,
    pub skipped_symlinks: u64,
    pub skipped_special_entries: u64,
    pub unreadable_entries: u64,
    pub unreadable_samples: Vec<Unreadable>,
    pub largest_files: Vec<FileSize>,
    pub costly_directories: Vec<DirectoryCost>,
    pub selected_problem_directories: u64,
    pub problem_directory_samples: Vec<ReportPath>,
    /// Advisory rule additions only; not applied by preflight.
    pub candidate_exclusions: Vec<String>,
    pub advice: &'static str,
    pub reasons: Vec<&'static str>,
    pub capabilities: serde_json::Value,
}
impl Report {
    fn unreadable(&mut self, path: &Path, operation: &'static str) {
        self.unreadable_entries += 1;
        self.complete = false;
        if self.unreadable_samples.len() < SAMPLE_LIMIT {
            self.unreadable_samples.push(Unreadable {
                path: ReportPath::new(path),
                operation,
            });
        }
    }
}
fn problematic(path: &Path) -> bool {
    matches!(
        path.file_name().and_then(|p| p.to_str()),
        Some(
            "node_modules"
                | "vendor"
                | "target"
                | "dist"
                | "build"
                | ".direnv"
                | "venv"
                | ".venv"
                | "__pycache__"
                | ".next"
        )
    )
}

/// Root must be a directory. The budget bounds enumeration, not blocking OS
/// calls or final report serialization. Symlinks encountered by the walk are
/// skipped, including dangling links. Like indexing, this is not an atomic FS
/// snapshot; a concurrent rename/replacement can invalidate observations.
pub fn scan(root: &Path, policy: &Policy, defaults: &Defaults, budget: Budget) -> Result<Report> {
    let start = Instant::now();
    let root = fs::canonicalize(root)
        .map_err(|_| PolicyError::new("invalid_path", "cannot resolve inventory directory"))?;
    if !root.is_dir() {
        return Err(PolicyError::new(
            "invalid_path",
            "inventory root must be a directory",
        ));
    }
    let rules = CompiledRules::new(&root, policy, defaults)?;
    let mut report = Report {
        scope: "selected_checkout",
        root: ReportPath::new(&root),
        complete: true,
        counts_are_lower_bounds: false,
        stop_reason: None,
        entry_limit: budget.entries,
        time_budget_ms: budget.duration.as_millis(),
        elapsed_ms: 0,
        visited_entries: 0,
        visited_regular_files: 0,
        tier1: Totals::default(),
        tier2: Totals::default(),
        observed_excluded_files: 0,
        pruned_directories: 0,
        pruned_directory_samples: vec![],
        excluded_descendant_count: Some(0),
        skipped_symlinks: 0,
        skipped_special_entries: 0,
        unreadable_entries: 0,
        unreadable_samples: vec![],
        largest_files: vec![],
        costly_directories: vec![],
        selected_problem_directories: 0,
        problem_directory_samples: vec![],
        candidate_exclusions: vec![],
        advice: "start",
        reasons: vec![],
        capabilities: serde_json::json!({
            "metadata_only":true, "content_validity":"not_checked", "git_ignores":false,
            "follows_symlinks":false, "atomic_filesystem_snapshot":false,
            "current_indexer_max_file_bytes":10*MIB, "structural_parse_limit_bytes":MIB,
            "sample_limit":SAMPLE_LIMIT, "hard_wall_clock_limit":false
        }),
    };
    // Iterators avoid reading an enormous directory into memory before checking
    // the entry budget. Only the current ancestry holds open directory handles.
    let mut stack = vec![];
    match fs::read_dir(&root) {
        Ok(entries) => stack.push((PathBuf::new(), entries)),
        Err(_) => report.unreadable(Path::new(""), "read_directory"),
    }
    let mut costs: HashMap<PathBuf, Totals> = HashMap::new();
    while !stack.is_empty() {
        if report.visited_entries >= budget.entries {
            report.stop_reason = Some("entry_limit");
            report.complete = false;
            break;
        }
        if start.elapsed() >= budget.duration {
            report.stop_reason = Some("time_limit");
            report.complete = false;
            break;
        }
        let (parent, entries) = stack.last_mut().unwrap();
        let entry = match entries.next() {
            None => {
                stack.pop();
                continue;
            }
            Some(Err(_)) => {
                report.visited_entries += 1;
                report.unreadable(parent, "read_entry");
                continue;
            }
            Some(Ok(entry)) => entry,
        };
        report.visited_entries += 1;
        let relative = parent.join(entry.file_name());
        if start.elapsed() >= budget.duration {
            report.stop_reason = Some("time_limit");
            report.complete = false;
            break;
        }
        let metadata = match fs::symlink_metadata(entry.path()) {
            Ok(value) => value,
            Err(_) => {
                report.unreadable(&relative, "metadata");
                continue;
            }
        };
        if metadata.file_type().is_symlink() {
            report.skipped_symlinks += 1;
            continue;
        }
        let decision = rules.classify_entry(&relative, metadata.is_dir());
        if metadata.is_dir() {
            if decision == Decision::Drop {
                report.pruned_directories += 1;
                if report.pruned_directory_samples.len() < SAMPLE_LIMIT {
                    report
                        .pruned_directory_samples
                        .push(ReportPath::new(&relative));
                }
            } else {
                if start.elapsed() >= budget.duration {
                    report.stop_reason = Some("time_limit");
                    report.complete = false;
                    break;
                }
                match fs::read_dir(entry.path()) {
                    Ok(entries) => stack.push((relative, entries)),
                    Err(_) => report.unreadable(&relative, "read_directory"),
                }
            }
            continue;
        }
        if !metadata.is_file() {
            report.skipped_special_entries += 1;
            continue;
        }
        report.visited_regular_files += 1;
        let totals = match decision {
            Decision::Drop => {
                report.observed_excluded_files += 1;
                continue;
            }
            Decision::Tier1 => &mut report.tier1,
            Decision::Tier2 => &mut report.tier2,
        };
        totals.files += 1;
        totals.bytes = totals.bytes.saturating_add(metadata.len());
        report.largest_files.push(FileSize {
            path: ReportPath::new(&relative),
            bytes: metadata.len(),
        });
        report.largest_files.sort_by(|a, b| {
            b.bytes
                .cmp(&a.bytes)
                .then_with(|| a.path.hex.cmp(&b.path.hex))
        });
        report.largest_files.truncate(SAMPLE_LIMIT);
        for ancestor in relative
            .ancestors()
            .skip(1)
            .take_while(|p| !p.as_os_str().is_empty())
        {
            let cost = costs.entry(ancestor.to_owned()).or_default();
            cost.files += 1;
            cost.bytes = cost.bytes.saturating_add(metadata.len());
        }
    }
    let mut costs: Vec<_> = costs.into_iter().collect();
    costs.sort_by(|(pa, a), (pb, b)| {
        b.bytes
            .cmp(&a.bytes)
            .then_with(|| b.files.cmp(&a.files))
            .then_with(|| pa.cmp(pb))
    });
    for (path, _) in costs.iter().filter(|(p, _)| problematic(p)) {
        report.selected_problem_directories += 1;
        // problematic() only accepts literal ASCII basenames, so no submitted
        // path is interpreted as glob syntax. These proposals are family-wide.
        let pattern = format!("**/{}/", path.file_name().unwrap().to_str().unwrap());
        if !report.candidate_exclusions.contains(&pattern) {
            report.candidate_exclusions.push(pattern);
        }
        if report.problem_directory_samples.len() < SAMPLE_LIMIT {
            report.problem_directory_samples.push(ReportPath::new(path));
        }
    }
    report.costly_directories = costs
        .into_iter()
        .take(SAMPLE_LIMIT)
        .map(|(path, selected)| DirectoryCost {
            dependency_build_or_environment: problematic(&path),
            path: ReportPath::new(&path),
            selected,
        })
        .collect();
    if report.tier1.files + report.tier2.files > 10_000 {
        report.reasons.push("selected_files_over_10000");
    }
    if report.tier1.bytes.saturating_add(report.tier2.bytes) > 100 * MIB {
        report.reasons.push("selected_bytes_over_100_mib");
    }
    if report
        .largest_files
        .first()
        .is_some_and(|f| f.bytes > 10 * MIB)
    {
        report.reasons.push("file_exceeds_indexer_10_mib_limit");
    }
    if report.selected_problem_directories > 0 {
        report
            .reasons
            .push("selected_dependency_build_or_environment_directory");
    }
    if !report.complete {
        report.reasons.push("incomplete_inventory");
    }
    if report.unreadable_entries > 0 {
        report.reasons.push("unreadable_entries");
    }
    if !report.reasons.is_empty() {
        report.advice = "refine_configuration_with_or_without_agent";
    }
    if report.stop_reason.is_none() && report.unreadable_entries > 0 {
        report.stop_reason = Some("unreadable_entries");
    }
    report.counts_are_lower_bounds = !report.complete;
    if report.pruned_directories > 0 || !report.complete {
        report.excluded_descendant_count = None;
    }
    report.elapsed_ms = start.elapsed().as_millis();
    Ok(report)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn policy() -> (Policy, Defaults) {
        let mut defaults = Defaults::shipped();
        defaults.index.exclude.clear();
        defaults.index.vendor.clear();
        (Policy::shipped("fixture".into()), defaults)
    }
    fn put(root: &Path, relative: &str, bytes: &[u8]) {
        let file = root.join(relative);
        fs::create_dir_all(file.parent().unwrap()).unwrap();
        fs::write(file, bytes).unwrap();
    }
    #[test]
    fn inventory_prunes_parents_ignores_gitignore_and_keeps_text_fallback() {
        let root = tempfile::tempdir().unwrap();
        for (path, bytes) in [
            ("src/main.rs", b"main".as_slice()),
            ("ignored.odd", b"hello"),
            (".gitignore", b"ignored.odd"),
            ("ignored.lock", b"excluded file"),
            ("node_modules/pkg/a.js", b"vendor"),
            ("excluded/deep/file", b"excluded"),
            (".git/config", b"admin"),
        ] {
            put(root.path(), path, bytes);
        }
        let (mut policy, defaults) = policy();
        policy.index.exclude = vec![
            "excluded/".into(),
            "!excluded/deep/file".into(),
            "*.lock".into(),
        ];
        policy.index.vendor = vec!["node_modules/".into()];
        let report = scan(root.path(), &policy, &defaults, Budget::default()).unwrap();
        assert!(report.complete);
        assert_eq!(report.tier1.files, 3);
        assert_eq!(report.tier1.bytes, 20);
        assert_eq!(report.tier2.files, 1);
        assert_eq!(report.tier2.bytes, 6);
        assert_eq!(report.pruned_directories, 2);
        assert_eq!(report.excluded_descendant_count, None);
        assert_eq!(report.visited_regular_files, 5);
        assert_eq!(report.observed_excluded_files, 1);
        assert_eq!(report.selected_problem_directories, 1);
        assert_eq!(report.candidate_exclusions, vec!["**/node_modules/"]);
        assert!(report
            .reasons
            .contains(&"selected_dependency_build_or_environment_directory"));
        policy.index.exclude.push("!excluded/".into());
        let report = scan(root.path(), &policy, &defaults, Budget::default()).unwrap();
        assert_eq!(report.tier1.files, 4);
    }
    #[test]
    fn budgets_report_lower_bounds_and_never_advise_start() {
        let root = tempfile::tempdir().unwrap();
        for i in 0..5 {
            put(root.path(), &format!("{i}.txt"), b"x");
        }
        let (policy, defaults) = policy();
        let report = scan(
            root.path(),
            &policy,
            &defaults,
            Budget {
                entries: 2,
                ..Budget::default()
            },
        )
        .unwrap();
        assert!(!report.complete);
        assert!(report.counts_are_lower_bounds);
        assert_eq!(report.visited_entries, 2);
        assert_eq!(report.tier1.files, 2);
        assert_eq!(report.stop_reason, Some("entry_limit"));
        assert_ne!(report.advice, "start");
        let report = scan(
            root.path(),
            &policy,
            &defaults,
            Budget {
                duration: Duration::ZERO,
                ..Budget::default()
            },
        )
        .unwrap();
        assert_eq!(report.stop_reason, Some("time_limit"));
        assert_eq!(report.visited_entries, 0);
    }
    #[test]
    fn metadata_only_reports_sparse_large_files_and_caps_samples() {
        let root = tempfile::tempdir().unwrap();
        for i in 1..=25 {
            let file = fs::File::create(root.path().join(format!("{i}.unknown"))).unwrap();
            file.set_len(i * MIB).unwrap();
        }
        let (policy, defaults) = policy();
        let report = scan(root.path(), &policy, &defaults, Budget::default()).unwrap();
        assert!(report.complete);
        assert_eq!(report.tier1.files, 25);
        assert_eq!(report.tier1.bytes, 325 * MIB);
        assert_eq!(report.largest_files.len(), 20);
        assert_eq!(report.largest_files[0].bytes, 25 * MIB);
        assert!(report
            .reasons
            .contains(&"file_exceeds_indexer_10_mib_limit"));
        assert!(report.reasons.contains(&"selected_bytes_over_100_mib"));
    }
    #[cfg(unix)]
    #[test]
    fn symlinks_are_not_followed_and_non_utf8_paths_are_lossless() {
        use std::os::unix::{ffi::OsStrExt, fs::symlink};
        let root = tempfile::tempdir().unwrap();
        let outside = tempfile::tempdir().unwrap();
        put(outside.path(), "secret.txt", b"outside");
        symlink(outside.path(), root.path().join("outside")).unwrap();
        symlink("absent", root.path().join("dangling")).unwrap();
        let file = std::ffi::OsStr::from_bytes(b"name\xff");
        fs::write(root.path().join(file), b"one").unwrap();
        let (policy, defaults) = policy();
        let report = scan(root.path(), &policy, &defaults, Budget::default()).unwrap();
        assert!(report.complete);
        assert_eq!(report.skipped_symlinks, 2);
        assert_eq!(report.tier1.files, 1);
        assert_eq!(report.tier1.bytes, 3);
        assert_eq!(report.largest_files[0].path.encoding, "unix-bytes");
        assert_eq!(report.largest_files[0].path.hex, "6e616d65ff");
    }
    #[cfg(unix)]
    #[test]
    fn unreadable_directory_keeps_partial_counts_and_refinement_advice() {
        use std::os::unix::fs::PermissionsExt;
        let root = tempfile::tempdir().unwrap();
        put(root.path(), "locked/file", b"x");
        let locked = root.path().join("locked");
        fs::set_permissions(&locked, fs::Permissions::from_mode(0o000)).unwrap();
        let actually_unreadable = fs::read_dir(&locked).is_err();
        let (policy, defaults) = policy();
        let report = scan(root.path(), &policy, &defaults, Budget::default()).unwrap();
        fs::set_permissions(&locked, fs::Permissions::from_mode(0o700)).unwrap();
        // Root/CAP_DAC_OVERRIDE can enumerate mode 000; the same test verifies
        // ordinary-user failures where the platform enforces the permission.
        if actually_unreadable {
            assert!(!report.complete);
            assert_eq!(report.unreadable_entries, 1);
            assert_eq!(report.stop_reason, Some("unreadable_entries"));
            assert!(report.counts_are_lower_bounds);
            assert_ne!(report.advice, "start");
        }
    }
}
