//! Process-level JSON errors, without opening any config or DB connection.
use serde_json::Value;
use std::process::Command;

#[test]
fn json_argument_errors_emit_one_sanitized_document_and_exit_two() {
    for args in [
        vec!["config", "/unused", "--json", "--apply", "do-not-echo-this"],
        vec!["config", "--json"],
        vec!["preflight", "--json"],
        vec!["config", "/unused", "--json", "--check", "do-not-echo-this"],
    ] {
        let result = Command::new(env!("CARGO_BIN_EXE_muninn"))
            .args(args)
            .output()
            .unwrap();
        assert_eq!(result.status.code(), Some(2));
        let document: Value = serde_json::from_slice(&result.stdout).unwrap();
        assert_eq!(document["api_version"], 1);
        assert_eq!(document["ok"], false);
        assert_eq!(document["error"]["code"], "invalid_request");
        assert!(!String::from_utf8_lossy(&result.stdout).contains("do-not-echo-this"));
        assert!(result.stderr.is_empty());
    }
}

#[test]
fn malformed_write_payloads_fail_before_loading_global_configuration() {
    use std::io::Write;
    use std::process::Stdio;
    for args in [
        vec!["config", "/unused", "--json", "--apply", "-"],
        vec!["add", "/unused", "--json", "--input", "-"],
    ] {
        let mut child = Command::new(env!("CARGO_BIN_EXE_muninn"))
            .args(args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        child
            .stdin
            .take()
            .unwrap()
            .write_all(b"{\"api_key\":\"do-not-echo-this\"}")
            .unwrap();
        let result = child.wait_with_output().unwrap();
        assert_eq!(result.status.code(), Some(2));
        let document: Value = serde_json::from_slice(&result.stdout).unwrap();
        assert_eq!(document["error"]["code"], "invalid_request");
        assert!(!String::from_utf8_lossy(&result.stdout).contains("do-not-echo-this"));
        assert!(result.stderr.is_empty());
    }
}

#[test]
fn interactive_forms_refuse_pipes_before_loading_config_or_database() {
    for command in ["add", "config"] {
        let result = Command::new(env!("CARGO_BIN_EXE_muninn"))
            .args([command, "/unused"])
            .output()
            .unwrap();
        assert!(!result.status.success());
        assert!(result.stdout.is_empty());
        assert!(String::from_utf8_lossy(&result.stderr).contains("requires a terminal"));
    }
}
