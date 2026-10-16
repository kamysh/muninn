use muninn_core::config::DatabaseConfig;

#[test]
fn password_and_file_roundtrip_without_debug_disclosure() {
    let text = r#"
host = "localhost"
port = 5432
dbname = "test"
user = "tester"
password = ' secret:"quoted"\with spaces '
pgpassfile = '/private/passwords'
ssl_mode = "verify-full"
ssl_root_cert = '/private/root.pem'
ssl_client_cert = '/private/client.pem'
ssl_client_key = '/private/client.key'
"#;
    let config: DatabaseConfig = toml::from_str(text).unwrap();
    assert_eq!(
        config.password.as_deref(),
        Some(" secret:\"quoted\"\\with spaces ")
    );
    assert_eq!(config.pgpassfile.as_deref(), Some("/private/passwords"));
    let debug = format!("{config:?}");
    assert!(!debug.contains("secret"));
    assert!(debug.contains("[REDACTED]"));
    let serialized = toml::to_string(&config).unwrap();
    assert_eq!(
        config,
        toml::from_str::<DatabaseConfig>(&serialized).unwrap()
    );
}

#[test]
fn existing_configuration_needs_no_new_keys() {
    let config: DatabaseConfig =
        toml::from_str("host='localhost'\nport=5432\ndbname='test'\nuser='tester'\n").unwrap();
    assert_eq!(config.password, None);
    assert_eq!(config.pgpassfile, None);
    let serialized = toml::to_string(&config).unwrap();
    assert!(!serialized.contains("password"));
    assert!(!serialized.contains("pgpassfile"));
}

#[test]
fn invalid_config_diagnostics_do_not_echo_passwords() {
    use muninn_core::config::{toml_get, toml_set, toml_unset, GlobalConfig};
    let content = "[database]\npassword = 'private-password' trailing-secret\n";
    let errors = [
        GlobalConfig::from_toml_str(content)
            .unwrap_err()
            .to_string(),
        toml_get(content, "database.password")
            .unwrap_err()
            .to_string(),
        toml_set(content, "database.host", "localhost")
            .unwrap_err()
            .to_string(),
        toml_unset(content, "database.password")
            .unwrap_err()
            .to_string(),
    ];
    for error in errors {
        assert!(!error.contains("private-password"));
        assert!(!error.contains("trailing-secret"));
    }
}
