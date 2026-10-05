# Working on Muninn

Muninn is persistent code search and repository knowledge for MCP clients,
including Codex and Claude Code. See [README.md](README.md) for purpose,
[AGENTS.md](AGENTS.md) for installation automation, and
[Development](docs/development.md) for the current architecture and build/test flow.
Reading these instructions does not authorize an installation or live migration.

## Repository conventions

- Use the existing Nix flake and intended checkout. `nix build .#muninn-static`
  builds the three distributable binaries; a plain Cargo release build is not
  a promise of static linking.
- Use postgres-ai for the compatible database stack. Inspect integration-test
  targets before running them; a dev-shell `DATABASE_URL` is not the application's
  actual configuration. The guarded disposable harness is
  `bash muninn-setup/test-persistence.sh` inside the dev environment.
- Current database access is tokio-postgres. Migration execution uses the Kryzhen
  Rust library. Do not use SQLx migration, revert or offline-cache commands.
- Existing migration blocks are immutable. Use semantic filenames and append
  related blocks. All files in `migrations/repo/` form one template applied to
  each family's application schema. AGE owns graph schemas through its API.
- One application schema belongs to a family; Git checkouts have separate AGE
  graphs and share chunk/vector file versions through a moving base and deltas.
  Retain the last completed index during incomplete Git operations/conflicts.
- New-family configuration lives in the database and has explicit first start.
  Use JSON for agent configuration, the TUI for humans. Credentials stay global.
  Legacy `.muninn.toml` handling is not the new configuration workflow.
- Read [spec/README.md](spec/README.md) before making formal claims. It records
  the model's scope and runtime gaps. Preserve general laws; a successful Agda
  check does not prove the Rust implementation correct.
- Keep credentials, machine-specific backups and generated build artifacts
  out of Git. Review source changes separately from deployment/data changes.

## Using the installed tools

The [shared Muninn skill](docs/claude-code-setup/skill/SKILL.md) explains when
indexed search helps, how to select a checkout and how to validate results.
Direct reads and `rg` remain appropriate for known locations and stale/missing
index results. Tool-use reminders are advisory, not compulsory search or rating
steps. Curated knowledge uses an exact repository-path key; code search resolves
checkout/family identity separately.

Refer to current guides rather than copying old commands from `docs/plans/` or
`docs/superpowers/`. Those files retain historical decisions and obsolete stages.
