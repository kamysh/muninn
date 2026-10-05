# AGENTS.md — Muninn installation and repository guidance

Muninn provides persistent code search and repository knowledge through MCP.
Read [README.md](README.md) for purpose and limits. Use this procedure when asked
to install it; for development use [docs/development.md](docs/development.md).
Reading this file during another task is not an instruction to install or upgrade.

## Determine the installation path

Inspect what already exists before proposing changes: binary versions, service,
MCP registration, global configuration presence and intended database. Preserve
existing connection settings and credentials. Do not print secrets into reports.

- **Existing install:** follow [Upgrading](docs/upgrading.md). Normal
  startup/preparation applies pending schema migrations automatically; no
  separate user-run migration script is required.
- **Fresh install:** follow the sequence below and the postgres-ai/platform
  commands in [Getting started](docs/get-started.md). The
  [custom database guide](docs/own-database.md) is an advanced alternative only
  when the user deliberately chooses to assemble the prerequisites.
- **Agent integration only:** use [Agent setup](docs/claude-code-setup/INSTALL.md).

These are 1.0.0 instructions. At the 2026-10-05 audit, the latest published
release was 0.9.4. Use a source checkout containing the 1.0 implementation until
a matching release exists; never silently install an older archive for this flow.

## Agree on consequential setup choices

Resolve missing choices from the user or existing installation: database/container
and volume identity, host/port, application role/database, local versus hosted
embeddings, binary destination, service manager and target agent client(s).
Use an existing suitable database/container when agreed; installation does not
imply permission to replace one. Do not re-ask choices already established.

Present the actual affected resources before creation, credential changes,
service changes or registration. After approval, complete and verify the agreed
stage. Leave unrelated hooks, permissions, client settings and other applications
unchanged. Never drop a database or overwrite another installation to resolve a
name or port conflict.

## Execute the fresh-install sequence

1. **Database.** Recommend [postgres-ai](https://github.com/kamysh/postgres-ai),
   creating or reusing an instance as agreed. It bundles the compatible PostgreSQL,
   pgvector, AGE and pgcrypto prerequisites. Verify readiness and the actual
   database's extensions/privileges: a fresh container seeds template1; an existing
   volume may differ. Do not present independent extension assembly as the default
   setup. Use the [advanced guide](docs/own-database.md) only for an explicitly
   chosen custom stack. Keep server upgrades separate from app installation.
2. **Credentials.** Reuse the matching `~/.pgpass` entry or establish a new one
   with owner-only permissions. The bundled `create-db-user.sh` changes the
   role password; use it only for that agreed setup. It expects simple identifiers
   and a password safe for SQL interpolation, such as generated hexadecimal.
   Verify the application role can connect to the intended database.
3. **Binaries.** Build `nix build .#muninn-static` from the selected source tree,
   or inspect and install all three binaries from a matching published release.
   Preserve old binaries on upgrade. Verify all versions and actual executable
   paths; use absolute paths in service/MCP registration.
4. **Global bootstrap.** Use `muninn init key=value …` for noninteractive setup.
   It writes `~/.config/muninn/config.toml` and applies public migrations. Do not
   run bare `init` against a missing file: it opens `$EDITOR`. Existing global
   settings can be inspected/updated through `config … --global`; family policy
   uses a different interface. Do not expose API keys in generated instructions.
5. **Daemon.** Install/enable the agreed systemd or launchd service using the
   [platform procedures](docs/get-started.md#5-run-the-watcher). Verify its actual
   state and logs. Existing enabled registrations may index when it starts.
6. **First family.** Use the JSON sequence below. Registration/configuration alone
   does not authorize first indexing. New-family defaults use Voyage rather than
   inheriting the global backend; explicitly choose the intended backend before
   registration. Existing embedding-profile changes are unsupported.
7. **Agent client.** Register Muninn in Codex and/or Claude and install the shared
   skill through [Agent setup](docs/claude-code-setup/INSTALL.md). Include the
   [purpose-focused reminder](docs/claude-code-setup/INSTALL.md#install-the-startup-reminder)
   in the proposed setup: choose Muninn-only or combined Mimir/Muninn wording
   according to the installed tools. Merge guidance rather than replacing whole
   settings files. Verify startup, resume and post-compaction delivery, including
   Codex hook review. The reminder supports informed tool choice; it does not
   require a search before every action, a score or a writeback each turn.

## JSON configuration and first start

Use an absolute path for the selected checkout. The shared
[Muninn skill](docs/claude-code-setup/skill/SKILL.md) defines complete request
examples, revision guards and error handling. Inspect and check operations do
not run migrations or write configuration. The examples below require `jq`.

For a new family, obtain creation policy and inventory first:

```sh
ROOT=/absolute/path/to/repo
muninn preflight "$ROOT" --json > inventory.json
jq -e '.ok' inventory.json
jq '{api_version:1, policy:.data.policy}' inventory.json > initial.json
```

Edit the complete request to reflect the intended file selection and backend.
For local embeddings specifically, set `policy.embeddings.backend` to `"local"`
and `policy.embeddings.model` to `null`. Keep credentials in the global setup.
Then check the candidate and inspect its inventory/advice before registration:

```sh
muninn config "$ROOT" --json --check - < initial.json
muninn add "$ROOT" --json --input - < initial.json
muninn preflight "$ROOT" --json > ready.json
jq -e '.ok' ready.json
```

When first indexing is approved, guard the decision against configuration changes:

```sh
jq '.data | {api_version:1, expected_family_id:.family_id,
  expected_revision:.revision}' ready.json > start.json
muninn start "$ROOT" --json --input - < start.json
```

Check every command's exit status and JSON `ok`; stop the sequence on an error.
These JSON files are temporary request/response artifacts, not stored config.
An enabled family discovers worktrees automatically. Policy saves for an enabled
family can trigger reconciliation. Do not repeatedly add each linked worktree.
For an existing family, inspect `config PATH --json` and use the skill's complete
revision-guarded check/apply request; do not reuse an initial registration request.

## Verify the result

Report each observed outcome separately:

- Three binary versions and installation paths.
- Database connection and required extensions under the application role.
- Family policy, indexing authorization and preflight warnings.
- Daemon status and indexing completion/error evidence.
- A fresh client MCP connection and a known-term search in the intended checkout.
- Skill discovery and reminder delivery in the chosen client. Distinguish tested
  command output from observed startup/resume/post-compaction delivery, and report
  any lifecycle check not performed or a reminder explicitly omitted by agreement.

`muninn status` is a registry overview. Its path form, and `pause`, `resume` and
`remove`, require the registered locator displayed there; arbitrary worktree paths
are supported by code search and policy commands, not those legacy controls.
`remove` deletes the family's code index, including its worktree graphs. Removing
one worktree should use Git's normal workflow and daemon reconciliation instead.
Curated knowledge remains keyed by exact repository-path strings.

## Development boundaries

The build uses tokio-postgres and the Kryzhen Rust library. Never run SQLx migrate,
revert or offline-cache commands for this source tree. Existing migration blocks
are immutable; append semantically related blocks or add semantic filenames.
`migrations/repo/` is one template applied to each family application schema.
AGE creates and removes its own graph schemas through its API.

Keep credentials and machine-specific backups outside Git. Treat files under `docs/plans/` and `docs/superpowers/` as historical design
records, not current installation instructions. See [the formal-model boundary](spec/README.md)
before claiming that an Agda theorem proves runtime behavior.
