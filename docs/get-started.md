# Get started with Muninn 1.0

This is the human procedure for a **new installation**. For an existing install,
start with [Upgrading](upgrading.md); do not create a replacement database.
Agents use [AGENTS.md](../AGENTS.md) for the automation sequence and this guide
for the shared platform commands.

A working installation needs a database with the required extensions, all three
binaries, global connection configuration, an enabled family with a completed
index, a running watcher, and an MCP connection in your chosen client. A binary
on PATH or an MCP registration alone does not verify the whole installation.

## 1. Choose the database and client

You need Git, a shell, a PostgreSQL client (`psql`), and Codex, Claude Code or
another client that can launch a local stdio MCP process. The recommended database
is [postgres-ai](https://github.com/kamysh/postgres-ai), used through Docker in
this guide. It supplies compatible PostgreSQL, pgvector, AGE and pgcrypto together.
You can reuse an existing postgres-ai instance. Assembling those prerequisites
yourself is an [advanced, non-recommended alternative](own-database.md).

The examples use container `postgres-ai`, volume `muninn_data`, host `localhost`,
port `5432`, and database/role `muninn`. Check `docker ps -a` and local listening
ports before creating anything. Reuse a suitable existing container if desired,
but keep the Muninn database/role distinct from other applications such as Mimir.
Choose different names/ports when needed and carry them through every command.

## 2. Prepare a new database

Only for a new container:

```sh
docker run -d \
  --name postgres-ai --restart always \
  -p 127.0.0.1:5432:5432 \
  -v muninn_data:/var/lib/postgresql/data \
  kamysh/postgres-ai:latest
```

Wait for readiness, then verify:

```sh
docker exec postgres-ai psql -U postgres -d postgres -c 'SELECT 1'
```

This image initializes extensions in `template1` for new databases. Reusing an
old volume does not rerun initialization: check extensions in the actual Muninn
database after creation. The image's server configuration preloads AGE.

For a **new** Muninn role, choose a password and add its entry to `~/.pgpass`:

```text
localhost:5432:muninn:muninn:YOUR_PASSWORD
```

Use a generated hexadecimal password (`openssl rand -hex 32` can generate one)
with the bundled setup helper: its SQL interpolation does not escape arbitrary
quotes. Edit the file without overwriting entries for other databases, and run:

```sh
chmod 600 "$HOME/.pgpass"
```

From the same source checkout as the binaries, run the helper after reviewing
its arguments. It creates a missing role/database, sets the role password and
grants AGE access; it does not install missing extensions:

```sh
bash muninn-setup/create-db-user.sh \
  --container postgres-ai --host localhost --port 5432 \
  --user muninn --db muninn
```

For an existing role, verify its credentials/ownership before using a helper
that can reset its password. Verify the actual target as the application user:

```sh
psql -X -h localhost -p 5432 -U muninn -d muninn -c '\conninfo'
psql -X -h localhost -p 5432 -U muninn -d muninn \
  -c 'SELECT extname, extversion FROM pg_extension ORDER BY extname;'
```

`age`, `vector` and `pgcrypto` must be present. See [own database](own-database.md)
for missing extensions, preload and privilege setup.

## 3. Install matching binaries

These docs describe the 1.0.0 source. At the 2026-10-05 audit, GitHub's latest
release was 0.9.4. Until a matching release is published, use a checkout containing
the 1.0 implementation and [Nix](https://nixos.org/download/), with flakes enabled:

```sh
# Run from the Muninn 1.0 source checkout.
nix build .#muninn-static
mkdir -p "$HOME/.local/bin"
install -m 755 result/bin/muninn result/bin/muninn-index result/bin/muninn-mcp \
  "$HOME/.local/bin/"
```

For an upgrade, stage the files and follow [Upgrading](upgrading.md) before
replacing running binaries. The `muninn-static` derivation produces portable
static Linux binaries; macOS still uses system frameworks. See
[build details](development.md#building-and-testing).

When using a published archive, select an explicit matching release and inspect
its assets. CI builds `linux-amd64`, `linux-arm64` and `darwin-arm64`; use an Intel
macOS archive only if that release actually provides one. Do not substitute a
`releases/latest` URL without checking the version. Each archive must contain
`muninn`, `muninn-index`, and `muninn-mcp`.

Put `~/.local/bin` on PATH in your shell startup file if necessary:

```sh
export PATH="$HOME/.local/bin:$PATH"
muninn --version
muninn-index --version
muninn-mcp --version
```

All three should report the intended version (1.0.0 for this tree).

## 4. Bootstrap the global configuration

This local-backend example needs no embedding API key:

```sh
muninn init database.host=localhost database.port=5432 \
  database.dbname=muninn database.user=muninn embeddings.backend=local
muninn status
```

`init` writes `~/.config/muninn/config.toml` with owner-only permissions and runs
public migrations. With no assignments, it opens an editor only when the file
does not exist; an existing file's contents are preserved. Credentials and runtime
settings belong here, while family policies are stored in the database.

For hosted embeddings, see [Configuration](configuration.md). Hosted embedding
requests include source chunks. The local model is downloaded on first use;
subsequent embedding work can run offline when cached.

## 5. Run the watcher

### Linux with systemd

Create `~/.config/systemd/user/muninn-index.service`:

```ini
[Unit]
Description=Muninn indexer daemon
After=network.target

[Service]
Type=simple
ExecStart=%h/.local/bin/muninn-index
Restart=on-failure
RestartSec=5
Environment=RUST_LOG=info

[Install]
WantedBy=default.target
```

Then:

```sh
systemctl --user daemon-reload
systemctl --user enable --now muninn-index
systemctl --user is-active muninn-index
journalctl --user -u muninn-index -n 30 --no-pager
```

This is a user service; whether it runs while logged out depends on the host's
user-service policy. No indexing starts for an unstarted family merely because
the daemon is active.

### macOS with launchd

Create `~/Library/LaunchAgents/org.muninn.index.plist` with the following content,
substituting your **absolute** binary path (launchd does not expand `~`):

```xml
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0"><dict>
  <key>Label</key><string>org.muninn.index</string>
  <key>ProgramArguments</key><array><string>/ABSOLUTE/HOME/.local/bin/muninn-index</string></array>
  <key>RunAtLoad</key><true/>
  <key>KeepAlive</key><true/>
</dict></plist>
```

Create the parent directory first if needed, then:

```sh
chmod 600 "$HOME/Library/LaunchAgents/org.muninn.index.plist"
launchctl bootstrap "gui/$(id -u)" "$HOME/Library/LaunchAgents/org.muninn.index.plist"
launchctl print "gui/$(id -u)/org.muninn.index"
```

For a home on an external volume, this installation has required the plist in
`/Library/LaunchAgents/` on the internal system volume, with administrator-assisted
installation and appropriate ownership. Use the actual installed plist path for
bootstrap and future upgrades; do not assume the user-directory path applies.

Without a service manager, `muninn-index` can run in a foreground terminal for
manual use. Closing it stops automatic updates; foreground indexing can still run.

## 6. Configure and start the first family

```sh
muninn add /absolute/path/to/repo
```

The TUI shows policy, frozen defaults, inventory and advice. On the policy page,
select the embedding backend before saving: **new-family defaults use Voyage,
even if Step 4 selected local globally**. Select Local for the local setup above.
The embedding profile cannot currently be changed after family registration.

Review excluded/vendor files. Git ignores are not used. Dependencies may be
large; the inventory suggests whether to start or refine rules, with or without
an agent. Save registers the family without indexing it. The TUI then offers a
separate Start confirmation. You can leave it unstarted and return with:

```sh
muninn config /absolute/path/to/repo
```

Agents use the [JSON workflow](claude-code-setup/skill/SKILL.md#configure-with-json)
instead of driving the TUI. After first start, linked Git worktrees are discovered
automatically and share the policy. Non-Git directories are independent families.

## 7. Connect and verify the agent

Follow [Agent setup](claude-code-setup/INSTALL.md) for **Codex or Claude Code**,
including MCP registration and the shared usage skill. Reminder hooks are optional.

Verify separately:

1. All three binary versions match.
2. `muninn status` reaches the configured database and lists the registration.
3. `muninn config /path/to/checkout --json` reports the intended policy and start state.
4. The watcher is active and its logs contain no unresolved indexing error.
5. The client lists Muninn and can call `search_fulltext` for a known indexed term,
   with `repo` set to the intended checkout. Inspect the returned source range.

For a linked worktree, use its path for search/config inspection. `status PATH`
is still a registered-locator lookup, not a per-worktree freshness report.
Search responses do not currently include a freshness field: if Git is in a
merge/rebase/conflict, results can be from the last completed index.
