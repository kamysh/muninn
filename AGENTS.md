# AGENTS.md — install instructions for AI coding agents

This file is the authoritative install procedure for AI coding agents
(Claude Code, Cursor, Aider, etc.). The human-facing
[docs/get-started.md](docs/get-started.md) contains the same information
but with hedges ("recommended", "alternative") that an agent should not
rely on. Follow this file instead.

## Read this first

- All steps are idempotent. Safe to rerun. If interrupted, restart from
  **State detection** below, not from Step 1.
- After every step, run the verify command. Do not stack failures —
  fix the current step before moving on.
- Destructive operations (dropping a database, removing a container,
  overwriting a file you did not author) require user confirmation.
  Stop and ask, even when a step appears to call for it.
- Every config-mutating command is scriptable — none block on `$EDITOR`.
  Bootstrap with `muninn init key=value …` (Step 4); register repos with
  `muninn add <path> [key=value …]` (Step 7); change config later with
  `muninn config set (--global | --repo <path>) key=value …`. `$EDITOR`
  opens **only** for the explicit `muninn config edit`, which an agent
  should not use.

## Variables

**Before doing anything else, ask the user for these values:**

1. **Docker container name** — the local name for the postgres-ai container
   (e.g. `local-postgres-ai`). Check `docker ps -a` and suggest a name that
   doesn't collide. The Docker image is always `kamysh/postgres-ai`.
2. **Port** — the host port to expose PostgreSQL on (default `5432`; check
   `lsof -nP -iTCP -sTCP:LISTEN` for conflicts).
3. **DB user** — the PostgreSQL role to create for muninn (default `muninn`).
4. **DB name** — the database to create (default `muninn`; usually matches the user).

If muninn is being installed alongside mimir (see "Companion tool" at the end),
also confirm whether they share one container or use separate ones.

Bind the answers as shell variables once, then re-use in every command below:

| Variable | Notes |
|---|---|
| `PORT` | Host port. Avoid 5000 (AirPlay on macOS), 6000 (X11), and anything in use. |
| `CONTAINER` | Local container name. Must not collide with an existing container. Image: `kamysh/postgres-ai`. |
| `VOLUME` | Docker volume for the postgres data dir (e.g. `muninn_data`). If sharing a container with mimir, use the same volume. |
| `DB_USER` | PostgreSQL role for muninn. |
| `DB_NAME` | Database for muninn. |
| `EMBEDDING_BACKEND` | `local` (no API key, offline) \| `voyage` \| `openai` |

Check assumptions before starting:

```sh
docker info >/dev/null                                                 # daemon running
! lsof -nP -iTCP:"$PORT" -sTCP:LISTEN | grep -q .                      # port free
! docker ps -a --format '{{.Names}}' | grep -qx "$CONTAINER"           # container name free
echo "$PATH" | tr ':' '\n' | grep -qx "$HOME/.local/bin"               # PATH includes target
```

If any check fails, stop and report the specific failure to the user.
Do not try to recover automatically (e.g. do not kill an existing
container — it may hold data the user cares about).

## State detection — skip steps already complete

These probes are for a **fresh** install. On a machine that already has muninn
they all pass — so if the goal is to move an *existing* install to a new
release, do **not** follow the steps below (they would no-op); jump to
[Upgrading an existing install](#upgrading-an-existing-install).

Run these probes before doing any work. For each that returns 0, skip
the corresponding step.

```sh
# Step 1 — postgres container running
docker ps --filter "name=^${CONTAINER}$" --filter "status=running" \
  --format '{{.Names}}' | grep -qx "$CONTAINER"

# Step 2 — DB and role exist
docker exec "$CONTAINER" psql -U postgres -lqt \
  | cut -d\| -f1 | grep -qw "$DB_NAME"

# Step 3 — binaries installed
command -v muninn && command -v muninn-index && command -v muninn-mcp >/dev/null

# Step 4 — config exists and is valid
[ -f "$HOME/.config/muninn/config.toml" ] && muninn status >/dev/null 2>&1

# Step 5 — indexer daemon running
pgrep -fl muninn-index >/dev/null

# Step 6 — MCP registered with Claude Code
claude mcp list 2>&1 | grep -E '^muninn:.*Connected' >/dev/null
```

## Step 1 — Start postgres

```sh
docker run -d \
  --name "$CONTAINER" \
  --restart always \
  -p "127.0.0.1:${PORT}:5432" \
  -v "${VOLUME}:/var/lib/postgresql/data" \
  kamysh/postgres-ai:latest
sleep 3
```

**Verify:**
```sh
docker exec "$CONTAINER" psql -U postgres -c 'SELECT 1' >/dev/null && echo OK
```

## Step 2 — Create role and database

Add a password line to `~/.pgpass` first (generate a fresh random
password — do not hardcode):

```sh
PASSWORD=$(openssl rand -hex 32)
touch "$HOME/.pgpass"
chmod 600 "$HOME/.pgpass"
printf 'localhost:%s:%s:%s:%s\n' "$PORT" "$DB_NAME" "$DB_USER" "$PASSWORD" >> "$HOME/.pgpass"
```

Run the setup script (creates role, DB, extensions, grants):

```sh
curl -fsSL https://raw.githubusercontent.com/kamysh/muninn/main/muninn-setup/create-db-user.sh \
  | bash -s -- --container "$CONTAINER" --port "$PORT" \
                --user "$DB_USER" --db "$DB_NAME"
```

**Verify:**
```sh
psql -h localhost -p "$PORT" -U "$DB_USER" -d "$DB_NAME" -c '\conninfo' >/dev/null && echo OK
```

## Step 3 — Install binaries

```sh
mkdir -p "$HOME/.local/bin"
case "$(uname -s)-$(uname -m)" in
  Darwin-arm64)  TARBALL=muninn-darwin-arm64.tar.gz ;;
  Darwin-x86_64) TARBALL=muninn-darwin-amd64.tar.gz ;;
  Linux-x86_64)  TARBALL=muninn-linux-amd64.tar.gz ;;
  Linux-aarch64) TARBALL=muninn-linux-arm64.tar.gz ;;
  *) echo "Unsupported platform: $(uname -s)-$(uname -m)" >&2; exit 1 ;;
esac
curl -fsSL "https://github.com/kamysh/muninn/releases/latest/download/${TARBALL}" \
  | tar -xz -C "$HOME/.local/bin"
chmod +x "$HOME/.local/bin/muninn" "$HOME/.local/bin/muninn-index" "$HOME/.local/bin/muninn-mcp"
```

Do **not** run `xattr -d com.apple.quarantine` on these files. The
quarantine flag is only set on browser downloads — `curl` does not set
it, so the command will error with "Permission denied" / "no such xattr"
even though nothing is wrong. Skip the step entirely.

**Verify:**
```sh
muninn --help >/dev/null && echo OK
```

## Step 4 — Write config and migrate (`muninn init`)

`muninn init` writes `~/.config/muninn/config.toml` (chmod 600 — it may
hold an API key) **and** runs the schema migrations, in one
non-interactive step. Pass settings as `key=value` positional arguments:
dotted keys, TOML values with a bare-string fallback so `backend=local`
works without extra quoting.

```sh
muninn init \
  database.host=localhost \
  database.port=${PORT} \
  database.dbname="${DB_NAME}" \
  database.user="${DB_USER}" \
  embeddings.backend="${EMBEDDING_BACKEND}"
```

For `voyage`/`openai`, also pass the model and key (ask the user for the
key — do not invent or fish for one from the environment):

```sh
muninn init \
  database.host=localhost database.port=${PORT} \
  database.dbname="${DB_NAME}" database.user="${DB_USER}" \
  embeddings.backend=voyage \
  embeddings.model=voyage-code-3 \
  embeddings.api_key="$VOYAGE_KEY"
```

`init` is idempotent — rerun it to re-apply migrations or change global
settings (or use `muninn config set --global key=value`).

**Verify:**
```sh
muninn status >/dev/null && echo OK
```

## Step 5 — Start the indexer daemon (REQUIRED)

The indexer is not optional. Without it, the index never updates on
file changes and searches silently return stale results — there is no
error to grep for, so this is the most common silent failure.

### macOS (launchd)

```sh
mkdir -p "$HOME/Library/LaunchAgents"
cat > "$HOME/Library/LaunchAgents/org.muninn.index.plist" <<EOF
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN"
  "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
  <key>Label</key><string>org.muninn.index</string>
  <key>ProgramArguments</key>
  <array><string>${HOME}/.local/bin/muninn-index</string></array>
  <key>EnvironmentVariables</key>
  <dict><key>RUST_LOG</key><string>info</string></dict>
  <key>RunAtLoad</key><true/>
  <key>KeepAlive</key><true/>
  <key>StandardOutPath</key><string>/tmp/muninn-index.log</string>
  <key>StandardErrorPath</key><string>/tmp/muninn-index.log</string>
</dict>
</plist>
EOF
launchctl bootstrap gui/$(id -u) "$HOME/Library/LaunchAgents/org.muninn.index.plist"
```

### Linux (systemd user service)

```sh
mkdir -p "$HOME/.config/systemd/user"
cat > "$HOME/.config/systemd/user/muninn-index.service" <<'EOF'
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
EOF
systemctl --user daemon-reload
systemctl --user enable --now muninn-index
```

**Verify (both platforms):**
```sh
sleep 2
pgrep -fl muninn-index >/dev/null && echo OK
```

Logs:
- macOS: `tail -f /tmp/muninn-index.log`
- Linux: `journalctl --user -u muninn-index -f`

## Step 6 — Register MCP server with Claude Code

```sh
claude mcp add --scope user muninn "$HOME/.local/bin/muninn-mcp"
```

Use `--scope user`, never `--scope project`. Muninn is a system-wide
tool, not project-local.

**Verify:**
```sh
claude mcp list 2>&1 | grep -E '^muninn:.*Connected' && echo OK
```

If status is anything other than `Connected`, the MCP server is
crashing on startup. Run `muninn-mcp` directly to see stderr.

## Step 7 — (Optional) Register the first repository

`muninn add <path>` registers a repo, writes a default `.muninn.toml`
(all fields inherit the global config), and runs the initial index —
non-interactive. Pass per-repo overrides as `key=value`:

```sh
REPO=/path/to/repo
muninn add "$REPO"                                    # defaults; index now
muninn add "$REPO" index.exclude='["target/","dist/"]'  # with excludes
muninn add "$REPO" --no-index                         # register only, index later
```

Change a repo's config afterward with
`muninn config set --repo "$REPO" key=value` (reindexes if needed).

**Verify:**
```sh
muninn status "$REPO" >/dev/null && echo OK
```

## Final verification gate

All six lines must print `OK`. If any fails, fix that step before
declaring the install complete.

```sh
muninn status >/dev/null                                                && echo OK  # 1
docker ps --filter "name=^${CONTAINER}$" --format '{{.Names}}' \
  | grep -qx "$CONTAINER"                                               && echo OK  # 2
command -v muninn-index >/dev/null                                      && echo OK  # 3
pgrep -fl muninn-index >/dev/null                                       && echo OK  # 4
{ launchctl list 2>/dev/null | grep -q org.muninn.index; } \
  || { systemctl --user is-active muninn-index >/dev/null 2>&1; }       && echo OK  # 5
claude mcp list 2>&1 | grep -qE '^muninn:.*Connected'                   && echo OK  # 6
```

## Upgrading an existing install

The **State detection** probes above are written for a *fresh* install — on a
machine that already has muninn they all pass, so re-running the steps is a
no-op. To move an existing install to a new release, do it explicitly. The DB
container, role, and `config.toml` are already in place; only the binaries and
the running processes change:

1. **Replace the binaries** — re-run **Step 3**; the tarball overwrites
   `~/.local/bin/muninn`, `muninn-index`, and `muninn-mcp` in place.
2. **Restart the daemon** so it execs the new binary:
   - macOS:  `launchctl kickstart -k gui/$(id -u)/org.muninn.index`
   - Linux:  `systemctl --user restart muninn-index`
3. **Pick up the new MCP server** — Claude Code launches `muninn-mcp` on demand
   from the same path, so a new Claude Code session uses the new binary; no
   `claude mcp add` is needed.

Schema migrations apply automatically: the first run of any new binary
(`muninn`, the daemon, or the MCP server) brings the database up to date.
Migrations are forward-only and idempotent — there is no manual migration step,
and the existing `config.toml` keeps working unchanged.

**Verify:**
```sh
muninn status >/dev/null && echo OK             # CLI talks to the migrated DB
pgrep -fl muninn-index   >/dev/null && echo OK  # daemon up on the new binary
```

## Uninstalling muninn

Reverse of the install. **The database / container steps are destructive and
irreversible — confirm with the user first. If the `postgres-ai` container is
shared with mimir, do NOT remove the container or volume; drop only muninn's
database and role.**

1. **Stop and remove the daemon:**
   - macOS:  `launchctl bootout gui/$(id -u)/org.muninn.index 2>/dev/null; rm -f "$HOME/Library/LaunchAgents/org.muninn.index.plist"`
   - Linux:  `systemctl --user disable --now muninn-index; rm -f "$HOME/.config/systemd/user/muninn-index.service"; systemctl --user daemon-reload`
2. **Unregister the MCP server:** `claude mcp remove muninn` (restart Claude Code to apply).
3. **Remove the binaries:** `rm -f "$HOME/.local/bin/muninn" "$HOME/.local/bin/muninn-index" "$HOME/.local/bin/muninn-mcp"`
4. **Remove config and state:** `rm -rf "$HOME/.config/muninn" "$HOME/.local/state/muninn"`, and delete muninn's line from `~/.pgpass` (the `localhost:${PORT}:${DB_NAME}:${DB_USER}:…` entry — edit carefully, the file serves all your PostgreSQL connections).
5. **(Optional) per-repo markers:** each indexed repo has a `.muninn.toml` at its root. Run `muninn remove <path>` *before* step 3 to drop a repo's index data and marker cleanly, or just delete the `.muninn.toml` files. (Moot if you drop the whole database next.)
6. **Drop the database and role** (confirm first):
   ```sh
   docker exec "$CONTAINER" psql -U postgres -c "DROP DATABASE IF EXISTS \"${DB_NAME}\";"
   docker exec "$CONTAINER" psql -U postgres -c "DROP ROLE IF EXISTS \"${DB_USER}\";"
   ```
   Only if the container is muninn-only (**not** shared with mimir) and the user
   wants it gone entirely:
   ```sh
   docker rm -f "$CONTAINER" && docker volume rm "$VOLUME"
   ```

**Verify removed:**
```sh
pgrep muninn       # prints nothing
command -v muninn  # prints nothing
```

## Known errors → fixes

| Error | Cause | Fix |
|---|---|---|
| `Cannot connect to the Docker daemon` | Daemon not running. | Tell the user to start Docker Desktop. Do not try to start it yourself. |
| `docker: Error response from daemon: Conflict. The container name "/postgres-ai" is already in use` | Name collision with an unrelated container. | Pick a different `CONTAINER`. Do **not** delete the existing one without user confirmation — it may hold data. |
| `bind: address already in use` on port 5432 | Another postgres or app on that port. | Pick a different `PORT`. Update `~/.pgpass`, `config.toml`, and the `docker run -p` flag together. |
| `xattr: [Errno 13] Permission denied` on `~/.local/bin/muninn*` | No quarantine flag exists (curl-downloaded). | Skip the `xattr -d` step entirely. The binaries are runnable as-is. |
| `~/.pgpass` ignored | Wrong permissions. | `chmod 600 ~/.pgpass`. |
| `muninn status` succeeds but search results are stale | Indexer daemon is not running. | Re-do Step 5. Check the verify line passes. |
| MCP server shows `Failed to connect` | `muninn-mcp` crashing on startup. | Run `muninn-mcp` directly in a shell; the panic/error message goes to stderr. Usually a DB connectivity or config issue. |

## Anti-patterns — things NOT to do

- **Do not use `muninn config edit` (it opens `$EDITOR` and blocks).**
  Use the non-interactive forms: `muninn init key=value …` (Step 4),
  `muninn add <path> [key=value …]` (Step 7), and `muninn config set
  (--global | --repo <path>) key=value …` to change config later.
- **Do not skip Step 5.** The CLI works without the daemon, which makes
  this failure mode invisible until the user notices stale results.
- **Do not delete or rename existing Docker containers/volumes to free a
  name.** Confirm with the user first. Data loss is irreversible.
- **Do not pick port 6000 on macOS** — it is X11. Likewise 5000 (AirPlay
  Receiver) and any port already shown by `lsof -nP -iTCP -sTCP:LISTEN`.
- **Do not register the MCP server at `--scope project`.** Muninn is
  installed once per user, not per repo.
- **Do not chase `xattr` permission errors on curl-downloaded files.**
  Skip the step.
- **Do not invent API keys** for `voyage`/`openai` embedding backends.
  Ask the user, or default `EMBEDDING_BACKEND=local`.
- **Do not declare install complete** before running the **Final
  verification gate** above and seeing six `OK` lines.

## Companion tool

If you are also installing [mimir](https://github.com/kamysh/mimir) (the
belief-graph MCP server), the two tools can share one postgres-ai
container — just create separate roles and databases. See mimir's own
`AGENTS.md` for its install procedure.
