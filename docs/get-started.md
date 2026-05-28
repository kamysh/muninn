# Get started with muninn

This guide walks you through getting muninn running using Docker for the database and pre-built binaries. No Rust, no Nix, no PostgreSQL knowledge required.

By the end you will have muninn's search tools available inside Claude Code, watching your first repository for changes.

## What a complete install consists of

Skipping any of these four pieces will leave muninn in a state that looks installed but fails silently:

1. A **PostgreSQL container** (or your own DB) holding the index.
2. **Three binaries** on `PATH` — `muninn`, `muninn-index`, `muninn-mcp`.
3. The `muninn-index` **daemon running in the background** under launchd (macOS) or systemd (Linux). Without it, the CLI still works, but the index never updates on file changes — searches return stale results with no error to alert you.
4. The **`muninn-mcp` server registered with Claude Code**. Without it, Claude Code has no tools to call.

A short "Verify the install" step near the end (Step 7) checks all four. Do not consider the install complete until it passes.

## Prerequisites

- [Docker](https://docs.docker.com/get-docker/) (or Docker-compatible runtime like OrbStack)
- [Claude Code](https://claude.ai/code)
- For semantic search: a [Voyage AI](https://dash.voyageai.com) or [OpenAI](https://platform.openai.com) API key — or nothing at all (local mode works offline, downloads ~200 MB on first use)

### Preflight check

Run these before you start. Each line should print `OK`:

```bash
docker info >/dev/null 2>&1 && echo OK                                            # Docker daemon running
! lsof -nP -iTCP:5432 -sTCP:LISTEN 2>/dev/null | grep -q . && echo OK              # port 5432 free
! docker ps -a --format '{{.Names}}' 2>/dev/null | grep -qx postgres-ai && echo OK # container name free
echo "$PATH" | tr ':' '\n' | grep -qx "$HOME/.local/bin" && echo OK                # PATH includes ~/.local/bin
command -v claude >/dev/null && echo OK                                            # Claude Code CLI installed
```

If any line fails:

- **Docker not running** → start Docker Desktop (or your runtime), then re-check.
- **Port 5432 in use** → either stop the conflicting service or pick a different port. If you change the port, update *everything* in this guide that mentions `5432`: the `docker run -p` flag, the `~/.pgpass` line, and `~/.config/muninn/config.toml`.
- **Container name `postgres-ai` in use** → either reuse the existing container (if it's a postgres-ai instance from another tool) or pick a new name for the one you're about to create. Do not delete the existing container without checking what data it holds.
- **`~/.local/bin` not on PATH** → add `export PATH="$HOME/.local/bin:$PATH"` to your shell's rc file (`~/.zshrc`, `~/.bashrc`) and reload it.
- **`claude` CLI missing** → install [Claude Code](https://claude.ai/code) before continuing; Step 6 needs it.

### Conventions used in this guide

This guide uses the following defaults. If you change any of them, change them everywhere they appear:

| Setting | Default | Used in |
|---|---|---|
| PostgreSQL port | `5432` | `docker run`, `~/.pgpass`, `config.toml` |
| Container name | `postgres-ai` | `docker run`, all `docker exec` calls |
| Docker volume | `muninn_data` | `docker run` |
| Database name | `muninn` | setup SQL, `~/.pgpass`, `config.toml` |
| Database user | `muninn` | setup SQL, `~/.pgpass`, `config.toml` |

On macOS, avoid ports `5000` (AirPlay Receiver) and `6000` (X11) if you change the port.

## Step 1: Start the database

```bash
docker run -d \
  --name postgres-ai \
  --restart always \
  -p 127.0.0.1:5432:5432 \
  -v muninn_data:/var/lib/postgresql/data \
  kamysh/postgres-ai:latest
```

This image has pgvector, Apache AGE, uuid-ossp, and pgcrypto pre-installed in every database. No extension setup required.

If you prefer Docker Compose, create a `docker-compose.yml`:

```yaml
services:
  postgres:
    image: kamysh/postgres-ai:latest
    container_name: postgres-ai
    restart: always
    ports:
      - "127.0.0.1:5432:5432"
    volumes:
      - muninn_data:/var/lib/postgresql/data

volumes:
  muninn_data:
```

Then run `docker compose up -d`.

**Verify:**

```bash
docker exec postgres-ai psql -U postgres -c 'SELECT 1' >/dev/null && echo OK
```

## Step 2: Create a database and user

Add a line to `~/.pgpass` with your chosen password:

```
# ~/.pgpass — format: hostname:port:database:username:password
localhost:5432:muninn:muninn:yourpassword
```

Lock down its permissions (PostgreSQL ignores the file if it is world-readable):

```bash
chmod 600 ~/.pgpass
```

Create the user and database. You can run the [setup script](https://github.com/kamysh/muninn/blob/main/muninn-setup/create-db-user.sh) or paste the following directly (the `postgres` superuser is only accessible from inside the container):

```bash
docker exec -i postgres-ai psql -U postgres -d postgres <<'SQL'
DO $$
BEGIN
    IF NOT EXISTS (SELECT 1 FROM pg_roles WHERE rolname = 'muninn') THEN
        CREATE ROLE muninn WITH LOGIN;
    END IF;
END
$$;
ALTER ROLE muninn PASSWORD 'yourpassword';
SELECT 'CREATE DATABASE muninn OWNER muninn'
WHERE NOT EXISTS (SELECT 1 FROM pg_database WHERE datname = 'muninn')\gexec
GRANT ALL PRIVILEGES ON DATABASE muninn TO muninn;
\c muninn
GRANT USAGE, CREATE ON SCHEMA public TO muninn;
ALTER DEFAULT PRIVILEGES IN SCHEMA public GRANT ALL ON TABLES TO muninn;
ALTER DEFAULT PRIVILEGES IN SCHEMA public GRANT ALL ON SEQUENCES TO muninn;
GRANT USAGE ON SCHEMA ag_catalog TO muninn;
GRANT SELECT, INSERT, UPDATE, DELETE ON ALL TABLES IN SCHEMA ag_catalog TO muninn;
GRANT EXECUTE ON ALL FUNCTIONS IN SCHEMA ag_catalog TO muninn;
GRANT USAGE ON ALL SEQUENCES IN SCHEMA ag_catalog TO muninn;
SQL
```

Replace `yourpassword` with the password you put in `~/.pgpass`. Replace `muninn` with a different username or database name if you prefer.

**Verify the connection works:**

```bash
psql -h localhost -U muninn -d muninn -c '\conninfo'
```

## Step 3: Install the muninn binaries

This step installs the three muninn binaries to `~/.local/bin`. It is one of four pieces — see Step 5 for the daemon and Step 6 for the MCP server.

Download the archive for your platform from the [latest release](https://github.com/kamysh/muninn/releases/latest):

| Platform | File |
|---|---|
| Linux x86_64 | `muninn-linux-amd64.tar.gz` |
| Linux ARM64 | `muninn-linux-arm64.tar.gz` |
| macOS Apple Silicon | `muninn-darwin-arm64.tar.gz` |
| macOS Intel | `muninn-darwin-amd64.tar.gz` |

```bash
# Linux x86_64
curl -L https://github.com/kamysh/muninn/releases/latest/download/muninn-linux-amd64.tar.gz \
  | tar -xz -C ~/.local/bin

# Linux ARM64
curl -L https://github.com/kamysh/muninn/releases/latest/download/muninn-linux-arm64.tar.gz \
  | tar -xz -C ~/.local/bin

# macOS Apple Silicon
curl -L https://github.com/kamysh/muninn/releases/latest/download/muninn-darwin-arm64.tar.gz \
  | tar -xz -C ~/.local/bin

# macOS Intel
curl -L https://github.com/kamysh/muninn/releases/latest/download/muninn-darwin-amd64.tar.gz \
  | tar -xz -C ~/.local/bin
```

Make the binaries executable:

```bash
chmod +x ~/.local/bin/muninn ~/.local/bin/muninn-index ~/.local/bin/muninn-mcp
```

**macOS only — quarantine flag.** macOS adds a quarantine attribute to files downloaded via a *browser*, which blocks them from running. If you downloaded the archive with a browser, remove it:

```bash
xattr -d com.apple.quarantine ~/.local/bin/muninn ~/.local/bin/muninn-index ~/.local/bin/muninn-mcp
```

`curl` downloads do **not** set this attribute, so the command above is unnecessary if you used the `curl` snippet. (It will print "Permission denied" or "no such xattr" — that's expected, not a problem.)

**Verify:**

```bash
muninn --help >/dev/null && echo OK
```

If you get "command not found", `~/.local/bin` is not on your `PATH`. Add `export PATH="$HOME/.local/bin:$PATH"` to your shell's rc file and reload it.

## Step 4: Configure muninn

`muninn config` opens a configuration file in your editor. You need to fill in two things: your database username and your choice of embedding backend.

```bash
muninn config
```

You will see:

```toml
# ~/.config/muninn/config.toml — muninn global configuration
#
# Lines marked REQUIRED must be filled in before muninn will work correctly.
# Everything else can be left at its default value to start.

[database]
host   = "localhost"
port   = 5432
dbname = "muninn"
user   = "YOUR_DB_USER"    # REQUIRED — replace with your PostgreSQL username (e.g. "alice")

# Password: muninn never stores a password here.
# Add a line to ~/.pgpass instead:  localhost:5432:muninn:alice:yourpassword
# (file must be chmod 600)

[embeddings]
backend    = "voyage"           # voyage | openai | local
model      = "voyage-code-3"
api_key    = "YOUR_API_KEY"     # REQUIRED for voyage/openai — paste your key here
batch_size = 64

[watcher]
debounce_ms = 300

[mcp]
record_usage = true

[mcp.logging]
enabled = true
dir = "~/.local/state/muninn/mcp"
retention_days = 7
prune_interval_hours = 24
```

Make these changes:

- Replace `YOUR_DB_USER` with the username you created in Step 2 (e.g. `alice`).
- Choose an embedding backend and update the `[embeddings]` section accordingly.

**Which embedding backend?**

- **`voyage`** — best search quality for code. Requires a [Voyage AI](https://dash.voyageai.com) account. Set `backend = "voyage"`, `model = "voyage-code-3"`, and paste your key. Short text chunks are sent to Voyage AI to generate embeddings; your source files are never transmitted.
- **`openai`** — good quality. Requires an [OpenAI](https://platform.openai.com) account. Set `backend = "openai"`, `model = "text-embedding-3-small"`, and paste your key. Same privacy guarantee as above.
- **`local`** — no account required, works offline. Set `backend = "local"`, `model = "potion-base-32M"`, and remove the `api_key` line entirely. Downloads ~120 MB on first use. Uses model2vec static embeddings — fast enough to index large repos (deps included) on CPU. Nothing leaves your machine.

If you are not sure, start with `local`. You can switch to Voyage AI later — just know that switching backends requires removing and re-adding the repo (`muninn remove` then `muninn add`), because the embedding format is locked in at registration time.

Save and close the editor. Muninn validates the config and sets up the database schema automatically. If there is an error, it will tell you and re-open the editor.

**Verify:**

```bash
muninn status >/dev/null && echo OK
```

## Step 5: Start the indexer daemon

The indexer (`muninn-index`) is a background daemon that watches your registered repositories for file changes and keeps the search index up to date. **This step is required, not optional.** Without it, the index never refreshes after the initial run, and searches will silently return stale results — no error message, no warning, just out-of-date answers.

Pick the method that matches your OS:

### Linux — systemd user service

```bash
mkdir -p ~/.config/systemd/user
cat > ~/.config/systemd/user/muninn-index.service << 'EOF'
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

`%h` is a systemd placeholder for your home directory and is filled in automatically — you do not need to substitute anything.

### macOS — launchd agent

The heredoc below uses `${HOME}` (no quotes around `EOF`), which the shell expands to your real home path before writing the file. You do not need to substitute anything manually.

```bash
mkdir -p ~/Library/LaunchAgents
cat > ~/Library/LaunchAgents/org.muninn.index.plist <<EOF
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN"
  "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
  <key>Label</key>
  <string>org.muninn.index</string>
  <key>ProgramArguments</key>
  <array>
    <string>${HOME}/.local/bin/muninn-index</string>
  </array>
  <key>EnvironmentVariables</key>
  <dict>
    <key>RUST_LOG</key>
    <string>info</string>
  </dict>
  <key>RunAtLoad</key>
  <true/>
  <key>KeepAlive</key>
  <true/>
  <key>StandardOutPath</key>
  <string>/tmp/muninn-index.log</string>
  <key>StandardErrorPath</key>
  <string>/tmp/muninn-index.log</string>
</dict>
</plist>
EOF
launchctl load ~/Library/LaunchAgents/org.muninn.index.plist
```

The agent will auto-start every time you log in.

**Verify (both platforms):**

```bash
sleep 2 && pgrep -fl muninn-index >/dev/null && echo OK
```

The first `muninn-index` startup will print a couple of log lines as it discovers your repos. On macOS, tail them with `tail -f /tmp/muninn-index.log`; on Linux, `journalctl --user -u muninn-index -f`.

> **Quick start without a service manager** — for ad-hoc use or debugging, you can just run `muninn-index &` in a shell. It will keep running until you log out or the process is killed, and it will not restart on failure. Prefer the launchd/systemd setup above for any real use.

## Step 6: Connect Claude Code

```bash
claude mcp add --scope user muninn ~/.local/bin/muninn-mcp
```

Use `--scope user` (not `--scope project`) — muninn is a system-wide tool, not project-local.

Restart Claude Code. Open its tools panel — you should see `search_hybrid`, `search_fulltext`, `search_semantic`, `search_structural`, `record_knowledge`, `search_knowledge`, `delete_knowledge`, and `list_knowledge` listed.

**Verify:**

```bash
claude mcp list 2>&1 | grep -E '^muninn:.*Connected' && echo OK
```

## Step 7: Verify the install

Before adding any real repos, confirm all four pieces are in place. Each line below should print `OK`:

```bash
muninn status >/dev/null                                                            && echo OK  # 1. CLI talks to DB
docker ps --filter "name=^postgres-ai$" --format '{{.Names}}' | grep -qx postgres-ai && echo OK  # 2. DB container running
command -v muninn-index >/dev/null                                                   && echo OK  # 3. daemon binary on PATH
pgrep -fl muninn-index >/dev/null                                                    && echo OK  # 4. daemon process running
claude mcp list 2>&1 | grep -qE '^muninn:.*Connected'                                && echo OK  # 5. MCP wired up to Claude Code
```

Five `OK`s = good to go. Any failure means that piece is broken; fix it before moving on. The most common failure is line 4 (daemon not running) — re-check Step 5.

## Step 8: Add your first repository

```bash
muninn add /path/to/your/repo
```

This opens your editor with a per-repo configuration file. For most repos, just save and close without changes — all settings are inherited from the global config. Muninn will then index the repo (you will see a progress bar).

When indexing completes, open Claude Code and ask something like "What does function X do?" or "Find all callers of Y" — muninn will search the repo and give Claude Code the context to answer.

## Step 9: Install the skill and hooks (recommended)

The skill teaches Claude Code *how* to use muninn — which search tool to pick, when to write knowledge back, and how it relates to other memory tools. The hooks ensure it queries muninn automatically before every task.

**Skill:**

```bash
mkdir -p ~/.claude/skills/muninn
cp skill/SKILL.md ~/.claude/skills/muninn/SKILL.md
```

**Hooks** — merge the following into `~/.claude/settings.json` under the top-level `"hooks"` key (create the key if it doesn't exist; append to existing arrays if you already have hooks for these events):

```json
{
  "hooks": {
    "UserPromptSubmit": [
      {
        "matcher": "",
        "hooks": [
          {
            "type": "command",
            "command": "echo 'Before acting: query muninn for relevant code knowledge (mcp__muninn__search_hybrid), query mimir for relevant rules (mcp__mimir__query_relevant). Do this BEFORE reading files or writing code.'"
          }
        ]
      }
    ]
  }
}
```

The hook references both muninn and [mimir](https://github.com/kamysh/mimir) — a companion belief graph that stores heuristics and patterns across sessions. If you are not using mimir, replace the hook command with:

```
"echo 'Before acting: query muninn for relevant code knowledge (mcp__muninn__search_hybrid). Do this BEFORE reading files or writing code.'"
```

Restart Claude Code for the hooks to take effect.

## What happens next

The daemon watches for file changes and re-indexes automatically. You do not have to do anything after this.

- `muninn list` shows all registered repos and their index status.
- `muninn add <path>` to add more repos.
- When a new muninn release comes out, see [docs/upgrading.md](upgrading.md).

## Sharing the database with mimir

If you also use [mimir](https://github.com/kamysh/mimir), the two tools can share one `postgres-ai` container — just create a separate role and database for mimir (see mimir's own install guide). The `kamysh/postgres-ai` image is designed for this: pgvector, AGE, and the support extensions are pre-installed cluster-wide.

## If something goes wrong

A few failure modes are common enough to call out explicitly:

| Symptom | Likely cause | Fix |
|---|---|---|
| `muninn status` works but searches return stale results | Indexer daemon stopped or never started — **most common silent failure** | Re-check Step 5. `pgrep -fl muninn-index` should print a PID. If not, restart the daemon. |
| MCP tools missing from Claude Code | `muninn-mcp` not registered, or registered at the wrong scope | Re-check Step 6. `claude mcp list` must show `muninn: ... Connected`. Use `--scope user`, not `--scope project`. |
| `Cannot connect to the Docker daemon` | Docker Desktop / runtime not running | Start it. Do not try to start Docker programmatically. |
| `docker run` fails with "container name in use" | Another container is already named `postgres-ai` | Either reuse it (if it's a compatible postgres-ai instance) or pick a different name for this one. Do not delete the existing container without checking what's in it. |
| `bind: address already in use` on port 5432 | Another postgres or app is using 5432 | Pick a different port. Update `docker run -p`, `~/.pgpass`, and `~/.config/muninn/config.toml` together. |
| `~/.pgpass` ignored, prompts for password | Wrong file permissions | `chmod 600 ~/.pgpass`. PostgreSQL silently ignores `~/.pgpass` if it is world- or group-readable. |
| `xattr: Permission denied` on macOS | The file does not actually have a quarantine flag (curl-downloaded) | Skip the `xattr` step. The binaries run fine without it. |
| MCP shows `Failed to connect` instead of `Connected` | `muninn-mcp` is crashing on startup, usually due to a DB / config error | Run `muninn-mcp` directly in a shell; the error message goes to stderr. Common causes: wrong port in `config.toml`, password mismatch with `~/.pgpass`. |

If something is broken in a way not listed here, file an [issue](https://github.com/kamysh/muninn/issues) with the output of:

```bash
muninn --version
muninn status 2>&1
pgrep -fl muninn-index
claude mcp list 2>&1 | grep muninn
docker ps --filter name=postgres-ai
```
