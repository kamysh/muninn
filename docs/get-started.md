# Get started with muninn

This guide walks you through getting muninn running using Docker for the database and pre-built binaries. No Rust, no Nix, no PostgreSQL knowledge required.

By the end you will have muninn's search tools available inside Claude Code, watching your first repository for changes.

## Prerequisites

- [Docker](https://docs.docker.com/get-docker/)
- [Claude Code](https://claude.ai/code)
- For semantic search: a [Voyage AI](https://dash.voyageai.com) or [OpenAI](https://platform.openai.com) API key — or nothing at all (local mode works offline, downloads ~200 MB on first use)

## Step 1: Start the database

```bash
docker run -d \
  --name muninn-postgres \
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
    container_name: muninn-postgres
    restart: always
    ports:
      - "127.0.0.1:5432:5432"
    volumes:
      - muninn_data:/var/lib/postgresql/data

volumes:
  muninn_data:
```

Then run `docker compose up -d`.

## Step 2: Create a database and user

Add a line to `~/.pgpass` with the username, database name, and password you want — these can be anything:

```
# ~/.pgpass — format: hostname:port:database:username:password
localhost:5432:muninn:alice:yourpassword
```

Lock down its permissions (PostgreSQL ignores the file if it is world-readable):

```bash
chmod 600 ~/.pgpass
```

Create the user and database with a single command (the `postgres` superuser is only accessible from inside the container):

```bash
docker exec muninn-postgres psql -U postgres -d postgres <<'SQL'
CREATE USER alice WITH PASSWORD 'yourpassword';
CREATE DATABASE muninn OWNER alice;
\c muninn
GRANT ALL PRIVILEGES ON DATABASE muninn TO alice;
GRANT USAGE, CREATE ON SCHEMA public TO alice;
ALTER DEFAULT PRIVILEGES IN SCHEMA public GRANT ALL ON TABLES TO alice;
ALTER DEFAULT PRIVILEGES IN SCHEMA public GRANT ALL ON SEQUENCES TO alice;
GRANT USAGE ON SCHEMA ag_catalog TO alice;
GRANT SELECT, INSERT, UPDATE, DELETE ON ALL TABLES IN SCHEMA ag_catalog TO alice;
GRANT EXECUTE ON ALL FUNCTIONS IN SCHEMA ag_catalog TO alice;
GRANT USAGE ON ALL SEQUENCES IN SCHEMA ag_catalog TO alice;
SQL
```

Replace `alice`, `yourpassword`, and `muninn` with the same values you put in `~/.pgpass`.

**Verify the connection works:**

```bash
psql -h localhost -U alice -d muninn -c '\conninfo'
```

## Step 3: Download muninn

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

Make sure `~/.local/bin` is on your `PATH`. If `muninn --help` does not work after this, add `export PATH="$HOME/.local/bin:$PATH"` to your shell's rc file and reload it.

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
- **`local`** — no account required, works offline. Set `backend = "local"`, `model = "bge-base-en-v1.5"`, and remove the `api_key` line entirely. Downloads ~200 MB on first use. Nothing leaves your machine.

If you are not sure, start with `local`. You can switch to Voyage AI later — just know that switching backends requires removing and re-adding the repo (`muninn remove` then `muninn add`), because the embedding format is locked in at registration time.

Save and close the editor. Muninn validates the config and sets up the database schema automatically. If there is an error, it will tell you and re-open the editor.

## Step 5: Start the indexer

The indexer (muninn-index) is a background daemon that watches your registered repositories for file changes and keeps the search index up to date. You start it once and it stays running.

**Linux — systemd user service (recommended):**

The service file is not included in the release tarball. Create it:

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

systemctl --user enable --now muninn-index
systemctl --user status muninn-index
```

The status output should show `active (running)`.

**macOS — launchd agent (recommended, auto-starts on login):**

Create the plist:

```bash
mkdir -p ~/Library/LaunchAgents
cat > ~/Library/LaunchAgents/org.muninn.index.plist << 'EOF'
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN"
  "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
  <key>Label</key>
  <string>org.muninn.index</string>
  <key>ProgramArguments</key>
  <array>
    <string>/Users/YOUR_USERNAME/.local/bin/muninn-index</string>
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
```

Replace `YOUR_USERNAME` with your macOS username (`whoami`). Then load it:

```bash
launchctl load ~/Library/LaunchAgents/org.muninn.index.plist
```

Check it started:
```bash
launchctl list | grep muninn
```
A PID in the first column means it is running.

**macOS — quick background start (no auto-restart):**

```bash
muninn-index &
```

## Step 6: Connect Claude Code

```bash
claude mcp add --scope user muninn ~/.local/bin/muninn-mcp
```

Restart Claude Code. Open its tools panel — you should see `search_hybrid`, `search_fulltext`, `search_semantic`, `search_structural`, `record_knowledge`, `search_knowledge`, `delete_knowledge`, and `list_knowledge` listed.

## Step 7: Add your first repository

```bash
muninn add /path/to/your/repo
```

This opens your editor with a per-repo configuration file. For most repos, just save and close without changes — all settings are inherited from the global config. Muninn will then index the repo (you will see a progress bar).

When indexing completes, open Claude Code and ask something like "What does function X do?" or "Find all callers of Y" — muninn will search the repo and give Claude Code the context to answer.

## What happens next

The daemon watches for file changes and re-indexes automatically. You do not have to do anything after this.

- `muninn list` shows all registered repos and their index status.
- `muninn add <path>` to add more repos.
- When a new muninn release comes out, see [docs/upgrading.md](upgrading.md).
