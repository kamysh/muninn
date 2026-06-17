<!-- AI CODING AGENTS: STOP. This is the HUMAN upgrade guide. Your procedure is
     ../AGENTS.md (repo root), section "Upgrading an existing install" — same
     end state, but with explicit variables and verify-after-each-step. Do not
     follow the steps below. -->

> ⛔ **AI coding agents — this guide is not for you.** It is the *human* upgrade
> path. Your procedure is **[AGENTS.md](../AGENTS.md)** (section "Upgrading an
> existing install") — follow that instead.

# Upgrading muninn

Two things to update: the binaries and the database schema (if the new release includes new migrations). Both take under a minute. Your indexed data is preserved — migrations are additive and never delete existing index data.

## Step 1: Stop the daemon

Linux (systemd):
```bash
systemctl --user stop muninn-index
```

macOS (launchd):
```bash
launchctl bootout gui/$(id -u)/org.muninn.index
```

## Step 2: Replace the binaries

Download the new release for your platform and overwrite the existing files:

```bash
# Example for Linux x86_64 — adjust the filename for your platform
curl -L https://github.com/kamysh/muninn/releases/latest/download/muninn-linux-amd64.tar.gz \
  | tar -xz -C ~/.local/bin
```

No `chmod` needed — the extracted files are already executable.

## Step 3: Apply schema migrations

Migrations apply **automatically** on the first run of any new binary — the
daemon you restart in the next step does it, as does any `muninn` command. To
apply them now without waiting:

```bash
muninn init
```

With no arguments and an existing config, `muninn init` leaves your config
untouched and just re-runs migrations. They are forward-only and idempotent:
already-applied ones are skipped and their checksums verified, and they never
modify existing index data — safe to re-run at any time.

If migration reports an error, the most common cause is a missing PostgreSQL
extension. See `docs/own-database.md` for extension setup instructions.

## Step 4: Restart the daemon

Linux (systemd):
```bash
systemctl --user start muninn-index
```

macOS (launchd):
```bash
launchctl bootstrap gui/$(id -u) ~/Library/LaunchAgents/org.muninn.index.plist
```

Verify: `muninn status` — all repos should appear with their index status.

## Step 5 (Docker users only): Update the database image

This is only needed occasionally when the `kamysh/postgres-ai` image is updated — check the release notes to see if this applies. It is separate from schema migrations.

```bash
# Pull the latest image
docker pull kamysh/postgres-ai:latest

# Stop and remove the old container (the volume with your data is NOT removed)
docker rm -f muninn-postgres

# Start a new container with the same volume
docker run -d \
  --name muninn-postgres \
  --restart always \
  -e POSTGRES_PASSWORD=changeme \
  -p 127.0.0.1:5432:5432 \
  -v muninn_data:/var/lib/postgresql/data \
  kamysh/postgres-ai:latest

# Apply any schema migrations (or just restart the daemon — it self-migrates)
muninn init
```

The `muninn_data` volume is preserved — your indexed data is not lost.
