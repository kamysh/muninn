# Upgrading muninn

Two things to update: the binaries and the database schema (if the new release includes new migrations). Both take under a minute. Your indexed data is preserved — migrations are additive and never delete existing index data.

## Step 1: Stop the daemon

Linux (systemd):
```bash
systemctl --user stop muninn-index
```

macOS / background process:
```bash
pkill muninn-index
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

```bash
muninn config
```

The editor will open your existing config. Save and close without changes. muninn connects to the database and applies any new migrations. If there are none, it exits immediately. This step is always safe — it never modifies existing index data.

Migrations are idempotent: already-applied ones are skipped, and checksums of applied ones are verified. Safe to re-run at any time.

If `muninn config` reports a migration error, the most common cause is a missing PostgreSQL extension. See `docs/own-database.md` for extension setup instructions.

## Step 4: Restart the daemon

Linux (systemd):
```bash
systemctl --user start muninn-index
```

macOS / background:
```bash
muninn-index &
```

Verify: `muninn list` — all repos should appear with their index status.

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

# Apply any schema migrations
muninn config
```

The `muninn_data` volume is preserved — your indexed data is not lost.
