# Uninstalling muninn

Steps to remove muninn entirely, or just parts of it. Follow only the sections that apply to your setup.

## Remove individual repos

Before tearing everything down, you can clean up repos one at a time:

```bash
muninn remove /path/to/repo
```

This deletes `.muninn.toml` from the repo root and removes all index data for that repo from the database. If the daemon is actively indexing the repo, `muninn remove` will print an error — stop the daemon first (see below) if needed.

To see all registered repos:

```bash
muninn list
```

## Stop and disable the daemon

Linux (systemd):
```bash
systemctl --user disable --now muninn-index
```

macOS / background process:
```bash
pkill muninn-index
```

## Disconnect from Claude Code

```bash
claude mcp remove muninn --scope user
```

Restart Claude Code to apply the change.

## Remove the binaries

```bash
rm -f ~/.local/bin/muninn ~/.local/bin/muninn-index ~/.local/bin/muninn-mcp
```

If you created a systemd unit file, remove it too:
```bash
rm -f ~/.config/systemd/user/muninn-index.service
systemctl --user daemon-reload
```

## Remove configuration and logs

```bash
rm -rf ~/.config/muninn
rm -rf ~/.local/state/muninn
```

Remove the muninn line from `~/.pgpass` (edit the file — the line looks like `localhost:5432:muninn:alice:changeme`). Edit carefully: this file controls access for all your PostgreSQL connections, not just muninn.

## Remove all index data from the database

**Docker users:**
```bash
# Connect inside the container
docker exec -it muninn-postgres psql -U postgres
```
```sql
DROP DATABASE muninn;
\q
```

Then stop and remove the container and volume:
```bash
docker rm -f muninn-postgres
docker volume rm muninn_data
```

**Own-database users:**
```bash
psql -h localhost -U postgres  # or however you connect as superuser
```
```sql
DROP DATABASE muninn;
-- Also remove the muninn role if you created one:
DROP ROLE alice;
```

## Verify nothing is left

```bash
# No muninn processes running
pgrep muninn  # should return nothing

# No muninn files
ls ~/.config/muninn 2>/dev/null && echo "still there" || echo "gone"
ls ~/.local/bin/muninn 2>/dev/null && echo "still there" || echo "gone"
```
