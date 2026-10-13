# Removing Muninn or an indexed family

Choose the scope: one worktree, one family's index, client integration, or the
whole installation. They have different effects. Keep backups if index data or
curated knowledge must be recoverable.

## One linked worktree

Remove the worktree through your normal Git workflow. The enabled family's daemon
discovers its absence from Git's worktree registry, retires its checkout index,
removes its structural snapshot and drops any older AGE graph. Shared versions
still used by other checkouts remain. If Git still lists a checkout whose local
directory stays missing for 60 seconds, Muninn retires its registration but
retains its stored index. Other filesystem errors do not trigger retirement.

The daemon also retires a registered family when its stored local root is
missing for 60 seconds. The retained index and policy are not deleted; the family
disappears from ordinary status and indexing, and a replacement clone can be
registered at the same path. Use explicit `muninn remove /registered/path` to
delete retained data if needed.

Do **not** use `muninn remove` to remove only one linked worktree: that command
operates on a registered family's index, not a checkout-specific removal intent.

## One registered family

First identify the registered locator:

```sh
muninn status
```

Use the exact registered path displayed there:

```sh
muninn remove /registered/path
```

Review the confirmation. The command removes the application schema and its code
index, including graphs for registered checkouts, and removes the registry row.
The command coordinates with active indexing and may wait for the index lock; the old blanket description
that removal always refuses while indexing is obsolete.

Source files and Git worktrees remain. Curated notes in `public.knowledge` are
separate and are not deleted by family removal; remove them explicitly through
the knowledge tools if intended. Family policies/history live in the removed
application schema and are lost with it. `--yes` skips confirmation; use it only
when this exact destructive scope is already approved.

## Disconnect agent clients

For the clients you configured:

```sh
codex mcp remove muninn
claude mcp remove --scope user muninn
```

Reconnect/reload the affected client so old MCP processes are no longer running.
Remove only the Muninn skill, instruction section and optional reminder hooks.
Preserve other tools, shared-hook behavior and permissions. See
[Agent setup](claude-code-setup/INSTALL.md) for the possible skill locations.

## Stop and remove the service

Linux:

```sh
systemctl --user disable --now muninn-index
rm "$HOME/.config/systemd/user/muninn-index.service"
systemctl --user daemon-reload
```

macOS:

```sh
launchctl bootout "gui/$(id -u)/org.muninn.index"
# Remove only the actual installed org.muninn.index.plist afterward.
```

The plist may be under `~/Library/LaunchAgents` or `/Library/LaunchAgents`; use
the installed location and its required permissions. For a foreground daemon,
stop that specific process. Check that neither daemon nor old MCP clients remain
before deleting binaries or attempting database removal.

## Remove local files

For the default standalone installation:

```sh
rm "$HOME/.local/bin/muninn" "$HOME/.local/bin/muninn-index" "$HOME/.local/bin/muninn-mcp"
```

A Nix profile installation should be removed through that profile instead.
Remove `~/.config/muninn` and `~/.local/state/muninn` only if you also want to discard
configuration/logs. Local model caches may be shared; identify their actual path
and other users before removing them. Edit only the matching `~/.pgpass` entry,
not the whole credential file. Backups are separate files and are not automatically
removed.

## Optional database removal

Stop writers and verify the **actual** database and role names first. As the
administrator, connected to a different database, the corresponding commands for
the default names are:

```sql
DROP DATABASE muninn;
DROP ROLE muninn;
```

This destroys code indexes, saved policies and curated knowledge. A shared role
may own other resources and should not be dropped merely because Muninn is gone.

If postgres-ai also hosts Mimir or another application, keep its container and
volume. Only a dedicated instance that you intend to destroy should be removed,
using its verified container/volume names. Keeping a shared server is compatible
with completely removing Muninn's own database.

## Verification

Check the selected scope: no Muninn client registration/process, service stopped,
binaries absent from PATH, and the intended registration/database absent if you
chose to remove it. Do not claim all data was removed merely because the CLI is
no longer installed.
