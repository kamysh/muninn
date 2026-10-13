# Upgrading Muninn

Application upgrades update the three Muninn binaries and apply schema changes
automatically during normal startup/preparation. PostgreSQL or extension upgrades
are a separate operation with their own compatibility requirements.

The worktree structural-snapshot migration adds a table to each prepared family
schema. New linked worktrees publish into it; existing linked AGE graphs remain
readable until those checkouts are reconciled. The first search of a new linked
worktree in an already indexed, enabled family can register and index it directly.

The missing-root migrations add a persisted 60-second absence timer for families
and Git-listed checkouts. The public registry's path constraint now applies only
to active families, so a replacement clone may use the path of a retired family.
Automatic retirement retains the old family's schema and index; explicit removal
is still required to delete them. Reconnect old MCP processes after this upgrade
because their registration SQL predates the changed path constraint.

These docs describe 1.1 source. At the 2026-10-05 audit, GitHub's latest release
was still 0.9.4. Use matching source/binaries; a `releases/latest` download can
silently install the wrong interface.

## Application upgrades

1. Read the target release notes. Record current versions, executable/service
   paths and the actual database target. Preserve the old binaries and take a
   database backup appropriate to the migration effects. Backups/config copies
   can contain private source or credentials; keep them outside the repository.
2. Build or download **all three** matching binaries to a staging directory and
   verify their versions before replacing the installed files. See
   [Building](development.md#building-and-testing).
3. For a coordinated runtime/schema upgrade, stop the indexer and disconnect old
   Muninn MCP processes through their clients. Stopping the indexer alone does
   not stop already-running MCP servers. Preserve the service definition.
4. Replace the binaries at their existing paths. Do not replace the database,
   global connection configuration or unrelated agent settings.
5. Start the new runtime. Public migrations run on normal CLI/daemon/MCP startup;
   family preparation applies pending family-template migrations. No recurring
   external migration script is required. `muninn init` with an existing config
   can explicitly apply public migrations; family preparation handles the
   application schemas.
6. Verify service logs, registered families, saved policies and known-term searches
   in both the primary checkout and a linked worktree. Reconnect the MCP clients
   and check tool availability. Update the [agent guidance](claude-code-setup/INSTALL.md)
   when interfaces or behavior changed.

Read-only `config PATH --json`, check and preflight deliberately **do not migrate**;
`schema_not_ready` from them is not permission to edit migration history. Use the
normal preparation/startup route and investigate its error.

Kryzhen skips recorded migration blocks and verifies their identity. Application
migrations commit block by block; later failure can leave earlier blocks applied.
Index creation can take substantial time on existing data. There is no guarantee
that upgrades finish in a minute, that every migration is additive, or that an
older binary is safe against a newer schema.

## Service commands

Linux:

```sh
systemctl --user stop muninn-index
# Replace the binaries after preparation above.
systemctl --user start muninn-index
systemctl --user is-active muninn-index
journalctl --user -u muninn-index -n 50 --no-pager
```

macOS:

```sh
launchctl bootout "gui/$(id -u)/org.muninn.index"
# Replace binaries, then use the actual installed plist location.
launchctl bootstrap "gui/$(id -u)" "$HOME/Library/LaunchAgents/org.muninn.index.plist"
launchctl print "gui/$(id -u)/org.muninn.index"
```

For an externally located home, the plist may instead be in `/Library/LaunchAgents`.
Do not remove an existing service definition just to restart it. A CLI-only fix
with no runtime/schema changes need not restart the indexer, but replacing files
does not update already-running processes.

## Failure and recovery

On a migration/indexing failure, retain the logs and old/new version identities.
Do not edit an applied SQL block, drop the database, create a replacement graph
or relabel migration history to make startup succeed. Retry only after resolving
the actual problem; completed migration blocks remain recorded.

Restoring old binaries alone is a recovery option only when schema compatibility
has been established. Otherwise recovery needs the matching database backup and
configuration, with writers stopped and restoration explicitly planned.

## PostgreSQL or container upgrades

A newer image can change the PostgreSQL major version or AGE/pgvector binaries.
It is **not** a generic `docker pull` / container replacement procedure. Check
server/extension compatibility, the actual container and volume identities,
backup/restore or PostgreSQL upgrade requirements, and other applications sharing
the server. Plan this separately. Preserving a volume alone does not establish
that a new PostgreSQL version can read it safely.
