# Agent setup — Muninn 1.0

This directory contains the shared Muninn skill, a short global-instructions
section, and Claude Code reminder-hook examples. The guidance applies to Codex
and Claude Code; the hook settings file is specific to Claude Code.

## Prerequisites

Verify the installed binaries (`muninn --version`), global connection config
(`muninn status`), and the existing Muninn MCP registration in the target client.
Use the current installation's database and credentials. The skill describes
repository registration, JSON configuration, preflight and explicit first start.

Agree on the setup changes before applying them. Approval covers the agreed
stage through verification; preserve unrelated instructions, hooks, permissions,
MCP registrations and settings.

## Skill and global instructions

| Client | Skill target | Global-instructions target |
| --- | --- | --- |
| Codex | `~/.codex/skills/muninn/SKILL.md` | Muninn guidance in `~/.codex/AGENTS.md` |
| Claude Code | `~/.claude/skills/muninn/SKILL.md` | Muninn section in `~/.claude/CLAUDE.md` |

Compare `skill/SKILL.md` with the installed skill, then copy the approved version.
Use `CLAUDE.md` here as the short Muninn guidance for either client; replace the
existing Muninn section or update equivalent prose rather than duplicating it.
The skill is client-neutral and contains the actual usage/configuration workflow.

## Reminder hooks

`settings.json` is a Claude Code reference, not a replacement for an existing
settings file. Merge only the agreed Muninn entries. Its hooks explain when
search helps, how to choose the checkout, and how to judge returned source.
They do not search automatically, block file access, require a relevance score,
create query sentinels, or require a writeback every turn.

When upgrading older integration, replace the old Muninn hooks and remove their
sentinel/rating requirements, including Muninn conditions in shared hooks.
Preserve unrelated behavior in shared hooks; do not install a second reminder
alongside an obsolete gate. Keep existing tool permissions unchanged unless
permission changes are part of the agreement. The reference lists the four
read-only code-search tools for installations that want explicit allow entries.

Codex installations can retain their existing advisory Mimir/Muninn reminder;
it should point to the updated skill. Do not copy Claude's settings file into
Codex or replace a collaboration/permission hook with a tool-use reminder.

## MCP registration

The existing client registration should point to the installed `muninn-mcp`.
For Claude Code, inspect it with `claude mcp list`. If setup requires a new
registration, the user-scoped command is:

```sh
claude mcp add --scope user muninn ~/.local/bin/muninn-mcp
```

Changing a registration is part of the agreed setup stage, not a reason to
reconfigure the database. Use the installed client's MCP controls for Codex.

## Verification

- Parse the edited JSON; inspect a focused diff for unrelated changes.
- Exercise changed reminder commands with representative event input: they
  should exit successfully without mutating repositories or invoking searches.
- Verify the skill's read-only `config`/`preflight` examples against the installed
  CLI, and code search with the intended checkout path.
- Inspect a fresh MCP process's `tools/list` descriptions. Existing MCP processes
  keep the executable they started with until reconnected.
- Distinguish verified files/fresh-process behavior from what an already-open
  client has loaded. Reload/reconnect through that client's controls or use a
  new session when needed; do not kill unrelated sessions to force a reload.
