# Agent setup — Codex and Claude Code

This directory retains its historical name but contains shared Muninn usage
instructions for both clients. The skill explains **why and when** search and
repository notes help, and **how** to select a checkout or configure its family.
The `settings.json` hook example is specific to Claude Code.

## Before changing client settings

Complete the [Muninn installation](../get-started.md): matching binaries, postgres-ai
(or a deliberately chosen custom compatible stack), global connection settings,
and a started/indexed family. Check binary versions and `muninn status`. Existing
installations should reuse their database, credentials and client registration.

Agree on the affected client settings and preserve unrelated instructions, hooks,
permissions and MCP servers. Registration makes a tool available; useful guidance
explains how to use it. Neither step guarantees that a particular client session
has loaded the new configuration.

## Register the stdio MCP server

Use the absolute installed `muninn-mcp` path. For the default binary destination:

### Codex

Inspect existing registrations with `codex mcp list` and `codex mcp get muninn`.
For a new registration:

```sh
codex mcp add muninn -- "$HOME/.local/bin/muninn-mcp"
codex mcp list
```

This configures a local process, not a remote HTTP service. See the
[official Codex MCP instructions](https://learn.chatgpt.com/docs/extend/mcp?surface=cli).

### Claude Code

Inspect with `claude mcp list` and `claude mcp get muninn`. For a new registration:

```sh
claude mcp add --transport stdio --scope user muninn -- "$HOME/.local/bin/muninn-mcp"
claude mcp list
```

User scope makes the local installation available across repositories. See the
[official Claude MCP instructions](https://code.claude.com/docs/en/mcp).

If a registration already exists, compare its executable path and intended scope;
do not add a duplicate or overwrite unrelated settings. In either client the
process must see the correct global Muninn configuration and database credentials.

## Install the skill and global guidance

| Client | User skill location for a new setup | Global instructions |
| --- | --- | --- |
| Codex | `~/.agents/skills/muninn/SKILL.md` | `~/.codex/AGENTS.md` (or the installation's configured Codex home) |
| Claude Code | `~/.claude/skills/muninn/SKILL.md` | `~/.claude/CLAUDE.md` |

Current Codex documentation uses `~/.agents/skills`. Some existing installations,
including the maintainer's setup, discover `~/.codex/skills`; update the working
location when that is the installation's actual skill source. Avoid installing
duplicate skills under both roots. Confirm discovery in the target client.
Sources: [Codex skills](https://learn.chatgpt.com/docs/build-skills),
[Codex global instructions](https://learn.chatgpt.com/docs/agent-configuration/agents-md),
[Claude skills](https://code.claude.com/docs/en/skills).

Compare [skill/SKILL.md](skill/SKILL.md) with the existing installed skill, then
copy the approved version into the chosen location. For a new standard Codex
installation, from the Muninn source root:

```sh
mkdir -p "$HOME/.agents/skills/muninn"
cp docs/claude-code-setup/skill/SKILL.md "$HOME/.agents/skills/muninn/SKILL.md"
```

For Claude Code:

```sh
mkdir -p "$HOME/.claude/skills/muninn"
cp docs/claude-code-setup/skill/SKILL.md "$HOME/.claude/skills/muninn/SKILL.md"
```

Use [CLAUDE.md](CLAUDE.md) here as a short Muninn section for either client's
global instructions. Merge or replace the existing Muninn section; do not replace
the entire global file or duplicate equivalent prose.

## Optional reminder hooks

The skill and guidance work without hooks. [settings.json](settings.json) provides
Claude reminders about selecting the checkout and inspecting results. Merge only
the agreed entries into an existing settings file. Do not copy that file into
Codex or replace a collaboration/permission hook with a search reminder.

The reminders do not search automatically, block file reads, require a relevance
score or demand a writeback each turn. When updating an older installation, remove
obsolete **Muninn** sentinel/rating requirements, including Muninn conditions in
shared hooks, while preserving unrelated behavior. Existing Mimir requirements
are a separate setting. The reference also includes optional tool-allow entries;
changing permissions requires its own agreement. The PostToolUse example needs
`jq` on the hook process's PATH.

Codex setups may retain an existing advisory reminder pointing to the shared
skill. No additional Codex hook installation is required by Muninn.

## Verify what actually loaded

1. Verify the installed skill content and merged instructions/settings. If hooks
   were changed, parse their JSON and run the reminder commands with representative
   input; they should exit successfully without mutation or automatic searches.
2. Reconnect Muninn through the client's controls, or start a new client session
   to load the executable, skills and guidance. Do not kill unrelated sessions.
3. Confirm Muninn's eight tools appear. `mcp list` verifies configuration; a real
   tool call verifies the connected server.
4. Ask for a known indexed term with `search_fulltext`, setting `repo` to the
   actual checkout. Read the returned source and verify its checkout path.
5. Check `config PATH --json` / `preflight PATH --json` with the installed CLI.
   Successful policy inspection does not itself mean first indexing completed.

Report fresh-process checks separately from behavior in an already-open client.
Existing MCP processes retain the executable they started with until reconnected.
