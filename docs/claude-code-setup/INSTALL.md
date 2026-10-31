# Agent setup — Codex and Claude Code

This directory retains its historical name but contains shared Muninn usage
instructions for both clients. The skill explains **why and when** search and
repository notes help, and **how** to select a checkout or configure its family.
The hook examples are client-specific: [codex-hooks.json](codex-hooks.json) for
Codex and [settings.json](settings.json) for Claude Code.

## Obtain the installation files

If you installed release binaries without a source checkout, download the matching
installation files before using the relative paths below:

```sh
mkdir -p "$HOME/.local/share/muninn"
curl -fL https://github.com/kamysh/muninn/archive/refs/tags/v1.2.2.tar.gz \
  | tar -xz -C "$HOME/.local/share/muninn"
cd "$HOME/.local/share/muninn/muninn-1.2.2"
```

If you already have that checkout, change to its root instead. This downloads
scripts and client guidance; it does not build the application.

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

## Install the startup reminder

Include this reminder in the standard agent setup. Tool registration alone does
not explain how search or persistent knowledge can improve the next decision.
The reminder gives concrete reasons to retrieve earlier reasoning and locate
relevant implementations before repeating broad exploration. Lifecycle delivery
restores that guidance when a session starts, resumes or compacts its context.
Muninn itself still works without a hook; record an intentional omission rather
than claiming that the complete agent setup was verified.

Choose **one** reusable text:

| Installed tools | Reminder |
| --- | --- |
| Muninn | [reminders/muninn.md](reminders/muninn.md) |
| Muninn and Mimir, with both MCP servers and skills available | [reminders/mimir-muninn.md](reminders/mimir-muninn.md) |

Mimir is optional and separately installed. The combined text explains how prior
decisions and failed approaches can change today's choices; it does not install
Mimir or assume that Muninn provides its tools. Both versions explain Muninn's
value for finding behavior when the implementation's location is unknown.

From the Muninn source root, select the appropriate file:

```sh
REMINDER_SOURCE=docs/claude-code-setup/reminders/muninn.md
# If both tools and skills are installed, use this instead:
# REMINDER_SOURCE=docs/claude-code-setup/reminders/mimir-muninn.md
```

Review an existing reminder before replacing it. Install the selected text at a
stable location so the hook keeps working after this source checkout is moved.
These examples use POSIX shells; adapt paths for a different client config root.

### Codex reminder

```sh
mkdir -p "${CODEX_HOME:-$HOME/.codex}"
cp "$REMINDER_SOURCE" "${CODEX_HOME:-$HOME/.codex}/muninn-reminder.md"
```

Merge the `SessionStart` entry from [codex-hooks.json](codex-hooks.json) into
`${CODEX_HOME:-$HOME/.codex}/hooks.json`. If an equivalent reminder already exists,
update that entry instead of adding another. Preserve other hooks and settings;
do not also register the same reminder in inline TOML or a project hook.

Review and trust the new or changed hook through Codex's `/hooks` interface.
Codex skips untrusted hook definitions; an agent editing JSON or successfully
running the command does not establish trust. Leave trust records to the client.
The example has no source filter, so `SessionStart` covers startup, resume,
clear and post-compaction delivery. See the
[official Codex hook reference](https://learn.chatgpt.com/docs/hooks).

### Claude Code reminder

```sh
mkdir -p "$HOME/.claude"
cp "$REMINDER_SOURCE" "$HOME/.claude/muninn-reminder.md"
```

Merge only the `SessionStart` entry from [settings.json](settings.json) into
`~/.claude/settings.json`, replacing an equivalent reminder if present. Its
unfiltered `SessionStart` also covers startup, resume and compaction. Use
Claude's `/hooks` interface to inspect the loaded entry, and a fresh session to
verify the saved setup. See the
[official Claude hook reference](https://code.claude.com/docs/en/hooks#sessionstart).

The reference file also contains optional prompt/result reminders and tool-allow
entries. They are not needed for startup delivery: do not copy the whole file
over existing settings or change permissions as part of installing this reminder.
The optional PostToolUse example needs `jq` on the hook process's PATH.

### Advisory behavior and existing setups

These hooks only print the selected text. They do not run searches, modify
memory, block reads or compute ratings. The guidance asks the agent to
explain retrieved information with a brief 0–5 usefulness assessment in
plain language. Instructions in a skill explain the detailed workflow and
limitations.

Preserve collaboration hooks and unrelated settings. When upgrading older
Muninn guidance, remove obsolete Muninn sentinel/rating conditions only within
the agreed scope. A combined reminder does not authorize changing existing Mimir
gates or duplicating a separate Mimir startup reminder; review any overlap.

## Verify what actually loaded

1. Verify the installed skill, chosen reminder and merged settings. Parse the JSON
   and run the reminder command directly as shown below. It should print the
   selected text, exit zero and perform no search or mutation. This checks the
   command, not lifecycle delivery.
2. Reconnect Muninn through the client's controls, or start a new client session
   to load the executable, skills and guidance. Do not kill unrelated sessions.
3. Confirm Muninn's eight tools appear. `mcp list` verifies configuration; a real
   tool call verifies the connected server.
4. Ask for a known indexed term with `search_fulltext`, setting `repo` to the
   actual checkout. Read the returned source and verify its checkout path.
5. Check `config PATH --json` / `preflight PATH --json` with the installed CLI.
   Successful policy inspection does not itself mean first indexing completed.
6. Check reminder delivery separately for a fresh session, a resumed session and
   after manual `/compact` in a disposable conversation. Resolve any hook review,
   disabled-hook or path errors. Use the client's hook diagnostics/transcript to
   confirm the emitted text reaches model context. If that evidence is unavailable,
   report delivery as unverified; merely seeing `/hooks` list the entry is not proof.
7. In a fresh session, give the agent a real repository question whose relevant
   implementation is not named. Observe whether it uses a focused search and
   verifies relevant source. For a combined installation, also try an approach
   question with a known, relevant Mimir lesson. Do not include an explicit tool
   command in these prompts: forced calls only check connectivity. Record whether
   retrieval helped, missed relevant information or was bypassed. Reminder delivery
   alone does not demonstrate useful tool selection. After retrieval, check
   that the agent gives a concise 0–5 usefulness assessment, a reason and a
   next step in plain language. A client-rendered tool preview may still
   show raw JSON; the guidance controls the agent’s explanation.

Direct command checks, after installing the selected text:

```sh
# Codex
printf '%s\n' '{"hook_event_name":"SessionStart","source":"compact"}' |
  sh -c 'cat "${CODEX_HOME:-$HOME/.codex}/muninn-reminder.md"'
# Claude Code
printf '%s\n' '{"hook_event_name":"SessionStart","source":"compact"}' |
  sh -c 'cat "$HOME/.claude/muninn-reminder.md"'
```

The commands deliberately ignore event input and print the same guidance for
each source. Supplying `source: compact` here does **not** exercise compaction
inside either client. Report lifecycle events and behavioral checks not performed,
including automatic compaction if only manual compaction was observed.

Report fresh-process checks separately from behavior in an already-open client.
Existing MCP processes retain the executable they started with until reconnected.
