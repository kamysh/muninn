# Claude Code setup — muninn

Hand this directory to Claude Code with the instruction:
**"Walk me through installing this. Show me each change before applying it and wait for my approval."**

Claude Code will read the reference files here, compare them against what is
already on the machine, propose the minimal diff for each step, and apply it
only after you confirm.

## Prerequisites (verify before starting)

- `~/.local/bin/muninn`, `~/.local/bin/muninn-mcp`, and `~/.local/bin/muninn-index` installed (`muninn --version` works)
- `~/.config/muninn/config.toml` configured (`muninn status` succeeds)
- `jq` on PATH
- Claude Code installed, `claude` on PATH

## What is in this directory

| File | Purpose |
|---|---|
| `skill/SKILL.md` | Target content for `~/.claude/skills/muninn/SKILL.md` |
| `CLAUDE.md` | Target content for the muninn section of `~/.claude/CLAUDE.md` |
| `settings.json` | Reference hooks and permissions — **not a drop-in replacement**, see Step 2 |

## Steps (each requires human approval before Claude Code acts)

### Step 1 — skill file

Claude Code should:
1. Read `skill/SKILL.md` and `~/.claude/skills/muninn/SKILL.md` (if it exists).
2. Show the diff.
3. Write the new file only after approval. Create `~/.claude/skills/muninn/` if absent.

### Step 2 — settings.json hooks and permissions

`settings.json` here is a **reference**, not a replacement. The existing
`~/.claude/settings.json` may have other permissions, hooks, and settings that
must be preserved.

Claude Code should:
1. Read `settings.json` and `~/.claude/settings.json`.
2. For each section (`permissions.allow`, each hook event), identify what is
   present in the reference but absent in the target.
3. Show the proposed additions as a clear before/after of the relevant sections.
4. Apply each addition only after approval. Never remove existing entries.

The things to add if absent:

**`permissions.allow`** — these muninn search tools should not prompt:
```
mcp__muninn__search_hybrid
mcp__muninn__search_fulltext
mcp__muninn__search_semantic
mcp__muninn__search_structural
```

**Hooks:**
- **`SessionStart`**: muninn skill reminder echo
- **`UserPromptSubmit`**: muninn search reminder + per-prompt sentinel reset
- **`PostToolUse`** (matcher `mcp__muninn__search_hybrid|…`): muninn sentinel creation

See `settings.json` for the exact commands.

### Step 3 — CLAUDE.md (global instructions)

`~/.claude/CLAUDE.md` is loaded by Claude Code at the start of every session.
The `CLAUDE.md` here contains the muninn section only.

Claude Code should:
1. Read `CLAUDE.md` and `~/.claude/CLAUDE.md` (if it exists).
2. If the muninn section is already present, show what would change.
3. If absent, show the section that would be appended.
4. Apply only after approval. Never remove unrelated sections.

### Step 4 — register MCP server

Claude Code should run `claude mcp list` and check whether `muninn` is registered
and pointing at `~/.local/bin/muninn-mcp`.

If missing or wrong path:
```
claude mcp remove muninn --scope user   # only if it exists with wrong path
claude mcp add --scope user muninn ~/.local/bin/muninn-mcp
```

Show the proposed commands and wait for approval before running each one.

### Step 5 — verify

After all changes are applied:
1. Show the final `~/.claude/settings.json` for a last review.
2. Run `claude mcp list` to confirm `muninn` is registered and Connected.
3. Prompt the user to restart Claude Code for hooks and the new MCP binary to take effect.

## If mimir is also installed

When both mimir and muninn are wired, you can add a stronger enforcement hook
that requires both tools to be queried before any file access. This goes in
`PreToolUse` with matcher `Read|Edit|Write|Grep|Glob`:

```json
{
  "matcher": "Read|Edit|Write|Grep|Glob",
  "hooks": [{
    "type": "command",
    "command": "sid=$(jq -r .session_id 2>/dev/null); { [ -f \"/tmp/claude-mm-mimir-$sid\" ] && [ -f \"/tmp/claude-mm-muninn-$sid\" ]; } || { echo 'Policy: query mimir (mcp__mimir__query_relevant) AND muninn (mcp__muninn__search_*) BEFORE reading files or writing code. Run both, then retry.' >&2; exit 2; }"
  }]
}
```

Also expand the `UserPromptSubmit` sentinel reset to cover both tools:
```
sid=$(jq -r .session_id 2>/dev/null); rm -f "/tmp/claude-mm-mimir-$sid" "/tmp/claude-mm-muninn-$sid"
```

See `docs/claude-code-setup/settings.json` in the mimir repo for the full mimir hook set.
