---
name: muninn
description: Use when mcp__muninn tools are available — guides how to call the code-index search tools, which one to pick, how to read results, when to prefer muninn over grep, and when to write knowledge back
---

# Using Muninn

Muninn indexes your repositories and exposes search tools so you can answer questions about a codebase by semantic/structural/full-text search instead of reading or grepping file-by-file.

The `UserPromptSubmit` hook does not run any search for you — it only prints a reminder before every message. **You must call a search tool yourself**, and **querying is not the goal — evaluating and using the result is.** Judge whether what came back actually answers the task; act on it, or refine and re-query. Do not fire a query, decide it "counts," and then grep for the same thing anyway.

## How to call

Every search tool takes:

- **`repo: <absolute path>`** — the repository to search. **Pass this explicitly whenever the target repo is not your shell's working directory.** Do NOT pass the target path as `cwd`.
- **`cwd`** — use only to let muninn walk up from your current directory to the nearest `.muninn.toml`.
- **`limit`** — pass a generous value (≈15–20) for discovery; the default is small.

## Reading results — evaluate relevance, then act

Each hit gives `file_path` plus a `start_line..end_line` range.

**Required discipline:** for each result, judge whether it is actually relevant
to the task before using it — do not treat "the query ran" as satisfying the
requirement. Then read the pointed-to range *before* doing anything else with
that file. Do not open the file from line 1 when muninn already told you where
the relevant section is. Do not grep for the same symbol you just searched.

If the top results are not relevant / not what you need:
- Switch tool (see table below) — do not silently fall back to Bash grep.
- Surface the miss to the user if the search should have found something and
  didn't (stale index, missing exclude, wrong repo path). This is a product signal.

Scores are **RRF rank-reciprocals (≈ 0.01–0.03), not relevance percentages.**
Use the *rank order*, not the magnitude. Near-uniform low scores are normal —
they are NOT a signal that "nothing matched."

If results look stale or wrong (paths that no longer exist, build artifacts like
`target/**`), the index is stale or mis-configured — run `muninn reindex <repo>`,
check the repo's `.muninn.toml` excludes, and say so.

## Choosing a tool — and when to prefer muninn over grep

| You want… | Tool |
|-----------|------|
| Find by *concept / behavior* when you don't know the symbol | `search_hybrid` (or `search_semantic`) |
| An *exact* symbol or string, repo-wide | `search_fulltext` — this is muninn's grep |
| Callers / callees / imports / inheritors / inherits / defines | `search_structural` — **don't grep for call sites** |
| Retrieve stored notes | `search_knowledge` |
| General / unsure | `search_hybrid` (semantic + full-text via RRF) |

**`search_structural` caveats:**
- Matches are **name-scoped, not path-scoped** — if multiple files define a same-named symbol (e.g. every crate's own `main`), a `callers`/`callees` result set can mix matches for different actual functions. Always check each result's `file_path`, don't assume the first hit is the one you meant.
- Cross-file call edges are only fully resolved by a **full reindex** (`muninn reindex <repo>` / `muninn add`). The daemon's incremental single-file watcher only re-resolves same-file calls, so a call added to a live-edited repo may not show up as a caller/callee until the next full reindex.

**Reach for muninn over grep/Read when:** you don't know the exact name (conceptual search → `search_hybrid`/`search_semantic`); you need the call graph (→ `search_structural` — its killer use); or you're searching across files/repos. **grep/Read are fine** when you already know the exact string *and* which file it's in. For an exact identifier across the whole repo, **`search_fulltext` is the muninn equivalent of grep** — prefer it; it is also the robust fallback when `search_hybrid` is drowned by a dominating corpus (vendored deps, generated files, `target/`).

**Anti-pattern:** call a search tool, ignore what it returned, then grep for the same thing. If a search misses what it should find, that is a product signal — refine the query or switch tool, and surface the miss. Don't silently fall back to grep.

## When to record knowledge

`record_knowledge` stores a note anchored to the codebase. Use it when you discover something that:

- Is **non-obvious** from reading the code (a hidden constraint, a non-local invariant, a surprising dependency)
- Would **save time** if recalled at the start of a related future task
- Is **stable** — not just the current state of in-progress work

Do not record things derivable by searching: function signatures, file locations, obvious naming. Record the *why*, not the *what*.

## Working alongside mimir

Muninn and mimir are complementary:

- **Muninn** — facts about your code: what exists, how it's connected, what's non-obvious
- **Mimir** — beliefs about how to work: heuristics, patterns, confidence-weighted rules that evolve over time

**Muninn answers "where is X in the code." Mimir answers "what did I learn that should change my approach."** Do not query mimir for code locations or muninn for lessons.

When the hook fires before a task, both should be used: read the muninn range hits, dispose of the mimir priors (follow or override with one line), then act.
