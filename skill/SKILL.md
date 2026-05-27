---
name: muninn
description: Use when mcp__muninn tools are available — guides when to search the code index, which search tool to pick, and when to write knowledge back
---

# Using Muninn

Muninn is a code knowledge store. It indexes your repositories and exposes search tools so Claude can answer questions about your codebase without reading files line by line.

The `UserPromptSubmit` hook fires `search_hybrid` before every message. Your job is to act on what comes back and write discoveries worth keeping.

## Choosing a search tool

| Situation | Tool |
|-----------|------|
| General questions about code, unclear what to look for | `search_hybrid` |
| You know the exact symbol or string | `search_fulltext` |
| You have a concept but not the exact name | `search_semantic` |
| Who calls X? What does Y import? What implements Z? | `search_structural` |
| Retrieving stored notes | `search_knowledge` |

Start with `search_hybrid` when in doubt — it combines semantic and full-text with RRF ranking and degrades gracefully when one signal is weak.

## When to record knowledge

`record_knowledge` stores a note anchored to the codebase. Use it when you discover something that:

- Is **non-obvious** from reading the code (a hidden constraint, a non-local invariant, a surprising dependency)
- Would **save time** if recalled at the start of a related future task
- Is **stable** — not just the current state of in-progress work

Do not record things derivable by searching: function signatures, file locations, obvious naming. Record the *why*, not the *what*.

## Working alongside mimir

Muninn and [mimir](https://github.com/kamysh/mimir) are complementary:

- **Muninn** — facts about your code: what exists, how it's connected, what's non-obvious
- **Mimir** — beliefs about how to work: heuristics, patterns, confidence-weighted rules that evolve over time

When the hook fires before a task, both should be queried: muninn for code context, mimir for approach guidance.
