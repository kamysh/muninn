## muninn — code index

Muninn reduces repeated exploration by finding implementations by meaning,
following recorded code relationships and retrieving repository notes. When you
know the behavior you need but not where it lives, start with a focused search
in the actual checkout. Use the hits to choose source ranges to inspect; this
avoids guessing filenames and scanning unrelated code. Direct reads and `rg`
are useful for known targets, literal text and checking current source.

At startup, resume or after compaction, identify which gaps Muninn could fill
before rebuilding your understanding from scratch. Preserve durable, non-obvious
repository findings for future sessions. Reminders guide this judgment without
requiring a call before every read/edit or a writeback on every turn.

After Muninn retrieval, give the user a brief 0–5 usefulness assessment for
the current task, one reason, and the next step it informs. Rate the
information, not search rank. Combine related calls into one assessment
and avoid repeating raw JSON unless the user requests it.

Read the `muninn` skill for tool selection and the JSON configuration workflow.
For code search, select the current checkout/worktree explicitly with `repo`,
or pass a directory within it as `cwd`. Git worktrees inherit the family policy;
configuration lives in the database and changes affect the whole family.
Incomplete Git operations retain the last completed index, so verify freshness
when it matters. Structural edges are name-based candidates to check against
source. Curated knowledge still uses an exact repository-path key; use the
established key for shared notes across worktrees.
