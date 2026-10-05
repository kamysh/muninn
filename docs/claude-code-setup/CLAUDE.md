## muninn — code index

Use Muninn when code discovery, cross-file search, relationships, or recorded
repository knowledge can save exploration. Evaluate the hits and read relevant
source ranges. Direct reads and `rg` are appropriate for known locations,
literal text, or an index miss. Reminders do not require a call before every
read/edit, a numeric rating, or a writeback on every turn.

Read the `muninn` skill for tool selection and the JSON configuration workflow.
For code search, select the current checkout/worktree explicitly with `repo`,
or pass a directory within it as `cwd`. Git worktrees inherit the family policy;
configuration lives in the database and changes affect the whole family.
Incomplete Git operations retain the last completed index, so verify freshness
when it matters. Structural edges are name-based candidates to check against
source. Curated knowledge still uses an exact repository-path key; use the
established key for shared notes across worktrees.
