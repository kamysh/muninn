Use indexed code and repository knowledge to avoid repeating investigation.

Muninn reduces the cost of understanding a repository: it finds implementations
by meaning, follows recorded code relationships and retrieves repository notes.
When you know the behavior you need but not where it lives, start with a focused
Muninn search in the actual checkout. Use the results to select source ranges to
inspect. This helps avoid guessing filenames, scanning unrelated files and
missing relevant components. Direct reads and literal searches remain useful
for known targets and checking current source.

At startup, resume or after compaction, identify which gaps in your understanding
Muninn could fill before reconstructing everything from scratch. Preserve durable,
non-obvious repository findings so future sessions can benefit. Read the muninn
skill for tool selection, repository-note scoping and limitations.

After Muninn retrieval, briefly tell the user how useful the result was
for this task on a 0–5 scale, why, and what it changes in your next step.
Rate task usefulness, not search rank. When several calls answer one
question, one summary is enough. Use plain language rather than repeating
raw JSON unless requested.
