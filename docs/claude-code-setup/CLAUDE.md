## muninn — code index

Muninn search results arrive via the `UserPromptSubmit` hook before every message.
**Using the result is the point, not firing the query.**

- Each hit gives `file_path` and a `start_line..end_line` range. **Read that range
  before reading the whole file.** Do not re-grep for a symbol muninn already located.
- If the top results miss what you need, switch tool (`search_fulltext` for an exact
  symbol, `search_structural` for call sites) and say so — do not silently fall back
  to grep while ignoring the muninn miss.
- Muninn answers "where is X in the code." Mimir answers "what did I learn about how
  to work here." Do not conflate them.
