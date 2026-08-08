## muninn — code index

The `UserPromptSubmit` hook does not fetch results for you — it only prints a
reminder before every message. **You must call a muninn search tool yourself**
before reading or editing code, and then **evaluate whether what came back is
actually relevant** to the task, not just fire the call and move on.

- Each hit gives `file_path` and a `start_line..end_line` range. **Read that range
  before reading the whole file.** Do not re-grep for a symbol muninn already located.
- Judge the results: do they actually answer what you need? If the top results miss
  what you need, switch tool (`search_fulltext` for an exact symbol, `search_structural`
  for call sites) and say so — do not silently fall back to grep while ignoring the
  muninn miss, and do not treat an irrelevant result set as satisfying the requirement.
- Muninn answers "where is X in the code." Mimir answers "what did I learn about how
  to work here." Do not conflate them.
