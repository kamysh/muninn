# Muninn

Code search and repository knowledge for AI coding agents through MCP.

Muninn maintains a searchable code index for Codex, Claude Code and other
compatible MCP clients. Ask where a behavior is implemented, retrieve relevant
source ranges, and inspect the code before changing it.

Git worktrees share unchanged content and embeddings while keeping separate
searchable views. A search selects the checkout named by `repo` or `cwd`, so a
feature branch and the primary checkout can return their own implementations.

- Combine semantic and full-text retrieval with hybrid search.
- Follow recorded structural relationships and verify them against source.
- Reuse unchanged indexed content across linked Git worktrees.
- Store and search curated repository notes.

Muninn needs PostgreSQL with pgvector, Apache AGE and pgcrypto, an indexing
watcher, and an MCP connection. Local and hosted embedding backends are
available; hosted embeddings send selected source chunks to the provider.

Start with [Getting started](docs/get-started.md). Agents performing installation
use [AGENTS.md](AGENTS.md).

**Article:** [Muninn code search across Git worktrees](docs/articles/worktree-code-search.md).

## Install the binaries with Nix

With Nix installed and its `nix-command` and `flakes` features enabled, build the
CLI, watcher and MCP server without installing them:

```sh
nix build github:kamysh/muninn#muninn
./result/bin/muninn --version
./result/bin/muninn-index --version
./result/bin/muninn-mcp --version
```

To add these programs to your user profile instead, use
`nix profile add github:kamysh/muninn#muninn`.
This installs binaries only. Follow [Getting started](docs/get-started.md) to
prepare PostgreSQL and its extensions, configure embeddings, start the watcher
and connect your MCP client. No database or service is created by this package.
Use the installed absolute executable paths when configuring the watcher and
MCP client; `command -v muninn-index` and `command -v muninn-mcp` show them after
installation.

The commands follow the repository's default branch. Append a commit to the
repository address, as in `github:kamysh/muninn/COMMIT#muninn`, to pin a version.

## Why Muninn exists

An agent repeatedly exploring a large codebase spends context and time finding
the same implementations. Plain text search is useful when the name is known;
questions about behavior, relationships and prior repository decisions need
other entry points. Muninn maintains a searchable index and durable notes so an
agent can find relevant source, then read and verify it.

Git worktrees add a second problem: each checkout has its own files, but copying
a full chunk/vector index for every branch wastes space and embedding work.
Muninn groups linked worktrees into a **repository family**. It shares
unchanged file versions and embeddings, stores file differences per checkout,
and searches the checkout the caller selected. Updating the primary checkout
adjusts those differences without changing another checkout's published view.

Registration is explicit. A cheap inventory helps a human or agent choose which
files matter before the first index starts. An enabled family discovers linked
worktrees automatically and shares its configuration across them. Independent
non-Git directories can also be registered.

## What runs

| Component | Role |
| --- | --- |
| `muninn` | CLI: bootstrap, configuration TUI/JSON, inventory and indexing control |
| `muninn-index` | Background watcher and reconciliation of enabled families |
| `muninn-mcp` | Stdio MCP server launched by the agent client |
| postgres-ai | Recommended database distribution: a compatible PostgreSQL, pgvector and Apache AGE stack |

Use [postgres-ai](https://github.com/kamysh/postgres-ai) for installation. The
underlying prerequisites are PostgreSQL with pgvector, Apache AGE and pgcrypto;
postgres-ai supplies them together. Assembling a compatible stack yourself is an
advanced, non-recommended alternative, documented separately in the
[custom database guide](docs/own-database.md).

MCP provides `search_hybrid`, `search_fulltext`, `search_semantic`,
`search_structural`, and `record_knowledge`, `search_knowledge`,
`list_knowledge`, `delete_knowledge`.

Search results are evidence to inspect, not compiler-verified answers. Full-text
search is tokenized; structural edges are name-based candidates. During a
merge, rebase or unresolved conflict, Muninn retains the last completed index
instead of indexing transient conflict contents. See [behavior and limits](docs/development.md#worktree-indexing-and-search).

The Codex and Claude Code guidance asks agents to explain, in plain language,
how useful a Muninn retrieval was for the current task: a 0–5 score, a reason
and the next step. This is the agent’s judgment, not a search rank. The
[agent setup guide](docs/claude-code-setup/INSTALL.md) installs that guidance.

## Data and privacy

The database and processes can run on your machine. Local embeddings run there
after the model is downloaded. Hosted Voyage/OpenAI embeddings send selected
source chunks and query text to the provider; those chunks **are source code**.
A remote PostgreSQL deployment also stores the index off-machine. MCP returns
source excerpts to the chosen agent client, whose model/data settings apply.
Local indexing alone does not make a cloud agent session offline.

## Start here

These docs describe the **1.2.1 source tree**. Install matching binaries from
[v1.2.1](https://github.com/kamysh/muninn/releases/tag/v1.2.1) or build from this source tree.

| Task | Guide |
| --- | --- |
| Install and use Muninn as a human | [Getting started](docs/get-started.md) |
| Have an agent perform an installation | [Agent installation procedure](AGENTS.md) |
| Connect Codex or Claude and install useful guidance | [Agent setup](docs/claude-code-setup/INSTALL.md) |
| Assemble a custom database stack (advanced, not recommended) | [Custom database guide](docs/own-database.md) |
| Configure file selection and embeddings | [Configuration](docs/configuration.md) |
| Upgrade an existing installation | [Upgrading](docs/upgrading.md) |
| Build, understand the design or contribute | [Development](docs/development.md) |
| Remove a family or installation | [Uninstalling](docs/uninstall.md) |

## Everyday commands

```sh
muninn add /path/to/repo                 # Human configuration TUI; separate Start confirmation
muninn config /path/to/checkout          # Review/edit shared family policy
muninn preflight /path/to/checkout --json
muninn config /path/to/checkout --json    # Agent inspection
muninn start /path/to/checkout --json     # Explicitly enable and run indexing
muninn status                           # Registered-family overview
muninn usage --days 30
```

Agents should check a complete JSON policy before saving it and guard saves and
start requests with the returned family ID/revision. See the
[shared skill](docs/claude-code-setup/skill/SKILL.md). New repositories snapshot global family settings at creation; review the
visible defaults and select the backend before registering. Saved settings do
not follow later global edits. `status PATH`, `pause`, `resume` and `remove` still use the
registered locator shown by `status`; they are not arbitrary-worktree commands.
In particular, `remove` deletes an entire registered family's code index.

## Related projects

| Project | Purpose |
| --- | --- |
| [Kryzhen](https://github.com/kamysh/kryzhen) | Dependency-based PostgreSQL migrations as a Rust library and CLI |
| [Mimir](https://github.com/kamysh/mimir) | Decisions, evidence and reasoning memory across agent sessions |

Muninn and Mimir can run independently. Their documented setup can share one
compatible PostgreSQL instance with separate roles and databases.

## License

Apache License 2.0 — see [LICENSE](LICENSE). Contributions are subject to the
[Contributor License Agreement](CLA.md).
