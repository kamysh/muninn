# Reading the Muninn specification

Start with the operation you want to understand. Each topic explains the
behavior before the Agda declarations and proofs that state its guarantees.
The links in each topic lead to the requirements, Rust code, and available
implementation checks.

| Topic | What it covers | Runtime evidence |
| --- | --- | --- |
| [Worktree publication and sharing](spec/Muninn/CheckoutPublication.lagda.md) | Shared file versions, checkout-local publication, search during indexing, current exclusions, and reuse after interruption | [Database persistence scenarios](crates/core/tests/family_persistence/worktrees.rs) exercise shared versions, interruption, concurrent requests, and checkout isolation |
| [First worktree search](spec/Muninn/FirstSearch.lagda.md) | Checkout resolution, first-start authorization, indexing on demand, coverage, and result eligibility | [The on-demand MCP test](crates/mcp/src/worktree_tests.rs) exercises the first structural search for a linked checkout. Reconnection of the same active search remains a runtime gap |

The [formal index](spec/README.md) maps the wider Agda model. The
[operation catalog](spec/OPERATION-CATALOG.md) lists the broader operation
surface, including areas that still need a reader topic. A checked Agda law
establishes the stated property under its premises. The linked runtime tests
provide separate evidence about Rust and PostgreSQL.

When changing behavior, update the relevant literate module and its
applicable laws first. Then update the implementation and its verification.
Run the reader check to type-check the aggregate, render its literate
modules, and validate local links in the source documents.

```sh
nix develop --command python3 scripts/check_reader_spec.py
```

To keep the rendered pages for inspection, pass `--output` with a new
directory path.
