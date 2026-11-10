# Database access and accepted-request resumption

`Muninn.DatabaseResumption` keeps a known conversation responsive while it
waits for database access. It starts with the existing local bootstrap
configuration and context. The enclosing connection/preparation adapter reports
when access to the shared receipt store is usable.

## Waiting requires no database transaction

The waiting branch produces the existing MCP dialogue reply directly. Its
explanation says the database is unreachable and saved work cannot currently
be checked. It asks the caller to continue with the same request ID once access
returns. It neither claims current progress nor invents offline access to
database-backed configuration.

`waitingIsPure` and `waitingResponds` establish the exact pure response.
`keepsContext`, `keepsRequestId` and `keepsBootstrap` preserve the full context
and configured credentials across arbitrary connection observations.
`bootstrapNotInReply` proves that these responses do not render bootstrap
values. No LLM call or terminal failure result is introduced.

## Resume from the current receipt

The usable branch performs one read-only shared transaction. `currentReceiptFirst`
checks the actual current receipt before business execution:

- Active matching work returns its current saved progress and original ID.
- Completed matching work returns its saved result.
- A reclaimed marker, changed request or missing receipt uses the existing
  identity-aware corrective dialogue without repeating a write.

The universal resume/replay laws cover each of those transitions.
`resumesAfterObservations` connects arbitrary waiting/reconnection observations
to actual saved-work resumption. There is no cached database snapshot in the
session, so other workers may advance while this caller waits; the restored
read uses the supplied current store.

`preservesWorld` states that this waiting/receipt-inspection step changes no
persistent records. It does not prevent independent background work or other
clients from changing the database between calls. A request to continue actual
business effects still goes through the existing governed operation protocol.

## Startup and migration readiness

`DatabaseStartup` retains the configured credential and TLS choices while
waiting for a connection and requires public schema readiness before continuing.
`prefer` permits its configured fallback when the server declines TLS; it is
not treated as `require`. Family readiness also requires AGE graph evidence.

`MigrationBlock` models a catalog update and its migration ledger entry in one
transaction. `MigrationSequence` models an ordered finite sequence of those
transactions, preserving unrelated records and resuming from committed ledger
entries. Its convergence goal is stated over the final world and independent
schema requirements; the proof assumes the supplied plan and requirements are
consistent. Interrupted transactions and completed retries use the shared
execution semantics.

## Boundary

The catalog records and ledger codec are logical representations. Binding the
independently specified requirements, real SQL migrations, ledger identities,
connection observations and actual schema changes to this model remains an
implementation correspondence obligation (#51 and #52). These proofs do not
verify the Rust adapter, repair the running server, or change live data.
