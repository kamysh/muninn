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

## Boundary

This is #100 under #46. The safe module is imported by the aggregate. Initial
bootstrap, credential/TLS choices, interrupted migration/preparation and
compatibility/upgrade rules remain under the parent. Runtime mapping of actual
connection/preparation events to the access observation remains a correspondence
obligation. A TCP connection alone is not evidence that receipt access is ready.

The existing admission schema, independent goals, receipt semantics and
credential/TLS policy are unchanged. These specification laws do not repair or
deploy the running MCP server. No Rust, live data, installation or system
configuration is changed.
