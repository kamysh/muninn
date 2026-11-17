# Proof-carrying dispatcher

The dispatcher is the only executable entry into the closed catalog. A request
can execute only by carrying the proof instance its operation requires; there
is no constructor that accepts a raw script, and local editing has no
executable state at all.

## Required instance

`Operation` fixes the required instance independently of the caller: the
operation's input and result types, the outcome goal and preservation frame
(interface parameters, never operation-supplied record fields), and a complete
`Recoverable` contract — a script with preservation at every committed prefix,
interruption/retry convergence to the goal, and constructive termination.

`OperationOf` maps every request constructor to the instance family its intent
requires. User requests require an instance over the canonical intent's input
family; background jobs over their job input; control events over their event
input.

## Total coverage and exclusions

`OperationRequest` covers every executable request constructor: user,
background and control. Local editing is explicitly not an operation — its
effectful Save, Check, Start and Refresh actions use their shared public
intents — and `localUiCannotExecute` proves it has no executable state.

`executesRegistered` proves that every executable state carries both its
registration and its full proof instance; nothing else is constructible.
`Contract` exposes the accepted operation's script, preservation, convergence,
termination and registration-retention laws.

## Coverage gates

Catalog and coverage consistency are enforced mechanically by the
`check_mcp_catalog.py`, `check_cli_catalog.py` and `check_daemon_catalog.py`
gates plus their negative tests (#48, #49, #50). The dispatcher requires the
instances those gates bind; matching names alone is not refinement. Rust
record/effect correspondence remains #52, crash injection #53, and the final
coverage audit #54.
