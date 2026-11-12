# Recovery contract

`Muninn.GeneralRecovery.Protocol` defines scripts over a shared effect interpretation.
Its generic prefix includes the boundary before execution and every boundary
after an effect, including when a committed effect does not deliver its reply.
A retry runs the original script against the state left at that boundary.

A `Recoverable` operation supplies a script and proofs that interrupted work
preserves its independently fixed frame, and that any completed retry reaches
the independently fixed world-level goal. It also supplies a constructive
completion proof under the independently fixed readiness condition. Readiness
states the environmental assumptions needed for progress; it is not a timeout
or a promise that unavailable services recover immediately.

`DatabaseProtocol` fixes transaction effects to `Muninn.Database.execute`,
including its commit and rollback semantics. Other effects, such as observations,
need their own shared interpretation. Issue #51 must make the dispatcher use the
fixed interpretations, goals and operation proofs. Issue #52 must check their
correspondence to the running application. This module alone does not establish
that Rust operations obey the contract.

The existing `Muninn.Recovery` module remains in use by current proofs. The dispatcher has not yet been connected to the general contract.
