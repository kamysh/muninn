# Reader admission during cleanup

`Muninn.CleanupAdmission.Family.admit` checks a proposed reader in the same
shared transaction that records its hold. It scans the complete current world;
the caller cannot supply a smaller set of cleanup claims or a weaker footprint.

The checks require a fresh unreserved identity, references that already resolve,
canonical filtered root versions in the proposed world, and no path from the
new reader to a currently pending cleanup record. Otherwise the transaction
writes nothing and returns the caller's existing current-view replanning
continuation. It introduces no new terminal or diagnostic result type.

## Exact new-holder footprint

Outstanding `cleanupWork` rows supply the family's saved captured IDs. A tracked
family-index record is pending when it is unneeded or its current projection is
not canonical. The guard checks every such saved workset under the effective
family rule.

The footprint starts with this proposed reader's own held references and follows
the existing exact temporary-dependency closure in the proposed stored world.
It is computed separately from older holders. An old protection flag therefore
cannot justify adding another reader that would extend the same wait.

`cannotExtend` is stated using the existing `Protected` proof and its originating
holder. An actual newly admitted reader cannot be the origin of protection for
any pending record, through either a direct reference or a transitive path.
This includes needed snapshots that still contain obsolete members.

`admitted` also proves that the stored reader's roots are canonical in the actual
resulting world. A proposal using an old mixed snapshot must replan its current
view. `replansWhenHeld` proves the exact continuation and unchanged world for a
proposal whose footprint touches pending work; `accepts` proves the concrete
successful write when the checks hold.

## Existing work and identities

`admissionSafety`, `admissionAdmissible` and `existingUse` preserve the complete
owned store and existing holders. `savedWorkset` preserves the saved task record
and its captured IDs exactly.

`CleanupAdmissionStorage.reserved` includes current row IDs and weak IDs retained
by cleanup worksets and continuations. `trackedAbsent` proves that admission
cannot reuse a tracked identity whose indexed row has already been deleted.
The weak-reference selector covers every owned body constructor explicitly.

`receiptFrame` proves the existing shared receipt-isolation contract in both
directions. The helper belongs inside the receipt-controlled request and can be
sealed with its checkpoint; it is not a separately retried write or a new
operation-identity protocol.

## Boundary

Both modules use `--safe` and are included in `Muninn.agda`. The guard reuses the
shared database semantics, keeper/dependency model and finite exact closure.
No proof assumes that a blocked proposal has become safe.

The current-view producer must prepare canonical, safe references before
admission can succeed. Producing fresh views, arranging durable cleanup work,
releasing completed holders and wiring the helper into all requesting paths
remain under #84. Outstanding work rows must follow the agreed completion and
supersession lifecycle; admission does not invent a separate task-status store.
This slice, #90, changes Agda and documentation only. It does not establish Rust
correspondence or change live data, binaries, services or deployment.
