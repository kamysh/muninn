# Shared transaction semantics

`Muninn.Database` gives every modeled operation the same finite-store effects.
A transaction can read, scan, write and delete; a committed transaction
publishes its resulting state and an aborted transaction preserves the entire
original state. The safe proofs cover deletion, unrelated-key preservation,
visible writes and rollback.

Bounded predicate deletion counts removed rows rather than rows examined. The
proofs state that retained rows remain available and that deleting an eligible
row strictly reduces the store size. The model specifies logical effects; it
does not prescribe SQL statements or claim Rust/PostgreSQL correspondence.
