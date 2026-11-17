# Record and effect correspondence

Agda proofs govern the product only if the modeled persistent records and
effects correspond to the implementation's real tables and statements. This
contract records that correspondence mechanically and keeps the gaps explicit.

## Manifest

`RECORD-CORRESPONDENCE.json` maps every formal `OwnedState.Body` constructor to
its physical realization: a concrete table, a column of a modeled table, a
derived representation, or an explicitly unmapped status. Each physical table
is mapped back to its formal category, and every persistent write statement in
the workspace crates is declared as a site (file, line, table, optional
template placeholder).

`scripts/check_record_correspondence.py` enforces both directions: a formal
constructor without a manifest entry fails; an undeclared write statement
fails; a manifested site whose line no longer matches its declared table or
template fails; a write-site table missing from the physical map fails. A
mapped category must name a realization. Unfamiliar source forms fail rather
than pass silently.

## Realized categories

Every formal record category has a physical realization: the seven previously
unmapped categories now have family-owned tables (`legacy_files`, `staging`,
`accepted_work`, `cleanup_work`, `active_readers`, `continuations`,
`receipts`) plus the installation-owned `receipt_markers` table for ID-only
markers, all written through `crates/core/src/owned_control.rs` and declared
as write sites in the manifest. `logFile` is local log files, not database
rows; system categories (migrations, bootstrap, model cache, coordination,
schema resources) map to their infrastructure roles.

## Boundary

Matching table names and statement sites does not prove that a statement
implements the modeled transition. Statement semantics, transaction
boundaries and receipt write paths remain the dispatcher (#51) and crash
injection (#53) obligations; the final audit (#54) consumes this manifest.
