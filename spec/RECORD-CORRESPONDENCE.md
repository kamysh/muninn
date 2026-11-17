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

## Honest gaps

Seven record categories have no current Rust realization and stay explicit in
the manifest: `acceptedWork`, `activeReader`, `cleanupWork`, `continuation`,
`legacy`, `receipt`, `staging`. Repairing them is separate work; this contract
records them rather than weakening the formal goal to match the
implementation. `logFile` is local log files, not database rows; system
categories (migrations, bootstrap, model cache, coordination, schema
resources) map to their infrastructure roles.

## Boundary

Matching table names and statement sites does not prove that a statement
implements the modeled transition. Statement semantics, transaction
boundaries and receipt write paths remain the dispatcher (#51) and crash
injection (#53) obligations; the final audit (#54) consumes this manifest.
