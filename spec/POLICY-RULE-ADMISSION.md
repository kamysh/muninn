# Strict policy-entry admission

`PolicyRuleAdmission` retains the original entry as its type index. Admission
normalizes surrounding whitespace, compiles the actual normalized characters,
requires a nonempty body and NUL-free input, and checks strict source evidence.
A leading hash remains literal in JSON policy entries; this is not Git ignore-file
comment processing.

`StrictGlob` defines that evidence independently over token and complete-body
source derivations. Quoted opening brackets remain literal. The unclosed raw
bracket fallback cannot satisfy strict policy syntax. Total decisions reflect
that predicate; transport laws prove strictness cannot depend on certificate
choice. Shared permissive scanning remains available to other syntax contexts.

`admitComplete` proves every valid entry can be admitted. `semanticUnique`
proves accepted meanings are unique. Complete-list admission preserves original
order and returns no accepted partial list; `admitAllComplete` proves valid lists
can be admitted in full.

## Actual family selection

`AdmittedSelection.FamilyEntries` requires strict entries for both actual effective
family axes, including frozen defaults. `compiledFamily` feeds their actual
normalized compilations into `OrderedSelection`, whose family input indices now
include that normalization. `familyComplete` proves complete family admission;
`unique` proves original-input certificates cannot change the final decision.

This connects admission to the existing resolver rather than leaving a separate,
permissive path as the family selection contract. Logical character/whitespace
primitives and filesystem/Rust correspondence remain explicit adapter boundaries.

## Boundary

This closes existing issue #137. Git ignore-file sources, scoped line evaluation,
tracked-file context, ignored-parent traversal and final stored-policy/indexing/
search/cleanup integration remain under existing #26. Invalid request explanation
uses the agreed corrective dialogue when the protocol is connected; this adds no
terminal product-failure result or live mutation.

Agda and documentation only. No installation, deployment, system configuration,
database change or runtime verification is implied.
