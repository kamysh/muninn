# Ordered selection from compiled rules

`OrderedSelection.Rules` retains a certified compiled rule for each source entry,
in its original order. The complete-list compiler returns a list only when all
entries compile. `compileComplete` proves every list of valid source certificates
can be compiled; invalid entries cannot silently become a shorter accepted list.

## Fixed precedence

`resolve` derives each match with the actual `RuleScope` matcher. Its independent
`Resolution` relation distinguishes unmatched preservation and matching polarity.
`resolveCorrect`, `recognized` and `deterministic` establish the exact result.

`resolveAppend` proves earlier/default rules run before later/family rules.
`lastMatchWins` proves a matching final rule determines the result regardless of
the initial Git decision or earlier rules. `explicitInclusionWins` and
`explicitExclusionWins` state both polarities. `unmatchedPreserves` proves an
unmatched rule list retains its initial decision.

`FamilyRules` is indexed by the actual effective inputs from `Config.familyConfig`,
which concatenates frozen family defaults and family-specific rules. It cannot
supply a different source list for those fields.

## Deterministic observable selection

`RuleScope.pathTransfer` transports matching across equal compiled meanings.
`matchesStable` proves that equal meanings compute the same match Boolean.
`resolveEquivalent` and `familyDecisionUnique` use those laws to prove that
different source certificates for the same inputs cannot change selection.

Exclusion starts from the Git decision; vendor membership starts from false.
`vendorCannotUnignore` proves changing the vendor rules cannot change inclusion.
This models the agreed explicit Muninn override without treating vendor
classification as permission to index ignored content.

## Remaining integration

This closes #135 under #26. Its Git decision is the input boundary for the future
Git ignore-file evaluator, not a proof of that evaluator. Entry-specific trimming,
comments, strict policy syntax validation and filesystem context still require
admission. Ignored-ancestor traversal and the shared indexing/search/cleanup
predicate must still be connected before #26 closes.

These modules replace per-rule match flags in this resolver with actual compiled
matching. Older `Config.resolveAxis` callers and `ExclusionOutcomes.Model` still
need migration; checking this aggregate alone does not complete that integration.
Agda and documentation only, with no runtime, database or system change.
