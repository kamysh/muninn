# Total glob syntax-tree matching

`GlobMatching` defines an independent matching relation and its total decision
procedure. A match is evidence built from literals, wildcards, character classes,
alternatives and concatenation; an operation cannot supply a match Boolean.

## Languages

`Glob` is a finite sequence of `Atom` values. The atoms represent:

- One literal character, including an explicitly escaped wildcard character.
- One non-separator character or any sequence of non-separator characters.
- A recursive path sequence that may cross directory separators.
- A recursive directory prefix: empty, or a prefix ending at a separator.
- Positive/negative character classes with the standard library's safe range
  semantics and an explicit prohibition on consuming separators.
- Finite alternatives, including nested glob sequences.

The outer repository-path contract will supply normalized relative paths.
Position-sensitive interpretation of raw `**`, anchoring, directory-only rules,
escaping and raw alternatives belongs to parsing, not a caller-provided match
hint. Literal separators remain explicit in the syntax tree.

## Complete finite concatenation

`splits` lists every prefix/suffix pair of a finite path. `splitSound` proves
every listed pair reconstructs the original path. `splitComplete` proves every
possible concatenation is listed. `splitCount` proves exactly one more candidate
than the path's length.

The matcher recursively checks the syntax tree and those finite split lists.
Its positive branch constructs `Matches`; its negative branch refutes every
possible matching derivation through complete split coverage. Alternatives are
checked structurally. Agda checks totality without postulates, unsafe termination
options or an arbitrary recursion cutoff.

The `matches` Boolean interface is computed from that decision procedure.
`matchSound` and `matchComplete` tie it to the independent relation for every
syntax tree and finite path. Character-class decisions reuse the standard
library's proved regular-expression membership decision, not an external engine.

## Boundary

This is #124 under #26. It does not close the parent: raw-string parsing,
Git/default/family precedence, automatic traversal for explicitly included
descendants and integration with indexing/search/cleanup remain required.
The agreed semantics and split are recorded on #26.

The logical alphabet uses the existing Agda character/string representation.
Filesystem/wire encoding and correspondence with Rust's matcher remain adapter
obligations; no Rust equivalence or runtime performance result is claimed here.
This specification decision procedure need not prescribe the runtime algorithm.

Agda and documentation only. Live data, installed binaries, system configuration
and deployment are unchanged.
