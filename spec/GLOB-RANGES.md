# Certified class-range interpretation

`GlobRanges` connects the actual `GlobLexing` result to the explicit
`GlobMatching.characterClass` atom.

## Independent ordered interpretation

`Ranges` defines singleton and interval meaning over the source units. An
unquoted hyphen between two endpoints introduces an interval; a quoted hyphen
remains a literal unit. A singleton step cannot bypass an available range
separator. Interval construction requires ordered endpoints.

The parser uses structural recursion over the unit list. `Parsed` carries the
actual interpretation proof, so an unordered interval cannot be accepted by
silently substituting another class. `recognized` proves every valid
interpretation is recognized. `deterministic` proves its range list is unique.

## Actual class compilation

`compile` first calls the certified lexical scanner, then interprets its actual
units. `Compiled` retains both certificates, including original source,
negation and saved suffix. Its matcher atom uses those exact fields.

`classRecognized` proves the composed parser recognizes every valid lexical and
range derivation with the same negation, ranges and suffix. `classDeterministic`
proves any two certificates for the same source give the same atom and suffix.
The source reconstruction and strict suffix progress laws are inherited from
the actual lexical certificate. Class matching uses the existing total atom
matcher, including its separator restriction.

## Boundary

This is #128 under #26. It does not close complete raw parsing: glob-body
sequencing/alternatives, position-sensitive recursive wildcards, anchoring and
directory-only framing remain. Rule precedence, ignored-parent traversal and
indexing/search/cleanup integration also remain required.

Private lexical/range absence belongs to the surrounding parser and existing
clarification process. It does not introduce a terminal product failure or
declare an intended request complete.

These are general safe laws, not pattern fixtures or a Rust correspondence
claim. Agda and documentation only; live data, installed binaries, system
configuration and deployment are unchanged.
