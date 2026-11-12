# Certified glob class scanning

`GlobLexing` gives an independent source grammar and a total scanner for escaped
character units and bracketed class bodies. It retains whether each character
was quoted, so later range interpretation can distinguish literal and structural
hyphens without guessing from the decoded character.

## Grammar evidence and source progress

`Units` permits an unescaped `]` as the first class unit and uses later unescaped
`]` characters to close the body. An escape consumes its backslash and the next
character. `Class` adds the opening bracket and distinguishes ordinary classes
from leading `!`/`^` negation. Positive classes cannot also take the negation path.

Successful `Scanned` and `Parsed` values carry their actual source-grammar proof
and remaining suffix. The scanner recurses on the source list; there is no
arbitrary recursion fuel or unchecked token constructor at its result boundary.

The general laws establish:

- `recognized` and `classRecognized`: every valid grammar derivation is recognized,
  with the same units, negation and remaining suffix.
- `deterministic` and `classDeterministic`: two derivations for one input give
  the same token and suffix meaning.
- `consumption` and `classConsumption`: the consumed characters and saved suffix
  reconstruct the original source.
- `suffixSmaller` and `classSuffixSmaller`: the suffix is strictly shorter than
  the source, giving the next parser stage a constructive progress bound.

These quantify over arbitrary source lists and derivations. No chosen patterns,
sample worlds, postulates or unsafe termination options are used.

## Boundary

This is #126 under #26, following #124 / #125. The module is not the complete
glob parser: range interpretation, raw glob-body syntax, anchoring/directory-only
framing, rule precedence and indexing/search/cleanup integration remain required.
Private lexical absence must be interpreted by the surrounding parser and
existing clarification dialogue; it is not a new terminal product failure.

The agreed syntax, ordered rules and automatic traversal for explicit
inclusions inside ignored parents remain unchanged. Logical character encoding
still has the adapter boundary described in [glob matching](GLOB-MATCHING.md).

Agda and documentation only. Rust, live data, installed binaries, system
configuration and deployment are unchanged.
