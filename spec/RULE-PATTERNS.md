# Source-certified rule framing and scope

`RulePatterns` strips leading negation, a root marker and a trailing directory
marker through independent `Peel` and `HeaderSource` derivations. Quoted leading
punctuation remains part of the body. Empty bodies cannot produce a compiled
rule. Root-relative scope follows either an explicit root marker or an internal
slash; other bodies receive directory-prefix scope.

A compiled rule keeps its actual header and the actual certified `GlobBody`
parse. General laws prove complete framing recognition, composed compilation
recognition and unique negation/scope/directory/glob meaning for arbitrary source.
This framing layer accepts rule characters after entry-specific whitespace and
comment admission; it does not yet interpret entire Git ignore files.

## Actual path matching

`RuleScope` defines independent scoped and directory-aware matching relations.
Its executable decisions use the actual compiled matcher tree. A directory-only
rule requires a directory target. An ancestor match covers paths below that
directory, so individual-file processing can use the same semantics as walking.

Complete finite path splits enumerate every possible parent boundary. The
`pathMatches?` decision proves either an actual match or absence from the entire
relation. `matchSound` and `matchComplete` connect its Boolean result to that
relation. Scope soundness/completeness connects root/basename interpretation to
the actual matcher tree, including directory-prefix wildcards.

Repository path normalization, tracked-file status and filesystem identity are
adapter obligations; no arbitrary precomputed per-rule match flag is accepted
by these functions.

## Boundary

This closes #133 under #26. Ordered Git/Muninn precedence, ignored-parent
traversal and integration with indexing, search and cleanup remain required.
Entry-specific whitespace/comment handling, strict policy validation and Git
ignore-file scope must be supplied at admission. In particular, the current
family-policy compiler rejects unclosed classes while the shared body scanner
can represent literal opening brackets; final admission must preserve the
agreed policy syntax rather than silently choose the scanner fallback.

Private parser absence is for the existing corrective dialogue to resolve. This
adds no terminal product-failure infrastructure. Agda and documentation only;
Rust, installed binaries, databases and system configuration are unchanged.
