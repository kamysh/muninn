# Complete raw glob-body parsing

`GlobBody` assembles complete raw pattern bodies from actual `GlobTokens`
certificates. It retains independent source evidence through sequences, nested
brace alternatives, quoted literals, classes and position-sensitive recursive
wildcards. Commas outside groups are literal characters.

## State and source grammar

A frame holds the current branch and completed alternatives. A finite stack
holds enclosing groups. Opening, separation and closing have explicit source
assembly rules; only an empty group stack can finish at end of input. Position
and group context are supplied from the actual parser state to token scanning.
Empty rendered alternatives retain the existing syntax interpretation: empty
branches are omitted beside nonempty branches, and a wholly empty group is the
empty expression.

Every computed step carries its assembly proof. Every successful parse carries
a complete `Source` derivation ending in the actual returned matcher tree.
Unbalanced groups, unfinished quoting or invalid ranges do not produce a fake
completed pattern. Private parser absence is for the existing corrective dialogue
to explain and resolve at protocol integration.

## General laws

`recognizedWith` proves recognition for every source derivation and every
accessibility witness. `recognized` specializes that law to a whole body.
`deterministic` proves unique assembled meaning even for arbitrary starting
parser states. `bounded` proves the number of token transitions is no greater
than the source-character count.

The parser recurses using the certified strict suffix-length decrease and
natural-number well-foundedness. There is no arbitrary fuel, timeout or unsafe
termination annotation. `matchSound` and `matchComplete` connect the actual
raw-body parser and matcher to the independent source-and-language relation.

## Boundary

This closes #132 under #26. Leading negation, path anchoring, directory-only
framing, Git ignore-file context, ordered policy precedence and ignored-parent
traversal remain separate from body syntax. Actual selection still needs to
connect those rules to indexing, search and cleanup before #26 can close.

The specification uses existing logical character/path types. Filesystem and
Rust adapters remain correspondence obligations; this is not a runtime repair,
installation or deployment.
