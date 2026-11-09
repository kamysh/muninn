# Mandatory analysis and embedding reuse

Ordinary reconciliation reuses every compatible completed value. Compatibility
is an equality of exact semantic inputs, rather than an optional optimization
or a hash match. `ArtifactIdentity` decides equality from every declared field.

Analysis identity includes family, full source bytes, language, parser/grammar/
extractor versions, chunker and normalization versions, maximum chunk bytes and
normalized remaining content-affecting configuration. The lookup hash is separate
metadata and cannot force recomputation or establish byte equality. Existing
supported languages and valid-input chunking behavior are retained and versioned.
Whole-file parsing uses the full file context; unchanged normalized chunk inputs
can reuse embeddings even when another part of a file changes.

A chunk has a half-open source byte span `[start,end)`. Its line range is display
metadata. Equal text at two positions has two identities; splitting a long line
does not collapse its pieces into one line-number key. `CanonicalChunks` keeps
the first candidate for each span. General laws establish unique spans, coverage
of every original span, preservation of retained payloads, and preservation of
all independently specified candidate validity/bounds laws. Normalized text need
not equal a raw byte slice: newline and other rendering choices belong to the
explicit normalization/chunker identity.

Embedding identity includes family, backend/model, normalized provider settings,
profile revision, task, normalization version, dimension and the exact submitted
input bytes. Source versions and spans still identify the referring chunks, but
do not force duplicate vectors for identical compatible provider input. Replies
are indexed by that submitted input and require the expected vector dimension.
Provider-effect correspondence is owned by #37/#52, not assumed from dimensions.

`CompletedWork` makes every action either reuse with a real saved lookup or
calculation with proof that no value exists. Therefore a completed hit cannot
choose calculation. The certified store requires both unique keys and valid
values; checkpointing preserves both. The first completed value is immutable,
repeated checkpoints are idempotent, unrelated writes preserve hits, and the
next action after a saved checkpoint must reuse it. These laws cover arbitrary
keys and values, including every analysis/embedding profile instantiated here.
The saved store is the checkpoint across yielding and reconnection.

`ArtifactReuse` instantiates that mechanism with the actual file/embedding
identity projections. Analysis results equal the independently specified
versioned model output after canonicalization, have unique spans, nonempty text, valid display ranges and stay within
source bounds. The model is fixed for the module; a handler cannot choose a
weaker cache predicate. #42 supplies parser/extractor semantics; these reuse laws
hold for every independent model satisfying the declared candidate-validity contract.

Each certified store belongs to a family. An explicit catalog `recreateIndex`
request permits a fresh store only for its expected family. The isolation law
preserves every other family. Ordinary CLI reindexing cannot construct that
permission and continues using mandatory reuse decisions. Physical remove/create
and closed-dispatch assembly remain governed by their existing issues.

Agda and documentation only. The aggregate includes all four new modules. Rust
correspondence and runtime execution have not been established by these proofs.
