# Normalized request identity

`Muninn.RequestIdentity` compares the complete typed meaning of public
mutations and finite background jobs. JSON whitespace and object-key order
are absent from these parsed types. CLI, MCP and editor adapters for the same
intent share one input type; equal semantic inputs have equal identities.

Every existing mutation and background-job constructor has an explicit codec.
The closed public-intent classifier also names every read-only intent. Reads,
control events and local editor actions do not acquire permanent receipt
markers; any durable maintenance they arrange has its own catalog job.

## Independent meaning and completeness

Meaning consists of an operation constructor and its original typed payload,
not a script, SQL statement list, JSON serialization or hash. Mutation payloads
include their operation ID. All actual typed values remain significant,
including locator values, repository identity, policy revision, secrets in
bootstrap input, absent versus present options, and list order. Rule lists are
never sorted. This model does not log, persist or publish request payloads.

`Muninn.Canonical` supplies a total comparison over canonical values and a
`Codec` interface with a universally quantified reconstruction law. Every
record codec reconstructs the entire original record from its field view.
Omitting a field, replacing it by a constant or dropping an ordered-list item
cannot satisfy this law for arbitrary inputs. Constructor coverage is also
checked by Agda's totality checker. Unknown constructor tags are rejected.

The general faithfulness theorem states that equal canonical content implies
equal complete typed meanings. Mutation classification retains the original
typed input, and transport independence is stated over the independent
intent/input pair. Canonical content is compared in full; a digest is not an
identity proof.

## Resolution and integration boundary

Normalization starts after parsing and semantic admission. Identity resolution,
expected revisions and selected defaults must be captured for the accepted
request. A retry compares against those saved inputs; it must not re-read newer
defaults or re-resolve a different repository and silently substitute them.
Validation, resolution and user correction remain the admission/dialogue
obligations, rather than fields a codec can invent.

The raw JSON parsers and Rust/CLI/MCP adapters are not proved by this module.
They must implement the typed contract and its formatting-independent parsing
through the adapter and correspondence work (#48, #49 and #52).

[Durable receipt transitions](RECEIPTS.md) and [identity-aware corrective
admission](IDENTITY-ADMISSION.md) now integrate this normalized identity model.
This slice does not change SQL, Rust, wire names, services or installation, and
does not claim that runtime retry isolation has already been implemented.
