# Generic corrective dialogue

`Muninn.Dialogue` specifies transient conversation around the closed operation
catalog. The calling agent supplies corrections and chooses alternatives;
Muninn renders structured guidance and checks the resulting request. It does not
invoke an LLM or generate another agent response internally.

## Context and corrections

Available context retains its request identity, original request statement,
known facts and references to completed/accepted work. A correction batch updates
the supplied fields; universal laws preserve the identity, original statement,
work references and every unmentioned fact. Only schema-recognized fields can
enter a correction transition.

Reconnection preserves a known phase, including an already certified answer.
Recovery can supply identity-checked context with an available answer. The answer
is reused before assessment; pending permissions are rechecked when relevant
environment observations change. A completed answer remains usable on the same
world when only environment observations change.

If usable context is unavailable, the generic prompt says:

> I no longer have the earlier context.
>
> Send the original request again, including the details you already supplied.

This is not a special unidentified-repository workflow. A fresh request carrying
its own context starts normally. An incomplete known request asks for specific
details instead of asking the agent to repeat everything. Context loss is an
ordinary dialogue step; it does not cancel accepted work or remove saved data.
No new server-level persistence or change to continuation ownership is introduced.

## Guidance and choice

Questions carry an explanation and concrete next action. A choice menu is
nonempty and every option has a label and explanation of its consequences.
Rendered options expose those descriptions, not the internal fact patches.
Applying an offered option requires an explicit calling-agent selection. Bad
or unsupported replies can lead to revised guidance while retaining context.

Explanations and actions are structurally nonempty. Their plain-language quality
and the accuracy of operation-specific labels still require review of the fixed
schema/renderer templates; the typechecker does not prove natural-language clarity.

## Execution and bounded local work

Every dialogue transition preserves the complete owned persistent world. Request
execution is a separate registered-operation handoff, available only with a
matching-request and prerequisite certificate. Reporting completion requires the
independently specified outcome certificate. A checker cannot ask for more input
when an admissible request already exists, and it cannot ignore an available
cached answer handed to the dialogue kernel.

The internal relation has only one assessment step: examining becomes responded.
A general theorem excludes two consecutive internal steps. Another agent reply,
recovered context or a changed external observation is required to continue.
Finite correction batches terminate structurally. There is no automatic fallback,
internal reasoning loop, arbitrary retry cutoff or terminal-failure constructor.

The world-preservation law concerns these local dialogue actions. Database
transactions, background indexing, reader release and process lifecycle effects
belong to their registered operations and can interleave separately. It is not a
claim that a full process restart freezes every external or database resource.

## Remaining integration obligations

The shared catalog/schema must instantiate recognized fields, request matching,
prerequisites, result types and outcome predicates independently of handlers.
[Identity-aware admission](IDENTITY-ADMISSION.md) connects identity validation,
receipt lookup and replay to this protocol. Concrete MCP/CLI/TUI parsing,
admission and rendering remain #48/#49; proof-requiring application
dispatch and Rust correspondence remain #51/#52. Those layers must preserve the
identity/provenance of recovered context and map real client/host events to the
appropriate transition. Source references do not establish that integration.

This PR is the generic protocol and its general laws. It neither repairs the
running MCP server nor introduces a persistence promise for unfinished context.
