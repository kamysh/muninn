# Deterministic hybrid ranking

`HybridRanking` defines the result-producing pipeline over actual selected-view
text and semantic candidates. It does not expose disconnected score helpers as
a substitute for retrieval. Both modalities use the eligibility and numerical
contracts of #39 and the same saved checkout, policy and repository profile.

## Inputs and permitted overrides

The default vendor multiplier is 0.3. The request may override it with a finite
value from 0 through 1. `HybridNumbers.Overrides` binds the admitted value to the
actual supplied request or its default; it cannot silently replace an invalid
override with another value. There is no per-file restriction or corresponding
request field. A file can contribute every matching chunk through pagination.

Zero is a valid ranking score. A zero vendor multiplier moves vendor matches
behind positive-scoring matches; it does not exclude them. Current stored
family rules classify the actual candidate path, including its saved Git
default. The retrieval universe is already policy-filtered, so classification
does not reopen excluded content.

Invalid override input remains part of the existing corrective conversation.
This adds no new failure-state framework, transport command or physical schema.

## Candidate pools and fusion

Text candidates must have actual postings, English-word match evidence and
measured provider ranks. Semantic candidates must have actual current-profile
vectors and the required stored-coordinate and calculated-score evidence.

Exact mode requires complete modality sources. Approximate mode fetches at
most ten times the page size, capped at 1000 candidates per modality. Its text
pool must contain the best available text matches within that budget; semantic
lookup may miss closer vectors. Those limits can also miss a stronger combined
match outside the two pools, which the response must not present as exact.
Coverage still describes the complete eligible inventory, independently of the
approximate pools.

Each modality is ordered by its own score, with the #39 chunk-identity/path
tie order. An eligible chunk/path occurring in both lists is merged once.
Its zero-based text and semantic positions contribute respectively
`1 / (60 + position)`; an absent modality contributes zero. Contributions are
added in text-then-semantic order, then multiplied by the vendor weight when
the current stored policy classifies the path as vendor content.

The computed binary64 score must match that formula exactly. Its finite,
nonnegative value and exact rational image drive the final ordering. The score
is a ranking signal, not a probability, confidence estimate or factual-accuracy
guarantee. No real-number algebra is assumed for rounded operations.

## Selection, preservation and bounds

`RetrievalSelection.By` generalizes the existing ordering/page implementation
to nonnegative score fractions while preserving the existing positive-score
interface. General soundness and completeness laws prove that ordering neither
invents nor drops candidates. In particular, weighting cannot become an
implicit vendor filter. The pipeline returns the requested prefix directly
from the complete ordered candidate list, without a diversity filter that
discards matches from a file. General laws prove membership and response-page
size bounds. Every final candidate still has its actual owned chunk and
selected-file-version evidence.

The response is tied to this complete executable pipeline. Two responses for
the same fixed source lists, scores, policy and request have the same result
order. Approximate search may obtain a different pool on a later independent
request; continuation must not silently substitute it into an existing query.

This slice defines selection of one page. #41 owns continuation and retains
unconsumed candidates from the ordered query. A response-page boundary does not
impose a quota on the number of matching chunks from a file or the total query.

## Proof and implementation boundary

The Agda laws prove reference-pipeline membership, deterministic output and
response-page bounds over arbitrary admitted inputs. They do not assert a
separate general transitivity theorem for all primitive floating-point
comparisons. Comparison uses natural-number products of the computed scores'
exact rational images; the source arithmetic and codec remain the existing
#52 correspondence obligation.

The SQL/ANN adapter must provide the stated complete or bounded-best modality
contracts and the actual score certificates. Rust currently has separate
worktree and legacy fusion paths and does not implement all of these settings.
The existing #51–#54 dispatcher, correspondence and coverage work must connect
them to this one pipeline. No Rust, provider, database, installation or
deployment change is included here.
