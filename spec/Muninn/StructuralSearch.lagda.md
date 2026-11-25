# Which structural relationships a search can return

A structural search selects a published checkout and names a symbol and a
relationship direction. Each candidate has a source and target symbol,
their file paths and positions, and the relation connecting them. Calls
and inheritance can be followed in either direction through their
corresponding operations. These candidates come from name-based analysis.

The model requires the relationship and both symbols to belong to the
selected snapshot, with both endpoint files visible under the current
policy. The decoder says how the stored symbol and relationship payloads
become the typed records the request compares. The caller supplies the full
eligible candidate universe. The result keeps all its candidates in source
order, using the related path and start position followed by the identity
of the relationship to break ties.

[Structural search contract](../STRUCTURAL-SEARCH.md) · [Checkout graph reader](../../crates/core/src/worktrees/mod.rs) · [On-demand MCP regression](../../crates/mcp/src/worktree_tests.rs)

```agda
{-# OPTIONS --safe #-}
-- Evidence-bearing name-based structural search over an actual checkout view.
module Muninn.StructuralSearch where
import Muninn.OwnedState as O
import Muninn.StoredPolicy as Policy
import Muninn.PublishedViews as Published
import Muninn.ContentViews as Content
import Muninn.Graph as Graph
import Muninn.ExclusionOutcomes as E
import Muninn.Types as T
import Muninn.RetrievalSelection as Selection
import Muninn.Dialogue as Dialogue
open import Data.Nat using (ℕ; _≟_; _≤?_; _≤_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.String using (String; toList)
import Data.String as String
open import Data.List using (List; []; _∷_; length)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Membership.DecPropositional
module Member = Data.List.Membership.DecPropositional _≟_
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
open import Relation.Nullary using (does; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
module DB = O.DB

familyInjective : ∀ {first second} → O.family first ≡ O.family second → first ≡ second
familyInjective refl = refl

-- The catalog keeps structural content opaque; the search boundary binds the
-- requested symbol and relation direction for the selected checkout.
data StructuralRelation : Set where
  callers callees imports defines inheritors inherits : StructuralRelation

kind : StructuralRelation → Graph.Relation
kind callers = Graph.Calls
kind callees = Graph.Calls
kind imports = Graph.Imports
kind defines = Graph.Defines
kind inheritors = Graph.InheritsFrom
kind inherits = Graph.InheritsFrom

incoming : StructuralRelation → Bool
incoming callers = true
incoming inheritors = true
incoming _ = false

-- Payload interpretation is fixed by the source adapter for the stored
-- parser/representation version; the dispatcher cannot choose a query outcome.
record SymbolData : Set where
  field name : String
        symbolKind : Graph.SymbolKind
        range : T.LineRange

record Decoder : Set where
  field symbol : String → Maybe SymbolData
        relation : String → Maybe Graph.Relation

-- The selected published structural snapshot fixes the view both endpoints
-- and the edge must belong to.
```

## Use the selected snapshot for the edge and both endpoints

A candidate must cite an actual relationship in the selected checkout's
structural snapshot. Both endpoints carry a path and source position backed
by the selected visible file versions. A caller lookup and a callee lookup
interpret the direction of that same edge differently. A name match in a
sibling checkout cannot supply a missing endpoint.

```agda
record SelectedSnapshot (owner : O.Owner) (checkout : ℕ) (world : O.World) : Set where
  constructor selectedSnapshot
  field pointer root : ℕ
        nodes edges : List ℕ
        payload : String
        pointerAt : DB.lookup pointer world ≡ just (O.recordOf owner (O.publishedView checkout root))
        snapshotAt : DB.lookup root world ≡ just (O.recordOf owner (O.structuralSnapshot checkout nodes edges payload))

module Family (family checkout pointer : ℕ) (world : O.World)
  (policy : Policy.Family.Saved family pointer world) (viewsValid : Published.Valid world)
  (filesValid : Content.Family.WellFormed (Policy.Family.rule family pointer policy) world)
  (view : SelectedSnapshot (O.family family) checkout world) (querySymbol : String) (relation : StructuralRelation)
  (decoder : Decoder) where
  owner = O.family family
  selection = Policy.Family.rule family pointer policy
  module Files = Content.Family selection

  -- A stored symbol whose source path matches the selected visible file map.
  record SymbolHit : Set where
    constructor symbolHit
    field path : T.FilePath
          key version : ℕ
          text : String
          gitDefault : Bool
          symbolAt : DB.lookup key world ≡ just (O.recordOf owner (O.symbol version (T.FilePath.value path) text))
          fileAt : Files.visible world checkout path ≡ just (Content.entry version gitDefault)
          inSnapshot : key ∈ SelectedSnapshot.nodes view

  symbolRow : ∀ path key → (value : Maybe O.Record) → DB.lookup key world ≡ value → Maybe SymbolHit
  symbolRow path key (just (O.recordOf actualOwner (O.symbol version source text))) symbolAt
    with E.ownerEqual actualOwner owner
  ... | no other = nothing
  ... | yes refl with T.FilePath.value path String.≟ source
  ...   | no other = nothing
  ...   | yes refl with key Member.∈? SelectedSnapshot.nodes view
  ...     | no other = nothing
  ...     | yes included with Files.visible world checkout path in fileAt
  ...       | nothing = nothing
  ...       | just cell with Content.Entry.version cell ≟ version
  ...         | no other = nothing
  ...         | yes refl = just (symbolHit path key version text (Content.Entry.gitDefault cell) symbolAt fileAt included)
  symbolRow path key value found = nothing

  symbol : T.FilePath → ℕ → Maybe SymbolHit
  symbol path key = symbolRow path key (DB.lookup key world) refl

  symbols : List (T.FilePath × ℕ) → List SymbolHit
  symbols [] = []
  symbols ((path , key) ∷ candidates) with symbol path key
  ... | nothing = symbols candidates
  ... | just hit = hit ∷ symbols candidates

  symbolIsCurrent : ∀ (hit : SymbolHit) → SymbolHit.key hit ∈ SelectedSnapshot.nodes view
  symbolIsCurrent = SymbolHit.inSnapshot

  record Candidate : Set where
    field edgeKey : ℕ
          source target : SymbolHit
          sourceData targetData : SymbolData
          edgePayload : String
          edgeAt : DB.lookup edgeKey world ≡ just (O.recordOf owner (O.edge (SymbolHit.key source) (SymbolHit.key target) edgePayload))
          inView : edgeKey ∈ SelectedSnapshot.edges view
          decodedSource : Decoder.symbol decoder (SymbolHit.text source) ≡ just sourceData
          decodedTarget : Decoder.symbol decoder (SymbolHit.text target) ≡ just targetData
          decodedRelation : Decoder.relation decoder edgePayload ≡ just (kind relation)
          queryMatches : (if incoming relation then SymbolData.name targetData else SymbolData.name sourceData) ≡ querySymbol

  related : Candidate → SymbolHit
  related candidate with incoming relation
  ... | true = Candidate.source candidate
  ... | false = Candidate.target candidate

  relatedData : Candidate → SymbolData
  relatedData candidate with incoming relation
  ... | true = Candidate.sourceData candidate
  ... | false = Candidate.targetData candidate

  record Universe : Set where
    field candidates : List Candidate
          complete : ∀ candidate → candidate ∈ candidates

  -- Results are candidates, not compiler-resolved bindings. Both endpoints
  -- include actual source path, position, and selected-view membership.
  endpointsInView : ∀ candidate → SymbolHit.key (Candidate.source candidate) ∈ SelectedSnapshot.nodes view ×
    SymbolHit.key (Candidate.target candidate) ∈ SelectedSnapshot.nodes view
  endpointsInView candidate = SymbolHit.inSnapshot (Candidate.source candidate) , SymbolHit.inSnapshot (Candidate.target candidate)

  edgeInView : ∀ candidate → Candidate.edgeKey candidate ∈ SelectedSnapshot.edges view
  edgeInView = Candidate.inView

  ownedEdge : ∀ candidate → DB.lookup (Candidate.edgeKey candidate) world ≡
    just (O.recordOf owner (O.edge (SymbolHit.key (Candidate.source candidate)) (SymbolHit.key (Candidate.target candidate)) (Candidate.edgePayload candidate)))
  ownedEdge = Candidate.edgeAt

  endpointEvidence : ∀ candidate →
    DB.lookup (SymbolHit.key (Candidate.source candidate)) world ≡ just (O.recordOf owner (O.symbol (SymbolHit.version (Candidate.source candidate)) (T.FilePath.value (SymbolHit.path (Candidate.source candidate))) (SymbolHit.text (Candidate.source candidate)))) ×
    DB.lookup (SymbolHit.key (Candidate.target candidate)) world ≡ just (O.recordOf owner (O.symbol (SymbolHit.version (Candidate.target candidate)) (T.FilePath.value (SymbolHit.path (Candidate.target candidate))) (SymbolHit.text (Candidate.target candidate))))
  endpointEvidence candidate = SymbolHit.symbolAt (Candidate.source candidate) , SymbolHit.symbolAt (Candidate.target candidate)

  otherFamilyCannotOwnEdge : ∀ candidate other body → family ≢ other →
    DB.lookup (Candidate.edgeKey candidate) world ≡ just (O.recordOf (O.family other) body) → ⊥
  otherFamilyCannotOwnEdge candidate other body different found = different
    (familyInjective (cong O.owner (just-injective (trans (sym (Candidate.edgeAt candidate)) found))))

  before : Candidate → Candidate → Bool
  before first second with T.FilePath.value (SymbolHit.path (related first)) String.≟ T.FilePath.value (SymbolHit.path (related second))
  ... | no _ = Selection.lexical (toList (T.FilePath.value (SymbolHit.path (related first)))) (toList (T.FilePath.value (SymbolHit.path (related second))))
  ... | yes _ with T.LineRange.start (SymbolData.range (relatedData first)) ≟ T.LineRange.start (SymbolData.range (relatedData second))
  ...   | no _ = does (T.LineRange.start (SymbolData.range (relatedData first)) ≤? T.LineRange.start (SymbolData.range (relatedData second)))
  ...   | yes _ = does (Candidate.edgeKey first ≤? Candidate.edgeKey second)

  insert : Candidate → List Candidate → List Candidate
  insert candidate [] = candidate ∷ []
  insert candidate (first ∷ rest) with before candidate first
  ... | true = candidate ∷ first ∷ rest
  ... | false = first ∷ insert candidate rest

  ordered : List Candidate → List Candidate
  ordered [] = []
  ordered (candidate ∷ rest) = insert candidate (ordered rest)

  result : Universe → List Candidate
  result universe = ordered (Universe.candidates universe)

  insertKeeps : ∀ candidate rows → candidate ∈ insert candidate rows
  insertKeeps candidate [] = here refl
  insertKeeps candidate (first ∷ rest) with before candidate first
  ... | true = here refl
  ... | false = there (insertKeeps candidate rest)

  insertRetains : ∀ candidate rows other → other ∈ rows → other ∈ insert candidate rows
  insertRetains candidate (first ∷ rest) other included with before candidate first
  ... | true = there included
  ... | false with included
  ...   | here refl = here refl
  ...   | there later = there (insertRetains candidate rest other later)

  orderedRetains : ∀ rows candidate → candidate ∈ rows → candidate ∈ ordered rows
  orderedRetains (candidate ∷ rest) .candidate (here refl) = insertKeeps candidate (ordered rest)
  orderedRetains (first ∷ rest) candidate (there later) = insertRetains first (ordered rest) candidate (orderedRetains rest candidate later)

  allCandidatesReturned : ∀ universe candidate → candidate ∈ result universe
  allCandidatesReturned universe candidate = orderedRetains (Universe.candidates universe) candidate (Universe.complete universe candidate)

  guidance : Dialogue.Prompt
  guidance = Dialogue.prompt (Dialogue.text 'T' "hese relationships are candidates based on matching names; they are not compiler-resolved bindings.")
    (Dialogue.text 'I' "f several definitions match, use their source paths and positions to narrow the search.") []

```

## Preserve multiple candidates and make the order reproducible

Several definitions can have the same name. The model ties the result to the
complete matching candidate universe and a canonical order. Keeping distinct
candidates lets the reader compare paths and positions to identify the
relationship relevant to the task. The returned evidence describes a
name-based candidate, with compiler resolution outside this model.

```agda
  record Response (universe : Universe) : Set where
    field rows : List Candidate
          completeOrder : rows ≡ result universe
          explanation : Dialogue.Prompt
          explainsLimit : explanation ≡ guidance

  response : (universe : Universe) → Response universe
  response universe = record { rows = result universe; completeOrder = refl; explanation = guidance; explainsLimit = refl }

  responseIncludesEveryCandidate : ∀ universe (answer : Response universe) candidate → candidate ∈ Response.rows answer
  responseIncludesEveryCandidate universe answer candidate = subst (λ rows → candidate ∈ rows) (sym (Response.completeOrder answer)) (allCandidatesReturned universe candidate)
```
