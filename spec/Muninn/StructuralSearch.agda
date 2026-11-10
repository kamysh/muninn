{-# OPTIONS --safe #-}
-- Evidence-bearing name-based structural search over an actual checkout view.
module Muninn.StructuralSearch where
import Muninn.OwnedState as O
import Muninn.StoredPolicy as Policy
import Muninn.PublishedViews as Published
import Muninn.ContentViews as Content
import Muninn.SearchView as View
import Muninn.Graph as Graph
import Muninn.CatalogInputs as I
import Muninn.Types as T
import Muninn.RetrievalSelection as Selection
import Muninn.Dialogue as Dialogue
open import Data.Nat using (ℕ; _≟_; _≤?_; _≤_; z≤n; s≤s)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.String using (String; toList)
import Data.String as String
open import Data.List using (List; []; _∷_; length; take)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

familyInjective : ∀ {first second} → O.family first ≡ O.family second → first ≡ second
familyInjective refl = refl

-- Payload interpretation is fixed by the source adapter for the stored
-- parser/representation version; the dispatcher cannot choose a query outcome.
record SymbolData : Set where
  field name : String
        kind : Graph.SymbolKind
        range : T.LineRange
record Decoder : Set where
  field symbol : String → Maybe SymbolData
        relation : String → Maybe Graph.Relation

kind : I.StructuralRelation → Graph.Relation
kind I.callers = Graph.Calls
kind I.callees = Graph.Calls
kind I.imports = Graph.Imports
kind I.defines = Graph.Defines
kind I.inheritors = Graph.InheritsFrom
kind I.inherits = Graph.InheritsFrom
incoming : I.StructuralRelation → Bool
incoming I.callers = true
incoming I.inheritors = true
incoming _ = false

module Family (family checkout pointer : ℕ) (world : O.World)
  (policy : Policy.Family.Saved family pointer world) (viewsValid : Published.Valid world)
  (filesValid : Content.Family.WellFormed (Policy.Family.rule family pointer policy) world)
  (view : View.Family.Stored family checkout world) (request : I.StructuralInput) (decoder : Decoder) where
  module Source = View.Family.ForPolicy.Current family checkout pointer world policy viewsValid filesValid view
  module Hit = Source.SymbolHit
  record Candidate : Set where
    field edgeKey : ℕ
          source target : Source.SymbolHit
          sourceData targetData : SymbolData
          edgePayload : String
          edgeAt : O.DB.lookup edgeKey world ≡ just (O.recordOf (O.family family) (O.edge (Hit.key source) (Hit.key target) edgePayload))
          inView : edgeKey ∈ View.Family.Stored.edges view
          decodedSource : Decoder.symbol decoder (Hit.text source) ≡ just sourceData
          decodedTarget : Decoder.symbol decoder (Hit.text target) ≡ just targetData
          decodedRelation : Decoder.relation decoder edgePayload ≡ just (kind (I.StructuralInput.relation request))
          queryMatches : (if incoming (I.StructuralInput.relation request) then SymbolData.name targetData else SymbolData.name sourceData) ≡ I.StructuralInput.symbol request
    related : Source.SymbolHit
    related with incoming (I.StructuralInput.relation request)
    ... | true = source
    ... | false = target
    relatedData : SymbolData
    relatedData with incoming (I.StructuralInput.relation request)
    ... | true = sourceData
    ... | false = targetData

  record Universe : Set where
    field candidates : List Candidate
          complete : ∀ candidate → candidate ∈ candidates

  -- Results are candidates, not compiler-resolved bindings. Both endpoints
  -- include actual source path, position, and selected-view membership.
  endpointsInView : ∀ candidate → Hit.key (Candidate.source candidate) ∈ View.Family.Stored.nodes view × Hit.key (Candidate.target candidate) ∈ View.Family.Stored.nodes view
  endpointsInView candidate = Hit.inSnapshot (Candidate.source candidate) , Hit.inSnapshot (Candidate.target candidate)
  edgeInView : ∀ candidate → Candidate.edgeKey candidate ∈ View.Family.Stored.edges view
  edgeInView = Candidate.inView
  ownedEdge : ∀ candidate → O.DB.lookup (Candidate.edgeKey candidate) world ≡ just (O.recordOf (O.family family) (O.edge (Hit.key (Candidate.source candidate)) (Hit.key (Candidate.target candidate)) (Candidate.edgePayload candidate)))
  ownedEdge = Candidate.edgeAt
  endpointEvidence : ∀ candidate →
    O.DB.lookup (Hit.key (Candidate.source candidate)) world ≡ just (O.recordOf (O.family family) (O.symbol (Hit.version (Candidate.source candidate)) (T.FilePath.value (Hit.path (Candidate.source candidate))) (Hit.text (Candidate.source candidate)))) ×
    O.DB.lookup (Hit.key (Candidate.target candidate)) world ≡ just (O.recordOf (O.family family) (O.symbol (Hit.version (Candidate.target candidate)) (T.FilePath.value (Hit.path (Candidate.target candidate))) (Hit.text (Candidate.target candidate))))
  endpointEvidence candidate = Hit.symbolAt (Candidate.source candidate) , Hit.symbolAt (Candidate.target candidate)
  otherFamilyCannotOwnEdge : ∀ candidate other body → family ≢ other →
    O.DB.lookup (Candidate.edgeKey candidate) world ≡ just (O.recordOf (O.family other) body) → ⊥
  otherFamilyCannotOwnEdge candidate other body different found = different
    (familyInjective (cong O.owner (just-injective (trans (sym (Candidate.edgeAt candidate)) found))))

  before : Candidate → Candidate → Bool
  before first second with T.FilePath.value (Hit.path (Candidate.related first)) String.≟ T.FilePath.value (Hit.path (Candidate.related second))
  ... | no _ = Selection.lexical (toList (T.FilePath.value (Hit.path (Candidate.related first)))) (toList (T.FilePath.value (Hit.path (Candidate.related second))))
  ... | yes _ with T.LineRange.start (SymbolData.range (Candidate.relatedData first)) ≟ T.LineRange.start (SymbolData.range (Candidate.relatedData second))
  ...   | no _ = does (T.LineRange.start (SymbolData.range (Candidate.relatedData first)) ≤? T.LineRange.start (SymbolData.range (Candidate.relatedData second)))
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
  record Response (universe : Universe) : Set where
    field rows : List Candidate
          completeOrder : rows ≡ result universe
          explanation : Dialogue.Prompt
          explainsLimit : explanation ≡ guidance
  response : (universe : Universe) → Response universe
  response universe = record { rows = result universe; completeOrder = refl; explanation = guidance; explainsLimit = refl }
  responseIncludesEveryCandidate : ∀ universe (answer : Response universe) candidate → candidate ∈ Response.rows answer
  responseIncludesEveryCandidate universe answer candidate = subst (λ rows → candidate ∈ rows) (sym (Response.completeOrder answer)) (allCandidatesReturned universe candidate)
