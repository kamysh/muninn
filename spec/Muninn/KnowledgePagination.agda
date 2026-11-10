{-# OPTIONS --safe #-}
-- Validate saved note-page identities against the current family and checkout.
module Muninn.KnowledgePagination where
import Muninn.OwnedState as O
import Muninn.PaginationData as P
import Muninn.PaginationSource as Source
import Muninn.PaginationCommit as Commit
import Muninn.StoredPolicy as Policy
import Muninn.KnowledgeViews as Views
import Muninn.KnowledgeRead as Read
import Muninn.VectorData as V
import Muninn.ArtifactIdentity as Equal
import Muninn.ExclusionOutcomes as E
import Muninn.Canonical as C
import Muninn.RequestCodecs as Codecs
import Muninn.CatalogInputs as I
import Muninn.Types as T
open import Data.String using (String)
open import Data.Nat using (ℕ; _≟_)
open import Data.List using (List; map; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
import Data.String as String
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
module DB = O.DB

module Family (family registrationSlot selected pointer : ℕ) (codec : Views.Codec)
  (queryId : I.OperationId) (tokenId : T.UUID) where
  owner = O.family family
  module Operation = Commit.Family family queryId tokenId
  module Notes = Read.Family family pointer codec
  module Visible = Notes.Source
  module Saved = Policy.Family family pointer

  module In (world : O.World) (current : Saved.Saved world) (view : P.View)
    (identity : Source.ScopeWitness family selected world view) where
    checkout : Visible.Checkout world
    checkout = record { slot = selected; info = Source.ScopeWitness.checkout identity
      ; stored = Source.ScopeWitness.checkoutAt identity; live = Source.ScopeWitness.activeCheckout identity }
    data Row : P.Ref → Set where
      text : (visible : Visible.Visible world current checkout) → Row (P.noteRef (Visible.Note.key (Visible.Visible.note visible)) nothing)
      vector : (visible : Visible.Visible world current checkout) → ∀ slot storedVector →
        DB.lookup slot world ≡ just (O.recordOf owner (O.noteVector (Visible.Note.key (Visible.Visible.note visible)) (V.usable storedVector))) →
        P.View.profile view ≡ just (V.Value.profile storedVector) →
        V.Value.source storedVector ≡ Visible.text (Visible.Note.item (Visible.Visible.note visible)) →
        Row (P.noteRef (Visible.Note.key (Visible.Visible.note visible)) (just slot))

    vectorAt : (visible : Visible.Visible world current checkout) → ∀ slot → Maybe (Row (P.noteRef (Visible.Note.key (Visible.Visible.note visible)) (just slot)))
    vectorAt visible slot with DB.lookup slot world in located
    ... | just (O.recordOf actualOwner (O.noteVector key (V.usable storedVector))) with
      E.ownerEqual actualOwner owner | key ≟ Visible.Note.key (Visible.Visible.note visible) |
      P.View.profile view in profile | V.Value.source storedVector String.≟ Visible.text (Visible.Note.item (Visible.Visible.note visible))
    ...   | yes refl | yes refl | just selectedProfile | yes content with Equal.EmbeddingKey? selectedProfile (V.Value.profile storedVector)
    ...     | yes refl = just (vector visible slot storedVector located profile content)
    ...     | no _ = nothing
    vectorAt visible slot | just (O.recordOf actualOwner (O.noteVector key (V.usable storedVector))) | _ | _ | _ | _ = nothing
    vectorAt visible slot | _ = nothing

    restore : (ref : P.Ref) → Maybe (Row ref)
    restore (P.noteRef key vectorSlot) with Notes.inspect world current checkout key (DB.lookup key world) refl
    ... | nothing = nothing
    ... | just visible with Visible.Note.key (Visible.Visible.note visible) ≟ key
    ...   | no _ = nothing
    ...   | yes refl with vectorSlot
    ...     | nothing = just (text visible)
    ...     | just slot = vectorAt visible slot
    restore _ = nothing
    restoreAll : (refs : List P.Ref) → Maybe (All Row refs)
    restoreAll [] = just []
    restoreAll (ref ∷ refs) with restore ref | restoreAll refs
    ... | just row | just rest = just (row ∷ rest)
    ... | _ | _ = nothing

  data NoteQuery : P.Query → Set where
    searched : ∀ target query page → NoteQuery (P.notes target query page)
    listed : ∀ target page → NoteQuery (P.listNotes target page)
  queryTarget : ∀ {query} → NoteQuery query → I.FamilyTarget
  queryTarget (searched target query page) = target
  queryTarget (listed target page) = target

  record Eligible (world : O.World) (plan : P.Plan) (rows : List P.Item) : Set where
    field query : NoteQuery (P.Plan.query plan)
          policy : Saved.Saved world
          identity : Source.ScopeWitness family selected world (P.Plan.view plan)
          version : Saved.Saved.version policy ≡ P.View.policyVersion (P.Plan.view plan)
          sameFamily : O.PolicyVersionInfo.familyId (Saved.Saved.info policy) ≡ O.RegistrationInfo.id (Source.ScopeWitness.registration identity)
          requestedFamily : I.FamilyTarget.expectedFamily (queryTarget query) ≡ O.RegistrationInfo.id (Source.ScopeWitness.registration identity)
    module SavedRows = In world policy (P.Plan.view plan) identity
    field visible : All SavedRows.Row (map P.Item.ref rows)

  query : (query : P.Query) → Maybe (NoteQuery query)
  query (P.notes target storedVector page) = just (searched target storedVector page)
  query (P.listNotes target page) = just (listed target page)
  query _ = nothing
  check : ∀ world plan rows → Maybe (Eligible world plan rows)
  check world plan rows with query (P.Plan.query plan) | Saved.observe world | Source.Identity.observe family registrationSlot selected world (P.Plan.view plan)
  ... | nothing | _ | _ = nothing
  ... | _ | nothing | _ = nothing
  ... | _ | _ | nothing = nothing
  ... | just request | just policy | just identity with Saved.Saved.version policy ≟ P.View.policyVersion (P.Plan.view plan) |
    C.compare Codecs.familyId (O.PolicyVersionInfo.familyId (Saved.Saved.info policy)) (O.RegistrationInfo.id (Source.ScopeWitness.registration identity)) |
    C.compare Codecs.familyId (I.FamilyTarget.expectedFamily (queryTarget request)) (O.RegistrationInfo.id (Source.ScopeWitness.registration identity)) |
    In.restoreAll world policy (P.Plan.view plan) identity (map P.Item.ref rows)
  ...   | yes version | yes sameFamily | yes requestedFamily | just visible = just record
    { query = request; policy = policy; identity = identity; version = version; sameFamily = sameFamily; requestedFamily = requestedFamily; visible = visible }
  ...   | _ | _ | _ | _ = nothing
  module Checked = Operation.Checked Eligible check
