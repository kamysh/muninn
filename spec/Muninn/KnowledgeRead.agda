{-# OPTIONS --safe #-}
-- Listing and searching derive candidates from the selected family's actual rows.
module Muninn.KnowledgeRead where
import Muninn.OwnedState as O
import Muninn.Knowledge as K
import Muninn.KnowledgeViews as Views
import Muninn.StoredPolicy as Policy
import Muninn.RepositoryProfile as Profile
import Muninn.RetrievalText as Text
import Muninn.RetrievalNumerics as Numeric
import Muninn.VectorData as V
import Muninn.Canonical as Canonical
import Muninn.RequestCodecs as Codecs
import Muninn.ExclusionOutcomes as E
import Muninn.SearchTarget as Target
import Muninn.RepositoryIdentity as Repository
import Muninn.Dialogue as D
import Muninn.CatalogInputs as I
open import Data.Nat using (ℕ)
open import Data.Bool using (false)
open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
module DB = O.DB

module Family (family pointer : ℕ) (codec : Views.Codec) where
  module Source = Views.Family family pointer codec
  module Saved = Policy.Family family pointer
  module Profiles = Profile.Family family pointer
  owner = O.family family

  allowed : ∀ item checkout → Maybe (Source.Allowed item checkout)
  allowed item checkout with K.KnowledgeItem.scope item in scope
  ... | nothing = just (Source.familyWide scope)
  ... | just selected with Canonical.compare Codecs.checkoutId selected (O.CheckoutInfo.id checkout)
  ...   | no _ = nothing
  ...   | yes same = just (Source.thisWorktree (trans scope (cong just same)))

  inspect : ∀ world (current : Saved.Saved world) (checkout : Source.Checkout world) slot →
    (row : Maybe O.Record) → DB.lookup slot world ≡ row → Maybe (Source.Visible world current checkout)
  inspect world current checkout slot (just (O.recordOf actualOwner (O.note payload))) stored with E.ownerEqual actualOwner owner
  ... | no _ = nothing
  ... | yes refl with Views.Codec.decode codec payload in decoded
  ...   | nothing = nothing
  ...   | just item with Canonical.compare Codecs.familyId (K.KnowledgeItem.family item) (O.PolicyVersionInfo.familyId (Saved.Saved.info current)) | allowed item (Source.Checkout.info checkout)
  ...     | yes same | just permitted = just record { note = record { key = slot; payload = payload; item = item; stored = stored; decoded = decoded; familyMatches = same }; allowed = permitted }
  ...     | _ | _ = nothing
  inspect world current checkout slot row stored = nothing

  scan : ∀ world (current : Saved.Saved world) (checkout : Source.Checkout world) → O.World → List (Source.Visible world current checkout)
  scan world current checkout [] = []
  scan world current checkout ((slot , ignored) ∷ rows) with inspect world current checkout slot (DB.lookup slot world) refl
  ... | nothing = scan world current checkout rows
  ... | just visible = visible ∷ scan world current checkout rows
  list : ∀ world (current : Saved.Saved world) (checkout : Source.Checkout world) → List (Source.Visible world current checkout)
  list world current checkout = scan world current checkout world

  listUsesActualFamily : ∀ world current checkout (visible : Source.Visible world current checkout) →
    K.KnowledgeItem.family (Source.Note.item (Source.Visible.note visible)) ≡ O.PolicyVersionInfo.familyId (Saved.Saved.info current)
  listUsesActualFamily world current checkout visible = Source.Note.familyMatches (Source.Visible.note visible)

  -- Resolve the requested location before selecting a checkout: an adapter
  -- cannot supply an unrelated worktree merely because it belongs to a family.
  module Request (registrationSlot selected : ℕ) (target : I.FamilyTarget)
    (context : D.Context) (observed : Repository.Observation) where
    module Resolve = Target.Family family registrationSlot selected (I.FamilyTarget.location target) context observed
    record Ready (world : O.World) : Set where
      field current : Saved.Saved world
            resolved : Resolve.Target world
            familyMatches : I.FamilyTarget.expectedFamily target ≡ O.RegistrationInfo.id (Resolve.Target.registration resolved)
            samePolicy : I.FamilyTarget.expectedFamily target ≡ O.PolicyVersionInfo.familyId (Saved.Saved.info current)
            live : O.CheckoutInfo.retired (Resolve.Target.checkout resolved) ≡ false
    checkout : ∀ {world} → Ready world → Source.Checkout world
    checkout ready = record { slot = selected; info = Resolve.Target.checkout (Ready.resolved ready)
      ; stored = Resolve.Target.checkoutAt (Ready.resolved ready); live = Ready.live ready }
    listResolved : ∀ world → (ready : Ready world) → List (Source.Visible world (Ready.current ready) (checkout ready))
    listResolved world ready = list world (Ready.current ready) (checkout ready)

  module Search (world : O.World) (active : Profiles.Active world) (checkout : Source.Checkout world)
    (query : String) (english : Text.Engine) where
    current = Profiles.Active.current active
    module Words = Text.Using english
    record QueryVector : Set where
      field value : V.Value
            profile : V.Value.profile value ≡ Profiles.noteKey active
            source : V.Value.source value ≡ query
            stored32 : Numeric.Stored32 (V.Value.values value)
    data Match : Maybe QueryVector → Source.Visible world current checkout → Set where
      words : ∀ {input visible} → Words.Match query (Source.text (Source.Note.item (Source.Visible.note visible))) → Match input visible
      semantic : ∀ {input visible} → (embedded : Source.Embedded world active (Source.Visible.note visible)) →
        Numeric.Cosine (V.Value.values (QueryVector.value input)) (V.Value.values (Source.Embedded.value embedded)) → Match (just input) visible
    -- A search outcome is over the complete visible set; adapters cannot
    -- claim a matching note is absent merely because it was outside a batch.
    record Candidate (input : Maybe QueryVector) : Set where
      field visible : Source.Visible world current checkout
            matches : Match input visible
    key : ∀ {input} → Candidate input → ℕ
    key candidate = Source.Note.key (Source.Visible.note (Candidate.visible candidate))
    record Universe (input : Maybe QueryVector) : Set where
      field items : List (Candidate input)
            complete : ∀ (candidate : Candidate input) → Σ (Candidate input) (λ saved → saved ∈ items × key saved ≡ key candidate)
    record Results (input : Maybe QueryVector) (universe : Universe input) : Set where
      field items : List (Candidate input)
            allCandidates : ∀ candidate → candidate ∈ Universe.items universe → Σ (Candidate input) (λ saved → saved ∈ items × key saved ≡ key candidate)
            noInvented : ∀ candidate → candidate ∈ items → candidate ∈ Universe.items universe
    everyMatchIncluded : ∀ input universe (results : Results input universe) candidate → Σ (Candidate input) (λ saved → saved ∈ Results.items results × key saved ≡ key candidate)
    everyMatchIncluded input universe results candidate with Universe.complete universe candidate
    ... | present , included , same with Results.allCandidates results present included
    ...   | saved , returned , equal = saved , returned , trans equal same
