{-# OPTIONS --safe #-}
-- Curated notes are owned by families and optionally narrowed to a worktree.
module Muninn.KnowledgeViews where
import Muninn.OwnedState as O
import Muninn.Knowledge as K
import Muninn.StoredPolicy as Policy
import Muninn.RepositoryProfile as Profile
import Muninn.Config as Config
import Muninn.RequestCodecs as Codecs
import Muninn.Canonical as Canonical
import Muninn.VectorData as V
import Muninn.RetrievalNumerics as Numeric
import Muninn.Worktree as W
open import Data.Nat using (ℕ)
open import Data.Bool using (false)
open import Data.String using (String; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
module DB = O.DB

-- The storage adapter must use this lossless encoding for the actual row,
-- rather than selecting note contents independently of persistent state.
record Codec : Set where
  field encode : K.KnowledgeItem → String
        decode : String → Maybe K.KnowledgeItem
        roundTrip : ∀ item → decode (encode item) ≡ just item

module Family (family pointer : ℕ) (codec : Codec) where
  owner = O.family family
  module Saved = Policy.Family family pointer
  module Profiles = Profile.Family family pointer
  record Note (world : O.World) (current : Saved.Saved world) : Set where
    field key : ℕ
          payload : String
          item : K.KnowledgeItem
          stored : DB.lookup key world ≡ just (O.recordOf owner (O.note payload))
          decoded : Codec.decode codec payload ≡ just item
          familyMatches : K.KnowledgeItem.family item ≡ O.PolicyVersionInfo.familyId (Saved.Saved.info current)

  data Allowed (item : K.KnowledgeItem) (checkout : O.CheckoutInfo) : Set where
    familyWide : K.KnowledgeItem.scope item ≡ nothing → Allowed item checkout
    thisWorktree : K.KnowledgeItem.scope item ≡ just (O.CheckoutInfo.id checkout) → Allowed item checkout

  record Checkout (world : O.World) : Set where
    field slot : ℕ
          info : O.CheckoutInfo
          stored : DB.lookup slot world ≡ just (O.recordOf owner (O.checkout info))
          live : O.CheckoutInfo.retired info ≡ false

  record Visible (world : O.World) (current : Saved.Saved world) (checkout : Checkout world) : Set where
    field note : Note world current
          allowed : Allowed (Note.item note) (Checkout.info checkout)

  familyWideShared : ∀ world current (note : Note world current) first second →
    K.KnowledgeItem.scope (Note.item note) ≡ nothing →
    Visible world current first × Visible world current second
  familyWideShared world current note first second wide =
    record { note = note; allowed = familyWide wide } , record { note = note; allowed = familyWide wide }
  scopedRequiresWorktree : ∀ item first second → Allowed item first → K.KnowledgeItem.scope item ≡ just (O.CheckoutInfo.id second) →
    O.CheckoutInfo.id first ≡ O.CheckoutInfo.id second
  scopedRequiresWorktree item first second (familyWide none) chosen with trans (sym none) chosen
  ... | ()
  scopedRequiresWorktree item first second (thisWorktree own) chosen = just-injective (trans (sym own) chosen)
  otherFamilyCannotOwnNote : ∀ world current (note : Note world current) other body → family ≢ other →
    DB.lookup (Note.key note) world ≡ just (O.recordOf (O.family other) body) → ⊥
  otherFamilyCannotOwnNote world current note other body different found = different
    (familyInjective (cong O.owner (just-injective (trans (sym (Note.stored note)) found))))
    where
    familyInjective : ∀ {first second} → O.family first ≡ O.family second → first ≡ second
    familyInjective refl = refl

  -- Embeddings are derived and must use the active repository profile. The
  -- note body stays independently stored and available without the vector.
  text : K.KnowledgeItem → String
  text item = K.KnowledgeItem.title item ++ "\n" ++ K.KnowledgeItem.body item
  record Embedded (world : O.World) (active : Profiles.Active world)
    (note : Note world (Profiles.Active.current active)) : Set where
    field slot : ℕ
          value : V.Value
          stored : DB.lookup slot world ≡ just (O.recordOf owner (O.noteVector (Note.key note) (V.usable value)))
          profile : V.Value.profile value ≡ Profiles.noteKey active
          content : V.Value.source value ≡ text (Note.item note)
          stored32 : Numeric.Stored32 (V.Value.values value)
  notesUseFamilyProfile : ∀ world active note (embedding : Embedded world active note) →
    V.Value.profile (Embedded.value embedding) ≡ Profiles.codeKey active
  notesUseFamilyProfile world active note embedding = Embedded.profile embedding
