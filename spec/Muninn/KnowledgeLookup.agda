{-# OPTIONS --safe #-}
-- Locate a family-owned note by its stable logical identity.
module Muninn.KnowledgeLookup where
import Muninn.OwnedState as O
import Muninn.Knowledge as K
import Muninn.KnowledgeViews as Views
import Muninn.Canonical as Canonical
import Muninn.RequestCodecs as Codecs
import Muninn.ExclusionOutcomes as E
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String)
open import Data.Product using (_,_ )
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
module DB = O.DB
module Family (family : ℕ) (codec : Views.Codec) (id : K.KnowledgeId) where
  owner = O.family family
  record Located (world : O.World) : Set where
    field slot : ℕ
          oldPayload : String
          oldItem : K.KnowledgeItem
          stored : DB.lookup slot world ≡ just (O.recordOf owner (O.note oldPayload))
          decoded : Views.Codec.decode codec oldPayload ≡ just oldItem
          sameId : K.KnowledgeItem.id oldItem ≡ id
  inspect : ∀ world slot → (row : Maybe O.Record) → DB.lookup slot world ≡ row → Maybe (Located world)
  inspect world slot (just (O.recordOf actualOwner (O.note oldPayload))) stored with E.ownerEqual actualOwner owner
  ... | no _ = nothing
  ... | yes refl with Views.Codec.decode codec oldPayload in decoded
  ...   | nothing = nothing
  ...   | just oldItem with Canonical.compare Codecs.knowledgeId (K.KnowledgeItem.id oldItem) (id)
  ...     | no _ = nothing
  ...     | yes sameId = just record { slot = slot; oldPayload = oldPayload; oldItem = oldItem; stored = stored; decoded = decoded; sameId = sameId }
  inspect world slot row stored = nothing
  scan : (world : O.World) → O.World → Maybe (Located world)
  scan world [] = nothing
  scan world ((slot , ignored) ∷ rows) with inspect world slot (DB.lookup slot world) refl
  ... | just found = just found
  ... | nothing = scan world rows
  find : (world : O.World) → Maybe (Located world)
  find world = scan world world
