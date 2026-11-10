{-# OPTIONS --safe #-}
-- Constructive text/symbol intake has no vector/provider precondition.
module Muninn.TextPublication where
import Muninn.OwnedState as O
import Muninn.RecordAllocation as Allocation
import Muninn.CleanupAdmissionStorage as Insert
import Muninn.ReceiptLedger as L
import Muninn.RegistryCreation as Frames
import Muninn.ViewPublication as Compose
import Muninn.IdentityCheckpoint as Checkpoint
import Muninn.RequestIdentity as N
import Muninn.CatalogInputs as I
import Muninn.ReceiptTypes as R
import Muninn.Dialogue as D
import Muninn.ExclusionOutcomes as E
import Muninn.IndexControl as Control
open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Data.Maybe using (just)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Data.List using ([]; _∷_)
import Data.List.Relation.Unary.All as All
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans)
module DB = O.DB

module Family (family version : ℕ) (text path symbol checkpoint : String) (nonempty : text ≢ "")
  (guidance : String → D.Prompt) where
  owner = O.family family
  chunk = O.recordOf owner (O.chunk version text)
  symbolRow = O.recordOf owner (O.symbol version path symbol)

  chunkSlot : O.World → ℕ
  chunkSlot = Allocation.freshId
  withChunk : O.World → O.World
  withChunk before = DB.write (chunkSlot before) chunk before
  posting : O.World → O.Record
  posting before = O.recordOf owner (O.posting (chunkSlot before) text)
  postingSlot : O.World → ℕ
  postingSlot before = Allocation.freshId (withChunk before)
  withPosting : O.World → O.World
  withPosting before = DB.write (postingSlot before) (posting before) (withChunk before)
  symbolSlot : O.World → ℕ
  symbolSlot before = Allocation.freshId (withPosting before)
  after : O.World → O.World
  after before = DB.write (symbolSlot before) symbolRow (withPosting before)

  writes : O.World → DB.Transaction String
  writes before = DB.put (chunkSlot before) chunk
    (DB.put (postingSlot before) (posting before)
      (DB.put (symbolSlot before) symbolRow (DB.commit checkpoint)))
  versionReady : O.World → Bool
  versionReady world with DB.lookup version world
  ... | just (O.recordOf actualOwner (O.fileVersion payload)) with E.ownerEqual actualOwner owner
  ...   | yes sameOwner = true
  ...   | no other = false
  versionReady world | _ = false

  snapshot : O.World → DB.Transaction String
  snapshot before with versionReady before
  ... | true = writes before
  ... | false = DB.abort "The source version changed. Continue using the current file version."

  transaction : DB.Transaction String
  transaction = DB.scan snapshot

  performs : ∀ before → versionReady before ≡ true → DB.evaluate transaction before ≡ DB.committed checkpoint (after before)
  performs before available with versionReady before
  ... | true = refl
  ... | false with available
  ...   | ()

  isolates : ∀ before result final → DB.evaluate transaction before ≡ DB.committed result final → L.ReceiptFrame before final
  isolates before result final committed with versionReady before
  ... | false with committed
  ...   | ()
  isolates before result final committed | true with committed
  ... | refl = Compose.composeFrames before (withChunk before) (after before)
    (Frames.freshFrame before (chunkSlot before) chunk (Allocation.fresh before) (λ ()))
    (Compose.composeFrames (withChunk before) (withPosting before) (after before)
      (Frames.freshFrame (withChunk before) (postingSlot before) (posting before) (Allocation.fresh (withChunk before)) (λ ()))
      (Frames.freshFrame (withPosting before) (symbolSlot before) symbolRow (Allocation.fresh (withPosting before)) (λ ())))

  effect : L.Effect
  effect = record { transaction = transaction; guidance = guidance; isolates = isolates }

  module Current (before : O.World) (valid : O.Admissible before) (versionPayload : String)
    (versionAt : DB.lookup version before ≡ just (O.recordOf owner (O.fileVersion versionPayload))) where
    versionAvailable : versionReady before ≡ true
    versionAvailable rewrite versionAt with E.ownerEqual owner owner
    ... | yes sameOwner = refl
    ... | no different = ⊥-elim (different refl)
    chunkResolved : O.Resolves before owner (O.reference version O.fileVersionK)
    chunkResolved = record { value = O.recordOf owner (O.fileVersion versionPayload); found = versionAt; rightKind = refl; rightOwner = O.own }

    chunkValid : O.Admissible (withChunk before)
    chunkValid = Insert.insertAdmissible before (chunkSlot before) chunk valid (Allocation.fresh before)
      O.local (chunkResolved All.∷ All.[]) (refl All.∷ All.[])

    postingResolved : O.Resolves (withChunk before) owner (O.reference (chunkSlot before) O.chunkK)
    postingResolved = record { value = chunk; found = DB.writeVisible (chunkSlot before) chunk before; rightKind = refl; rightOwner = O.own }

    postingValid : O.Admissible (withPosting before)
    postingValid = Insert.insertAdmissible (withChunk before) (postingSlot before) (posting before) chunkValid
      (Allocation.fresh (withChunk before)) O.local (postingResolved All.∷ All.[]) (refl All.∷ All.[])

    symbolResolved : O.Resolves (withPosting before) owner (O.reference version O.fileVersionK)
    symbolResolved = Insert.oldResolve (withChunk before) (postingSlot before) (posting before)
      (Allocation.fresh (withChunk before)) owner (O.reference version O.fileVersionK)
      (Insert.oldResolve before (chunkSlot before) chunk (Allocation.fresh before) owner (O.reference version O.fileVersionK) chunkResolved)

    afterValid : O.Admissible (after before)
    afterValid = Insert.insertAdmissible (withPosting before) (symbolSlot before) symbolRow postingValid
      (Allocation.fresh (withPosting before)) O.local (symbolResolved All.∷ All.[]) (refl All.∷ All.[])

    chunkAt : DB.lookup (chunkSlot before) (after before) ≡ just chunk
    chunkAt = Insert.oldLookup (withPosting before) (symbolSlot before) symbolRow (Allocation.fresh (withPosting before))
      (chunkSlot before) chunk (Insert.oldLookup (withChunk before) (postingSlot before) (posting before)
        (Allocation.fresh (withChunk before)) (chunkSlot before) chunk (DB.writeVisible (chunkSlot before) chunk before))

    postingAt : DB.lookup (postingSlot before) (after before) ≡ just (posting before)
    postingAt = Insert.oldLookup (withPosting before) (symbolSlot before) symbolRow (Allocation.fresh (withPosting before))
      (postingSlot before) (posting before) (DB.writeVisible (postingSlot before) (posting before) (withChunk before))

    symbolAt : DB.lookup (symbolSlot before) (after before) ≡ just symbolRow
    symbolAt = DB.writeVisible (symbolSlot before) symbolRow (withPosting before)

    -- The actual accepted indexing job seals these rows with its receipt.
    module Run (id : I.OperationId) (input : N.Meaning) (named : R.Names id input)
      (receiptSlot : ℕ) (progress : R.Work)
      (accepted : L.find id before ≡ just (L.found receiptSlot owner (R.active input named progress)))
      (receiptAt : DB.lookup receiptSlot before ≡ just (L.recordAt {id = id} owner (R.active input named progress)))
      (familySlot workSlot generation : ℕ)
      (permission : Control.Worker.allowed family familySlot workSlot id generation before ≡ true) where
      module Worker = Control.Worker family familySlot workSlot id generation
      continuation = "Indexing is paused or its saved work has changed. Continue from the current checkpoint."
      guarded = Worker.effect effect continuation
      module Saved = Checkpoint.Run id input named owner receiptSlot progress checkpoint guarded before (after before)
        afterValid accepted receiptAt (trans
          (Worker.ready (L.Effect.transaction effect) continuation before permission) (performs before versionAvailable))
      durableChunk : DB.lookup (chunkSlot before) Saved.after ≡ just chunk
      durableChunk = Saved.preservesData (chunkSlot before) chunk chunkAt (λ ())
      durablePosting : DB.lookup (postingSlot before) Saved.after ≡ just (posting before)
      durablePosting = Saved.preservesData (postingSlot before) (posting before) postingAt (λ ())
      durableSymbol : DB.lookup (symbolSlot before) Saved.after ≡ just symbolRow
      durableSymbol = Saved.preservesData (symbolSlot before) symbolRow symbolAt (λ ())
