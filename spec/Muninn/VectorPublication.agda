{-# OPTIONS --safe #-}
-- Publish one vector association or preparation explanation without touching text.
module Muninn.VectorPublication where
import Muninn.OwnedState as O
import Muninn.VectorData as V
import Muninn.StagedVectors as Coverage
import Muninn.Worktree as W
import Muninn.ArtifactIdentity as Equal
import Muninn.ExclusionOutcomes as E
import Muninn.RecordAllocation as Allocation
import Muninn.CleanupAdmissionStorage as Insert
import Muninn.CleanupStorage as Storage
import Muninn.RetirementControl as Frames
import Muninn.RegistryCreation as Fresh
import Muninn.Dialogue as D
import Muninn.ReceiptLedger as L
import Muninn.ContentViews as Views
import Muninn.IdentityCheckpoint as Checkpoint
import Muninn.IndexControl as Control
import Muninn.ContentPublication as Publication
import Muninn.CatalogInputs as I
import Muninn.RequestIdentity as N
import Muninn.ReceiptTypes as R
open import Data.Nat using (ℕ; _≟_)
open import Data.Bool using (Bool; true; false)
open import Data.String using (String; _++_)
import Data.String as String
open import Data.List using ([]; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym; cong)
module DB = O.DB

checkpoint : V.State → String
checkpoint (V.pending profile text) = "Vector preparation is pending; existing text and symbols are retained."
checkpoint (V.waiting profile text explanation) = V.Guidance.reason explanation ++ " Next: " ++
  V.Guidance.nextAction explanation ++ " Existing text and symbols are retained."
checkpoint (V.usable saved) = "The compatible vector is saved; existing text and symbols are retained."

module Family (selection : E.Rule) (profile : W.EmbeddingKey) (chunk : ℕ)
  (desired : V.State) (profileMatches : V.profile desired ≡ profile)
  (guidance : String → D.Prompt) where
  module Cache = Coverage.Family selection profile
  owner = E.targetOwner selection
  text = V.source desired

  chosen : O.World → V.State
  chosen world with Cache.ready world text
  ... | just saved = V.usable saved
  ... | nothing = desired

  -- Published compatible cache data takes precedence over another calculation.
  choosesCompleted : ∀ world saved → Cache.ready world text ≡ just saved → chosen world ≡ V.usable saved
  choosesCompleted world saved found rewrite found = refl

  chosenMatches : ∀ world → V.profile (chosen world) ≡ profile × V.source (chosen world) ≡ text
  chosenMatches world with Cache.ready world text in found
  ... | nothing = profileMatches , refl
  ... | just saved with Cache.readySound world text saved found
  ...   | row , present , selected = Cache.completedMatches text (proj₂ row) saved selected

  StoredReady : O.World → Set
  StoredReady world = Σ ℕ (λ slot → Σ V.Value (λ saved →
    DB.lookup slot world ≡ just (O.recordOf owner (O.vector chunk (V.usable saved))) ×
    (V.Value.profile saved ≡ profile × V.Value.source saved ≡ text)))

  record Source (world : O.World) : Set where
    constructor source
    field version : ℕ
          located : DB.lookup chunk world ≡ just (O.recordOf owner (O.chunk version text))

  sourceValue : ∀ world → (value : Maybe O.Record) → DB.lookup chunk world ≡ value → Maybe (Source world)
  sourceValue world (just (O.recordOf actualOwner (O.chunk version content))) found with E.ownerEqual actualOwner owner | content String.≟ text
  ... | yes refl | yes refl = just (source version found)
  ... | _ | _ = nothing
  sourceValue world value found = nothing

  observeSource : (world : O.World) → Maybe (Source world)
  observeSource world = sourceValue world (DB.lookup chunk world) refl

  record Existing (world : O.World) : Set where
    constructor existing
    field slot : ℕ
          state : V.State
          located : DB.lookup slot world ≡ just (O.recordOf owner (O.vector chunk state))
          sameProfile : V.profile state ≡ profile
          sameText : V.source state ≡ text

  vectorValue : ∀ world slot → (value : Maybe O.Record) → DB.lookup slot world ≡ value → Maybe (Existing world)
  vectorValue world slot (just (O.recordOf actualOwner (O.vector parent state))) found with
    E.ownerEqual actualOwner owner | parent ≟ chunk | Equal.EmbeddingKey? (V.profile state) profile | V.source state String.≟ text
  ... | yes refl | yes refl | yes sameProfile | yes sameText = just (existing slot state found sameProfile sameText)
  ... | _ | _ | _ | _ = nothing
  vectorValue world slot value found = nothing

  scan : (world : O.World) → O.World → Maybe (Existing world)
  scan world [] = nothing
  scan world ((slot , ignored) ∷ rest) with vectorValue world slot (DB.lookup slot world) refl
  ... | just stored = just stored
  ... | nothing = scan world rest

  observe : (world : O.World) → Maybe (Existing world)
  observe world = scan world world

  completed : V.State → Bool
  completed (V.usable saved) = true
  completed _ = false

  value : O.World → O.Record
  value world = O.recordOf owner (O.vector chunk (chosen world))

  store : ∀ world → Maybe (Existing world) → DB.Transaction String
  store world nothing = DB.put (Allocation.freshId world) (value world) (DB.commit (checkpoint (chosen world)))
  store world (just current) with completed (Existing.state current)
  ... | true = DB.commit (checkpoint (Existing.state current))
  ... | false = DB.put (Existing.slot current) (value world) (DB.commit (checkpoint (chosen world)))

  snapshot : ∀ world → Maybe (Source world) → DB.Transaction String
  snapshot world nothing = DB.abort "The source chunk changed. Continue from the current text before preparing its vectors."
  snapshot world (just current) = store world (observe world)

  transaction : DB.Transaction String
  transaction = DB.scan (λ world → snapshot world (observeSource world))

  storeFrame : ∀ world current result after → DB.evaluate (store world current) world ≡ DB.committed result after → L.ReceiptFrame world after
  storeFrame world nothing result after committed with committed
  ... | refl = Fresh.freshFrame world (Allocation.freshId world) (value world) (Allocation.fresh world) (λ ())
  storeFrame world (just current) result after committed with completed (Existing.state current)
  ... | true with committed
  ...   | refl = λ key recordOwner receipt → (λ present → present) , (λ present → present)
  storeFrame world (just current) result after committed | false with committed
  ... | refl = Frames.writeFrame world (Existing.slot current)
    (O.recordOf owner (O.vector chunk (Existing.state current))) (value world) (Existing.located current) (λ ()) (λ ())

  isolates : ∀ before result after → DB.evaluate transaction before ≡ DB.committed result after → L.ReceiptFrame before after
  isolates before result after committed with observeSource before
  ... | nothing with committed
  ...   | ()
  isolates before result after committed | just current = storeFrame before (observe before) result after committed

  effect : L.Effect
  effect = record { transaction = transaction; guidance = guidance; isolates = isolates }

  writtenReady : ∀ before slot saved → chosen before ≡ V.usable saved → StoredReady (DB.write slot (value before) before)
  writtenReady before slot saved chosenReady = slot , saved ,
    trans (DB.writeVisible slot (value before) before)
      (cong (λ state → just (O.recordOf owner (O.vector chunk state))) chosenReady) ,
    (trans (sym (cong V.profile chosenReady)) (proj₁ (chosenMatches before)) ,
     trans (sym (cong V.source chosenReady)) (proj₂ (chosenMatches before)))

  -- Every storage branch preserves the source chunk, postings and symbols.
  -- Existing usable vectors are immutable, including when later work waits.
  module Current (before : O.World) (valid : O.Admissible before) (source : Source before)
    (observed : observeSource before ≡ just source) where
    resolved : O.Resolves before owner (O.reference chunk O.chunkK)
    resolved = record { value = O.recordOf owner (O.chunk (Source.version source) text)
      ; found = Source.located source; rightKind = refl; rightOwner = O.own }

    storeValid : ∀ current → O.Admissible (proj₂ (DB.execute (store before current) before))
    storeValid nothing = Insert.insertAdmissible before (Allocation.freshId before) (value before) valid (Allocation.fresh before)
      O.local (resolved All.∷ All.[]) (refl All.∷ All.[])
    storeValid (just current) with completed (Existing.state current)
    ... | true = valid
    ... | false = Storage.writeAdmissible before (Existing.slot current)
      (O.recordOf owner (O.vector chunk (Existing.state current))) (value before) valid (Existing.located current)
      refl refl O.local (λ ref included → included)

    afterValid : O.Admissible (proj₂ (DB.execute transaction before))
    afterValid rewrite observed = storeValid (observe before)

    storeRetains : ∀ current key saved → DB.lookup key before ≡ just saved → O.kind (O.body saved) ≢ O.vectorK →
      DB.lookup key (proj₂ (DB.execute (store before current) before)) ≡ just saved
    storeRetains nothing key saved found nonVector = Insert.oldLookup before (Allocation.freshId before)
      (value before) (Allocation.fresh before) key saved found
    storeRetains (just current) key saved found nonVector with completed (Existing.state current)
    ... | true = found
    ... | false = trans (DB.writePreservesOther (Existing.slot current) key (value before) before different) found
      where
      different : Existing.slot current ≢ key
      different refl = nonVector (sym (cong (λ row → O.kind (O.body row))
        (just-injective (trans (sym (Existing.located current)) found))))

    retainsTextAndSymbols : ∀ key saved → DB.lookup key before ≡ just saved → O.kind (O.body saved) ≢ O.vectorK →
      DB.lookup key (proj₂ (DB.execute transaction before)) ≡ just saved
    retainsTextAndSymbols key saved found nonVector rewrite observed = storeRetains (observe before) key saved found nonVector

    storeReady : ∀ current saved → chosen before ≡ V.usable saved →
      StoredReady (proj₂ (DB.execute (store before current) before))
    storeReady nothing saved selected = writtenReady before (Allocation.freshId before) saved selected
    storeReady (just (existing slot (V.usable completedValue) located sameProfile sameText)) saved selected =
      slot , completedValue , located , sameProfile , sameText
    storeReady (just (existing slot (V.pending storedProfile storedText) located sameProfile sameText)) saved selected =
      writtenReady before slot saved selected
    storeReady (just (existing slot (V.waiting storedProfile storedText why) located sameProfile sameText)) saved selected =
      writtenReady before slot saved selected

    committedStore : ∀ current → DB.evaluate (store before current) before ≡ DB.committed
      (proj₁ (DB.execute (store before current) before)) (proj₂ (DB.execute (store before current) before))
    committedStore nothing = refl
    committedStore (just current) with completed (Existing.state current)
    ... | true = refl
    ... | false = refl

    result = proj₁ (DB.execute (store before (observe before)) before)
    changed = proj₂ (DB.execute (store before (observe before)) before)

    performs : DB.evaluate transaction before ≡ DB.committed result changed
    performs rewrite observed = committedStore (observe before)

    module Run (id : I.OperationId) (input : N.Meaning) (named : R.Names id input)
      (receiptSlot : ℕ) (progress : R.Work)
      (accepted : L.find id before ≡ just (L.found receiptSlot owner (R.active input named progress)))
      (receiptAt : DB.lookup receiptSlot before ≡ just (L.recordAt {id = id} owner (R.active input named progress)))
      (familySlot workSlot generation policyPointer policyVersion : ℕ)
      (permission : Control.Worker.allowed (E.family selection) familySlot workSlot id generation before ≡ true)
      (currentPolicy : Publication.PolicyGuard.At owner policyPointer policyVersion before) where
      module Worker = Control.Worker (E.family selection) familySlot workSlot id generation
      module Guard = Publication.PolicyGuard owner policyPointer policyVersion
      waiting = "Indexing is paused or the saved work or policy changed. Continue from the current checkpoint."
      guarded = Guard.effect (Worker.effect effect waiting) waiting
      guardedPerforms : DB.evaluate (L.Effect.transaction guarded) before ≡ DB.committed result changed
      guardedPerforms = trans
        (Guard.ready (L.Effect.transaction (Worker.effect effect waiting)) waiting before
          (Guard.foundAt before currentPolicy) (proj₂ currentPolicy))
        (trans (Worker.ready transaction waiting before permission) performs)
      changedValid : O.Admissible changed
      changedValid = storeValid (observe before)
      module Saved = Checkpoint.Run id input named owner receiptSlot progress result guarded before changed
        changedValid accepted receiptAt guardedPerforms

      keepsPublishedText : ∀ key dataRow → DB.lookup key before ≡ just dataRow →
        O.kind (O.body dataRow) ≢ O.vectorK → O.kind (O.body dataRow) ≢ O.receiptK →
        DB.lookup key Saved.after ≡ just dataRow
      keepsPublishedText key dataRow found nonVector nonReceipt = Saved.preservesData key dataRow
        (storeRetains (observe before) key dataRow found nonVector) nonReceipt

      readyAfterSeal : ∀ saved → chosen before ≡ V.usable saved → Cache.availability Saved.after chunk text ≡ Coverage.usable
      readyAfterSeal saved selected with storeReady (observe before) saved selected
      ... | slot , prepared , located , sameProfile , sameText = Cache.storedVectorIsReported Saved.after slot chunk text prepared
        (Saved.preservesData slot (O.recordOf owner (O.vector chunk (V.usable prepared))) located (λ ())) sameProfile sameText
