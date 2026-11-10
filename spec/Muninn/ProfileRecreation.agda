{-# OPTIONS --safe #-}
-- Atomic derived-data removal and new profile publication under one receipt.
module Muninn.ProfileRecreation where
import Muninn.OwnedState as O
import Muninn.RecreationStore as Purge
import Muninn.StoredPolicy as Policy
import Muninn.Config as C
import Muninn.CatalogInputs as I
import Muninn.RequestIdentity as N
import Muninn.ReceiptTypes as R
import Muninn.ReceiptLedger as L
import Muninn.IdentityCheckpoint as Checkpoint
import Muninn.ExclusionOutcomes as E
import Muninn.ArtifactIdentity as Equal
import Muninn.RecordAllocation as Allocation
import Muninn.CleanupAdmissionStorage as Insert
import Muninn.CleanupStorage as Storage
import Muninn.CleanupOrder as Order
import Muninn.CleanupObservations as Observations
import Muninn.RegistryCreation as Fresh
import Muninn.ViewPublication as Compose
import Muninn.RetirementControl as Frames
import Muninn.Dialogue as D
import Muninn.ContentPublication as Publication
open import Data.Nat using (ℕ; suc; _≟_)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.String using (String)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
module DB = O.DB

falseNotTrue : false ≢ true
falseNotTrue ()

checkpoint : String
checkpoint = "The old derived index is removed and the replacement profile is saved. Reindexing and note-vector preparation remain active; repository identity, note text and other settings are preserved."

-- The reservation law preserves immutable incarnation identity even though
-- recreation removes records before inserting the new policy version.
reservedSubset : ∀ rows before → (∀ row → row ∈ rows → row ∈ before) →
  ∀ key → key ∈ Insert.reserved rows → key ∈ Insert.reserved before
reservedSubset [] before subset key ()
reservedSubset ((slot , value) ∷ rows) before subset .slot (here refl) = Insert.rowReserved before slot value (subset (slot , value) (here refl))
reservedSubset ((slot , value) ∷ rows) before subset key (there present) with ∈-++⁻ (Insert.weakIds (O.body value)) present
... | inj₁ tracked = Insert.weakReserved before slot value key (subset (slot , value) (here refl)) tracked
... | inj₂ later = reservedSubset rows before (λ row member → subset row (there member)) key later

module Family (family pointer expectedVersion : ℕ) (requestInput : I.IntentInput I.recreateIndex)
  (guidance : String → D.Prompt) where
  module Rows = Purge.Family family
  module Saved = Policy.Family family pointer
  owner = O.family family
  replacement = proj₂ (I.Mutation.input requestInput)
  target = proj₁ (I.Mutation.input requestInput)

  info : ∀ {world} → Saved.Saved world → O.PolicyVersionInfo
  info current = record (Saved.Saved.info current)
    { revision = suc (O.PolicyVersionInfo.revision (Saved.Saved.info current))
    ; contents = record (O.PolicyVersionInfo.contents (Saved.Saved.info current)) { embeddings = replacement } }
  row : ∀ {world} → Saved.Saved world → O.Record
  row current = O.recordOf owner (O.policyVersion (Saved.Saved.defaultsSlot current) (info current))
  slot : O.World → ℕ
  slot = Allocation.freshId
  inserted : ∀ world → Saved.Saved world → O.World
  inserted world current = DB.write (slot world) (row current) (Rows.final world)
  newPointer : O.World → O.Record
  newPointer world = O.recordOf owner (O.currentPolicy (slot world))
  changed : ∀ world → Saved.Saved world → O.World
  changed world current = DB.write pointer (newPointer world) (inserted world current)

  writes : ∀ world → Saved.Saved world → DB.Transaction String
  writes world current = Rows.compile world
    (DB.put (slot world) (row current) (DB.put pointer (newPointer world) (DB.commit checkpoint)))
  expected : ∀ {world} → Saved.Saved world → Bool
  expected current with expectedVersion ≟ Saved.Saved.version current
  ... | yes same with Equal.FamilyId? (I.FamilyTarget.expectedFamily target) (O.PolicyVersionInfo.familyId (Saved.Saved.info current))
  ...   | yes sameFamily = true
  ...   | no different = false
  expected current | no different = false

  withCurrent : ∀ world → Maybe (Saved.Saved world) → DB.Transaction String
  withCurrent world nothing = DB.abort "I cannot identify the current repository policy. Send the repository context again before recreating its index."
  withCurrent world (just current) with expected current
  ... | false = DB.abort "The repository or policy changed. Inspect the current policy and continue this request before recreating its index."
  ... | true with Purge.unique? world
  ...   | no invalid = DB.abort "The saved record identities are inconsistent. Repair the database identities before continuing; no data was changed."
  ...   | yes valid with Rows.ready world | E.pendingRemovalFor owner world
  ...     | false | _ = DB.abort "Earlier work still uses derived index records. Let that work finish, or cancel it, then continue this request. Note text and settings are unchanged."
  ...     | true | true = DB.abort "Repository removal is already active. Continue that request before changing the embedding profile."
  ...     | true | false = writes world current

  transaction : DB.Transaction String
  transaction = DB.scan (λ world → withCurrent world (Saved.observe world))
  writesResult : ∀ world current → DB.evaluate (writes world current) world ≡ DB.committed checkpoint (changed world current)
  writesResult world current = Rows.performs world world _

  pointerAfterPurge : (world : O.World) (current : Saved.Saved world) → O.Unique world →
    DB.lookup pointer (Rows.final world) ≡ just (O.recordOf owner (O.currentPolicy (Saved.Saved.version current)))
  pointerAfterPurge world current valid = Rows.retained world pointer _ valid (Saved.Saved.pointerAt current) (Rows.metadataKept (O.recordOf owner (O.currentPolicy (Saved.Saved.version current))) refl)
  purgedSubset : ∀ world → O.Unique world → ∀ row → row ∈ Rows.final world → row ∈ world
  purgedSubset world valid row present = Observations.lookupMember world (proj₁ row) (proj₂ row)
    (Rows.Source.found (Rows.sourceOf world _ _ valid
      (Order.memberLookup (Rows.final world) _ _ (Rows.runUnique world world valid) present)))
  freshAfterPurge : ∀ world → O.Unique world → Insert.Fresh (Rows.final world) (slot world)
  freshAfterPurge world valid present = Allocation.fresh world (reservedSubset (Rows.final world) world (purgedSubset world valid) (slot world) present)
  frames : ∀ world current → O.Unique world → L.ReceiptFrame world (changed world current)
  frames world current valid = Compose.composeFrames world (Rows.final world) (changed world current) (Rows.receiptFrame world valid)
    (Compose.composeFrames (Rows.final world) (inserted world current) (changed world current)
      (Fresh.freshFrame (Rows.final world) (slot world) (row current) (freshAfterPurge world valid) (λ ()))
      (Frames.writeFrame (inserted world current) pointer (O.recordOf owner (O.currentPolicy (Saved.Saved.version current))) (newPointer world)
        (Insert.oldLookup (Rows.final world) (slot world) (row current) (freshAfterPurge world valid) pointer _ (pointerAfterPurge world current valid)) (λ ()) (λ ())))

  isolatesCurrent : ∀ world current result after → DB.evaluate (withCurrent world current) world ≡ DB.committed result after → L.ReceiptFrame world after
  isolatesCurrent world nothing result after ()
  isolatesCurrent world (just current) result after committed with expected current
  ... | false with committed
  ...   | ()
  isolatesCurrent world (just current) result after committed | true with Purge.unique? world
  ... | no invalid with committed
  ...   | ()
  isolatesCurrent world (just current) result after committed | true | yes valid with Rows.ready world | E.pendingRemovalFor owner world
  ... | false | _ with committed
  ...   | ()
  isolatesCurrent world (just current) result after committed | true | yes valid | true | true with committed
  ... | ()
  isolatesCurrent world (just current) result after committed | true | yes valid | true | false
    rewrite writesResult world current with committed
  ... | refl = frames world current valid
  effect : L.Effect
  effect = record { transaction = transaction; guidance = guidance
    ; isolates = λ before result after committed → isolatesCurrent before (Saved.observe before) result after committed }

  module Current (before : O.World) (valid : O.Admissible before) (current : Saved.Saved before)
    (observed : Saved.observe before ≡ just current) (matching : expected current ≡ true)
    (released : Rows.ready before ≡ true) (notRemoving : E.pendingRemovalFor owner before ≡ false) where
    module Purged = Rows.Valid before valid released
    unique = O.Admissible.unique valid
    purged = Rows.final before
    withVersion = inserted before current
    after = changed before current
    newSlot = slot before
    newRow = row current
    oldPointer = O.recordOf owner (O.currentPolicy (Saved.Saved.version current))
    pointerRow = newPointer before
    fresh = freshAfterPurge before unique
    keeps : ∀ key value → DB.lookup key before ≡ just value → Rows.keep value ≡ true → key ≢ pointer → DB.lookup key after ≡ just value
    keeps key value found retained distinct = trans (DB.writePreservesOther pointer key pointerRow withVersion (λ same → distinct (sym same)))
      (Insert.oldLookup purged newSlot newRow fresh key value (Rows.retained before key value unique found retained))

    defaultsFound : DB.lookup (Saved.Saved.defaultsSlot current) purged ≡ just (O.recordOf owner (O.defaults (Saved.Saved.frozen current)))
    defaultsFound = Rows.retained before _ _ unique (Saved.Saved.defaultsAt current) (Rows.metadataKept (O.recordOf owner (O.defaults (Saved.Saved.frozen current))) refl)
    defaultsResolved : O.Resolves purged owner (O.reference (Saved.Saved.defaultsSlot current) O.defaultsK)
    defaultsResolved = record { value = O.recordOf owner (O.defaults (Saved.Saved.frozen current)); found = defaultsFound; rightKind = refl; rightOwner = O.own }
    versionValid : O.Admissible withVersion
    versionValid = Insert.insertAdmissible purged newSlot newRow Purged.admissible fresh O.local (defaultsResolved All.∷ All.[]) (refl All.∷ All.[])
    pointerLocated : DB.lookup pointer withVersion ≡ just oldPointer
    pointerLocated = Insert.oldLookup purged newSlot newRow fresh pointer oldPointer (pointerAfterPurge before current unique)
    versionResolved : O.Resolves withVersion owner (O.reference newSlot O.policyVersionK)
    versionResolved = record { value = newRow; found = DB.writeVisible newSlot newRow purged; rightKind = refl; rightOwner = O.own }
    afterValid : O.Admissible after
    afterValid = Storage.writeResolvedAdmissible withVersion pointer oldPointer pointerRow versionValid pointerLocated refl refl O.local
      (versionResolved All.∷ All.[]) (refl All.∷ All.[])
    performs : DB.evaluate transaction before ≡ DB.committed checkpoint after
    performs rewrite observed | matching with Purge.unique? before
    ... | no invalid = ⊥-elim (invalid unique)
    ... | yes sameUnique rewrite released | notRemoving = writesResult before current

    absent : ∀ key body → DB.lookup key before ≡ just (O.recordOf owner body) → Purge.derived (O.kind body) ≡ true → DB.lookup key after ≡ nothing
    absent key body found dataRow = trans
      (DB.writePreservesOther pointer key pointerRow withVersion pointerDifferent)
      (trans (DB.writePreservesOther newSlot key newRow purged freshDifferent) (Rows.removed before key body unique found dataRow))
      where
      pointerDifferent : pointer ≢ key
      pointerDifferent refl with trans (sym (Saved.Saved.pointerAt current)) found
      ... | refl = falseNotTrue dataRow
      freshDifferent : newSlot ≢ key
      freshDifferent refl = Allocation.fresh before (Insert.storedReserved before key _ found)

    pointerVisible : DB.lookup pointer after ≡ just pointerRow
    pointerVisible = DB.writeVisible pointer pointerRow withVersion
    pointerDifferentFromVersion : pointer ≢ newSlot
    pointerDifferentFromVersion refl = Allocation.fresh before
      (Insert.storedReserved before pointer oldPointer (Saved.Saved.pointerAt current))
    versionVisible : DB.lookup newSlot after ≡ just newRow
    versionVisible = trans (DB.writePreservesOther pointer newSlot pointerRow withVersion pointerDifferentFromVersion)
      (DB.writeVisible newSlot newRow purged)
    defaultsDifferent : Saved.Saved.defaultsSlot current ≢ pointer
    defaultsDifferent refl with trans (sym (Saved.Saved.defaultsAt current)) (Saved.Saved.pointerAt current)
    ... | ()
    defaultsVisible : DB.lookup (Saved.Saved.defaultsSlot current) after ≡ just (O.recordOf owner (O.defaults (Saved.Saved.frozen current)))
    defaultsVisible = keeps _ _ (Saved.Saved.defaultsAt current) (Rows.metadataKept (O.recordOf owner (O.defaults (Saved.Saved.frozen current))) refl) defaultsDifferent
    selectedPolicy : Saved.selectedPolicy after ≡ just (Policy.policyFrom (info current) (Saved.Saved.frozen current))
    selectedPolicy = Saved.selectsKnown after newSlot (Saved.Saved.defaultsSlot current) (info current) (Saved.Saved.frozen current)
      pointerVisible versionVisible defaultsVisible
    requestedProfile : C.FamilyPolicy.embeddings (Policy.policyFrom (info current) (Saved.Saved.frozen current)) ≡ replacement
    requestedProfile = refl
    otherSettings :
      C.FamilyPolicy.family (Policy.policyFrom (info current) (Saved.Saved.frozen current)) ≡ C.FamilyPolicy.family (Saved.policy current) ×
      (C.FamilyPolicy.name (Policy.policyFrom (info current) (Saved.Saved.frozen current)) ≡ C.FamilyPolicy.name (Saved.policy current) ×
      (C.FamilyPolicy.index (Policy.policyFrom (info current) (Saved.Saved.frozen current)) ≡ C.FamilyPolicy.index (Saved.policy current) ×
      (C.FamilyPolicy.watcher (Policy.policyFrom (info current) (Saved.Saved.frozen current)) ≡ C.FamilyPolicy.watcher (Saved.policy current) ×
       C.FamilyPolicy.defaults (Policy.policyFrom (info current) (Saved.Saved.frozen current)) ≡ C.FamilyPolicy.defaults (Saved.policy current))))
    otherSettings = refl , refl , refl , refl , refl

    noDerived : ∀ key body → Purge.derived (O.kind body) ≡ true → DB.lookup key after ≢ just (O.recordOf owner body)
    noDerived key body dataRow found with pointer ≟ key
    ... | yes refl with just-injective (trans (sym pointerVisible) found)
    ...   | refl = falseNotTrue dataRow
    noDerived key body dataRow found | no pointerOther with newSlot ≟ key
    ... | yes refl with just-injective (trans (sym versionVisible) found)
    ...   | refl = falseNotTrue dataRow
    noDerived key body dataRow found | no pointerOther | no versionOther = impossible
      (trans (sym (Rows.localDropped body dataRow)) (Rows.Source.kept source))
      where
      original : DB.lookup key purged ≡ just (O.recordOf owner body)
      original = trans (sym (trans (DB.writePreservesOther pointer key pointerRow withVersion pointerOther)
        (DB.writePreservesOther newSlot key newRow purged versionOther))) found
      source = Rows.sourceOf before key (O.recordOf owner body) unique original
      impossible : false ≢ true
      impossible ()

    module Run (receiptSlot : ℕ) (progress : R.Work)
      (accepted : L.find (I.Mutation.operationId requestInput) before ≡ just (L.found receiptSlot owner
        (R.active (N.mutation N.kRecreateIndex requestInput) refl progress)))
      (receiptAt : DB.lookup receiptSlot before ≡ just (L.recordAt owner (R.active (N.mutation N.kRecreateIndex requestInput) refl progress))) where
      id = I.Mutation.operationId requestInput
      input = N.mutation N.kRecreateIndex requestInput
      module SavedRequest = Checkpoint.Run id input refl owner receiptSlot progress checkpoint effect before after afterValid accepted receiptAt performs

      protected : ∀ key value → DB.lookup key before ≡ just value → Purge.derived (O.kind (O.body value)) ≡ false →
        O.kind (O.body value) ≢ O.currentPolicyK → O.kind (O.body value) ≢ O.receiptK → DB.lookup key SavedRequest.after ≡ just value
      protected key value found metadata nonPointer nonReceipt = SavedRequest.preservesData key value
        (keeps key value found (Rows.metadataKept value metadata) different) nonReceipt
        where
        different : key ≢ pointer
        different refl = nonPointer (cong (λ value → O.kind (O.body value)) (just-injective (trans (sym found) (Saved.Saved.pointerAt current))))

      -- No pre-recreation code/vector incarnation can survive the receipt seal.
      derivedAbsent : ∀ key body → DB.lookup key before ≡ just (O.recordOf owner body) → Purge.derived (O.kind body) ≡ true → DB.lookup key SavedRequest.after ≡ nothing
      derivedAbsent key body found dataRow = trans (DB.writePreservesOther receiptSlot key SavedRequest.newReceipt after receiptDifferent) (absent key body found dataRow)
        where
        receiptDifferent : receiptSlot ≢ key
        receiptDifferent refl with trans (sym receiptAt) found
        ... | refl = falseNotTrue dataRow

      pointerAfterSeal : DB.lookup pointer SavedRequest.after ≡ just pointerRow
      pointerAfterSeal = SavedRequest.preservesData pointer pointerRow pointerVisible (λ ())
      versionAfterSeal : DB.lookup newSlot SavedRequest.after ≡ just newRow
      versionAfterSeal = SavedRequest.preservesData newSlot newRow versionVisible (λ ())
      defaultsAfterSeal : DB.lookup (Saved.Saved.defaultsSlot current) SavedRequest.after ≡ just (O.recordOf owner (O.defaults (Saved.Saved.frozen current)))
      defaultsAfterSeal = SavedRequest.preservesData (Saved.Saved.defaultsSlot current)
        (O.recordOf owner (O.defaults (Saved.Saved.frozen current))) defaultsVisible (λ ())
      selectedAfterSeal : Saved.selectedPolicy SavedRequest.after ≡ just (Policy.policyFrom (info current) (Saved.Saved.frozen current))
      selectedAfterSeal = Saved.selectsKnown SavedRequest.after newSlot (Saved.Saved.defaultsSlot current) (info current) (Saved.Saved.frozen current)
        pointerAfterSeal versionAfterSeal defaultsAfterSeal
      noDerivedAfterSeal : ∀ key body → Purge.derived (O.kind body) ≡ true → DB.lookup key SavedRequest.after ≢ just (O.recordOf owner body)
      noDerivedAfterSeal key body dataRow found with receiptSlot ≟ key
      ... | yes refl with just-injective (trans (sym (DB.writeVisible receiptSlot SavedRequest.newReceipt after)) found)
      ...   | refl = falseNotTrue dataRow
      noDerivedAfterSeal key body dataRow found | no other = noDerived key body dataRow
        (trans (sym (DB.writePreservesOther receiptSlot key SavedRequest.newReceipt after other)) found)

      notePreserved : ∀ key text → DB.lookup key before ≡ just (O.recordOf owner (O.note text)) → DB.lookup key SavedRequest.after ≡ just (O.recordOf owner (O.note text))
      notePreserved key text found = protected key _ found refl (λ ()) (λ ())
      interruptedNotePreserved : ∀ key text observed → DB.lookup key before ≡ just (O.recordOf owner (O.note text)) →
        O.Execution.Interrupted (O.Execution.atomic SavedRequest.request O.Execution.done) before observed →
        DB.lookup key observed ≡ just (O.recordOf owner (O.note text))
      interruptedNotePreserved key text observed found interrupted with SavedRequest.boundary observed interrupted
      ... | inj₁ same rewrite same = found
      ... | inj₂ same rewrite same = notePreserved key text found

      otherOwners : ∀ key value → DB.lookup key before ≡ just value → O.owner value ≢ owner → DB.lookup key SavedRequest.after ≡ just value
      otherOwners key value found foreign = trans
        (DB.writePreservesOther receiptSlot key SavedRequest.newReceipt after receiptDifferent)
        (keeps key value found (Rows.foreignKept value foreign) pointerDifferent)
        where
        pointerDifferent : key ≢ pointer
        pointerDifferent refl = foreign (cong O.owner (just-injective (trans (sym found) (Saved.Saved.pointerAt current))))
        receiptDifferent : receiptSlot ≢ key
        receiptDifferent refl = foreign (sym (cong O.owner (just-injective (trans (sym receiptAt) found))))

      oldVersionDistinct : newSlot ≢ Saved.Saved.version current
      oldVersionDistinct refl = Allocation.fresh before (Insert.storedReserved before _ _ (Saved.Saved.versionAt current))
      -- Both code and note publication must use this same current-policy gate.
      -- A late callback for the old policy cannot republish an old vector.
      oldCallbackBlocked : ∀ {A : Set} (body : DB.Transaction A) waiting →
        DB.evaluate (Publication.PolicyGuard.transaction owner pointer (Saved.Saved.version current) body waiting) SavedRequest.after ≡ DB.aborted waiting
      oldCallbackBlocked body waiting with Publication.PolicyGuard.at? owner pointer (Saved.Saved.version current) SavedRequest.after
      ... | no stale = refl
      ... | yes allowed = ⊥-elim (oldVersionDistinct
        (pointerVersion (just-injective (trans (sym pointerAfterSeal)
          (Publication.PolicyGuard.foundAt owner pointer (Saved.Saved.version current) SavedRequest.after allowed)))))
        where
        pointerVersion : ∀ {first second} → O.recordOf owner (O.currentPolicy first) ≡ O.recordOf owner (O.currentPolicy second) → first ≡ second
        pointerVersion refl = refl
