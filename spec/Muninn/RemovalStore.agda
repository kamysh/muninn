{-# OPTIONS --safe #-}
-- Fixed complete-world removal policy and finite concrete DB transaction.
module Muninn.RemovalStore where
import Muninn.OwnedState as O
import Muninn.CatalogInputs as I
import Muninn.ExclusionOutcomes as E
import Muninn.ReceiptTypes as R
import Muninn.ReceiptLedger as Ledger
import Muninn.CleanupStorage as Storage
import Muninn.CleanupOrder as Order
open import Data.Nat using (ℕ; _≟_)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Data.String using (String)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
module DB = O.DB

data Scope : Set where unregister forget : Scope

-- Exhaustive policy: adding an owned kind requires deciding its removal scope.
settingsOrNotes : O.Kind → Bool
settingsOrNotes O.registrationK = false
settingsOrNotes O.checkoutK = false
settingsOrNotes O.creationIntentK = true
settingsOrNotes O.defaultsK = true
settingsOrNotes O.policyVersionK = true
settingsOrNotes O.currentPolicyK = true
settingsOrNotes O.noteK = true
settingsOrNotes O.notePostingK = true
settingsOrNotes O.noteVectorK = true
settingsOrNotes O.fileVersionK = false
settingsOrNotes O.baseBindingK = false
settingsOrNotes O.deltaBindingK = false
settingsOrNotes O.basePointerK = false
settingsOrNotes O.chunkK = false
settingsOrNotes O.postingK = false
settingsOrNotes O.vectorK = false
settingsOrNotes O.symbolK = false
settingsOrNotes O.edgeK = false
settingsOrNotes O.structuralSnapshotK = false
settingsOrNotes O.publishedViewK = false
settingsOrNotes O.legacyK = false
settingsOrNotes O.stagingK = false
settingsOrNotes O.acceptedWorkK = false
settingsOrNotes O.cleanupWorkK = false
settingsOrNotes O.activeReaderK = false
settingsOrNotes O.continuationK = false
settingsOrNotes O.receiptK = false
settingsOrNotes O.graphResourceK = false
settingsOrNotes O.migrationK = false
settingsOrNotes O.usageK = false
settingsOrNotes O.bootstrapK = false
settingsOrNotes O.modelCacheK = false
settingsOrNotes O.coordinationK = false
settingsOrNotes O.schemaResourceK = false
settingsOrNotes O.logFileK = false
settingsOrNotes O.bootstrapStageK = false

data Action : Set where
  keep erase : Action
  compact : I.OperationId → Action

localActionFor : Scope → O.Body → Action
localActionFor scope (O.receipt (R.entry id state)) = compact id
localActionFor scope value with scope
... | forget = erase
... | unregister with settingsOrNotes (O.kind value)
...   | true = keep
...   | false = erase

localMetadata : ∀ body → settingsOrNotes (O.kind body) ≡ true → localActionFor unregister body ≡ keep
localMetadata (O.registration _) ()
localMetadata (O.checkout _) ()
localMetadata (O.creationIntent _) valid = refl
localMetadata (O.defaults _) valid = refl
localMetadata (O.policyVersion _ _) valid = refl
localMetadata (O.currentPolicy _) valid = refl
localMetadata (O.note _) valid = refl
localMetadata (O.notePosting _ _) valid = refl
localMetadata (O.noteVector _ _) valid = refl
localMetadata (O.fileVersion _) ()
localMetadata (O.baseBinding _ _ _) ()
localMetadata (O.deltaBinding _ _ _ _) ()
localMetadata (O.basePointer _) ()
localMetadata (O.chunk _ _) ()
localMetadata (O.posting _ _) ()
localMetadata (O.vector _ _) ()
localMetadata (O.symbol _ _ _) ()
localMetadata (O.edge _ _ _) ()
localMetadata (O.publishedView _ _) ()
localMetadata (O.structuralSnapshot _ _ _ _) ()
localMetadata (O.legacy _ _ _) ()
localMetadata (O.staging _ _) ()
localMetadata (O.acceptedWork _ _) ()
localMetadata (O.cleanupWork _ _ _) ()
localMetadata (O.activeReader _ _) ()
localMetadata (O.continuation _ _) ()
localMetadata (O.receipt _) ()
localMetadata (O.migration _) ()
localMetadata (O.usage _) ()
localMetadata (O.bootstrap _) ()
localMetadata (O.modelCache _) ()
localMetadata (O.coordination _) ()
localMetadata (O.schemaResource _) ()
localMetadata (O.graphResource _ _ _) ()
localMetadata (O.logFile _) ()
localMetadata (O.bootstrapStage _) ()

localKeepMetadata : ∀ scope body → localActionFor scope body ≡ keep → scope ≡ unregister × settingsOrNotes (O.kind body) ≡ true
localKeepMetadata forget (O.registration _) ()
localKeepMetadata unregister (O.registration _) ()
localKeepMetadata forget (O.checkout _) ()
localKeepMetadata unregister (O.checkout _) ()
localKeepMetadata forget (O.creationIntent _) ()
localKeepMetadata unregister (O.creationIntent _) chosen = refl , refl
localKeepMetadata forget (O.defaults _) ()
localKeepMetadata unregister (O.defaults _) chosen = refl , refl
localKeepMetadata forget (O.policyVersion _ _) ()
localKeepMetadata unregister (O.policyVersion _ _) chosen = refl , refl
localKeepMetadata forget (O.currentPolicy _) ()
localKeepMetadata unregister (O.currentPolicy _) chosen = refl , refl
localKeepMetadata forget (O.note _) ()
localKeepMetadata unregister (O.note _) chosen = refl , refl
localKeepMetadata forget (O.notePosting _ _) ()
localKeepMetadata unregister (O.notePosting _ _) chosen = refl , refl
localKeepMetadata forget (O.noteVector _ _) ()
localKeepMetadata unregister (O.noteVector _ _) chosen = refl , refl
localKeepMetadata forget (O.fileVersion _) ()
localKeepMetadata unregister (O.fileVersion _) ()
localKeepMetadata forget (O.baseBinding _ _ _) ()
localKeepMetadata unregister (O.baseBinding _ _ _) ()
localKeepMetadata forget (O.deltaBinding _ _ _ _) ()
localKeepMetadata unregister (O.deltaBinding _ _ _ _) ()
localKeepMetadata forget (O.basePointer _) ()
localKeepMetadata unregister (O.basePointer _) ()
localKeepMetadata forget (O.chunk _ _) ()
localKeepMetadata unregister (O.chunk _ _) ()
localKeepMetadata forget (O.posting _ _) ()
localKeepMetadata unregister (O.posting _ _) ()
localKeepMetadata forget (O.vector _ _) ()
localKeepMetadata unregister (O.vector _ _) ()
localKeepMetadata forget (O.symbol _ _ _) ()
localKeepMetadata unregister (O.symbol _ _ _) ()
localKeepMetadata forget (O.edge _ _ _) ()
localKeepMetadata unregister (O.edge _ _ _) ()
localKeepMetadata forget (O.publishedView _ _) ()
localKeepMetadata unregister (O.publishedView _ _) ()
localKeepMetadata forget (O.structuralSnapshot _ _ _ _) ()
localKeepMetadata unregister (O.structuralSnapshot _ _ _ _) ()
localKeepMetadata forget (O.legacy _ _ _) ()
localKeepMetadata unregister (O.legacy _ _ _) ()
localKeepMetadata forget (O.staging _ _) ()
localKeepMetadata unregister (O.staging _ _) ()
localKeepMetadata forget (O.acceptedWork _ _) ()
localKeepMetadata unregister (O.acceptedWork _ _) ()
localKeepMetadata forget (O.cleanupWork _ _ _) ()
localKeepMetadata unregister (O.cleanupWork _ _ _) ()
localKeepMetadata forget (O.activeReader _ _) ()
localKeepMetadata unregister (O.activeReader _ _) ()
localKeepMetadata forget (O.continuation _ _) ()
localKeepMetadata unregister (O.continuation _ _) ()
localKeepMetadata scope (O.receipt _) ()
localKeepMetadata forget (O.migration _) ()
localKeepMetadata unregister (O.migration _) ()
localKeepMetadata forget (O.usage _) ()
localKeepMetadata unregister (O.usage _) ()
localKeepMetadata forget (O.bootstrap _) ()
localKeepMetadata unregister (O.bootstrap _) ()
localKeepMetadata forget (O.modelCache _) ()
localKeepMetadata unregister (O.modelCache _) ()
localKeepMetadata forget (O.coordination _) ()
localKeepMetadata unregister (O.coordination _) ()
localKeepMetadata forget (O.schemaResource _) ()
localKeepMetadata unregister (O.schemaResource _) ()
localKeepMetadata forget (O.graphResource _ _ _) ()
localKeepMetadata unregister (O.graphResource _ _ _) ()
localKeepMetadata forget (O.logFile _) ()
localKeepMetadata unregister (O.logFile _) ()
localKeepMetadata forget (O.bootstrapStage _) ()
localKeepMetadata unregister (O.bootstrapStage _) ()

metadataReferences : ∀ body → settingsOrNotes (O.kind body) ≡ true → ∀ ref → ref ∈ O.references body → settingsOrNotes (O.expected ref) ≡ true
metadataReferences (O.registration _) ()
metadataReferences (O.checkout _) ()
metadataReferences (O.creationIntent _) valid ref ()
metadataReferences (O.defaults _) valid ref ()
metadataReferences (O.policyVersion value _) valid ._ (here refl) = refl
metadataReferences (O.policyVersion value _) valid ref (there ())
metadataReferences (O.currentPolicy value) valid ._ (here refl) = refl
metadataReferences (O.currentPolicy value) valid ref (there ())
metadataReferences (O.note _) valid ref ()
metadataReferences (O.notePosting value _) valid ._ (here refl) = refl
metadataReferences (O.notePosting value _) valid ref (there ())
metadataReferences (O.noteVector value _) valid ._ (here refl) = refl
metadataReferences (O.noteVector value _) valid ref (there ())
metadataReferences (O.fileVersion _) ()
metadataReferences (O.baseBinding _ _ _) ()
metadataReferences (O.deltaBinding _ _ _ _) ()
metadataReferences (O.basePointer _) ()
metadataReferences (O.chunk _ _) ()
metadataReferences (O.posting _ _) ()
metadataReferences (O.vector _ _) ()
metadataReferences (O.symbol _ _ _) ()
metadataReferences (O.edge _ _ _) ()
metadataReferences (O.publishedView _ _) ()
metadataReferences (O.structuralSnapshot _ _ _ _) ()
metadataReferences (O.legacy _ _ _) ()
metadataReferences (O.staging _ _) ()
metadataReferences (O.acceptedWork _ _) ()
metadataReferences (O.cleanupWork _ _ _) ()
metadataReferences (O.activeReader _ _) ()
metadataReferences (O.continuation _ _) ()
metadataReferences (O.receipt _) ()
metadataReferences (O.migration _) ()
metadataReferences (O.usage _) ()
metadataReferences (O.bootstrap _) ()
metadataReferences (O.modelCache _) ()
metadataReferences (O.coordination _) ()
metadataReferences (O.schemaResource _) ()
metadataReferences (O.graphResource _ _ _) ()
metadataReferences (O.logFile _) ()
metadataReferences (O.bootstrapStage _) ()

AllowedFor : Scope → O.Owner → O.Record → Set
AllowedFor forget owner value = O.owner value ≢ owner
AllowedFor unregister owner value = (O.owner value ≢ owner) ⊎ (settingsOrNotes (O.kind (O.body value)) ≡ true)

allowedOther : ∀ scope owner value → O.owner value ≢ owner → AllowedFor scope owner value
allowedOther forget owner value foreign = foreign
allowedOther unregister owner value foreign = inj₁ foreign

module Family (family : ℕ) (scope : Scope) where
  owner = O.family family


  action : O.Record → Action
  action value with E.ownerEqual (O.owner value) owner
  ... | no other = keep
  ... | yes same = localActionFor scope (O.body value)

  apply : ℕ → Action → O.World → O.World
  apply key keep world = world
  apply key erase world = DB.delete key world
  apply key (compact id) world = DB.write key (Ledger.markerAt id) world

  transform : Action → Maybe O.Record → Maybe O.Record
  transform keep previous = previous
  transform erase previous = nothing
  transform (compact id) previous = just (Ledger.markerAt id)

  intendedRow : O.Record → Maybe O.Record
  intendedRow value = transform (action value) (just value)

  intendedAt : Maybe O.Record → Maybe O.Record
  intendedAt nothing = nothing
  intendedAt (just value) = intendedRow value

  -- A finite scan is compiled to ordinary put/remove operations in ONE shared
  -- transaction. Unrelated rows and retained metadata do not get rewritten.
  run : O.World → O.World → O.World
  run [] world = world
  run ((key , value) ∷ rows) world = run rows (apply key (action value) world)

  next : ℕ → Action → DB.Transaction String → DB.Transaction String
  next key keep body = body
  next key erase body = DB.remove key body
  next key (compact id) body = DB.put key (Ledger.markerAt id) body

  compile : O.World → String → DB.Transaction String
  compile [] result = DB.commit result
  compile ((key , value) ∷ rows) result = next key (action value) (compile rows result)

  performs : ∀ rows world result → DB.evaluate (compile rows result) world ≡ DB.committed result (run rows world)
  performs [] world result = refl
  performs ((key , value) ∷ rows) world result with action value
  ... | keep = performs rows world result
  ... | erase = performs rows (DB.delete key world) result
  ... | compact id = performs rows (DB.write key (Ledger.markerAt id) world) result

  applyAt : ∀ key chosen world → DB.lookup key (apply key chosen world) ≡ transform chosen (DB.lookup key world)
  applyAt key keep world = refl
  applyAt key erase world = DB.deleteAbsent key world
  applyAt key (compact id) world = DB.writeVisible key (Ledger.markerAt id) world

  applyElsewhere : ∀ key other chosen world → key ≢ other → DB.lookup other (apply key chosen world) ≡ DB.lookup other world
  applyElsewhere key other keep world different = refl
  applyElsewhere key other erase world different = DB.deletePreservesOther key other world different
  applyElsewhere key other (compact id) world different = DB.writePreservesOther key other (Ledger.markerAt id) world different

  applyUnique : ∀ key chosen world → O.Unique world → O.Unique (apply key chosen world)
  applyUnique key keep world valid = valid
  applyUnique key erase world valid = O.deleteUnique key world valid
  applyUnique key (compact id) world valid = Storage.writeUnique key (Ledger.markerAt id) world valid

  runUnique : ∀ rows world → O.Unique world → O.Unique (run rows world)
  runUnique [] world valid = valid
  runUnique ((key , value) ∷ rows) world valid = runUnique rows (apply key (action value) world) (applyUnique key (action value) world valid)

  updateAt : Maybe O.Record → Maybe O.Record → Maybe O.Record
  updateAt nothing previous = previous
  updateAt (just value) previous = transform (action value) previous

  runAt : ∀ rows world key → O.Unique rows → DB.lookup key (run rows world) ≡ updateAt (DB.lookup key rows) (DB.lookup key world)
  runAt [] world key unique = refl
  runAt ((first , value) ∷ rows) world key (absent , unique) with key ≟ first
  ... | yes refl rewrite runAt rows (apply key (action value) world) key unique | absent = applyAt key (action value) world
  ... | no different rewrite runAt rows (apply first (action value) world) key unique |
      applyElsewhere first key (action value) world (λ same → different (sym same)) = refl

  final : O.World → O.World
  final world = run world world

  exact : ∀ world key → O.Unique world → DB.lookup key (final world) ≡ intendedAt (DB.lookup key world)
  exact world key unique rewrite runAt world world key unique with DB.lookup key world
  ... | nothing = refl
  ... | just value = refl

  lookupAll : ∀ {P : ℕ × O.Record → Set} world key value → DB.lookup key world ≡ just value → All P world → P (key , value)
  lookupAll ((first , stored) ∷ rows) key value found (proof ∷ rest) with key ≟ first
  ... | yes refl with found
  ...   | refl = proof
  lookupAll ((first , stored) ∷ rows) key value found (proof ∷ rest) | no other = lookupAll rows key value found rest

  record Source (before : O.World) (key : ℕ) (value : O.Record) : Set where
    constructor origin
    field original : O.Record
          found : DB.lookup key before ≡ just original
          projected : intendedRow original ≡ just value

  sourceOf : ∀ before key value → O.Unique before → DB.lookup key (final before) ≡ just value → Source before key value
  sourceOf before key value unique found with DB.lookup key before in observed
  ... | nothing = ⊥-elim (impossible (trans (sym (trans (exact before key unique) (cong intendedAt observed))) found))
    where impossible : nothing ≢ just value
          impossible ()
  ... | just original = origin original observed (trans (sym (trans (exact before key unique) (cong intendedAt observed))) found)

  foreignUnchanged : ∀ value → O.owner value ≢ owner → intendedRow value ≡ just value
  foreignUnchanged value foreign with E.ownerEqual (O.owner value) owner
  ... | yes same = ⊥-elim (foreign same)
  ... | no other = refl

  preservesOthers : ∀ world key value → O.Unique world → DB.lookup key world ≡ just value → O.owner value ≢ owner → DB.lookup key (final world) ≡ just value
  preservesOthers world key value unique found foreign = trans (exact world key unique)
    (trans (cong intendedAt found) (foreignUnchanged value foreign))

  localReceipt : ∀ id state → intendedRow (O.recordOf owner (O.receipt (R.entry id state))) ≡ just (Ledger.markerAt id)
  localReceipt id state with E.ownerEqual owner owner
  ... | yes same = refl
  ... | no other = ⊥-elim (other refl)

  receiptCompacted : ∀ world key id state → O.Unique world → DB.lookup key world ≡ just (O.recordOf owner (O.receipt (R.entry id state))) →
    DB.lookup key (final world) ≡ just (Ledger.markerAt id)
  receiptCompacted world key id state unique found = trans (exact world key unique) (trans (cong intendedAt found) (localReceipt id state))

  metadataUnchanged : ∀ value → scope ≡ unregister → settingsOrNotes (O.kind (O.body value)) ≡ true → intendedRow value ≡ just value
  metadataUnchanged value mode metadata with E.ownerEqual (O.owner value) owner
  ... | no other = refl
  ... | yes same rewrite mode | localMetadata (O.body value) metadata = refl

  foreignReference : ∀ source target → source ≢ owner → O.MayReference source target → target ≢ owner
  foreignReference source .source foreign O.own = foreign
  foreignReference source .O.installation foreign O.shared ()

  referenceKept : ∀ before value ref → action value ≡ keep → ref ∈ O.references (O.body value) →
    (resolved : O.Resolves before (O.owner value) ref) → intendedRow (O.Resolves.value resolved) ≡ just (O.Resolves.value resolved)
  referenceKept before value ref chosen member resolved with E.ownerEqual (O.owner value) owner
  ... | no foreign = foreignUnchanged (O.Resolves.value resolved)
    (foreignReference (O.owner value) (O.owner (O.Resolves.value resolved)) foreign (O.Resolves.rightOwner resolved))
  ... | yes same with localKeepMetadata scope (O.body value) chosen
  ...   | mode , metadata = metadataUnchanged (O.Resolves.value resolved) mode
      (trans (cong settingsOrNotes (O.Resolves.rightKind resolved)) (metadataReferences (O.body value) metadata ref member))

  referencesSubset : ∀ old value → intendedRow old ≡ just value → ∀ ref → ref ∈ O.references (O.body value) → ref ∈ O.references (O.body old)
  referencesSubset old value projected ref member with action old
  ... | keep with projected
  ...   | refl = member
  referencesSubset old value projected ref member | erase with projected
  ... | ()
  referencesSubset old value projected ref member | compact id with projected
  ... | refl with member
  ...   | ()

  referenceOwner : ∀ old value → intendedRow old ≡ just value → ∀ ref → ref ∈ O.references (O.body value) → O.owner value ≡ O.owner old
  referenceOwner old value projected ref member with action old
  ... | keep with projected
  ...   | refl = refl
  referenceOwner old value projected ref member | erase with projected
  ... | ()
  referenceOwner old value projected ref member | compact id with projected
  ... | refl with member
  ...   | ()

  projectedPlaced : ∀ old value → intendedRow old ≡ just value → O.Placed old → O.Placed value
  projectedPlaced old value projected placed with action old
  ... | keep with projected
  ...   | refl = placed
  projectedPlaced old value projected placed | erase with projected
  ... | ()
  projectedPlaced old value projected placed | compact id with projected
  ... | refl = Ledger.markerPlaced id

  targetUnchanged : ∀ before old value → intendedRow old ≡ just value → ∀ ref → ref ∈ O.references (O.body value) →
    (resolved : O.Resolves before (O.owner old) ref) → intendedRow (O.Resolves.value resolved) ≡ just (O.Resolves.value resolved)
  targetUnchanged before old value projected ref member resolved with action old in chosen
  ... | keep with projected
  ...   | refl = referenceKept before old ref chosen member resolved
  targetUnchanged before old value projected ref member resolved | erase with projected
  ... | ()
  targetUnchanged before old value projected ref member resolved | compact id with projected
  ... | refl with member
  ...   | ()

  Allowed : O.Record → Set
  Allowed = AllowedFor scope owner

  allowedForeign : ∀ value → O.owner value ≢ owner → Allowed value
  allowedForeign = allowedOther scope owner

  projectedAllowed : ∀ old value → intendedRow old ≡ just value → Allowed value
  projectedAllowed old value projected with E.ownerEqual (O.owner old) owner
  ... | no foreign with projected
  ...   | refl = allowedForeign old foreign
  projectedAllowed old value projected | yes owned with localActionFor scope (O.body old) in chosen
  ... | keep with projected | localKeepMetadata scope (O.body old) chosen
  ...   | refl | mode , metadata = subst (λ selected → AllowedFor selected owner old) (sym mode) (inj₂ metadata)
  projectedAllowed old value projected | yes owned | erase with projected
  ... | ()
  projectedAllowed old value projected | yes owned | compact id with projected
  ... | refl = allowedForeign (Ledger.markerAt id) (λ ())

  projectFamilySame : ∀ old value other → O.owner value ≡ O.family other → intendedRow old ≡ just value → old ≡ value
  projectFamilySame old value other owned projected with action old
  ... | keep with projected
  ...   | refl = refl
  projectFamilySame old value other owned projected | erase with projected
  ... | ()
  projectFamilySame old value other owned projected | compact id with projected
  ... | refl with owned
  ...   | ()

  module Valid (before : O.World) (valid : O.Admissible before) where
    unique = O.Admissible.unique valid
    after = final before
    afterUnique : O.Unique after
    afterUnique = runUnique before before unique

    sourceAt : ∀ {row} → row ∈ after → Source before (proj₁ row) (proj₂ row)
    sourceAt {row} member = sourceOf before (proj₁ row) (proj₂ row) unique (Order.memberLookup after (proj₁ row) (proj₂ row) afterUnique member)

    placedRow : ∀ {row} → row ∈ after → O.Placed (proj₂ row)
    placedRow {row} member = projectedPlaced original (proj₂ row) projected
      (lookupAll before (proj₁ row) original found (O.Admissible.placed valid))
      where open Source (sourceAt member)

    privateRow : ∀ {row} → row ∈ after → O.PrivateBookkeepingReferences (proj₂ row)
    privateRow {row} member = All.tabulate (λ {ref} present → All.lookup oldPrivate (referencesSubset original (proj₂ row) projected ref present))
      where
      open Source (sourceAt member)
      oldPrivate = lookupAll before (proj₁ row) original found (O.Admissible.privateBookkeeping valid)

    soundRow : ∀ {row} → row ∈ after → O.SoundReferences after row
    soundRow {row} member = All.tabulate resolved
      where
      open Source (sourceAt member)
      oldSound = lookupAll before (proj₁ row) original found (O.Admissible.sound valid)
      resolved : ∀ {ref} → ref ∈ O.references (O.body (proj₂ row)) → O.Resolves after (O.owner (proj₂ row)) ref
      resolved {ref} present = record
        { value = O.Resolves.value old
        ; found = trans (exact before (O.target ref) unique)
            (trans (cong intendedAt (O.Resolves.found old)) (targetUnchanged before original (proj₂ row) projected ref present old))
        ; rightKind = O.Resolves.rightKind old
        ; rightOwner = subst (λ source → O.MayReference source (O.owner (O.Resolves.value old)))
            (sym (referenceOwner original (proj₂ row) projected ref present)) (O.Resolves.rightOwner old) }
        where old = All.lookup oldSound (referencesSubset original (proj₂ row) projected ref present)

    admissible : O.Admissible after
    admissible = record { unique = afterUnique; placed = All.tabulate placedRow; sound = All.tabulate soundRow; privateBookkeeping = All.tabulate privateRow }

    completeScope : All (λ row → Allowed (proj₂ row)) after
    completeScope = All.tabulate (λ {row} member → projectedAllowed (Source.original (sourceAt member)) (proj₂ row) (Source.projected (sourceAt member)))
