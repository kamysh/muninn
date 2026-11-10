{-# OPTIONS --safe #-}
-- Derived-index recreation has a fixed complete-world deletion policy.
module Muninn.RecreationStore where
import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.CleanupOrder as Order
import Muninn.CleanupStorage as Storage
import Muninn.CleanupObservations as Observations
import Muninn.ReceiptLedger as L
open import Data.Nat using (ℕ; _≟_)
open import Data.Bool using (Bool; true; false; not; _∧_)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
module DB = O.DB

-- Code-derived data and note vectors are recreated. Identity, note text,
-- textual note postings, settings/history and execution receipts are retained.
derived : O.Kind → Bool
derived O.registrationK = false
derived O.checkoutK = false
derived O.creationIntentK = false
derived O.defaultsK = false
derived O.policyVersionK = false
derived O.currentPolicyK = false
derived O.noteK = false
derived O.notePostingK = false
derived O.noteVectorK = true
derived O.fileVersionK = true
derived O.baseBindingK = true
derived O.deltaBindingK = true
derived O.basePointerK = true
derived O.chunkK = true
derived O.postingK = true
derived O.vectorK = true
derived O.symbolK = true
derived O.edgeK = true
derived O.structuralSnapshotK = true
derived O.publishedViewK = true
derived O.legacyK = true
derived O.stagingK = true
derived O.acceptedWorkK = false
derived O.cleanupWorkK = false
derived O.activeReaderK = false
derived O.continuationK = false
derived O.receiptK = false
derived O.migrationK = false
derived O.usageK = false
derived O.bootstrapK = false
derived O.modelCacheK = false
derived O.coordinationK = false
derived O.schemaResourceK = false
derived O.graphResourceK = true
derived O.logFileK = false
derived O.bootstrapStageK = false

unique? : (world : O.World) → Dec (O.Unique world)
unique? [] = yes tt
unique? ((key , value) ∷ rows) with DB.lookup key rows in found
... | just stored = no (λ { (() , valid) })
... | nothing with unique? rows
...   | yes valid = yes (refl , valid)
...   | no invalid = no (λ valid → invalid (proj₂ valid))

andLeft : ∀ a b → a ∧ b ≡ true → a ≡ true
andLeft true b proof = refl
andLeft false b ()
andRight : ∀ a b → a ∧ b ≡ true → b ≡ true
andRight true b proof = proof
andRight false b ()

module Family (family : ℕ) where
  owner = O.family family
  keep : O.Record → Bool
  keep value = not (E.sameOwner (O.owner value) owner ∧ derived (O.kind (O.body value)))

  foreignKept : ∀ value → O.owner value ≢ owner → keep value ≡ true
  foreignKept value different with E.ownerEqual (O.owner value) owner
  ... | yes same = ⊥-elim (different same)
  ... | no other = refl

  metadataKept : ∀ value → derived (O.kind (O.body value)) ≡ false → keep value ≡ true
  metadataKept value metadata with E.ownerEqual (O.owner value) owner
  ... | no other = refl
  ... | yes same rewrite metadata = refl

  localDropped : ∀ body → derived (O.kind body) ≡ true → keep (O.recordOf owner body) ≡ false
  localDropped body dataRow with E.ownerEqual owner owner
  ... | no different = ⊥-elim (different refl)
  ... | yes same rewrite dataRow = refl

  apply : ℕ → Bool → O.World → O.World
  apply key true world = world
  apply key false world = DB.delete key world
  project : Bool → Maybe O.Record → Maybe O.Record
  project true value = value
  project false value = nothing
  intended : Maybe O.Record → Maybe O.Record
  intended nothing = nothing
  intended (just value) = project (keep value) (just value)

  run : O.World → O.World → O.World
  run [] world = world
  run ((key , value) ∷ rows) world = run rows (apply key (keep value) world)
  final : O.World → O.World
  final world = run world world

  compile : ∀ {A : Set} → O.World → DB.Transaction A → DB.Transaction A
  compile [] next = next
  compile ((key , value) ∷ rows) next with keep value
  ... | true = compile rows next
  ... | false = DB.remove key (compile rows next)

  performs : ∀ {A : Set} rows world (next : DB.Transaction A) → DB.evaluate (compile rows next) world ≡ DB.evaluate next (run rows world)
  performs [] world next = refl
  performs ((key , value) ∷ rows) world next with keep value
  ... | true = performs rows world next
  ... | false = performs rows (DB.delete key world) next

  applyAt : ∀ key chosen world → DB.lookup key (apply key chosen world) ≡ project chosen (DB.lookup key world)
  applyAt key true world = refl
  applyAt key false world = DB.deleteAbsent key world
  applyOther : ∀ key other chosen world → key ≢ other → DB.lookup other (apply key chosen world) ≡ DB.lookup other world
  applyOther key other true world different = refl
  applyOther key other false world different = DB.deletePreservesOther key other world different
  applyUnique : ∀ key chosen world → O.Unique world → O.Unique (apply key chosen world)
  applyUnique key true world valid = valid
  applyUnique key false world valid = O.deleteUnique key world valid
  runUnique : ∀ rows world → O.Unique world → O.Unique (run rows world)
  runUnique [] world valid = valid
  runUnique ((key , value) ∷ rows) world valid = runUnique rows (apply key (keep value) world) (applyUnique key (keep value) world valid)
  update : Maybe O.Record → Maybe O.Record → Maybe O.Record
  update nothing previous = previous
  update (just value) previous = project (keep value) previous
  runAt : ∀ rows world key → O.Unique rows → DB.lookup key (run rows world) ≡ update (DB.lookup key rows) (DB.lookup key world)
  runAt [] world key valid = refl
  runAt ((first , value) ∷ rows) world key (absent , valid) with key ≟ first
  ... | yes refl rewrite runAt rows (apply key (keep value) world) key valid | absent = applyAt key (keep value) world
  ... | no different rewrite runAt rows (apply first (keep value) world) key valid |
      applyOther first key (keep value) world (λ same → different (sym same)) = refl
  exact : ∀ world key → O.Unique world → DB.lookup key (final world) ≡ intended (DB.lookup key world)
  exact world key valid rewrite runAt world world key valid with DB.lookup key world
  ... | nothing = refl
  ... | just value = refl
  retained : ∀ world key value → O.Unique world → DB.lookup key world ≡ just value → keep value ≡ true → DB.lookup key (final world) ≡ just value
  retained world key value valid found kept rewrite exact world key valid | found | kept = refl
  removed : ∀ world key body → O.Unique world → DB.lookup key world ≡ just (O.recordOf owner body) → derived (O.kind body) ≡ true → DB.lookup key (final world) ≡ nothing
  removed world key body valid found dataRow rewrite exact world key valid | found | localDropped body dataRow = refl

  -- A derived object still used by an accepted operation must be released
  -- before the atomic replacement; no reference is silently broken.
  targetKept : O.World → O.Reference → Bool
  targetKept world ref with DB.lookup (O.target ref) world
  ... | nothing = true
  ... | just value = keep value
  refsKept : O.World → List O.Reference → Bool
  refsKept world [] = true
  refsKept world (ref ∷ rest) = targetKept world ref ∧ refsKept world rest
  checks : O.World → O.World → Bool
  checks world [] = true
  checks world ((key , value) ∷ rest) with keep value
  ... | false = checks world rest
  ... | true = refsKept world (O.references (O.body value)) ∧ checks world rest
  graphBusy : O.Record → Bool
  graphBusy (O.recordOf actualOwner (O.graphResource selected true payload)) = E.sameOwner actualOwner owner
  graphBusy value = false
  graphsIdle : O.World → Bool
  graphsIdle world = not (E.anyRow (λ key value → graphBusy value) world)

  ready : O.World → Bool
  ready world = checks world world ∧ graphsIdle world
  refsSound : ∀ world refs → refsKept world refs ≡ true → All (λ ref → targetKept world ref ≡ true) refs
  refsSound world [] proof = []
  refsSound world (ref ∷ rest) proof = andLeft _ _ proof ∷ refsSound world rest (andRight _ _ proof)
  checksSound : ∀ world rows → checks world rows ≡ true → All (λ row → keep (proj₂ row) ≡ true → All (λ ref → targetKept world ref ≡ true) (O.references (O.body (proj₂ row)))) rows
  checksSound world [] proof = []
  checksSound world ((key , value) ∷ rest) proof with keep value in kept
  ... | false = (λ proof → ⊥-elim (impossible (trans (sym kept) proof))) ∷ checksSound world rest proof
    where impossible : false ≢ true
          impossible ()
  ... | true = (λ ignored → refsSound world (O.references (O.body value)) (andLeft _ _ proof)) ∷ checksSound world rest (andRight _ _ proof)

  busyHit : ∀ rows key value → (key , value) ∈ rows → graphBusy value ≡ true → E.anyRow (λ key value → graphBusy value) rows ≡ true
  busyHit ((key , value) ∷ rows) .key .value (here refl) hit rewrite hit = refl
  busyHit ((first , stored) ∷ rows) key value (there present) hit with graphBusy stored
  ... | true = refl
  ... | false = busyHit rows key value present hit

  ownedGraphBusy : ∀ selected payload → graphBusy (O.recordOf owner (O.graphResource selected true payload)) ≡ true
  ownedGraphBusy selected payload with E.ownerEqual owner owner
  ... | yes same = refl
  ... | no different = ⊥-elim (different refl)

  graphUsePreventsRecreation : ∀ world key selected payload →
    DB.lookup key world ≡ just (O.recordOf owner (O.graphResource selected true payload)) → ready world ≡ false
  graphUsePreventsRecreation world key selected payload found
    rewrite busyHit world key (O.recordOf owner (O.graphResource selected true payload))
      (Observations.lookupMember world key _ found) (ownedGraphBusy selected payload) with checks world world
  ... | true = refl
  ... | false = refl

  record Source (before : O.World) (key : ℕ) (value : O.Record) : Set where
    field found : DB.lookup key before ≡ just value
          kept : keep value ≡ true
  rowOrigin : ∀ original value → intended (just original) ≡ just value → original ≡ value × keep original ≡ true
  rowOrigin original value proof with keep original in kept
  ... | false with proof
  ...   | ()
  rowOrigin original value proof | true with proof
  ... | refl = refl , refl
  sourceOf : ∀ before key value → O.Unique before → DB.lookup key (final before) ≡ just value → Source before key value
  sourceOf before key value valid found with DB.lookup key before in observed
  ... | nothing = ⊥-elim (impossible (trans (sym (trans (exact before key valid) (cong intended observed))) found))
    where impossible : nothing ≢ just value
          impossible ()
  ... | just original with rowOrigin original value (trans (sym (trans (exact before key valid) (cong intended observed))) found)
  ...   | refl , kept = record { found = observed; kept = kept }

  receiptFrame : ∀ world → O.Unique world → L.ReceiptFrame world (final world)
  receiptFrame world valid key actualOwner receiptData =
    (λ found → retained world key _ valid found (metadataKept (O.recordOf actualOwner (O.receipt receiptData)) refl)) , backward
    where
    backward : DB.lookup key (final world) ≡ just (O.recordOf actualOwner (O.receipt receiptData)) → DB.lookup key world ≡ just (O.recordOf actualOwner (O.receipt receiptData))
    backward found = Source.found (sourceOf world key _ valid found)

  module Valid (before : O.World) (valid : O.Admissible before) (released : ready before ≡ true) where
    unique = O.Admissible.unique valid
    source : ∀ {row} → row ∈ final before → Source before (proj₁ row) (proj₂ row)
    source {row} present = sourceOf before _ _ unique (Order.memberLookup (final before) _ _ (runUnique before before unique) present)
    sound : ∀ {row} → row ∈ final before → O.SoundReferences (final before) row
    sound {row} present = All.tabulate resolve
      where
      origin = source present
      oldSound = Storage.lookupAll before (proj₁ row) (proj₂ row) (O.Admissible.sound valid) (Source.found origin)
      checksHere = Storage.lookupAll before (proj₁ row) (proj₂ row) (checksSound before before (andLeft (checks before before) (graphsIdle before) released)) (Source.found origin)
      resolve : ∀ {ref} → ref ∈ O.references (O.body (proj₂ row)) → O.Resolves (final before) (O.owner (proj₂ row)) ref
      resolve {ref} included = record
        { value = O.Resolves.value old; found = retained before (O.target ref) (O.Resolves.value old) unique (O.Resolves.found old) kept
        ; rightKind = O.Resolves.rightKind old; rightOwner = O.Resolves.rightOwner old }
        where
        old = All.lookup oldSound included
        kept : keep (O.Resolves.value old) ≡ true
        kept with DB.lookup (O.target ref) before | O.Resolves.found old | All.lookup (checksHere (Source.kept origin)) included
        ... | .(just (O.Resolves.value old)) | refl | proof = proof
    admissible : O.Admissible (final before)
    admissible = record
      { unique = runUnique before before unique
      ; placed = All.tabulate (λ {row} present → Storage.lookupAll before _ _ (O.Admissible.placed valid) (Source.found (source present)))
      ; sound = All.tabulate sound
      ; privateBookkeeping = All.tabulate (λ {row} present → Storage.lookupAll before _ _ (O.Admissible.privateBookkeeping valid) (Source.found (source present))) }
