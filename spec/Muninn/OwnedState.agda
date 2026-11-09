{-# OPTIONS --safe #-}
-- Logical decomposition of ALL owned state, independent of physical tables.
-- Identifiers denote record incarnations, not a choice of UUID/SQL layout.
module Muninn.OwnedState where

open import Data.Nat using (ℕ; _≟_)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans; sym)
import Muninn.Database
import Muninn.Recovery
import Muninn.ReceiptTypes as Receipt
import Muninn.CatalogInputs as Input
import Muninn.Config as Config
import Muninn.FileLimits as Limits
import Muninn.PolicyRuleAdmission as Admission
import Muninn.GitIgnore as Git
import Data.String as String
import Muninn.Worktree as Worktree
import Data.List.Relation.Unary.All as All

data Owner : Set where
  installation : Owner
  family : ℕ → Owner

data Kind : Set where
  registrationK checkoutK creationIntentK defaultsK policyVersionK currentPolicyK : Kind
  noteK notePostingK noteVectorK fileVersionK baseBindingK deltaBindingK basePointerK : Kind
  chunkK postingK vectorK symbolK edgeK structuralSnapshotK publishedViewK legacyK stagingK : Kind
  acceptedWorkK cleanupWorkK activeReaderK continuationK receiptK : Kind
  migrationK usageK bootstrapK modelCacheK coordinationK schemaResourceK graphResourceK logFileK bootstrapStageK : Kind

record Reference : Set where
  constructor reference
  field target : ℕ
        expected : Kind
open Reference public

-- Bodies keep every independently reclaimable category visible. Strings retain
-- uninterpreted metadata; later operation modules specify their interpretation.
-- Strong references are derived below, never supplied as an operation goal.
record RegistrationInfo : Set where
  constructor registrationInfo
  field retired legacyReadable : Bool
        missingSince : Maybe ℕ
        metadata : String

record CheckoutInfo : Set where
  constructor checkoutInfo
  field retired paused gitSuspended : Bool
        missingSince : Maybe ℕ
        metadata : String

record PolicyVersionInfo : Set where
  constructor policyVersionInfo
  field familyId : Worktree.FamilyId
        revision : ℕ
        contents : Input.PolicyDraft

  field excludeValid : Admission.Entries
          (map String.toList (Config.IndexConfig.exclude (Input.PolicyDraft.index contents)))
        vendorValid : Admission.Entries
          (map String.toList (Config.IndexConfig.vendor (Input.PolicyDraft.index contents)))

SelectionFor : Maybe ℕ → String → Set
SelectionFor nothing path = ⊤
SelectionFor (just version) path = Git.Answer path

record DefaultsInfo : Set where
  constructor defaultsInfo
  field value : Config.PolicyDefaults
        excludeValid : Admission.Entries
          (map String.toList (Config.IndexConfig.exclude (Config.PolicyDefaults.rules value)))
        vendorValid : Admission.Entries
          (map String.toList (Config.IndexConfig.vendor (Config.PolicyDefaults.rules value)))

  field concreteLimits : Σ Limits.Limits (λ caps → Config.IndexConfig.limits (Config.PolicyDefaults.rules value) ≡ just caps)

captureDefaults : ∀ revision global →
  Admission.Entries (map String.toList (Config.IndexConfig.exclude global)) →
  Admission.Entries (map String.toList (Config.IndexConfig.vendor global)) → DefaultsInfo
captureDefaults revision global excludes vendors = defaultsInfo
  (Config.captureDefaults revision global) excludes vendors (Limits.initial (Config.IndexConfig.limits global) , refl)

data Body : Set where
  registration : RegistrationInfo → Body
  creationIntent : String → Body
  defaults : DefaultsInfo → Body
  checkout : CheckoutInfo → Body
  policyVersion : ℕ → PolicyVersionInfo → Body
  currentPolicy : ℕ → Body
  note : String → Body
  notePosting noteVector : ℕ → String → Body
  fileVersion : String → Body
  baseBinding : (version : ℕ) (path : String) → Git.Answer path → Body
  deltaBinding : (selected : ℕ) (version : Maybe ℕ) (path : String) → SelectionFor version path → Body
  basePointer : ℕ → Body
  chunk posting vector : ℕ → String → Body
  symbol : ℕ → String → String → Body -- version, source path, payload
  edge : ℕ → ℕ → String → Body
  publishedView : ℕ → ℕ → Body
  structuralSnapshot : ℕ → List ℕ → List ℕ → String → Body
  legacy : (path : String) → Git.Answer path → String → Body -- saved Git default, remaining payload
  staging : ℕ → String → Body
  acceptedWork : List ℕ → String → Body
  cleanupWork : Input.OperationId → List ℕ → String → Body
  activeReader : List Reference → String → Body
  continuation : List ℕ → String → Body
  receipt : Receipt.Entry → Body
  graphResource : Maybe ℕ → Bool → String → Body -- selected checkout, current read use
  migration usage bootstrap modelCache coordination schemaResource logFile bootstrapStage : String → Body

kind : Body → Kind
kind (registration _) = registrationK
kind (checkout _) = checkoutK
kind (creationIntent _) = creationIntentK
kind (defaults _) = defaultsK
kind (policyVersion _ _) = policyVersionK
kind (currentPolicy _) = currentPolicyK
kind (note _) = noteK
kind (notePosting _ _) = notePostingK
kind (noteVector _ _) = noteVectorK
kind (fileVersion _) = fileVersionK
kind (baseBinding _ _ _) = baseBindingK
kind (deltaBinding _ _ _ _) = deltaBindingK
kind (basePointer _) = basePointerK
kind (chunk _ _) = chunkK
kind (posting _ _) = postingK
kind (vector _ _) = vectorK
kind (symbol _ _ _) = symbolK
kind (edge _ _ _) = edgeK
kind (publishedView _ _) = publishedViewK
kind (structuralSnapshot _ _ _ _) = structuralSnapshotK
kind (legacy _ _ _) = legacyK
kind (staging _ _) = stagingK
kind (acceptedWork _ _) = acceptedWorkK
kind (cleanupWork _ _ _) = cleanupWorkK
kind (activeReader _ _) = activeReaderK
kind (continuation _ _) = continuationK
kind (receipt _) = receiptK
kind (migration _) = migrationK
kind (usage _) = usageK
kind (bootstrap _) = bootstrapK
kind (modelCache _) = modelCacheK
kind (coordination _) = coordinationK
kind (schemaResource _) = schemaResourceK
kind (graphResource _ _ _) = graphResourceK
kind (logFile _) = logFileK
kind (bootstrapStage _) = bootstrapStageK

references : Body → List Reference
references (registration _) = []
references (checkout _) = []
references (creationIntent _) = []
references (defaults _) = []
references (policyVersion initial _) = reference initial defaultsK ∷ []
references (currentPolicy revision) = reference revision policyVersionK ∷ []
references (note _) = []
references (notePosting source _) = reference source noteK ∷ []
references (noteVector source _) = reference source noteK ∷ []
references (fileVersion _) = []
references (baseBinding version _ gitAnswer) = reference version fileVersionK ∷ []
references (deltaBinding selected nothing _ _) = reference selected checkoutK ∷ []
references (deltaBinding selected (just version) _ gitAnswer) = reference selected checkoutK ∷ reference version fileVersionK ∷ []
references (basePointer selected) = reference selected checkoutK ∷ []
references (chunk source _) = reference source fileVersionK ∷ []
references (posting source _) = reference source chunkK ∷ []
references (vector source _) = reference source chunkK ∷ []
references (symbol source _ _) = reference source fileVersionK ∷ []
references (edge source target _) = reference source symbolK ∷ reference target symbolK ∷ []
references (publishedView selected snapshot) = reference selected checkoutK ∷ reference snapshot structuralSnapshotK ∷ []
references (structuralSnapshot selected nodes edges _) = reference selected checkoutK ∷
  (map (λ v → reference v symbolK) nodes ++ map (λ v → reference v edgeK) edges)
references (legacy _ _ _) = []
references (staging source _) = reference source fileVersionK ∷ []
references (acceptedWork versions _) = map (λ v → reference v fileVersionK) versions
references (cleanupWork _ _ _) = []
references (activeReader retained _) = retained
references (continuation _ _) = []
references (receipt (Receipt.entry id (Receipt.active input names progress))) =
  map (λ v → reference v fileVersionK) (Receipt.versions progress)
references (receipt (Receipt.entry id (Receipt.finished input names result))) = []
references (receipt (Receipt.entry id Receipt.used)) = []
references (migration _) = []
references (usage _) = []
references (bootstrap _) = []
references (modelCache _) = []
references (coordination _) = []
references (schemaResource _) = []
references (graphResource _ _ _) = []
references (logFile _) = []
references (bootstrapStage _) = []

-- Cleanup captures and idle continuations contain weak incarnation identities:
-- already-deleted records are valid checkpoints and must not be resurrected.
-- Only accepted work and active readers keep their required records alive.
record Record : Set where
  constructor recordOf
  field owner : Owner
        body : Body
open Record public

module DB = Muninn.Database.Store ℕ Record _≟_
module Execution = Muninn.Recovery.Protocol ℕ Record _≟_

World : Set
World = DB.Rows

data LocalTo : Owner → Set where
  local : ∀ {id} → LocalTo (family id)

data SharedAt : Owner → Set where
  shared : SharedAt installation

GitFamily : ∀ {path} → Owner → Git.Answer path → Set
GitFamily installation answer = ⊥
GitFamily (family id) answer = Git.Context.family (Git.at answer) ≡ id

DeltaOrigin : (owner : Owner) (selected : ℕ) (version : Maybe ℕ) (path : String) → SelectionFor version path → Set
DeltaOrigin owner selected nothing path source = ⊤
-- Preserved entries retain their true original Git query provenance. Fresh
-- intake separately requires the current checkout in IndexSelection.File.
DeltaOrigin owner selected (just version) path source = GitFamily owner source

-- Every persistent constructor has an explicit ownership clause. Adding a
-- category cannot silently inherit the ownership policy of a catch-all case.
Placed : Record → Set
Placed (recordOf o (registration _)) = LocalTo o
Placed (recordOf o (checkout _)) = LocalTo o
Placed (recordOf o (creationIntent _)) = LocalTo o
Placed (recordOf o (defaults _)) = LocalTo o
Placed (recordOf o (policyVersion _ _)) = LocalTo o
Placed (recordOf o (currentPolicy _)) = LocalTo o
Placed (recordOf o (note _)) = LocalTo o
Placed (recordOf o (notePosting _ _)) = LocalTo o
Placed (recordOf o (noteVector _ _)) = LocalTo o
Placed (recordOf o (fileVersion _)) = LocalTo o
Placed (recordOf o (baseBinding version path source)) = LocalTo o × GitFamily o source
Placed (recordOf o (deltaBinding selected version path source)) = LocalTo o × DeltaOrigin o selected version path source
Placed (recordOf o (basePointer _)) = LocalTo o
Placed (recordOf o (chunk _ _)) = LocalTo o
Placed (recordOf o (posting _ _)) = LocalTo o
Placed (recordOf o (vector _ _)) = LocalTo o
Placed (recordOf o (symbol _ _ _)) = LocalTo o
Placed (recordOf o (edge _ _ _)) = LocalTo o
Placed (recordOf o (publishedView _ _)) = LocalTo o
Placed (recordOf o (structuralSnapshot _ _ _ _)) = LocalTo o
Placed (recordOf o (legacy path source payload)) = LocalTo o × GitFamily o source
Placed (recordOf o (staging _ _)) = LocalTo o
Placed (recordOf o (acceptedWork _ _)) = LocalTo o
Placed (recordOf o (cleanupWork _ _ _)) = LocalTo o
Placed (recordOf o (activeReader _ _)) = LocalTo o
Placed (recordOf o (continuation _ _)) = LocalTo o
Placed (recordOf o (receipt (Receipt.entry id (Receipt.active input names progress)))) = ⊤
Placed (recordOf o (receipt (Receipt.entry id (Receipt.finished input names result)))) = ⊤
Placed (recordOf o (receipt (Receipt.entry id Receipt.used))) = SharedAt o
Placed (recordOf o (migration _)) = ⊤
Placed (recordOf o (usage _)) = ⊤
Placed (recordOf o (bootstrap _)) = SharedAt o
Placed (recordOf o (modelCache _)) = SharedAt o
Placed (recordOf o (coordination _)) = ⊤
Placed (recordOf o (schemaResource _)) = LocalTo o
Placed (recordOf o (graphResource _ _ _)) = LocalTo o
Placed (recordOf o (logFile _)) = SharedAt o
Placed (recordOf o (bootstrapStage _)) = SharedAt o

data MayReference : Owner → Owner → Set where
  own : ∀ {o} → MayReference o o
  shared : ∀ {o} → MayReference o installation

record Resolves (world : World) (source : Owner) (ref : Reference) : Set where
  field value : Record
        found : DB.lookup (target ref) world ≡ just value
        rightKind : kind (body value) ≡ expected ref
        rightOwner : MayReference source (owner value)

Unique : World → Set
Unique [] = ⊤
Unique ((key , value) ∷ rest) = (DB.lookup key rest ≡ nothing) × Unique rest

SoundReferences : World → ℕ × Record → Set
SoundReferences world row = All (Resolves world (owner (proj₂ row))) (references (body (proj₂ row)))

-- Every owned kind has an explicit search-hold visibility decision.
executionBookkeeping : Kind → Bool
executionBookkeeping registrationK = false
executionBookkeeping checkoutK = false
executionBookkeeping creationIntentK = false
executionBookkeeping defaultsK = false
executionBookkeeping policyVersionK = false
executionBookkeeping currentPolicyK = false
executionBookkeeping noteK = false
executionBookkeeping notePostingK = false
executionBookkeeping noteVectorK = false
executionBookkeeping fileVersionK = false
executionBookkeeping baseBindingK = false
executionBookkeeping deltaBindingK = false
executionBookkeeping basePointerK = false
executionBookkeeping chunkK = false
executionBookkeeping postingK = false
executionBookkeeping vectorK = false
executionBookkeeping symbolK = false
executionBookkeeping edgeK = false
executionBookkeeping structuralSnapshotK = false
executionBookkeeping publishedViewK = false
executionBookkeeping legacyK = false
executionBookkeeping stagingK = false
executionBookkeeping acceptedWorkK = true
executionBookkeeping cleanupWorkK = true
executionBookkeeping activeReaderK = true
executionBookkeeping continuationK = true
executionBookkeeping receiptK = true
executionBookkeeping migrationK = false
executionBookkeeping usageK = false
executionBookkeeping bootstrapK = false
executionBookkeeping modelCacheK = false
executionBookkeeping coordinationK = false
executionBookkeeping schemaResourceK = false
executionBookkeeping graphResourceK = false
executionBookkeeping logFileK = false
executionBookkeeping bootstrapStageK = false

-- Searches retain the selected snapshot, never its mutable current selector.
privateTarget : Kind → Bool
privateTarget publishedViewK = true
privateTarget baseBindingK = true
privateTarget deltaBindingK = true
privateTarget kind = executionBookkeeping kind

PublicReference : Reference → Set
PublicReference ref = privateTarget (expected ref) ≡ false

publicReference? : ∀ ref → Dec (PublicReference ref)
publicReference? ref with privateTarget (expected ref)
... | true = no (λ ())
... | false = yes refl

PrivateBookkeepingReferences : Record → Set
PrivateBookkeepingReferences value = All PublicReference (references (body value))

PrivateReaderReferences : Record → Set
PrivateReaderReferences value = All (λ ref → expected ref ≢ activeReaderK) (references (body value))

privateReferenceImpossible : ∀ internal → privateTarget internal ≡ true → ∀ ref → PublicReference ref → expected ref ≢ internal
privateReferenceImpossible internal hidden ref visible same = impossible
  (trans (sym hidden) (trans (cong privateTarget (sym same)) visible))
  where impossible : true ≢ false
        impossible ()

record Admissible (world : World) : Set where
  field unique : Unique world
        placed : All (λ row → Placed (proj₂ row)) world
        sound : All (SoundReferences world) world
        privateBookkeeping : All (λ row → PrivateBookkeepingReferences (proj₂ row)) world

  -- Compatibility projection; privacy has one authoritative stored invariant.
  privateReaders : All (λ row → PrivateReaderReferences (proj₂ row)) world
  privateReaders = All.map (λ {row} refs → All.map
    (λ {ref} visible → privateReferenceImpossible activeReaderK refl ref visible) refs) privateBookkeeping

-- Deleting one family record preserves every already-present record of a
-- different owner, regardless of its category, checkout or payload.
deletePreservesOtherOwner : ∀ key other before removed retained →
  DB.lookup key before ≡ just removed → DB.lookup other before ≡ just retained →
  owner removed ≢ owner retained → DB.lookup other (DB.delete key before) ≡ just retained
deletePreservesOtherOwner key other before removed retained removedHere retainedHere distinct =
  trans (DB.deletePreservesOther key other before differentKeys) retainedHere
  where
  differentKeys : key ≢ other
  differentKeys refl = distinct (cong owner (just-injective (trans (sym removedHere) retainedHere)))

referenceSurvivesOtherDeletion : ∀ before source ref key → target ref ≢ key →
  Resolves before source ref → Resolves (DB.delete key before) source ref
referenceSurvivesOtherDeletion before source ref key distinct valid = record
  { value = Resolves.value valid
  ; found = trans (DB.deletePreservesOther key (target ref) before
      (λ equal → distinct (sym equal))) (Resolves.found valid)
  ; rightKind = Resolves.rightKind valid
  ; rightOwner = Resolves.rightOwner valid
  }

deleteAll : ∀ {P : ℕ × Record → Set} key rows → All P rows → All P (DB.delete key rows)
deleteAll key [] [] = []
deleteAll key ((other , value) ∷ rows) (proof ∷ rest) with key ≟ other
... | yes _ = deleteAll key rows rest
... | no _ = proof ∷ deleteAll key rows rest

deleteKeepsAbsent : ∀ key other rows → DB.lookup other rows ≡ nothing →
  DB.lookup other (DB.delete key rows) ≡ nothing
deleteKeepsAbsent key other rows absent with key ≟ other
... | yes refl = DB.deleteAbsent key rows
... | no distinct = trans (DB.deletePreservesOther key other rows distinct) absent

deleteUnique : ∀ key rows → Unique rows → Unique (DB.delete key rows)
deleteUnique key [] unique = tt
deleteUnique key ((other , value) ∷ rows) (absent , unique) with key ≟ other
... | yes _ = deleteUnique key rows unique
... | no _ = deleteKeepsAbsent key other rows absent , deleteUnique key rows unique

NoIncomingTo : ℕ → ℕ × Record → Set
NoIncomingTo key row = All (λ ref → target ref ≢ key) (references (body (proj₂ row)))

shiftReferences : ∀ before source refs key → All (Resolves before source) refs →
  All (λ ref → target ref ≢ key) refs → All (Resolves (DB.delete key before) source) refs
shiftReferences before source [] key [] [] = []
shiftReferences before source (ref ∷ refs) key (valid ∷ rest) (distinct ∷ others) =
  referenceSurvivesOtherDeletion before source ref key distinct valid ∷
  shiftReferences before source refs key rest others

shiftSound : ∀ key before rows → All (SoundReferences before) rows →
  All (NoIncomingTo key) rows → All (SoundReferences (DB.delete key before)) rows
shiftSound key before [] [] [] = []
shiftSound key before ((id , value) ∷ rows) (valid ∷ rest) (unreferenced ∷ others) =
  shiftReferences before (owner value) (references (body value)) key valid unreferenced ∷
  shiftSound key before rows rest others

-- A record needed by any checkout, pending work or active reader cannot meet
-- this guard. Removing an unreferenced record preserves the WHOLE state model.
deleteUnreferencedPreservesAdmissibility : ∀ key world → Admissible world →
  All (NoIncomingTo key) world → Admissible (DB.delete key world)
deleteUnreferencedPreservesAdmissibility key world valid unreferenced = record
  { unique = deleteUnique key world (Admissible.unique valid)
  ; placed = deleteAll key world (Admissible.placed valid)
  ; sound = deleteAll key world (shiftSound key world world (Admissible.sound valid) unreferenced)
  ; privateBookkeeping = deleteAll key world (Admissible.privateBookkeeping valid)
  }

-- Privacy and reference soundness derive the deletion guard for bookkeeping.
privateUnreferenced : ∀ key world value → Admissible world → DB.lookup key world ≡ just value →
  privateTarget (kind (body value)) ≡ true → All (NoIncomingTo key) world
privateUnreferenced key world value valid found hidden =
  All.tabulate (λ {row} present → All.tabulate (λ {ref} included equal →
    privateReferenceImpossible (kind (body value)) hidden ref (All.lookup (All.lookup (Admissible.privateBookkeeping valid) present) included) (sym (trans (cong (λ stored → kind (body stored)) (just-injective (trans (sym found) (trans (cong (λ id → DB.lookup id world) (sym equal)) (Resolves.found (All.lookup (All.lookup (Admissible.sound valid) present) included)))))) (Resolves.rightKind (All.lookup (All.lookup (Admissible.sound valid) present) included))))))
