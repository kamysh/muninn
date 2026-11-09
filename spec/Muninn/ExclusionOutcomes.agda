{-# OPTIONS --safe #-}
-- Independent whole-world outcomes; no deletion script or keeper predicate.
module Muninn.ExclusionOutcomes where

import Muninn.OwnedState as O
import Muninn.ReceiptTypes as Receipt
import Muninn.Config as Config
open import Data.Nat using (ℕ; _≟_)
open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.String using (String)
import Data.String as String
open import Data.List using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; does; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)

module DB = O.DB

ownerEqual : (a b : O.Owner) → Dec (a ≡ b)
ownerEqual O.installation O.installation = yes refl
ownerEqual O.installation (O.family _) = no (λ ())
ownerEqual (O.family _) O.installation = no (λ ())
ownerEqual (O.family a) (O.family b) with a ≟ b
... | yes refl = yes refl
... | no different = no (λ { refl → different refl })

sameNat : ℕ → ℕ → Bool
sameNat a b = does (a ≟ b)

sameOwner : O.Owner → O.Owner → Bool
sameOwner a b = does (ownerEqual a b)

record Rule : Set where
  constructor rule
  field family : ℕ
        exclusions : List String -- ordered EFFECTIVE defaults + family rules
open Rule public

fromStoredPolicy : ℕ → Config.FamilyPolicy → Rule
fromStoredPolicy owner policy = rule owner (Config.EffectiveConfig.exclude (Config.familyConfig policy))

targetOwner : Rule → O.Owner
targetOwner selection = O.family (family selection)

data Gate : Set where
  content : Gate
  sourcePath : ℕ → String → Gate
  transient : Gate

-- This one exhaustive classification controls roots, footprint attachment and
-- control/data separation. A new owned constructor cannot inherit a default.
data Role : Set where
  administrative holder artifact baselineAnchor : Role
  baselineBinding : String → Role
  checkoutBinding : ℕ → String → Role
  snapshot : ℕ → Role
  legacyFile : String → Role
  graphContainer : Maybe ℕ → Bool → Role
  attached : O.Reference → Gate → Role

classify : O.Body → Role
classify (O.registration _) = administrative
classify (O.checkout _) = administrative
classify (O.creationIntent _) = administrative
classify (O.defaults _) = administrative
classify (O.policyVersion _ _) = administrative
classify (O.currentPolicy _) = administrative
classify (O.note _) = administrative
classify (O.notePosting _ _) = administrative
classify (O.noteVector _ _) = administrative
classify (O.fileVersion _) = artifact
classify (O.baseBinding version path) = baselineBinding path
classify (O.deltaBinding checkout version path) = checkoutBinding checkout path
classify (O.basePointer _) = baselineAnchor
classify (O.chunk version _) = attached (O.reference version O.fileVersionK) content
classify (O.posting chunk _) = attached (O.reference chunk O.chunkK) content
classify (O.vector chunk _) = attached (O.reference chunk O.chunkK) content
classify (O.symbol version path _) = attached (O.reference version O.fileVersionK) (sourcePath version path)
classify (O.edge _ _ _) = artifact
classify (O.structuralSnapshot selected _ _ _) = snapshot selected
classify (O.legacy path _) = legacyFile path
classify (O.staging version _) = attached (O.reference version O.fileVersionK) transient
classify (O.acceptedWork _ _) = holder
classify (O.cleanupWork _ _ _) = administrative
classify (O.activeReader _ _) = holder
classify (O.continuation _ _) = administrative
classify (O.receipt (Receipt.entry id (Receipt.active input names work))) = holder
classify (O.receipt (Receipt.entry id (Receipt.finished input names result))) = administrative
classify (O.receipt (Receipt.entry id Receipt.used)) = administrative
classify (O.migration _) = administrative
classify (O.usage _) = administrative
classify (O.bootstrap _) = administrative
classify (O.modelCache _) = administrative
classify (O.coordination _) = administrative
classify (O.schemaResource _) = administrative
classify (O.graphResource selected inUse _) = graphContainer selected inUse
classify (O.logFile _) = administrative
classify (O.bootstrapStage _) = administrative

indexedRole : Role → Bool
indexedRole administrative = false
indexedRole holder = false
indexedRole artifact = true
indexedRole baselineAnchor = true
indexedRole (baselineBinding _) = true
indexedRole (checkoutBinding _ _) = true
indexedRole (snapshot _) = true
indexedRole (legacyFile _) = true
indexedRole (graphContainer _ _) = true
indexedRole (attached _ _) = true

indexed : O.Record → Bool
indexed value = indexedRole (classify (O.body value))

anyRow : (ℕ → O.Record → Bool) → O.World → Bool
anyRow test [] = false
anyRow test ((key , value) ∷ rows) = test key value ∨ anyRow test rows

filterKeys : (ℕ → Bool) → List ℕ → List ℕ
filterKeys keep [] = []
filterKeys keep (key ∷ keys) with keep key
... | true = key ∷ filterKeys keep keys
... | false = filterKeys keep keys

filterKeysSound : ∀ keep keys key → key ∈ filterKeys keep keys → keep key ≡ true
filterKeysSound keep [] key ()
filterKeysSound keep (first ∷ rest) key present with keep first in decision
... | true with present
...   | here refl = decision
...   | there later = filterKeysSound keep rest key later
filterKeysSound keep (first ∷ rest) key present | false = filterKeysSound keep rest key present

filterKeysComplete : ∀ keep keys key → key ∈ keys → keep key ≡ true → key ∈ filterKeys keep keys
filterKeysComplete keep (first ∷ rest) .first (here refl) selected with keep first | selected
... | true | refl = here refl
filterKeysComplete keep (first ∷ rest) key (there later) selected with keep first
... | true = there (filterKeysComplete keep rest key later selected)
... | false = filterKeysComplete keep rest key later selected

snapshotNodes : O.Record → List ℕ
snapshotNodes (O.recordOf owner (O.structuralSnapshot selected nodes edges payload)) = nodes
snapshotNodes _ = []

snapshotEdges : O.Record → List ℕ
snapshotEdges (O.recordOf owner (O.structuralSnapshot selected nodes edges payload)) = edges
snapshotEdges _ = []

filterKeysIdempotent : ∀ keep keys → filterKeys keep (filterKeys keep keys) ≡ filterKeys keep keys
filterKeysIdempotent keep [] = refl
filterKeysIdempotent keep (key ∷ keys) with keep key in decision
... | true rewrite decision = cong (key ∷_) (filterKeysIdempotent keep keys)
... | false = filterKeysIdempotent keep keys

checkoutAvailable : O.CheckoutInfo → Bool
checkoutAvailable info = not (O.CheckoutInfo.retired info)

pauseAndGitDoNotChangeAvailability : ∀ retired pause git metadata pause′ git′ metadata′ →
  checkoutAvailable (O.checkoutInfo retired pause git metadata) ≡
    checkoutAvailable (O.checkoutInfo retired pause′ git′ metadata′)
pauseAndGitDoNotChangeAvailability retired pause git metadata pause′ git′ metadata′ = refl

-- The policy matcher is fixed once by the shared selection semantics (#26).
-- It is not a field supplied by a cleanup operation. No raw rule parsing here.
module Model (excluded : List String → String → Bool) where
  included : Rule → O.Owner → String → Bool
  included selection owner path =
    if sameOwner owner (targetOwner selection) then not (excluded (exclusions selection) path) else true

  record Location : Set where
    constructor location
    field owner : O.Owner
          checkout : ℕ
          path : String

  SearchVisible : Rule → Location → Set
  SearchVisible selection whereAt = included selection (Location.owner whereAt) (Location.path whereAt) ≡ true

  allCheckoutsUseSameMask : ∀ selection owner path first second →
    SearchVisible selection (location owner first path) ≡ SearchVisible selection (location owner second path)
  allCheckoutsUseSameMask selection owner path first second = refl

  excludedCannotAppear : ∀ selection whereAt →
    included selection (Location.owner whereAt) (Location.path whereAt) ≡ false →
    ¬ SearchVisible selection whereAt
  excludedCannotAppear selection whereAt blocked visible with trans (sym visible) blocked
  ... | ()

  registeredValue : Rule → O.Record → Bool
  registeredValue selection (O.recordOf owner (O.registration info)) = sameOwner owner (targetOwner selection) ∧ not (O.RegistrationInfo.retired info)
  registeredValue selection _ = false

  familyRegistered : Rule → O.World → Bool
  familyRegistered selection = anyRow (λ key value → registeredValue selection value)

  legacyValue : Rule → O.Record → Bool
  legacyValue selection (O.recordOf owner (O.registration info)) = sameOwner owner (targetOwner selection) ∧
    (not (O.RegistrationInfo.retired info) ∧ O.RegistrationInfo.legacyReadable info)
  legacyValue selection _ = false

  legacyReadable : Rule → O.World → Bool
  legacyReadable selection = anyRow (λ key value → legacyValue selection value)

  liveValue : Rule → O.Record → Bool
  liveValue selection (O.recordOf owner (O.checkout info)) = sameOwner owner (targetOwner selection) ∧ checkoutAvailable info
  liveValue selection _ = false

  checkoutObservation : Rule → Maybe O.Record → Bool
  checkoutObservation selection (just value) = liveValue selection value
  checkoutObservation selection nothing = false

  checkoutLive : Rule → O.World → ℕ → Bool
  checkoutLive selection world key = checkoutObservation selection (DB.lookup key world)

  anyCheckoutLive : Rule → O.World → Bool
  anyCheckoutLive selection = anyRow (λ key value → liveValue selection value)

  deltaValue : O.Owner → ℕ → String → O.Record → Bool
  deltaValue owner selected path (O.recordOf storedOwner (O.deltaBinding checkout version storedPath)) =
    sameOwner owner storedOwner ∧ (sameNat selected checkout ∧ does (path String.≟ storedPath))
  deltaValue owner selected path _ = false

  hasDelta : O.Owner → ℕ → String → O.World → Bool
  hasDelta owner selected path = anyRow (λ key value → deltaValue owner selected path value)

  bindingValue : Rule → O.World → O.Owner → ℕ → String → ℕ → O.Record → Bool
  bindingValue selection world owner selected path version (O.recordOf storedOwner (O.baseBinding storedVersion storedPath)) =
    sameOwner owner storedOwner ∧ (does (path String.≟ storedPath) ∧
      (sameNat version storedVersion ∧ not (hasDelta owner selected path world)))
  bindingValue selection world owner selected path version (O.recordOf storedOwner (O.deltaBinding checkout nothing storedPath)) = false
  bindingValue selection world owner selected path version (O.recordOf storedOwner (O.deltaBinding checkout (just storedVersion) storedPath)) =
    sameOwner owner storedOwner ∧ (sameNat checkout selected ∧
      (does (path String.≟ storedPath) ∧ sameNat version storedVersion))
  bindingValue selection world owner selected path version _ = false

  versionAtPath : Rule → O.World → O.Owner → ℕ → String → ℕ → Bool
  versionAtPath selection world owner selected path version =
    checkoutLive selection world selected ∧
      (included selection owner path ∧ anyRow (λ key value → bindingValue selection world owner selected path version value) world)

  checkoutVersionValue : Rule → O.World → O.Owner → String → ℕ → ℕ → O.Record → Bool
  checkoutVersionValue selection world owner path version key (O.recordOf storedOwner (O.checkout info)) =
    sameOwner owner storedOwner ∧ versionAtPath selection world owner key path version
  checkoutVersionValue selection world owner path version key _ = false

  versionPublishedAtPath : Rule → O.World → O.Owner → String → ℕ → Bool
  versionPublishedAtPath selection world owner path version = anyRow (checkoutVersionValue selection world owner path version) world

  symbolObservation : Rule → O.World → O.Owner → ℕ → Maybe O.Record → Bool
  symbolObservation selection world owner selected (just (O.recordOf storedOwner (O.symbol version path payload))) =
    sameOwner owner storedOwner ∧ versionAtPath selection world owner selected path version
  symbolObservation selection world owner selected _ = false

  symbolVisible : Rule → O.World → O.Owner → ℕ → ℕ → Bool
  symbolVisible selection world owner selected key = symbolObservation selection world owner selected (DB.lookup key world)

  edgeObservation : Rule → O.World → O.Owner → ℕ → Maybe O.Record → Bool
  edgeObservation selection world owner selected (just (O.recordOf storedOwner (O.edge source target payload))) =
    sameOwner owner storedOwner ∧ (symbolVisible selection world owner selected source ∧
      symbolVisible selection world owner selected target)
  edgeObservation selection world owner selected _ = false

  edgeVisible : Rule → O.World → O.Owner → ℕ → ℕ → Bool
  edgeVisible selection world owner selected key = edgeObservation selection world owner selected (DB.lookup key world)

  -- A needed snapshot may contain both included and excluded members. Keeping
  -- its header does NOT make every old member permanently needed.
  project : Rule → O.World → O.Record → O.Record
  project selection world value@(O.recordOf owner (O.structuralSnapshot selected nodes edges payload))
    with ownerEqual owner (targetOwner selection)
  ... | yes _ = O.recordOf owner (O.structuralSnapshot selected
    (filterKeys (symbolVisible selection world owner selected) nodes)
    (filterKeys (edgeVisible selection world owner selected) edges) payload)
  ... | no _ = value
  project selection world value = value

  rootedRole : Rule → O.World → Role → Bool
  rootedRole selection world administrative = true
  rootedRole selection world holder = true
  rootedRole selection world artifact = false
  rootedRole selection world baselineAnchor = familyRegistered selection world ∧ anyCheckoutLive selection world
  rootedRole selection world (baselineBinding path) = familyRegistered selection world ∧
    (anyCheckoutLive selection world ∧ included selection (targetOwner selection) path)
  rootedRole selection world (checkoutBinding selected path) = familyRegistered selection world ∧
    (checkoutLive selection world selected ∧ included selection (targetOwner selection) path)
  rootedRole selection world (snapshot selected) = familyRegistered selection world ∧ checkoutLive selection world selected
  rootedRole selection world (legacyFile path) = familyRegistered selection world ∧
    (legacyReadable selection world ∧ included selection (targetOwner selection) path)
  rootedRole selection world (graphContainer nothing inUse) = inUse ∧ (familyRegistered selection world ∧ anyCheckoutLive selection world)
  rootedRole selection world (graphContainer (just selected) inUse) = inUse ∧ (familyRegistered selection world ∧ checkoutLive selection world selected)
  rootedRole selection world (attached parent gate) = false

  rootedFrom : Rule → O.World → O.Owner → Role → Bool
  rootedFrom selection world owner role with ownerEqual owner (targetOwner selection)
  ... | yes same = rootedRole selection world role
  ... | no different = true

  rooted : Rule → O.World → O.Record → Bool
  rooted selection world value = rootedFrom selection world (O.owner value) (classify (O.body value))

  data Mode : Set where permanent temporary reading : Mode

  temporaryFor : Bool → Mode
  temporaryFor true = reading
  temporaryFor false = temporary

  reader : O.Record → Bool
  reader (O.recordOf owner (O.activeReader refs payload)) = true
  reader _ = false

  readerAt : O.World → ℕ → Bool
  readerAt world source with DB.lookup source world
  ... | just value = reader value
  ... | nothing = false

  readerAtMatches : ∀ world source value → DB.lookup source world ≡ just value → readerAt world source ≡ reader value
  readerAtMatches world source value found rewrite found = refl

  referencesFor : Mode → Rule → O.World → O.Record → List O.Reference
  referencesFor temporary selection world value = O.references (O.body value)
  referencesFor reading selection world value = O.references (O.body value)
  referencesFor permanent selection world value with classify (O.body value)
  ... | holder = []
  ... | _ = O.references (O.body (project selection world value))

  gateAllows : Mode → Rule → O.World → O.Owner → Gate → Bool
  gateAllows temporary selection world owner gate = true
  gateAllows reading selection world owner gate = false
  gateAllows permanent selection world owner content = true
  gateAllows permanent selection world owner (sourcePath version path) =
    versionPublishedAtPath selection world owner path version
  gateAllows permanent selection world owner transient = false

  parentOf : Mode → Rule → O.World → O.Record → Maybe O.Reference
  parentOf reading selection world value = nothing
  parentOf mode selection world value with classify (O.body value)
  ... | attached parent gate = if gateAllows mode selection world (O.owner value) gate then just parent else nothing
  ... | _ = nothing

  data Dependency (mode : Mode) (selection : Rule) (world : O.World) : ℕ → ℕ → Set where
    reference : ∀ source value ref → DB.lookup source world ≡ just value →
      ref ∈ referencesFor mode selection world value →
      O.Resolves world (O.owner value) ref → Dependency mode selection world source (O.target ref)
    attachment : ∀ parent parentValue child childValue →
      DB.lookup parent world ≡ just parentValue → DB.lookup child world ≡ just childValue →
      parentOf mode selection world childValue ≡ just (O.reference parent (O.kind (O.body parentValue))) →
      O.owner parentValue ≡ O.owner childValue → Dependency mode selection world parent child

  -- Least rooted closure: an orphan cycle cannot justify its own retention.
  data Needed (selection : Rule) (world : O.World) : ℕ → Set where
    root : ∀ key value → DB.lookup key world ≡ just value → rooted selection world value ≡ true → Needed selection world key
    required : ∀ {source target} → Needed selection world source →
      Dependency permanent selection world source target → Needed selection world target

  heldReferences : O.Record → List O.Reference
  heldReferences value with classify (O.body value)
  ... | holder = O.references (O.body value)
  ... | _ = []

  -- The origin fixes the dependency interpretation. A search follows its
  -- actual saved roots and strong dependencies; work keeps its existing scope.
  mutual
    data Protected (selection : Rule) (world : O.World) : ℕ → Set where
      held : ∀ source value ref → DB.lookup source world ≡ just value →
        ref ∈ heldReferences value → O.Resolves world (O.owner value) ref → Protected selection world (O.target ref)
      required : ∀ {source target} → (previous : Protected selection world source) →
        Dependency (temporaryFor (readerOrigin previous)) selection world source target → Protected selection world target

    readerOrigin : ∀ {selection world key} → Protected selection world key → Bool
    readerOrigin (held source value ref found included resolved) = reader value
    readerOrigin (required previous dependency) = readerOrigin previous

  holdingReferences : ∀ flag selection world value → referencesFor (temporaryFor flag) selection world value ≡ O.references (O.body value)
  holdingReferences true selection world value = refl
  holdingReferences false selection world value = refl

  requireReference : ∀ {selection world} source value ref → Protected selection world source → DB.lookup source world ≡ just value →
    ref ∈ O.references (O.body value) → O.Resolves world (O.owner value) ref → Protected selection world (O.target ref)
  requireReference {selection} {world} source value ref previous found included resolved = required previous
    (reference source value ref found
      (Relation.Binary.PropositionalEquality.subst (λ refs → ref ∈ refs) (sym (holdingReferences (readerOrigin previous) selection world value)) included) resolved)

  -- Reading dependencies are exactly actual typed strong references. Both
  -- saved-view members and their prerequisites remain retained; mere
  -- attachment to the same file version does not add another read.
  ReadReference : O.World → ℕ → ℕ → Set
  ReadReference world source target = Σ O.Record (λ value → DB.lookup source world ≡ just value ×
    Σ O.Reference (λ ref → ref ∈ O.references (O.body value) × (O.target ref ≡ target × O.Resolves world (O.owner value) ref)))

  readingDependency : ∀ {selection world source target} → Dependency reading selection world source target → ReadReference world source target
  readingDependency (reference source value ref found included resolved) = value , found , ref , included , refl , resolved
  readingDependency (attachment parent parentValue child childValue parentFound childFound () sameOwner)

  referenceIsReadingDependency : ∀ selection world source target → ReadReference world source target → Dependency reading selection world source target
  referenceIsReadingDependency selection world source target (value , found , ref , included , refl , resolved) =
    reference source value ref found included resolved

  referenceKeepsOrigin : ∀ {selection world} source value ref (previous : Protected selection world source) found included resolved →
    readerOrigin (requireReference source value ref previous found included resolved) ≡ readerOrigin previous
  referenceKeepsOrigin source value ref previous found included resolved = refl

  -- Capture every owned key, including records whose registry/pointer is gone.
  -- Eligibility is decided separately; metadata cannot be deleted by the core.
  capture : Rule → O.World → List ℕ
  capture selection [] = []
  capture selection ((key , value) ∷ rows) with ownerEqual (O.owner value) (targetOwner selection)
  ... | yes _ = key ∷ capture selection rows
  ... | no _ = capture selection rows

  captureComplete : ∀ selection world key value → (key , value) ∈ world →
    O.owner value ≡ targetOwner selection → key ∈ capture selection world
  captureComplete selection ((key , value) ∷ rows) .key .value (here refl) owned
    with ownerEqual (O.owner value) (targetOwner selection)
  ... | yes _ = here refl
  ... | no different = ⊥-elim (different owned)
  captureComplete selection ((other , stored) ∷ rows) key value (there present) owned
    with ownerEqual (O.owner stored) (targetOwner selection)
  ... | yes _ = there (captureComplete selection rows key value present owned)
  ... | no _ = captureComplete selection rows key value present owned

  record Intent (selection : Rule) (before : O.World) : Set where
    field keys : List ℕ
          covers : ∀ key value → (key , value) ∈ before → O.owner value ≡ targetOwner selection → key ∈ keys
          uniqueBefore : O.Unique before

  captureIntent : ∀ selection before → O.Unique before → Intent selection before
  captureIntent selection before unique = record
    { keys = capture selection before; covers = captureComplete selection before; uniqueBefore = unique }

  record Safety (selection : Rule) (before after : O.World) : Set where
    field
      unrelated : ∀ key value → DB.lookup key before ≡ just value → O.owner value ≢ targetOwner selection →
        DB.lookup key after ≡ just value
      metadata : ∀ key value → DB.lookup key before ≡ just value → indexed value ≡ false →
        DB.lookup key after ≡ just value
      needed : ∀ key value → DB.lookup key before ≡ just value → Needed selection before key →
        Σ O.Record (λ retained → (DB.lookup key after ≡ just retained) ×
          ((project selection before retained ≡ project selection before value) ×
            ((∀ member → member ∈ snapshotNodes retained → member ∈ snapshotNodes value) ×
             (∀ member → member ∈ snapshotEdges retained → member ∈ snapshotEdges value))))
      protected : ∀ key value → DB.lookup key before ≡ just value → Protected selection before key →
        DB.lookup key after ≡ just value

  -- Safety holds even before the first step. Mixed snapshots may retain old
  -- members while waiting for readers, but cannot lose a still-needed member.
  safetyReflexive : ∀ selection world → Safety selection world world
  safetyReflexive selection world = record
    { unrelated = λ key value present distinct → present
    ; metadata = λ key value present control → present
    ; needed = λ key value present live → value , (present , (refl , ((λ member seen → seen) , (λ member seen → seen))))
    ; protected = λ key value present pinned → present
    }

  -- Accepted capture and current assessment are separate worlds. Indexing may
  -- advance while the immutable set of captured incarnation IDs stays fixed.
  record Complete (selection : Rule) (accepted : O.World) (intent : Intent selection accepted)
    (before after : O.World) : Set where
    field
      safety : Safety selection before after
      uniqueAfter : O.Unique after
      canonical : ∀ key value → key ∈ Intent.keys intent → DB.lookup key before ≡ just value →
        Needed selection before key → DB.lookup key after ≡ just (project selection before value)
      outsideCapture : ∀ key value → DB.lookup key before ≡ just value → key ∉ Intent.keys intent →
        DB.lookup key after ≡ just value
      reclaimed : ∀ key value → key ∈ Intent.keys intent → DB.lookup key before ≡ just value →
        O.owner value ≡ targetOwner selection → indexed value ≡ true → ¬ Needed selection before key →
        DB.lookup key after ≡ nothing
      noNewRecords : ∀ key value → (key , value) ∈ after → Σ O.Record (λ original → DB.lookup key before ≡ just original)

  completeRemovesUnneeded : ∀ selection accepted intent before after key value → Complete selection accepted intent before after →
    key ∈ Intent.keys intent → DB.lookup key before ≡ just value → O.owner value ≡ targetOwner selection →
    indexed value ≡ true → ¬ Needed selection before key → DB.lookup key after ≡ nothing
  completeRemovesUnneeded selection accepted intent before after key value completed = Complete.reclaimed completed key value

  completePreservesNeeded : ∀ selection accepted intent before after key value → Complete selection accepted intent before after →
    key ∈ Intent.keys intent → DB.lookup key before ≡ just value → Needed selection before key →
    DB.lookup key after ≡ just (project selection before value)
  completePreservesNeeded selection accepted intent before after key value completed = Complete.canonical completed key value

  temporaryNeedDoesNotPermitEarlyCompletion : ∀ selection accepted intent before after key value →
    key ∈ Intent.keys intent → DB.lookup key before ≡ just value → O.owner value ≡ targetOwner selection →
    indexed value ≡ true → Protected selection before key → ¬ Needed selection before key →
    ¬ Complete selection accepted intent before after
  temporaryNeedDoesNotPermitEarlyCompletion selection accepted intent before after key value captured present owned index protected unneeded completed
    with trans (sym (Safety.protected (Complete.safety completed) key value present protected))
      (Complete.reclaimed completed key value captured present owned index unneeded)
  ... | ()

  sourceDependencyIsNeeded : ∀ {selection world source target} → Needed selection world source →
    Dependency permanent selection world source target → Needed selection world target
  sourceDependencyIsNeeded = Needed.required

  activeWorkProtectsDependency : ∀ {selection world source target} → (previous : Protected selection world source) →
    Dependency (temporaryFor (readerOrigin previous)) selection world source target → Protected selection world target
  activeWorkProtectsDependency = Protected.required

  -- Rootless components, including cycles, cannot retain themselves merely
  -- because their rows reference one another. Incoming dependencies must stay
  -- inside the component; the theorem is independent of any cleanup algorithm.
  rootlessComponentIsUnneeded : ∀ selection world (component : ℕ → Set) →
    (∀ key value → component key → DB.lookup key world ≡ just value →
      ¬ (rooted selection world value ≡ true)) →
    (∀ {source target} → Dependency permanent selection world source target → component target → component source) →
    ∀ key → component key → ¬ Needed selection world key
  rootlessComponentIsUnneeded selection world component noRoots closed key inside
    (Needed.root .key value present live) = noRoots key value inside present live
  rootlessComponentIsUnneeded selection world component noRoots closed key inside
    (Needed.required sourceNeeded dependency) =
    rootlessComponentIsUnneeded selection world component noRoots closed _ (closed dependency inside) sourceNeeded

  completePreservesUnrelated : ∀ selection accepted intent before after key value →
    Complete selection accepted intent before after → DB.lookup key before ≡ just value →
    O.owner value ≢ targetOwner selection → DB.lookup key after ≡ just value
  completePreservesUnrelated selection accepted intent before after key value completed =
    Safety.unrelated (Complete.safety completed) key value

  completePreservesMetadata : ∀ selection accepted intent before after key value →
    Complete selection accepted intent before after → DB.lookup key before ≡ just value →
    indexed value ≡ false → DB.lookup key after ≡ just value
  completePreservesMetadata selection accepted intent before after key value completed =
    Safety.metadata (Complete.safety completed) key value

  projectedOwnerIsUnchanged : ∀ selection world owner selected nodes edges payload →
    O.owner (project selection world (O.recordOf owner (O.structuralSnapshot selected nodes edges payload))) ≡ owner
  projectedOwnerIsUnchanged selection world owner selected nodes edges payload
    with ownerEqual owner (targetOwner selection)
  ... | yes _ = refl
  ... | no _ = refl

  projectedNodesAreVisible : ∀ selection world selected nodes edges payload key →
    key ∈ snapshotNodes (project selection world
      (O.recordOf (targetOwner selection) (O.structuralSnapshot selected nodes edges payload))) →
    symbolVisible selection world (targetOwner selection) selected key ≡ true
  projectedNodesAreVisible selection world selected nodes edges payload key present
    with ownerEqual (targetOwner selection) (targetOwner selection)
  ... | yes _ = filterKeysSound (symbolVisible selection world (targetOwner selection) selected) nodes key present
  ... | no different = ⊥-elim (different refl)

  projectedEdgesAreVisible : ∀ selection world selected nodes edges payload key →
    key ∈ snapshotEdges (project selection world
      (O.recordOf (targetOwner selection) (O.structuralSnapshot selected nodes edges payload))) →
    edgeVisible selection world (targetOwner selection) selected key ≡ true
  projectedEdgesAreVisible selection world selected nodes edges payload key present
    with ownerEqual (targetOwner selection) (targetOwner selection)
  ... | yes _ = filterKeysSound (edgeVisible selection world (targetOwner selection) selected) edges key present
  ... | no different = ⊥-elim (different refl)
