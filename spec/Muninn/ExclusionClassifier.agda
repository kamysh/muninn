{-# OPTIONS --safe #-}
-- Effective decisions for the independently fixed whole-world outcome model.
module Muninn.ExclusionClassifier where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.FiniteClosure as F
open import Data.Nat using (ℕ; _≟_)
open import Data.Bool using (Bool; true; false)
import Data.Bool.Properties as BoolProperties
open import Data.String using (String)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
module DB = O.DB

mapDecision : ∀ {A B : Set} → (A → B) → (B → A) → Dec A → Dec B
mapDecision forward backward (yes proof) = yes (forward proof)
mapDecision forward backward (no denied) = no (λ proof → denied (backward proof))

both : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
both (no denied) right = no (λ proof → denied (proj₁ proof))
both (yes left) (no denied) = no (λ proof → denied (proj₂ proof))
both (yes left) (yes right) = yes (left , right)

either : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
either (yes proof) right = yes (inj₁ proof)
either (no left) (yes proof) = yes (inj₂ proof)
either (no left) (no right) = no (λ { (inj₁ proof) → left proof; (inj₂ proof) → right proof })

true? : ∀ b → Dec (b ≡ true)
true? true = yes refl
true? false = no (λ ())

-- A checked retraction makes kind equality decidable without comparing payloads.
kindCode : O.Kind → ℕ
kindCode O.registrationK = 0
kindCode O.checkoutK = 1
kindCode O.creationIntentK = 2
kindCode O.defaultsK = 3
kindCode O.policyVersionK = 4
kindCode O.currentPolicyK = 5
kindCode O.noteK = 6
kindCode O.notePostingK = 7
kindCode O.noteVectorK = 8
kindCode O.fileVersionK = 9
kindCode O.baseBindingK = 10
kindCode O.deltaBindingK = 11
kindCode O.basePointerK = 12
kindCode O.chunkK = 13
kindCode O.postingK = 14
kindCode O.vectorK = 15
kindCode O.symbolK = 16
kindCode O.edgeK = 17
kindCode O.structuralSnapshotK = 18
kindCode O.legacyK = 19
kindCode O.stagingK = 20
kindCode O.acceptedWorkK = 21
kindCode O.cleanupWorkK = 22
kindCode O.activeReaderK = 23
kindCode O.continuationK = 24
kindCode O.receiptK = 25
kindCode O.migrationK = 26
kindCode O.usageK = 27
kindCode O.bootstrapK = 28
kindCode O.modelCacheK = 29
kindCode O.coordinationK = 30
kindCode O.schemaResourceK = 31
kindCode O.graphResourceK = 32
kindCode O.logFileK = 33
kindCode O.bootstrapStageK = 34
kindCode O.publishedViewK = 35

kindFromCode : ℕ → Maybe O.Kind
kindFromCode number = nth number
  (
    O.registrationK ∷ O.checkoutK ∷ O.creationIntentK ∷ O.defaultsK ∷
    O.policyVersionK ∷ O.currentPolicyK ∷ O.noteK ∷ O.notePostingK ∷
    O.noteVectorK ∷ O.fileVersionK ∷ O.baseBindingK ∷ O.deltaBindingK ∷
    O.basePointerK ∷ O.chunkK ∷ O.postingK ∷ O.vectorK ∷
    O.symbolK ∷ O.edgeK ∷ O.structuralSnapshotK ∷ O.legacyK ∷
    O.stagingK ∷ O.acceptedWorkK ∷ O.cleanupWorkK ∷ O.activeReaderK ∷
    O.continuationK ∷ O.receiptK ∷ O.migrationK ∷ O.usageK ∷
    O.bootstrapK ∷ O.modelCacheK ∷ O.coordinationK ∷ O.schemaResourceK ∷
    O.graphResourceK ∷ O.logFileK ∷ O.bootstrapStageK ∷ O.publishedViewK ∷
    [])
  where
  nth : ℕ → List O.Kind → Maybe O.Kind
  nth number [] = nothing
  nth Data.Nat.zero (kind ∷ kinds) = just kind
  nth (Data.Nat.suc number) (kind ∷ kinds) = nth number kinds

kindRoundTrip : ∀ kind → kindFromCode (kindCode kind) ≡ just kind

kindRoundTrip O.registrationK = refl
kindRoundTrip O.checkoutK = refl
kindRoundTrip O.creationIntentK = refl
kindRoundTrip O.defaultsK = refl
kindRoundTrip O.policyVersionK = refl
kindRoundTrip O.currentPolicyK = refl
kindRoundTrip O.noteK = refl
kindRoundTrip O.notePostingK = refl
kindRoundTrip O.noteVectorK = refl
kindRoundTrip O.fileVersionK = refl
kindRoundTrip O.baseBindingK = refl
kindRoundTrip O.deltaBindingK = refl
kindRoundTrip O.basePointerK = refl
kindRoundTrip O.chunkK = refl
kindRoundTrip O.postingK = refl
kindRoundTrip O.vectorK = refl
kindRoundTrip O.symbolK = refl
kindRoundTrip O.edgeK = refl
kindRoundTrip O.structuralSnapshotK = refl
kindRoundTrip O.legacyK = refl
kindRoundTrip O.stagingK = refl
kindRoundTrip O.acceptedWorkK = refl
kindRoundTrip O.cleanupWorkK = refl
kindRoundTrip O.activeReaderK = refl
kindRoundTrip O.continuationK = refl
kindRoundTrip O.receiptK = refl
kindRoundTrip O.migrationK = refl
kindRoundTrip O.usageK = refl
kindRoundTrip O.bootstrapK = refl
kindRoundTrip O.modelCacheK = refl
kindRoundTrip O.coordinationK = refl
kindRoundTrip O.schemaResourceK = refl
kindRoundTrip O.graphResourceK = refl
kindRoundTrip O.logFileK = refl
kindRoundTrip O.bootstrapStageK = refl
kindRoundTrip O.publishedViewK = refl

kindEqual : ∀ a b → Dec (a ≡ b)
kindEqual a b with kindCode a ≟ kindCode b
... | yes same = yes (just-injective (trans (sym (kindRoundTrip a))
    (trans (cong kindFromCode same) (kindRoundTrip b))))
... | no different = no (λ same → different (cong kindCode same))

referenceEqual : (a b : O.Reference) → Dec (a ≡ b)
referenceEqual (O.reference a ka) (O.reference b kb) with a ≟ b | kindEqual ka kb
... | yes refl | yes refl = yes refl
... | no different | _ = no (λ { refl → different refl })
... | _ | no different = no (λ { refl → different refl })

parentEqual : (a : Maybe O.Reference) → (ref : O.Reference) → Dec (a ≡ just ref)
parentEqual nothing ref = no (λ ())
parentEqual (just stored) ref = mapDecision (cong just) just-injective (referenceEqual stored ref)

mayReference? : ∀ source target → Dec (O.MayReference source target)
mayReference? source O.installation = yes O.shared
mayReference? source target@(O.family id) with E.ownerEqual source target
... | yes refl = yes O.own
... | no different = no (λ { O.own → different refl })

At : O.World → ℕ → (O.Record → Set) → Set
At world key P = Σ O.Record (λ value → DB.lookup key world ≡ just value × P value)

at? : ∀ world key P → (∀ value → Dec (P value)) → Dec (At world key P)
at? world key P decide = inspect (DB.lookup key world)
  where
  inspect : ∀ snapshot → Dec (Σ O.Record (λ value → snapshot ≡ just value × P value))
  inspect nothing = no (λ { (_ , () , _) })
  inspect (just value) with decide value
  ... | yes proof = yes (value , refl , proof)
  ... | no denied = no (λ { (other , equal , proof) → denied
      (subst P (sym (just-injective equal)) proof) })

resolves? : ∀ world owner ref → Dec (O.Resolves world owner ref)
resolves? world owner ref = mapDecision
  (λ { (value , found , kind , allowed) → record
    { value = value; found = found; rightKind = kind; rightOwner = allowed } })
  (λ proof → O.Resolves.value proof , O.Resolves.found proof ,
    O.Resolves.rightKind proof , O.Resolves.rightOwner proof)
  (at? world (O.target ref) (λ value → O.kind (O.body value) ≡ O.expected ref × O.MayReference owner (O.owner value))
    (λ value → both (kindEqual (O.kind (O.body value)) (O.expected ref)) (mayReference? owner (O.owner value))))

keys : O.World → List ℕ
keys = map proj₁

foundInKeys : ∀ world key value → DB.lookup key world ≡ just value → key ∈ keys world
foundInKeys [] key value ()
foundInKeys ((other , stored) ∷ rows) key value found with key ≟ other
... | yes same = here same
... | no different = there (foundInKeys rows key value found)

module Model (excluded : List String → String → Bool) where
  module M = E.Model excluded

  module Assessment (selection : E.Rule) (world : O.World) where
    ReferenceEvidence : M.Mode → ℕ → ℕ → Set
    ReferenceEvidence mode source target = At world source (λ value →
      Σ O.Reference (λ ref → ref ∈ M.referencesFor mode selection world value ×
        (O.target ref ≡ target × O.Resolves world (O.owner value) ref)))

    reference? : ∀ mode source target → Dec (ReferenceEvidence mode source target)
    reference? mode source target = at? world source _ (λ value →
      F.choose (λ ref → O.target ref ≡ target × O.Resolves world (O.owner value) ref)
        (λ ref → both (O.target ref ≟ target) (resolves? world (O.owner value) ref))
        (M.referencesFor mode selection world value))

    AttachmentEvidence : M.Mode → ℕ → ℕ → Set
    AttachmentEvidence mode parent child = At world parent (λ parentValue →
      At world child (λ childValue →
        M.parentOf mode selection world childValue ≡ just (O.reference parent (O.kind (O.body parentValue))) ×
        O.owner parentValue ≡ O.owner childValue))

    attachment? : ∀ mode parent child → Dec (AttachmentEvidence mode parent child)
    attachment? mode parent child = at? world parent _ (λ parentValue → at? world child _
      (λ childValue → both
        (parentEqual (M.parentOf mode selection world childValue) (O.reference parent (O.kind (O.body parentValue))))
        (E.ownerEqual (O.owner parentValue) (O.owner childValue))))

    dependency? : ∀ mode source target → Dec (M.Dependency mode selection world source target)
    dependency? mode source target = mapDecision forward backward (either (reference? mode source target) (attachment? mode source target))
      where
      forward : ReferenceEvidence mode source target ⊎ AttachmentEvidence mode source target → M.Dependency mode selection world source target
      forward (inj₁ (value , found , ref , present , refl , resolved)) = M.reference source value ref found present resolved
      forward (inj₂ (parentValue , parentFound , childValue , childFound , parent , owner)) =
        M.attachment source parentValue target childValue parentFound childFound parent owner
      backward : M.Dependency mode selection world source target → ReferenceEvidence mode source target ⊎ AttachmentEvidence mode source target
      backward (M.reference source value ref found present resolved) = inj₁ (value , found , ref , present , refl , resolved)
      backward (M.attachment parent parentValue child childValue parentFound childFound attached sameOwner) =
        inj₂ (parentValue , parentFound , childValue , childFound , attached , sameOwner)

    dependencyTargetIn : ∀ mode {source target} → M.Dependency mode selection world source target → target ∈ keys world
    dependencyTargetIn mode (M.reference source value ref found present resolved) =
      foundInKeys world (O.target ref) (O.Resolves.value resolved) (O.Resolves.found resolved)
    dependencyTargetIn mode (M.attachment parent parentValue child childValue parentFound childFound attached sameOwner) =
      foundInKeys world child childValue childFound

    Root : ℕ → Set
    Root key = At world key (λ value → M.rooted selection world value ≡ true)

    root? : ∀ key → Dec (Root key)
    root? key = at? world key _ (λ value → true? (M.rooted selection world value))

    rootIn : ∀ {key} → Root key → key ∈ keys world
    rootIn (value , found , rooted) = foundInKeys world _ value found

    HeldAt : ℕ → ℕ → Set
    HeldAt target source = At world source (λ value → Σ O.Reference (λ ref →
      ref ∈ M.heldReferences value × (O.target ref ≡ target × O.Resolves world (O.owner value) ref)))

    heldAt? : ∀ target source → Dec (HeldAt target source)
    heldAt? target source = at? world source _ (λ value →
      F.choose (λ ref → O.target ref ≡ target × O.Resolves world (O.owner value) ref)
        (λ ref → both (O.target ref ≟ target) (resolves? world (O.owner value) ref)) (M.heldReferences value))

    Held : ℕ → Set
    Held target = Σ ℕ (λ source → source ∈ keys world × HeldAt target source)

    held? : ∀ key → Dec (Held key)
    held? key = F.choose (HeldAt key) (heldAt? key) (keys world)

    heldIn : ∀ {key} → Held key → key ∈ keys world
    heldIn (source , sourceIn , value , found , ref , present , refl , resolved) =
      foundInKeys world (O.target ref) (O.Resolves.value resolved) (O.Resolves.found resolved)

    module Permanent = F.Closure Root (M.Dependency M.permanent selection world)
      root? (dependency? M.permanent) (keys world) rootIn (dependencyTargetIn M.permanent)

    toNeeded : ∀ {key} → Permanent.Reach key → M.Needed selection world key
    toNeeded (Permanent.root (value , found , rooted)) = M.root _ value found rooted
    toNeeded (Permanent.step previous dependency) = M.required (toNeeded previous) dependency

    fromNeeded : ∀ {key} → M.Needed selection world key → Permanent.Reach key
    fromNeeded (M.root key value found rooted) = Permanent.root (value , found , rooted)
    fromNeeded (M.required previous dependency) = Permanent.step (fromNeeded previous) dependency

    HeldWith : Bool → ℕ → ℕ → Set
    HeldWith flag target source = At world source (λ value → M.reader value ≡ flag ×
      Σ O.Reference (λ ref → ref ∈ M.heldReferences value ×
        (O.target ref ≡ target × O.Resolves world (O.owner value) ref)))

    heldWith? : ∀ flag target source → Dec (HeldWith flag target source)
    heldWith? flag target source = at? world source _ (λ value → both (BoolProperties._≟_ (M.reader value) flag)
      (F.choose (λ ref → O.target ref ≡ target × O.Resolves world (O.owner value) ref)
        (λ ref → both (O.target ref ≟ target) (resolves? world (O.owner value) ref)) (M.heldReferences value)))

    module Temporary (flag : Bool) where
      Seed : ℕ → Set
      Seed target = Σ ℕ (λ source → source ∈ keys world × HeldWith flag target source)

      seed? : ∀ key → Dec (Seed key)
      seed? key = F.choose (HeldWith flag key) (heldWith? flag key) (keys world)

      seedIn : ∀ {key} → Seed key → key ∈ keys world
      seedIn (source , sourceIn , value , found , origin , ref , present , refl , resolved) =
        foundInKeys world (O.target ref) (O.Resolves.value resolved) (O.Resolves.found resolved)

      module Closure = F.Closure Seed (M.Dependency (M.temporaryFor flag) selection world)
        seed? (dependency? (M.temporaryFor flag)) (keys world) seedIn (dependencyTargetIn (M.temporaryFor flag))
      open Closure public

      mutual
        toProtected : ∀ {key} → Reach key → M.Protected selection world key
        toProtected (root (source , sourceIn , value , found , origin , ref , present , refl , resolved)) =
          M.held source value ref found present resolved
        toProtected (step previous dependency) = M.required (toProtected previous)
          (subst (λ mode → M.Dependency mode selection world _ _) (cong M.temporaryFor (sym (originIsReader previous))) dependency)

        originIsReader : ∀ {key} (path : Reach key) → M.readerOrigin (toProtected path) ≡ flag
        originIsReader (root (source , sourceIn , value , found , origin , ref , present , refl , resolved)) = origin
        originIsReader (step previous dependency) = originIsReader previous

      fromProtected : ∀ {key} (pin : M.Protected selection world key) → M.readerOrigin pin ≡ flag → Reach key
      fromProtected (M.held source value ref found present resolved) origin = root
        (source , foundInKeys world source value found , value , found , origin , ref , present , refl , resolved)
      fromProtected (M.required previous dependency) origin = step (fromProtected previous origin)
        (subst (λ mode → M.Dependency mode selection world _ _) (cong M.temporaryFor origin) dependency)

    module Readers = Temporary true
    module Background = Temporary false

    toProtected : ∀ {key} → Readers.Reach key ⊎ Background.Reach key → M.Protected selection world key
    toProtected (inj₁ path) = Readers.toProtected path
    toProtected (inj₂ path) = Background.toProtected path

    fromProtected : ∀ {key} → M.Protected selection world key → Readers.Reach key ⊎ Background.Reach key
    fromProtected pin with M.readerOrigin pin in origin
    ... | true = inj₁ (Readers.fromProtected pin origin)
    ... | false = inj₂ (Background.fromProtected pin origin)

    needed? : ∀ key → Dec (M.Needed selection world key)
    needed? key = mapDecision toNeeded fromNeeded (Permanent.decide key)

    protected? : ∀ key → Dec (M.Protected selection world key)
    protected? key = mapDecision toProtected fromProtected (either (Readers.decide key) (Background.decide key))

    -- Independent evidence: a record can be needed AND protected. No priority
    -- enum may discard its lease and permit premature snapshot rewriting.
    classify : ∀ key → Dec (M.Needed selection world key) × Dec (M.Protected selection world key)
    classify key = needed? key , protected? key

    neededKeys : List ℕ
    neededKeys = Permanent.Saturated.known Permanent.saturation

    protectedKeys : List ℕ
    protectedKeys = Readers.Saturated.known Readers.saturation ++ Background.Saturated.known Background.saturation

    neededSound : ∀ {key} → key ∈ neededKeys → M.Needed selection world key
    neededSound present = toNeeded (Permanent.Saturated.sound Permanent.saturation present)

    neededComplete : ∀ {key} → M.Needed selection world key → key ∈ neededKeys
    neededComplete needed = Permanent.complete (fromNeeded needed)

    protectedSound : ∀ {key} → key ∈ protectedKeys → M.Protected selection world key
    protectedSound present with ∈-++⁻ (Readers.Saturated.known Readers.saturation) present
    ... | inj₁ reader = Readers.toProtected (Readers.Saturated.sound Readers.saturation reader)
    ... | inj₂ work = Background.toProtected (Background.Saturated.sound Background.saturation work)

    protectedComplete : ∀ {key} → M.Protected selection world key → key ∈ protectedKeys
    protectedComplete protected with fromProtected protected
    ... | inj₁ reader = ∈-++⁺ˡ (Readers.complete reader)
    ... | inj₂ work = ∈-++⁺ʳ (Readers.Saturated.known Readers.saturation) (Background.complete work)
