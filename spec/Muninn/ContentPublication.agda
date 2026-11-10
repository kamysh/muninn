{-# OPTIONS --safe #-}
-- Fixed publication intent over owned rows. Storage must realize this intent;
-- neither a handler nor a storage adapter can choose a weaker success predicate.
module Muninn.ContentPublication where

import Muninn.ContentViews as Content
import Muninn.ExclusionOutcomes as E
import Muninn.OwnedState as O
import Muninn.IndexControl as IndexControl
import Muninn.StoredPolicy as Policy
import Muninn.PublishedViews as Views
import Muninn.ReceiptLedger as Ledger
import Muninn.ReceiptTypes as R
import Muninn.RequestIdentity as Identity
import Muninn.CatalogInputs as I
import Muninn.Dialogue as D
import Muninn.ExclusionClassifier as Classify
open import Muninn.Types using (FilePath)
open import Data.Nat using (ℕ; _≟_)
import Data.Bool as Bool
open import Data.Bool using (Bool; true; false)
open import Data.String using (String)
open import Data.List using (List)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
module DB = O.DB
module Exec = O.Execution
module Files = Content.Files
module M = E.Model

entryEqual : (first second : Content.Entry) → Dec (first ≡ second)
entryEqual (Content.entry version ignored) (Content.entry other otherIgnored) with version ≟ other | ignored Bool.≟ otherIgnored
... | yes refl | yes refl = yes refl
... | no different | _ = no (λ same → different (cong Content.Entry.version same))
... | _ | no different = no (λ same → different (cong Content.Entry.gitDefault same))

maybeEqual : (first second : Maybe Content.Entry) → Dec (first ≡ second)
maybeEqual nothing nothing = yes refl
maybeEqual nothing (just _) = no (λ ())
maybeEqual (just _) nothing = no (λ ())
maybeEqual (just first) (just second) with entryEqual first second
... | yes refl = yes refl
... | no different = no (λ same → different (just-injective same))

-- One model for base publication and non-base publication. Desired is the
-- completed selected checkout map, independent of the rows used to store it.
module Plan (selection : E.Rule) (before : O.World) (selected : ℕ)
  (advanceBase : Bool) (desired : Files.Manifest) where
  module C = Content.Family selection

  safeDesired : Files.Manifest
  safeDesired path = C.mask path (desired path)

  nextBase : Files.Manifest
  nextBase = Bool.if_then_else_ advanceBase safeDesired (λ path → C.mask path (C.base before path))

  intended : ℕ → Files.Manifest
  intended checkout with checkout ≟ selected
  ... | yes same = safeDesired
  ... | no different = C.visible before checkout

  nextOverlay : ℕ → Files.Overlay
  nextOverlay checkout = Files.overlayForFiles maybeEqual nextBase (intended checkout)

  resolves : ∀ checkout path → Files.applyOverride (nextBase path) (nextOverlay checkout path) ≡ intended checkout path
  resolves checkout path = Files.fileDifferenceResolves maybeEqual (nextBase path) (intended checkout path)

  minimal : ∀ checkout → Files.MinimalOverlay nextBase (nextOverlay checkout)
  minimal checkout path = Files.fileDifferenceMinimal maybeEqual (nextBase path) (intended checkout path)

  selectedIntent : ∀ path → intended selected path ≡ safeDesired path
  selectedIntent path with selected ≟ selected
  ... | yes same = refl
  ... | no different = ⊥-elim (different refl)

  otherIntent : ∀ checkout → checkout ≢ selected → ∀ path → intended checkout path ≡ C.visible before checkout path
  otherIntent checkout distinct path with checkout ≟ selected
  ... | yes same = ⊥-elim (distinct same)
  ... | no different = refl

  intendedFiltered : ∀ checkout path → C.mask path (intended checkout path) ≡ intended checkout path
  intendedFiltered checkout path with checkout ≟ selected
  ... | yes same = C.maskIdempotent path (desired path)
  ... | no different = C.maskIdempotent path (C.rawView before checkout path)

  Existing : ℕ → Set
  Existing checkout = Σ O.CheckoutInfo (λ info → DB.lookup checkout before ≡ just (O.recordOf (E.targetOwner selection) (O.checkout info)))

  -- These are representation obligations, not configurable goals. Their right
  -- sides are calculated above from the actual before-world and latest rule.
  record Represents (after : O.World) : Set where
    field baseExact : ∀ path → C.base after path ≡ nextBase path
          overlayExact : ∀ checkout → Existing checkout → ∀ path → C.overlay after checkout path ≡ nextOverlay checkout path
          consistent : C.WellFormed after

  rawIntended : ∀ after → Represents after → ∀ checkout → Existing checkout → ∀ path → C.rawView after checkout path ≡ intended checkout path
  rawIntended after represented checkout exists path rewrite Represents.baseExact represented path | Represents.overlayExact represented checkout exists path = resolves checkout path

  visibleIntended : ∀ after → Represents after → ∀ checkout → Existing checkout → ∀ path → C.visible after checkout path ≡ intended checkout path
  visibleIntended after represented checkout exists path = trans
    (cong (C.mask path) (rawIntended after represented checkout exists path)) (intendedFiltered checkout path)

  selectedView : ∀ after → Represents after → Existing selected → ∀ path → C.visible after selected path ≡ safeDesired path
  selectedView after represented exists path = trans (visibleIntended after represented selected exists path) (selectedIntent path)

  otherView : ∀ after → Represents after → ∀ checkout → Existing checkout → checkout ≢ selected → ∀ path →
    C.visible after checkout path ≡ C.visible before checkout path
  otherView after represented checkout exists distinct path = trans (visibleIntended after represented checkout exists path) (otherIntent checkout distinct path)

  noResurrection : ∀ after → Represents after → ∀ checkout → Existing checkout → ∀ path saved →
    C.rawView after checkout path ≡ just saved →
    M.includedWithGit selection (E.targetOwner selection) (Content.Entry.gitDefault saved) (FilePath.value path) ≡ true
  noResurrection after represented checkout exists path saved found = C.includedResult path (C.rawView after checkout path) saved
    (trans (visibleIntended after represented checkout exists path) (trans (sym (rawIntended after represented checkout exists path)) found))

  minimalStored : ∀ after → Represents after → ∀ checkout → Existing checkout → Files.MinimalOverlay (C.base after) (C.overlay after checkout)
  minimalStored after represented checkout exists path rewrite Represents.baseExact represented path | Represents.overlayExact represented checkout exists path = minimal checkout path

-- The guard is executed inside the shared DB transaction. A plan prepared for
-- an older immutable policy version cannot publish after the pointer advances.
policyVersion : O.Body → Maybe ℕ
policyVersion (O.currentPolicy version) = just version
policyVersion _ = nothing

policyVersion? : ∀ expected body → Dec (policyVersion body ≡ just expected)
policyVersion? expected body with policyVersion body
... | nothing = no (λ ())
... | just actual with actual ≟ expected
...   | yes refl = yes refl
...   | no different = no (λ same → different (just-injective same))

policyBody : ∀ body expected → policyVersion body ≡ just expected → body ≡ O.currentPolicy expected
policyBody (O.currentPolicy actual) expected same with just-injective same
... | refl = refl

module PolicyGuard (owner : O.Owner) (pointer expected : ℕ) where
  At : O.World → Set
  At world = Classify.At world pointer (λ value → O.owner value ≡ owner × policyVersion (O.body value) ≡ just expected) ×
    E.pendingRemovalFor owner world ≡ false

  at? : ∀ world → Dec (At world)
  at? world = Classify.both (Classify.at? world pointer _ (λ value → Classify.both
    (E.ownerEqual (O.owner value) owner) (policyVersion? expected (O.body value))))
    (E.pendingRemovalFor owner world Bool.≟ false)

  foundAt : ∀ world → At world → DB.lookup pointer world ≡ just (O.recordOf owner (O.currentPolicy expected))
  foundAt world ((O.recordOf actualOwner body , found , owned , version) , noRemoval)
    rewrite owned | policyBody body expected version = found

  choose : ∀ {A : Set} → DB.Transaction A → A → O.World → DB.Transaction A
  choose next wait world with at? world
  ... | yes verified = next
  ... | no changed = DB.abort wait

  transaction : ∀ {A : Set} → DB.Transaction A → A → DB.Transaction A
  transaction next wait = DB.scan (choose next wait)

  ready : ∀ {A : Set} (next : DB.Transaction A) wait world →
    DB.lookup pointer world ≡ just (O.recordOf owner (O.currentPolicy expected)) →
    E.pendingRemovalFor owner world ≡ false → DB.evaluate (transaction next wait) world ≡ DB.evaluate next world
  ready next wait world found noRemoval with at? world
  ... | yes verified = refl
  ... | no different = ⊥-elim (different ((O.recordOf owner (O.currentPolicy expected) , found , refl , refl) , noRemoval))

  committed : ∀ {A : Set} (next : DB.Transaction A) wait world result after →
    DB.evaluate (transaction next wait) world ≡ DB.committed result after →
    (DB.lookup pointer world ≡ just (O.recordOf owner (O.currentPolicy expected))) ×
    (DB.evaluate next world ≡ DB.committed result after)
  committed next wait world result after done with at? world
  ... | yes verified = foundAt world verified , done
  ... | no changed with done
  ...   | ()

  removalBlocksPublication : ∀ {A : Set} (next : DB.Transaction A) wait world → E.pendingRemovalFor owner world ≡ true →
    DB.evaluate (transaction next wait) world ≡ DB.aborted wait
  removalBlocksPublication next wait world removing with at? world
  ... | no changed = refl
  ... | yes (located , notRemoving) = ⊥-elim (impossible (trans (sym removing) notRemoving))
    where impossible : true ≢ false
          impossible ()

  effect : Ledger.Effect → String → Ledger.Effect
  effect body wait = record
    { transaction = transaction (Ledger.Effect.transaction body) wait
    ; guidance = Ledger.Effect.guidance body
    ; isolates = λ before result after done → Ledger.Effect.isolates body before result after
        (proj₂ (committed (Ledger.Effect.transaction body) wait before result after done)) }

-- Storage layout is deliberately absent. The adapter supplies a shared DB
-- transaction and PROOFS of these fixed logical outcomes, never another goal.
-- This is a refinement boundary; Rust correspondence is checked separately.
module Family (family policyPointer : ℕ) where
  module Stored = Policy.Family family policyPointer
  owner = O.family family

  module Current (before : O.World) (current : Stored.Saved before)
    (selected : ℕ) (advanceBase : Bool) (desired : Files.Manifest)
    (nodes edges : List ℕ) (payload : String)
    (id : I.OperationId) (input : Identity.Meaning) (names : R.Names id input)
    (receiptSlot : ℕ) (progress : R.Work)
    (notRemoving : E.pendingRemovalFor owner before ≡ false)
    (found : Ledger.find id before ≡ just (Ledger.found receiptSlot owner (R.active input names progress))) where
    selection = Stored.rule current
    module P = Plan selection before selected advanceBase desired
    module Guard = PolicyGuard owner policyPointer (Stored.Saved.version current)
    captured = M.capture selection before

    -- Rows holding content, metadata, readers and existing jobs are retained.
    -- Only mutable binding/selector rows and the original receipt can change.
    data Retained : O.Kind → Set where
      keep : ∀ {kind} → kind ≢ O.baseBindingK → kind ≢ O.deltaBindingK →
        kind ≢ O.publishedViewK → kind ≢ O.receiptK → Retained kind

    record Outcome (after : O.World) : Set where
      field
        content : P.Represents after
        storeValid : O.Admissible after
        viewsValid : Views.Valid after
        selectedExists : P.Existing selected
        -- The base flag must agree with the actual family base pointer.
        baseRole : Σ ℕ (λ slot → Σ ℕ (λ baseCheckout →
          DB.lookup slot before ≡ just (O.recordOf owner (O.basePointer baseCheckout)) ×
          (advanceBase ≡ Relation.Nullary.does (selected ≟ baseCheckout))))
        snapshot pointer : ℕ
        currentAt : DB.lookup pointer after ≡ just (O.recordOf owner (O.publishedView selected snapshot))
        snapshotAt : DB.lookup snapshot after ≡ just (O.recordOf owner (O.structuralSnapshot selected nodes edges payload))
        structuralCurrent : M.project selection after (O.recordOf owner (O.structuralSnapshot selected nodes edges payload)) ≡
          O.recordOf owner (O.structuralSnapshot selected nodes edges payload)
        otherSelectors : ∀ key otherOwner checkout root → checkout ≢ selected →
          DB.lookup key before ≡ just (O.recordOf otherOwner (O.publishedView checkout root)) →
          DB.lookup key after ≡ just (O.recordOf otherOwner (O.publishedView checkout root))
        retained : ∀ key value → Retained (O.kind (O.body value)) →
          DB.lookup key before ≡ just value → DB.lookup key after ≡ just value
        otherFamilies : ∀ key value → O.owner value ≢ owner →
          (DB.lookup key before ≡ just value → DB.lookup key after ≡ just value) ×
          (DB.lookup key after ≡ just value → DB.lookup key before ≡ just value)
        -- Capturing all old family IDs covers every newly detached reference;
        -- the existing bounded worker rechecks actual need before reclamation.
        cleanupSlot : ℕ
        cleanupText : String
        cleanupAt : DB.lookup cleanupSlot after ≡ just (O.recordOf owner (O.cleanupWork id captured cleanupText))

    record Prepared : Set where
      field
        workerFamilySlot workerSlot claim : ℕ
        workerAllowed : IndexControl.Worker.allowed family workerFamilySlot workerSlot id claim before ≡ true
        body : Ledger.Effect
        result continuation : String
        changed : O.World
        performs : DB.evaluate (Ledger.Effect.transaction body) before ≡ DB.committed result changed
        -- Proof is about the REAL final world, including the receipt write.
        outcome : Outcome (DB.write receiptSlot
          (Ledger.recordAt {id = id} owner (R.active input names (R.nextWork progress (R.versions progress) result))) changed)

    module Run (prepared : Prepared) where
      open Prepared prepared
      module Worker = IndexControl.Worker family workerFamilySlot workerSlot id claim
      work = Guard.effect (Worker.effect body continuation) continuation
      nextProgress = R.nextWork progress (R.versions progress) result
      after = DB.write receiptSlot (Ledger.recordAt {id = id} owner (R.active input names nextProgress)) changed
      change = Ledger.checkpoint (R.versions progress)
      request = Ledger.update id input (R.generation progress) change work

      guardedPerforms : DB.evaluate (Ledger.Effect.transaction work) before ≡ DB.committed result changed
      guardedPerforms = trans (Guard.ready (Ledger.Effect.transaction (Worker.effect body continuation)) continuation before (Stored.Saved.pointerAt current) notRemoving)
        (trans (Worker.ready (Ledger.Effect.transaction body) continuation before workerAllowed) performs)

      commits : DB.execute request before ≡ (Ledger.resume receiptSlot nextProgress , after)
      commits = Ledger.committedUpdate id input names change work receiptSlot owner progress before result changed found guardedPerforms

      goal : Outcome after
      goal = outcome

      selectedView : ∀ path → P.C.visible after selected path ≡ P.safeDesired path
      selectedView = P.selectedView after (Outcome.content goal) (Outcome.selectedExists goal)

      otherView : ∀ checkout → P.Existing checkout → checkout ≢ selected → ∀ path →
        P.C.visible after checkout path ≡ P.C.visible before checkout path
      otherView = P.otherView after (Outcome.content goal)

      obsoleteReferencesCovered : ∀ key value → (key , value) ∈ before → O.owner value ≡ owner → key ∈ captured
      obsoleteReferencesCovered = M.captureComplete selection before

      receiptWritten : Ledger.find id after ≡ just (Ledger.found receiptSlot owner (R.active input names nextProgress))
      receiptWritten = Ledger.writtenReceiptVisible id receiptSlot owner (R.active input names nextProgress) changed

      retry : DB.execute request after ≡ (Ledger.resume receiptSlot nextProgress , after)
      retry = Ledger.staleStepSkipsEffect id input names (R.generation progress) change work receiptSlot owner nextProgress after receiptWritten
        (Ledger.nextGenerationDifferent (R.generation progress))

      completes : ∀ world → Σ Ledger.Reply (λ reply → Σ O.World (λ final → Exec.Completed (Exec.atomic request Exec.done) world reply final))
      completes world = proj₁ (DB.execute request world) , proj₂ (DB.execute request world) , Exec.committed Exec.stop

      boundary : ∀ observed → Exec.Interrupted (Exec.atomic request Exec.done) before observed → (observed ≡ before) ⊎ (observed ≡ after)
      boundary observed interrupted with Ledger.atomicBoundary request before observed interrupted
      ... | inj₁ same = inj₁ same
      ... | inj₂ same = inj₂ (trans same (cong proj₂ commits))

      completedAtomic : ∀ observed reply final → Exec.Completed (Exec.atomic request Exec.done) observed reply final →
        DB.execute request observed ≡ (reply , final)
      completedAtomic observed reply final (Exec.committed Exec.stop) = refl

      converges : ∀ observed final reply → Exec.Interrupted (Exec.atomic request Exec.done) before observed →
        Exec.Completed (Exec.atomic request Exec.done) observed reply final → Outcome final
      converges observed final reply interrupted completed = subst Outcome (sym sameFinal) goal
        where
        sameFinal : final ≡ after
        sameFinal with boundary observed interrupted
        ... | inj₁ same = trans (sym (cong proj₂ (completedAtomic observed reply final completed)))
          (trans (cong (λ world → proj₂ (DB.execute request world)) same) (cong proj₂ commits))
        ... | inj₂ same = trans (sym (cong proj₂ (completedAtomic observed reply final completed)))
          (trans (cong (λ world → proj₂ (DB.execute request world)) same) (cong proj₂ retry))
