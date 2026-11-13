{-# OPTIONS --safe #-}
-- Current-policy resolution and one captured cleanup edit share a transaction.
module Muninn.PolicyCleanupBatch where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.PolicyRuleAdmission as Admission
import Muninn.CleanupEffects as Effects
import Muninn.CleanupProgress as Progress
import Muninn.CleanupReleased as Released
import Muninn.CleanupFinalization as Finalization
import Muninn.PublishedViews as Views
import Muninn.StoredPolicy as Stored
import Muninn.ReceiptTypes as R
import Muninn.ReceiptLedger as Ledger
import Muninn.CatalogInputs as I
import Muninn.RequestIdentity as Identity
open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Bool using (Bool; false)
open import Data.String using (String)
open import Data.List using (List)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (yes; no; ¬_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
module DB = O.DB

receiptControl : ∀ recordOwner receiptData → E.indexed (O.recordOf recordOwner (O.receipt receiptData)) ≡ false
receiptControl recordOwner (R.entry requestId (R.active input names work)) = refl
receiptControl recordOwner (R.entry requestId (R.finished input names result)) = refl
receiptControl recordOwner (R.entry requestId R.used) = refl

module Model where
  module M = E.Model

  module Family (family pointer : ℕ) (accepted : O.World) (originalRules : List String)
    (originalValid : Admission.Entries (Data.List.map Data.String.toList originalRules))
    (original : M.Intent (E.rule family originalRules originalValid) accepted) (id : I.OperationId) (taskSlot : ℕ) where
    owner = O.family family
    captured = M.Intent.keys original
    module Policy = Stored.Family family pointer
    module Task = Finalization.Model.Task (E.rule family originalRules originalValid) accepted original id taskSlot

    module Selected {world : O.World} (current : Policy.Saved world) where
      selection = Policy.rule current

      intent : M.Intent selection accepted
      intent = record
        { keys = captured
        ; uniqueBefore = M.Intent.uniqueBefore original
        ; covers = M.Intent.covers original }

      module Core = Effects.Model.Core selection accepted intent
      module Pass = Progress.Model.Pass selection accepted intent
      module Use = Released.Model.Loop selection accepted intent

      captureUnchanged : M.Intent.keys intent ≡ captured
      captureUnchanged = refl

    run : ∀ {world} → Policy.Saved world → ℕ → DB.Transaction Effects.Reply
    run current key = Step.Core.transaction key
      where module Step = Selected current

    snapshot : (world : O.World) → Maybe (Policy.Saved world) → ℕ → Effects.Reply → DB.Transaction Effects.Reply
    snapshot world nothing key continuation = DB.abort continuation
    snapshot world (just current) key continuation with Task.taskAt? world
    ... | no context = DB.abort continuation
    ... | yes actual = run current key

    batch : ℕ → Effects.Reply → DB.Transaction Effects.Reply
    batch key continuation = DB.scan (λ world → snapshot world (Policy.observe world) key continuation)

    snapshotBound : ∀ world current key continuation → Effects.MutationBound 1 (snapshot world current key continuation)
    snapshotBound world nothing key continuation = Effects.abortWithin 1 continuation
    snapshotBound world (just current) key continuation with Task.taskAt? world
    ... | no context = Effects.abortWithin 1 continuation
    ... | yes actual = Step.Core.transactionBound key
      where module Step = Selected current

    bounded : ∀ key continuation → Effects.MutationBound 1 (batch key continuation)
    bounded key continuation = Effects.scanWithin 1 (λ world → snapshot world (Policy.observe world) key continuation)
      (λ world → snapshotBound world (Policy.observe world) key continuation)

    executes : ∀ world (current : Policy.Saved world) key continuation →
      Policy.observe world ≡ just current → Task.TaskAt world →
      DB.execute (batch key continuation) world ≡ DB.execute (run current key) world
    executes world current key continuation observed actual rewrite observed with Task.taskAt? world
    ... | yes same = refl
    ... | no context = ⊥-elim (context actual)

    missingPolicy : ∀ world key continuation → Policy.observe world ≡ nothing →
      DB.execute (batch key continuation) world ≡ (continuation , world)
    missingPolicy world key continuation missing rewrite missing = refl

    missingTask : ∀ world (current : Policy.Saved world) key continuation →
      Policy.observe world ≡ just current → ¬ Task.TaskAt world →
      DB.execute (batch key continuation) world ≡ (continuation , world)
    missingTask world current key continuation observed missing rewrite observed with Task.taskAt? world
    ... | yes actual = ⊥-elim (missing actual)
    ... | no context = refl

    module Current (before : O.World) (current : Policy.Saved before)
      (observed : Policy.observe before ≡ just current) (actual : Task.TaskAt before)
      (key : ℕ) (continuation : Effects.Reply) where
      module Step = Selected current
      after = proj₂ (DB.execute (batch key continuation) before)
      changed = proj₂ (DB.execute (run current key) before)

      sameEffect : after ≡ changed
      sameEffect = cong proj₂ (executes before current key continuation observed actual)

      safety : M.Safety Step.selection before after
      safety = subst (M.Safety Step.selection before) (sym sameEffect) (Step.Core.transactionSafety key before)

      admissible : O.Admissible before → O.Admissible after
      admissible valid = subst O.Admissible (sym sameEffect) (Step.Core.transactionAdmissible key before valid)

      productive : Step.Pass.Ready key before → Progress.mass after < Progress.mass before
      productive ready = subst (λ world → Progress.mass world < Progress.mass before) (sym sameEffect)
        (Step.Pass.editDecreases key before ready)

      savedTask : Σ String (λ payload → DB.lookup taskSlot after ≡ just (O.recordOf owner (O.cleanupWork id captured payload)))
      savedTask with Task.savedRecord before actual
      ... | payload , found = payload , M.Safety.metadata safety taskSlot _ found refl

      activeReceipt : ∀ requestId input names work slot recordOwner →
        DB.lookup slot before ≡ just (Ledger.recordAt {id = requestId} recordOwner (R.active input names work)) →
        DB.lookup slot after ≡ just (Ledger.recordAt {id = requestId} recordOwner (R.active input names work))
      activeReceipt requestId input names work slot recordOwner found = M.Safety.metadata safety slot _ found refl

      protected : ∀ recordKey value → DB.lookup recordKey before ≡ just value → M.Protected Step.selection before recordKey →
        DB.lookup recordKey after ≡ just value
      protected = M.Safety.protected safety

      outsideCapture : ∀ other value → DB.lookup other before ≡ just value →
        ¬ (other ∈ captured) → DB.lookup other after ≡ just value
      outsideCapture other value found outside = trans (cong (DB.lookup other) sameEffect)
        (Step.Core.transactionOutsideCapture key before other value found outside)

      selectedPolicyPreserved : Policy.selectedPolicy after ≡ just (Policy.policy current)
      selectedPolicyPreserved = Policy.selectsKnown after (Policy.Saved.version current) (Policy.Saved.defaultsSlot current)
        (Policy.Saved.info current) (Policy.Saved.frozen current)
        (M.Safety.metadata safety pointer _ (Policy.Saved.pointerAt current) refl)
        (M.Safety.metadata safety (Policy.Saved.version current) _ (Policy.Saved.versionAt current) refl)
        (M.Safety.metadata safety (Policy.Saved.defaultsSlot current) _ (Policy.Saved.defaultsAt current) refl)

      receiptFrame : Ledger.ReceiptFrame before after
      receiptFrame slot recordOwner receiptData =
        (λ found → M.Safety.metadata safety slot _ found (receiptControl recordOwner receiptData)) ,
        (λ found → Step.Use.metadataEarlier key before slot _
          (trans (sym (cong (DB.lookup slot) sameEffect)) found) (receiptControl recordOwner receiptData))

      idle : ¬ Step.Pass.Ready key before → changed ≡ before
      idle none with Step.Core.decide key before
      ... | Step.Core.retain denied = refl
      ... | Step.Core.erase ready = ⊥-elim (none (inj₁ ready))
      ... | Step.Core.trim ready = ⊥-elim (none (inj₂ ready))

      trail : Σ ℕ (λ count → Step.Pass.Trace count before changed)
      trail with Step.Pass.ready? key before
      ... | no none = zero , subst (Step.Pass.Trace zero before) (sym (idle none)) (Step.Pass.stop before)
      ... | yes ready = suc zero , Step.Pass.edit key before ready (Step.Pass.stop changed)

      currentViews : O.Admissible before → Views.Valid before → Views.Valid after
      currentViews valid viewsValid = subst Views.Valid (sym sameEffect)
        (ViewCleanup.validAfterCleanup (proj₂ trail) valid viewsValid)
        where module ViewCleanup = Views.Model.Cleanup Step.selection accepted Step.intent
