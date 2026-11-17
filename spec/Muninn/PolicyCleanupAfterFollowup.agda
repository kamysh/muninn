{-# OPTIONS --safe #-}
-- Completing a follow-up resumes the original task with the advanced receipt.
module Muninn.PolicyCleanupAfterFollowup where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.PolicyRuleAdmission as Admission
import Muninn.CleanupObservations as Observations
import Muninn.CleanupFinalization as Finalization
import Muninn.CleanupLoop as Loop
import Muninn.PolicyCleanupFollowupOutcome as FollowupOutcome
import Muninn.PolicyCleanupBatch as Batch
import Muninn.PolicyCleanupFinish as Finish
import Muninn.PolicyCleanupWorker as Worker
import Muninn.PolicyCleanupWorkerFinish as WorkerFinish
import Muninn.PolicyCleanupWorkerContinue as Continue
import Muninn.PolicyCleanupRetry as Retry
import Muninn.StoredPolicy as Stored
import Muninn.ReceiptLedger as Ledger
import Muninn.ReceiptTypes as Receipt
import Muninn.CatalogInputs as Input
import Muninn.RequestIdentity as Identity
import Muninn.Dialogue as Dialogue
open import Data.Nat using (ℕ; _≟_)
open import Data.Bool using (Bool)
open import Data.String using (String)
open import Data.List using (List)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
module DB = O.DB
module Exec = O.Execution

module Model where
  module Outcome = E.Model
  module Family (family pointer : ℕ) (accepted : O.World) (rules : List String)
    (validRules : Admission.Entries (Data.List.map Data.String.toList rules))
    (intent : Outcome.Intent (E.rule family rules validRules) accepted)
    (childAccepted : O.World) (childRules : List String)
    (childValidRules : Admission.Entries (Data.List.map Data.String.toList childRules))
    (childIntent : Outcome.Intent (E.rule family childRules childValidRules) childAccepted)
    (request : Input.Mutation (Input.PolicyTarget × Input.PolicyDraft))
    (taskSlot childSlot receiptSlot : ℕ)
    (names : Receipt.Names (Input.Mutation.operationId request) (Identity.mutation Identity.kApplyPolicy request))
    (progress : Receipt.Work) (guidance : String → Dialogue.Prompt) where
    module Policy = Stored.Family family pointer
    open Worker.Model.Family family pointer accepted rules validRules intent request taskSlot using (id; meaning; owner)
    open Continue.Model.Family family pointer accepted rules validRules intent request taskSlot receiptSlot names progress guidance
      using (Context)
    open Context using (current; seen; valid; task; located; receipt)
    module Parent = Finalization.Model.Task (E.rule family rules validRules) accepted intent id taskSlot
    open Finish.Model.Family family pointer childAccepted childRules childValidRules childIntent request childSlot using (result)

    module At (world : O.World) (ctx : Context world) (distinct : taskSlot ≢ childSlot) where
      module ChildStep = Batch.Model.Family.Selected family pointer childAccepted childRules childValidRules childIntent id childSlot (current ctx)
      module Child = Finalization.Model.Task ChildStep.selection childAccepted ChildStep.intent id childSlot

      module Completed (ready : Child.Ready world) (quiet : ChildStep.Pass.NoEdit world) where
        module ParentStep = Batch.Model.Family.Selected family pointer accepted rules validRules intent id taskSlot (current ctx)
        module ChildLoop = Loop.Model.Run ChildStep.selection childAccepted ChildStep.intent
        module SharedOutcome = FollowupOutcome.Model.Family ChildStep.selection accepted ParentStep.intent childAccepted ChildStep.intent

        parentPendingCleared : ChildLoop.Covered world → SharedOutcome.Parent.Final.NoPending world
        parentPendingCleared covered = SharedOutcome.parentComplete world covered (proj₂ ready)

        module ParentCanFinish (covered : ChildLoop.Covered world) where
          parentReady = task ctx , parentPendingCleared covered
          parentQuiet = SharedOutcome.parentQuiet world covered (proj₂ ready)
          open WorkerFinish.Model.Family.At.Verified family pointer accepted rules validRules intent request taskSlot
            world (current ctx) (seen ctx) (valid ctx) receiptSlot names progress guidance (located ctx) (receipt ctx) parentReady parentQuiet
            public using (reply; after; tickFinishes)

          module ParentTask = Finalization.Model.Task ParentStep.selection accepted ParentStep.intent id taskSlot
          open Finish.Model.Family family pointer accepted rules validRules intent request taskSlot using () renaming (result to parentResult)
          module Transaction = ParentTask.Current world (valid ctx) parentReady (parentResult (current ctx))
            "Cleanup is waiting for remaining work." guidance meaning names receiptSlot progress (located ctx) (receipt ctx)

          childSibling : ParentTask.OtherTask world
          childSibling with Child.savedRecord world (proj₁ ready)
          ... | payload , found = ((childSlot , O.recordOf owner (O.cleanupWork id (Outcome.Intent.keys childIntent) payload)) ,
            Observations.lookupMember world childSlot _ found , (λ same → distinct (sym same)) , Outcome.Intent.keys childIntent , refl)

          requestRemainsActive : Ledger.find id after ≡
            just (Ledger.found receiptSlot owner (Receipt.active meaning names
              (Receipt.nextWork progress (Receipt.versions progress) (parentResult (current ctx)))))
          requestRemainsActive = Transaction.siblingActive childSibling

        continuation = "Cleanup is waiting for remaining work."
        childResult = result (current ctx)
        nextProgress = Receipt.nextWork progress (Receipt.versions progress) childResult
        open Child.Current world (valid ctx) ready childResult continuation guidance meaning names receiptSlot progress (located ctx) (receipt ctx)
          public using (after; cleaned; oldReceipt; newReceipt; taskRemoved; afterValid; siblingActive; otherRecord; commits; reply)
        open WorkerFinish.Model.Family.At.Verified family pointer childAccepted childRules childValidRules childIntent request childSlot
          world (current ctx) (seen ctx) (valid ctx) receiptSlot names progress guidance (located ctx) (receipt ctx) ready quiet
          public using (tickFinishes)

        coverageAfterFinalization : ChildLoop.Covered world → ChildLoop.Covered after
        coverageAfterFinalization covered key value found owned with receiptSlot ≟ key
        ... | yes refl = covered receiptSlot oldReceipt (located ctx) refl
        ... | no notReceipt with childSlot ≟ key
        ...   | yes refl = ⊥-elim (nothingIsJust (trans (sym taskRemoved) found))
          where
          nothingIsJust : nothing ≡ just value → ⊥
          nothingIsJust ()
        ...   | no notChild = covered key value oldLookup owned
          where
          oldLookup : DB.lookup key world ≡ just value
          oldLookup = trans (sym (DB.deletePreservesOther childSlot key world notChild))
            (trans (sym (DB.writePreservesOther receiptSlot key newReceipt cleaned notReceipt)) found)

        parentRecord : Σ String (λ payload → DB.lookup taskSlot world ≡ just (O.recordOf owner (O.cleanupWork id (Outcome.Intent.keys intent) payload)))
        parentRecord = Parent.savedRecord world (task ctx)

        sibling : Child.OtherTask world
        sibling with parentRecord
        ... | payload , found = ((taskSlot , O.recordOf owner (O.cleanupWork id (Outcome.Intent.keys intent) payload)) ,
          Observations.lookupMember world taskSlot _ found , distinct , Outcome.Intent.keys intent , refl)

        notReceipt : ∀ key value → DB.lookup key world ≡ just value → O.kind (O.body value) ≢ O.receiptK → key ≢ receiptSlot
        notReceipt .receiptSlot value found notKind refl = notKind
          (cong (λ row → O.kind (O.body row)) (just-injective (trans (sym found) (located ctx))))

        keepPolicy : ∀ key value → DB.lookup key world ≡ just value → O.kind (O.body value) ≢ O.cleanupWorkK →
          O.kind (O.body value) ≢ O.receiptK → DB.lookup key after ≡ just value
        keepPolicy key value found notTask notReceiptKind = otherRecord key value
          (Child.differentKind world (proj₁ ready) key value found notTask)
          (notReceipt key value found notReceiptKind) found

        selected : Policy.selectedPolicy after ≡ just (Policy.policy (current ctx))
        selected = Policy.selectsKnown after (Policy.Saved.version (current ctx)) (Policy.Saved.defaultsSlot (current ctx))
          (Policy.Saved.info (current ctx)) (Policy.Saved.frozen (current ctx))
          (keepPolicy pointer _ (Policy.Saved.pointerAt (current ctx)) (λ ()) (λ ()))
          (keepPolicy (Policy.Saved.version (current ctx)) _ (Policy.Saved.versionAt (current ctx)) (λ ()) (λ ()))
          (keepPolicy (Policy.Saved.defaultsSlot (current ctx)) _ (Policy.Saved.defaultsAt (current ctx)) (λ ()) (λ ()))

        NextContext = Continue.Model.Family.Context family pointer accepted rules validRules intent request taskSlot receiptSlot names nextProgress guidance after

        nextContext : NextContext
        nextContext with parentRecord | Policy.observe after in observed
        ... | payload , parentFound | nothing = ⊥-elim (impossible selected)
          where
          impossible : Policy.selectedPolicy after ≡ just (Policy.policy (current ctx)) → ⊥
          impossible proof rewrite observed = contradiction proof
            where
            contradiction : nothing ≡ just (Policy.policy (current ctx)) → ⊥
            contradiction ()
        ... | payload , parentFound | just new = Continue.Model.Family.context new observed afterValid nextTask nextLocated (siblingActive sibling)
          where
          nextTask : Parent.TaskAt after
          nextTask = O.recordOf owner (O.cleanupWork id (Outcome.Intent.keys intent) payload) ,
            otherRecord taskSlot _ distinct (notReceipt taskSlot _ parentFound (λ ())) parentFound , refl , refl
          nextLocated : DB.lookup receiptSlot after ≡ just (Ledger.recordAt {id = id} owner (Receipt.active meaning names nextProgress))
          nextLocated = trans (DB.writeVisible receiptSlot newReceipt cleaned)
            (cong (λ change → just (Ledger.recordAt {id = id} owner (Ledger.updatedState change meaning names progress childResult)))
              (Child.siblingChange progress world sibling))

        open Worker.Model.Family family pointer childAccepted childRules childValidRules childIntent request childSlot
          public using () renaming (tick to childTick)
        module ParentRetry = Retry.Model.Family family pointer accepted rules validRules intent request taskSlot receiptSlot names nextProgress guidance
        resumed = ParentRetry.build after nextContext

        continueAfterFollowup : Exec.Script ⊤
        continueAfterFollowup = Exec.atomic (childTick guidance) (λ _ → ParentRetry.script (ParentRetry.Run.path resumed))

        continues : Exec.Completed continueAfterFollowup world tt (ParentRetry.Run.after resumed)
        continues = Exec.committed (subst
          (λ initial → Exec.Completed (ParentRetry.script (ParentRetry.Run.path resumed)) initial tt (ParentRetry.Run.after resumed))
          (sym (cong proj₂ tickFinishes)) (ParentRetry.completes (ParentRetry.Run.path resumed)))

        Restartable : O.World → Set
        Restartable observed = Σ Receipt.Work (λ savedProgress →
          Continue.Model.Family.Context family pointer accepted rules validRules intent request taskSlot receiptSlot names savedProgress guidance observed)

        restartContext : ∀ {observed} → Exec.Interrupted continueAfterFollowup world observed → Restartable observed
        restartContext (residual , Exec.stop) = progress , ctx
        restartContext {observed} (residual , Exec.committed prefix) = nextProgress ,
          ParentRetry.prefixContext (ParentRetry.Run.path resumed)
            (subst (λ initial → Exec.Prefix (ParentRetry.script (ParentRetry.Run.path resumed)) initial residual observed)
              (cong proj₂ tickFinishes) prefix)

        retryAfterInterruption : ∀ {observed} (interruption : Exec.Interrupted continueAfterFollowup world observed) →
          Σ Receipt.Work (λ savedProgress →
            Σ (Continue.Model.Family.Context family pointer accepted rules validRules intent request taskSlot receiptSlot names savedProgress guidance observed)
              (λ savedContext → Retry.Model.Family.Run family pointer accepted rules validRules intent request taskSlot receiptSlot names savedProgress guidance observed savedContext))
        retryAfterInterruption {observed} interruption with restartContext interruption
        ... | savedProgress , savedContext = savedProgress , savedContext ,
          Retry.Model.Family.build family pointer accepted rules validRules intent request taskSlot receiptSlot names savedProgress guidance observed savedContext
