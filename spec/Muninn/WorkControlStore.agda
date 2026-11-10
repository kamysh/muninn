{-# OPTIONS --safe #-}
-- Durable controls over the real owned world; no client-session state.
module Muninn.WorkControlStore where
import Muninn.OwnedState as O
import Muninn.WorkQueue as Q
import Muninn.CatalogInputs as I
import Muninn.RequestIdentity as N
import Muninn.ReceiptTypes as R
import Muninn.ReceiptLedger as L
import Muninn.ExclusionOutcomes as E
import Muninn.RecordAllocation as Allocation
import Muninn.CleanupScheduling as Scheduling
import Muninn.CleanupStorage as Storage
import Muninn.CleanupOrder as Order
import Muninn.CleanupObservations as Observations
import Muninn.CleanupAdmissionStorage as Insert
import Muninn.CleanupFinalization as Finalization
import Muninn.RetirementCleanup as Reclamation
open import Data.Nat using (ℕ; _≟_)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Unit using (tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
import Data.List.Relation.Unary.All as All
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
module DB = O.DB
module Exec = O.Execution

-- A job carries the original accepted request through every handoff.
jobParent : (fallback : I.OperationId) → (job : I.Job) → I.JobInput job → I.OperationId
jobParent fallback I.preparePublic input = fallback
jobParent fallback I.prepareFamily input = I.FamilyJob.operationId input
jobParent fallback I.prepareGraph input = I.FamilyJob.operationId (proj₁ input)
jobParent fallback I.fleetScan input = input
jobParent fallback I.discoverCheckouts input = I.FamilyJob.operationId input
jobParent fallback I.observeCheckout input = I.FamilyJob.operationId (I.CheckoutJob.parent input)
jobParent fallback I.reconcileFamily input = I.FamilyJob.operationId input
jobParent fallback I.reconcileCheckout input = I.FamilyJob.operationId (I.CheckoutJob.parent input)
jobParent fallback I.watchBatch input = I.FamilyJob.operationId (proj₁ input)
jobParent fallback I.analyzeFile input = I.FamilyJob.operationId (I.CheckoutJob.parent (I.FileJob.parent input))
jobParent fallback I.publishCheckout input = I.FamilyJob.operationId (I.CheckoutJob.parent input)
jobParent fallback I.embedCode input = I.FamilyJob.operationId (proj₁ input)
jobParent fallback I.embedNote input = I.FamilyJob.operationId (proj₁ input)
jobParent fallback I.reclaimExcluded input = I.FamilyJob.operationId input
jobParent fallback I.reclaimRetired input = I.FamilyJob.operationId input
jobParent fallback I.handoff input = I.FamilyJob.operationId input
jobParent fallback I.recoverOperation input = input
jobParent fallback I.recordUsage input = fallback
jobParent fallback I.appendLog input = fallback
jobParent fallback I.pruneLogs input = fallback
jobParent fallback I.flushDiagnostics input = fallback

parent : I.OperationId → N.Meaning → I.OperationId
parent id (N.mutation kind input) = id
parent id (N.durableJob job input) = jobParent id job input

same : I.OperationId → I.OperationId → Bool
same first second = does (L.sameId first second)

data Command : Set where
  pauseFamily resumeFamily : Command
  pauseCurrent cancelCurrent : I.OperationId → Command

-- Every concrete edit carries its preservation evidence. A future control
-- cannot silently introduce a broken owner, dangling reference or public hold.
data Edit (original : O.Record) : Set where
  keep : Edit original
  erase : O.privateTarget (O.kind (O.body original)) ≡ true → Edit original
  replace : (value : O.Record) → O.owner value ≡ O.owner original →
    O.kind (O.body value) ≡ O.kind (O.body original) → O.Placed value →
    (∀ ref → ref ∈ O.references (O.body value) → ref ∈ O.references (O.body original)) → Edit original

-- Cancellation never changes indexing authorization or the family pause flag.
-- No cancelled queue/continuation is left behind to resume.
module Family (family : ℕ) where
  owner = O.family family

  registration : Command → O.RegistrationInfo → O.RegistrationInfo
  registration pauseFamily info = record info { paused = true }
  registration resumeFamily info = record info { paused = false }
  registration (pauseCurrent id) info = info
  registration (cancelCurrent id) info = info

  selected : I.OperationId → Q.Info → Bool
  selected id info = same id (Q.Info.id info) ∨ same id (Q.Info.parent info)

  queued : Q.Info → Q.Info
  queued info with Q.Info.phase info
  ... | Q.paused = Q.move Q.queued info
  ... | _ = info

  localEdit : (command : Command) → (body : O.Body) → Edit (O.recordOf owner body)
  localEdit command (O.registration info) = replace (O.recordOf owner (O.registration (registration command info))) refl refl O.local (λ ref ())
  localEdit pauseFamily (O.acceptedWork versions info) = replace (O.recordOf owner (O.acceptedWork versions (Q.move Q.paused info))) refl refl O.local (λ ref included → included)
  localEdit resumeFamily (O.acceptedWork versions info) = replace (O.recordOf owner (O.acceptedWork versions (queued info))) refl refl O.local (λ ref included → included)
  localEdit (pauseCurrent id) (O.acceptedWork versions info) with selected id info
  ... | true = replace (O.recordOf owner (O.acceptedWork versions (Q.move Q.paused info))) refl refl O.local (λ ref included → included)
  ... | false = keep
  localEdit (cancelCurrent id) (O.acceptedWork versions info) with selected id info
  ... | true = erase refl
  ... | false = keep
  localEdit (cancelCurrent id) (O.continuation versions info) with same id (Q.Continuation.parent info)
  ... | true = erase refl
  ... | false = keep
  localEdit (cancelCurrent target) (O.receipt (R.entry id (R.active input names progress))) with same target (parent id input)
  ... | false = keep
  ... | true with L.sameId target id
  ...   | yes sameId = replace (L.recordAt {id = id} owner (R.active input names (R.nextWork progress [] "Cancellation accepted; finishing cleanup. Earlier published results are retained."))) refl refl tt (λ ref ())
  ...   | no child = replace (L.recordAt {id = id} owner (R.finished input names
      "Stopped with the original request. Its cleanup is continuing; earlier published results are retained.")) refl refl tt (λ ref ())
  localEdit command body = keep

  edit : (command : Command) → (value : O.Record) → Edit value
  edit command (O.recordOf actualOwner body) with E.ownerEqual actualOwner owner
  ... | yes refl = localEdit command body
  ... | no other = keep

  transform : ∀ {original} → Edit original → Maybe O.Record → Maybe O.Record
  transform keep previous = previous
  transform (erase hidden) previous = nothing
  transform (replace value owned kind placed subset) previous = just value

  intendedAt : Command → Maybe O.Record → Maybe O.Record
  intendedAt command nothing = nothing
  intendedAt command (just value) = transform (edit command value) (just value)

  apply : ∀ {original} → ℕ → Edit original → O.World → O.World
  apply key keep world = world
  apply key (erase hidden) world = DB.delete key world
  apply key (replace value owned kind placed subset) world = DB.write key value world

  run : Command → O.World → O.World → O.World
  run command [] world = world
  run command ((key , value) ∷ rows) world = run command rows (apply key (edit command value) world)

  next : ∀ {original} → ℕ → Edit original → DB.Transaction String → DB.Transaction String
  next key keep rest = rest
  next key (erase hidden) rest = DB.remove key rest
  next key (replace value owned kind placed subset) rest = DB.put key value rest

  compile : Command → O.World → DB.Transaction String → DB.Transaction String
  compile command [] rest = rest
  compile command ((key , value) ∷ rows) rest = next key (edit command value) (compile command rows rest)

  performs : ∀ command rows world rest →
    DB.evaluate (compile command rows rest) world ≡ DB.evaluate rest (run command rows world)
  performs command [] world rest = refl
  performs command ((key , value) ∷ rows) world rest with edit command value
  ... | keep = performs command rows world rest
  ... | erase hidden = performs command rows (DB.delete key world) rest
  ... | replace changed owned kind placed subset = performs command rows (DB.write key changed world) rest

  applyAt : ∀ {original} key (chosen : Edit original) world → DB.lookup key (apply key chosen world) ≡ transform chosen (DB.lookup key world)
  applyAt key keep world = refl
  applyAt key (erase hidden) world = DB.deleteAbsent key world
  applyAt key (replace value owned kind placed subset) world = DB.writeVisible key value world

  applyOther : ∀ {original} key other (chosen : Edit original) world → key ≢ other → DB.lookup other (apply key chosen world) ≡ DB.lookup other world
  applyOther key other keep world distinct = refl
  applyOther key other (erase hidden) world distinct = DB.deletePreservesOther key other world distinct
  applyOther key other (replace value owned kind placed subset) world distinct = DB.writePreservesOther key other value world distinct

  updateAt : Command → Maybe O.Record → Maybe O.Record → Maybe O.Record
  updateAt command nothing previous = previous
  updateAt command (just value) previous = transform (edit command value) previous

  runAt : ∀ command rows world key → O.Unique rows →
    DB.lookup key (run command rows world) ≡ updateAt command (DB.lookup key rows) (DB.lookup key world)
  runAt command [] world key unique = refl
  runAt command ((first , value) ∷ rows) world key (absent , unique) with key ≟ first
  ... | yes refl rewrite runAt command rows (apply key (edit command value) world) key unique | absent = applyAt key (edit command value) world
  ... | no different rewrite runAt command rows (apply first (edit command value) world) key unique |
      applyOther first key (edit command value) world (λ same → different (sym same)) = refl

  final : Command → O.World → O.World
  final command world = run command world world

  exact : ∀ command world key → O.Unique world → DB.lookup key (final command world) ≡ intendedAt command (DB.lookup key world)
  exact command world key unique rewrite runAt command world world key unique with DB.lookup key world
  ... | nothing = refl
  ... | just value = refl

  applyValid : ∀ key original (chosen : Edit original) world → O.Admissible world →
    DB.lookup key world ≡ just original → O.Admissible (apply key chosen world)
  applyValid key original keep world valid located = valid
  applyValid key original (erase hidden) world valid located =
    O.deleteUnreferencedPreservesAdmissibility key world valid
      (O.privateUnreferenced key world original valid located hidden)
  applyValid key original (replace value owned kind placed subset) world valid located =
    Storage.writeAdmissible world key original value valid located owned kind placed subset

  Source : O.World → O.World → Set
  Source rows world = ∀ key value → (key , value) ∈ rows → DB.lookup key world ≡ just value

  runValid : ∀ command rows world → O.Unique rows → O.Admissible world → Source rows world →
    O.Admissible (run command rows world)
  runValid command [] world unique valid known = valid
  runValid command ((first , original) ∷ rows) world (absent , unique) valid known =
    runValid command rows (apply first (edit command original) world) unique
      (applyValid first original (edit command original) world valid (known first original (here refl))) shifted
    where
    apart : ∀ key value → (key , value) ∈ rows → first ≢ key
    apart .first value included refl = impossible (trans (sym absent) (Order.memberLookup rows first value unique included))
      where impossible : nothing ≢ just value
            impossible ()
    shifted : Source rows (apply first (edit command original) world)
    shifted key value included = trans (applyOther first key (edit command original) world (apart key value included))
      (known key value (there included))

  finalValid : ∀ command world → O.Admissible world → O.Admissible (final command world)
  finalValid command world valid = runValid command world world (O.Admissible.unique valid) valid
    (λ key value included → Order.memberLookup world key value (O.Admissible.unique valid) included)

  otherFamily : ∀ command world key value → O.Unique world → O.owner value ≢ owner →
    DB.lookup key world ≡ just value → DB.lookup key (final command world) ≡ just value
  otherFamily command world key value unique distinct found rewrite exact command world key unique | found with E.ownerEqual (O.owner value) owner
  ... | yes sameOwner = ⊥-elim (distinct sameOwner)
  ... | no other = refl

  -- Published content is unchanged by controls, including cancellation.
  published : ∀ command world key actualOwner checkout snapshot → O.Unique world →
    DB.lookup key world ≡ just (O.recordOf actualOwner (O.publishedView checkout snapshot)) →
    DB.lookup key (final command world) ≡ just (O.recordOf actualOwner (O.publishedView checkout snapshot))
  published command world key actualOwner checkout snapshot unique found rewrite exact command world key unique | found with E.ownerEqual actualOwner owner
  ... | no different = refl
  ... | yes refl with command
  ...   | pauseFamily = refl
  ...   | resumeFamily = refl
  ...   | pauseCurrent id = refl
  ...   | cancelCurrent id = refl

  authorization : ∀ command info → O.RegistrationInfo.indexingEnabled (registration command info) ≡ O.RegistrationInfo.indexingEnabled info
  authorization pauseFamily info = refl
  authorization resumeFamily info = refl
  authorization (pauseCurrent id) info = refl
  authorization (cancelCurrent id) info = refl

  pauseRetainsWork : ∀ world key versions info target → O.Unique world →
    DB.lookup key world ≡ just (O.recordOf owner (O.acceptedWork versions info)) → selected target info ≡ true →
    DB.lookup key (final (pauseCurrent target) world) ≡ just (O.recordOf owner (O.acceptedWork versions (Q.move Q.paused info)))
  pauseRetainsWork world key versions info target unique located chosen rewrite exact (pauseCurrent target) world key unique | located
    with E.ownerEqual owner owner
  ... | no different = ⊥-elim (different refl)
  ... | yes refl rewrite chosen = refl

  cancelRemovesWork : ∀ world key versions info target → O.Unique world →
    DB.lookup key world ≡ just (O.recordOf owner (O.acceptedWork versions info)) → selected target info ≡ true →
    DB.lookup key (final (cancelCurrent target) world) ≡ nothing
  cancelRemovesWork world key versions info target unique located chosen rewrite exact (cancelCurrent target) world key unique | located
    with E.ownerEqual owner owner
  ... | no different = ⊥-elim (different refl)
  ... | yes refl rewrite chosen = refl

  -- Connection loss is not a control request and cannot pause or cancel work.
  disconnect : String → DB.Transaction String
  disconnect reply = DB.commit reply

  disconnectKeepsWork : ∀ reply world → proj₂ (DB.execute (disconnect reply) world) ≡ world
  disconnectKeepsWork reply world = refl

  controls : Command → String → DB.Transaction String
  controls command result = DB.scan (λ world → compile command world (DB.commit result))

  controlsPerform : ∀ command result world → DB.execute (controls command result) world ≡ (result , final command world)
  controlsPerform command result world rewrite performs command world world (DB.commit result) = refl

  -- Cancellation and its durable cleanup obligation are ONE transaction.
  -- The existing bounded cleanup worker keeps the original receipt active
  -- until all tasks for this ID have finished; it never needs a live MCP caller.
  module Cancellation (selection : E.Rule) (owned : E.targetOwner selection ≡ owner)
    (target : I.OperationId) (input : N.Meaning) (payload result : String) where
    module Capture = Scheduling.Model.Family selection
    command = cancelCurrent target
    middle : O.World → O.World
    middle = final command
    slot : O.World → ℕ
    slot world = Allocation.freshId (middle world)
    captured : O.World → O.World
    captured world = Capture.created target (slot world) payload (middle world)
    cleanup : O.World → DB.Transaction String
    cleanup world = compile command world
      (DB.scan (λ changed → DB.put (Allocation.freshId changed)
        (Capture.task target (Allocation.freshId changed) payload changed) (DB.commit result)))
    performsCleanup : ∀ world → DB.evaluate (cleanup world) world ≡ DB.committed result (captured world)
    performsCleanup world rewrite performs command world world
      (DB.scan (λ changed → DB.put (Allocation.freshId changed)
        (Capture.task target (Allocation.freshId changed) payload changed) (DB.commit result))) = refl

    advance : ℕ → (original : N.Meaning) → R.Names target original → R.Work → O.World → DB.Transaction L.Reply
    advance receiptSlot original named progress world = L.seal receiptSlot
      (λ answer → L.recordAt {id = target} owner (R.active original named (R.nextWork progress [] result)))
      (λ answer → L.resume receiptSlot (R.nextWork progress [] result))
      (λ reason → L.resume receiptSlot progress) (cleanup world)

    active : ℕ → ℕ → (original : N.Meaning) → R.Names target original → R.Work → O.World → DB.Transaction L.Reply
    active expected receiptSlot original named progress world with N.sameRequest input original
    ... | no different = DB.commit (L.explain L.differentRequest)
    ... | yes sameInput with R.generation progress ≟ expected
    ...   | no stale = DB.commit (L.resume receiptSlot progress)
    ...   | yes current = advance receiptSlot original named progress world

    found : ℕ → O.World → L.Found target → DB.Transaction L.Reply
    found expected world (L.found receiptSlot actualOwner state) with E.ownerEqual actualOwner owner
    ... | no different = DB.commit (L.explain L.differentRequest)
    ... | yes sameOwner with state
    ...   | R.active original named progress = active expected receiptSlot original named progress world
    ...   | _ = DB.commit (L.existing input (L.found receiptSlot actualOwner state))

    snapshot : ℕ → O.World → DB.Transaction L.Reply
    snapshot expected world with L.find target world
    ... | nothing = DB.commit (L.explain L.unknownId)
    ... | just stored = found expected world stored

    transaction : ℕ → DB.Transaction L.Reply
    transaction expected = DB.scan (snapshot expected)

    retainedEntry : R.Names target input → R.Work → R.Entry
    retainedEntry named progress with same target (parent target input)
    ... | false = R.entry target (R.active input named progress)
    ... | true = R.entry target (R.active input named
      (R.nextWork progress [] "Cancellation accepted; finishing cleanup. Earlier published results are retained."))

    module Current (before : O.World) (valid : O.Admissible before) (receiptSlot : ℕ)
      (named : R.Names target input) (progress : R.Work)
      (located : DB.lookup receiptSlot before ≡ just (L.recordAt {id = target} owner (R.active input named progress)))
      (accepted : L.find target before ≡ just (L.found receiptSlot owner (R.active input named progress))) where
      nextProgress = R.nextWork progress [] result
      after = DB.write receiptSlot (L.recordAt {id = target} owner (R.active input named nextProgress)) (captured before)
      request = transaction (R.generation progress)

      middleValid : O.Admissible (middle before)
      middleValid = finalValid command before valid

      middleReceipt = O.recordOf owner (O.receipt (retainedEntry named progress))

      middleLocated : DB.lookup receiptSlot (middle before) ≡ just middleReceipt
      middleLocated rewrite exact command before receiptSlot (O.Admissible.unique valid) | located
        with E.ownerEqual owner owner
      ... | no different = ⊥-elim (different refl)
      ... | yes refl with same target (parent target input)
      ...   | false = refl
      ...   | true with L.sameId target target
      ...     | no different = ⊥-elim (different refl)
      ...     | yes sameId = refl

      capturedValid : O.Admissible (captured before)
      capturedValid = Insert.insertAdmissible (middle before) (slot before)
        (Capture.task target (slot before) payload (middle before)) middleValid
        (Allocation.fresh (middle before)) O.local All.[] All.[]

      capturedLocated : DB.lookup receiptSlot (captured before) ≡ just middleReceipt
      capturedLocated = Insert.oldLookup (middle before) (slot before)
        (Capture.task target (slot before) payload (middle before)) (Allocation.fresh (middle before))
        receiptSlot middleReceipt middleLocated

      afterValid : O.Admissible after
      afterValid = Storage.writeAdmissible (captured before) receiptSlot middleReceipt
        (L.recordAt {id = target} owner (R.active input named nextProgress)) capturedValid capturedLocated
        refl refl tt (λ ref ())

      receiptDifferent : receiptSlot ≢ slot before
      receiptDifferent refl = Allocation.fresh (middle before)
        (Insert.storedReserved (middle before) (slot before) middleReceipt middleLocated)

      durableCleanup : DB.lookup (slot before) after ≡ just (Capture.task target (slot before) payload (middle before))
      durableCleanup = trans (DB.writePreservesOther receiptSlot (slot before)
        (L.recordAt {id = target} owner (R.active input named nextProgress)) (captured before) receiptDifferent)
        (DB.writeVisible (slot before) (Capture.task target (slot before) payload (middle before)) (middle before))

      removedWorkStaysRemoved : ∀ key versions info actualOwner otherVersions otherInfo →
        DB.lookup key before ≡ just (O.recordOf owner (O.acceptedWork versions info)) → selected target info ≡ true →
        DB.lookup key after ≢ just (O.recordOf actualOwner (O.acceptedWork otherVersions otherInfo))
      removedWorkStaysRemoved key versions info actualOwner otherVersions otherInfo previous chosen claimed with receiptSlot ≟ key
      ... | yes refl = different (just-injective (trans
        (sym (DB.writeVisible receiptSlot (L.recordAt {id = target} owner (R.active input named nextProgress)) (captured before))) claimed))
        where
        different : L.recordAt {id = target} owner (R.active input named nextProgress) ≢ O.recordOf actualOwner (O.acceptedWork otherVersions otherInfo)
        different ()
      ... | no notReceipt with slot before ≟ key
      ...   | yes refl = different (just-injective (trans
        (sym (trans (DB.writePreservesOther receiptSlot (slot before)
          (L.recordAt {id = target} owner (R.active input named nextProgress)) (captured before) notReceipt)
          (DB.writeVisible (slot before) (Capture.task target (slot before) payload (middle before)) (middle before)))) claimed))
        where
        different : Capture.task target (slot before) payload (middle before) ≢ O.recordOf actualOwner (O.acceptedWork otherVersions otherInfo)
        different ()
      ...   | no notTask = different (trans (sym gone) claimed)
        where
        gone : DB.lookup key after ≡ nothing
        gone = trans (DB.writePreservesOther receiptSlot key
          (L.recordAt {id = target} owner (R.active input named nextProgress)) (captured before) notReceipt)
          (trans (DB.writePreservesOther (slot before) key (Capture.task target (slot before) payload (middle before))
            (middle before) notTask) (cancelRemovesWork before key versions info target (O.Admissible.unique valid) previous chosen))
        different : nothing ≢ just (O.recordOf actualOwner (O.acceptedWork otherVersions otherInfo))
        different ()

      capturedKeys = Capture.ids (slot before) (middle before)

      coversAfter : ∀ key value → DB.lookup key after ≡ just value → O.owner value ≡ E.targetOwner selection → key ∈ capturedKeys
      coversAfter key value present belongs with receiptSlot ≟ key
      ... | yes refl = there (E.Model.captureComplete selection (middle before) receiptSlot middleReceipt
        (Observations.lookupMember (middle before) receiptSlot middleReceipt middleLocated) (sym owned))
      ... | no notReceipt with slot before ≟ key
      ...   | yes refl = here refl
      ...   | no notTask = there (E.Model.captureComplete selection (middle before) key value
        (Observations.lookupMember (middle before) key value (trans
          (sym (DB.writePreservesOther (slot before) key (Capture.task target (slot before) payload (middle before)) (middle before) notTask))
          (trans (sym (DB.writePreservesOther receiptSlot key
            (L.recordAt {id = target} owner (R.active input named nextProgress)) (captured before) notReceipt)) present))) belongs)

      intent : E.Model.Intent selection after
      intent = record
        { keys = capturedKeys; uniqueBefore = O.Admissible.unique afterValid
        ; covers = λ key value included belongs → coversAfter key value
            (Order.memberLookup after key value (O.Admissible.unique afterValid) included) belongs }

      -- These are the existing bounded worker and last-task finalizer, applied
      -- to this actual saved capture. The original request remains active until
      -- the finalizer verifies all of its tasks; no separate worker receipt.
      module Cleanup = Reclamation.Cleanup selection after intent
      module Finalizer = Finalization.Model.Task selection after intent target (slot before)

      commits : DB.execute request before ≡ (L.resume receiptSlot nextProgress , after)
      commits rewrite accepted with E.ownerEqual owner owner
      ... | no different = ⊥-elim (different refl)
      ... | yes sameOwner with N.sameRequest input input
      ...   | no different = ⊥-elim (different refl)
      ...   | yes sameInput with R.generation progress ≟ R.generation progress
      ...     | no different = ⊥-elim (different refl)
      ...     | yes current rewrite L.sealCommitted receiptSlot
        (λ answer → L.recordAt {id = target} owner (R.active input named nextProgress))
        (λ answer → L.resume receiptSlot nextProgress) (λ reason → L.resume receiptSlot progress)
        (cleanup before) before result (captured before) (performsCleanup before) = refl

      receiptWritten : L.find target after ≡ just (L.found receiptSlot owner (R.active input named nextProgress))
      receiptWritten = L.writtenReceiptVisible target receiptSlot owner (R.active input named nextProgress) (captured before)

      retry : DB.execute request after ≡ (L.resume receiptSlot nextProgress , after)
      retry rewrite receiptWritten with E.ownerEqual owner owner
      ... | no different = ⊥-elim (different refl)
      ... | yes sameOwner with N.sameRequest input input
      ...   | no different = ⊥-elim (different refl)
      ...   | yes sameInput with R.generation nextProgress ≟ R.generation progress
      ...     | no stale = refl
      ...     | yes impossible = ⊥-elim (L.nextGenerationDifferent (R.generation progress) impossible)

      boundary : ∀ observed → Exec.Interrupted (Exec.atomic request Exec.done) before observed →
        observed ≡ before ⊎ observed ≡ after
      boundary observed interrupted with L.atomicBoundary request before observed interrupted
      ... | inj₁ sameWorld = inj₁ sameWorld
      ... | inj₂ sameWorld = inj₂ (trans sameWorld (cong proj₂ commits))

      completedAtomic : ∀ observed reply finalWorld → Exec.Completed (Exec.atomic request Exec.done) observed reply finalWorld →
        DB.execute request observed ≡ (reply , finalWorld)
      completedAtomic observed reply finalWorld (Exec.committed Exec.stop) = refl

      converges : ∀ observed finalWorld reply → Exec.Interrupted (Exec.atomic request Exec.done) before observed →
        Exec.Completed (Exec.atomic request Exec.done) observed reply finalWorld → finalWorld ≡ after
      converges observed finalWorld reply interrupted completed with boundary observed interrupted
      ... | inj₁ sameWorld = trans (sym (cong proj₂ (completedAtomic observed reply finalWorld completed)))
        (trans (cong (λ world → proj₂ (DB.execute request world)) sameWorld) (cong proj₂ commits))
      ... | inj₂ sameWorld = trans (sym (cong proj₂ (completedAtomic observed reply finalWorld completed)))
        (trans (cong (λ world → proj₂ (DB.execute request world)) sameWorld) (cong proj₂ retry))
