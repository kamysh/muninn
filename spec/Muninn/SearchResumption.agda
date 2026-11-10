{-# OPTIONS --safe #-}
-- Recover exact query context, follow its verified scope, and continue work.
module Muninn.SearchResumption where
import Muninn.OwnedState as O
import Muninn.WorkQueue as Q
import Muninn.FirstSearch as Start
import Muninn.SearchTarget as Target
import Muninn.SearchView as View
import Muninn.RepositoryIdentity as Identity
import Muninn.CatalogInputs as I
import Muninn.RequestCodecs as Codecs
import Muninn.Canonical as C
import Muninn.ReceiptTypes as R
import Muninn.ReceiptLedger as L
import Muninn.RecordAllocation as Allocation
import Muninn.CleanupAdmissionStorage as Insert
import Muninn.Dialogue as D
import Muninn.ExclusionOutcomes as E
import Muninn.CleanupObservations as Observations
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false; not; _∧_)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
module DB = O.DB

lostQuery : D.Prompt
lostQuery = D.prompt (D.text 'I' " cannot recover the saved search from this continuation.")
  (D.text 'S' "end the query and repository/worktree again. I will use any context that is still known and continue the search.") []
differentScope : D.Prompt
differentScope = D.prompt (D.text 'T' "his directory does not identify the worktree saved with the query.")
  (D.text 'L' "ocate the original repository/worktree or complete the existing identification dialogue. To search a different worktree, submit a new query; this saved query is preserved.") []

module Family (family registrationSlot checkoutSlot policyPointer : ℕ) (queryId jobId : I.OperationId)
  (separateIds : queryId ≢ jobId) (ctx : D.Context) (observed : Identity.Observation) where
  owner = O.family family
  module Context = Start.Context family queryId
  module Scope = Target.Family family registrationSlot checkoutSlot (Identity.Observation.requested observed) ctx observed
  module Published = View.Family family checkoutSlot

  sameScope : ∀ {world} → Q.SavedSearch → Scope.Target world → Bool
  sameScope saved selected = does (C.compare Codecs.familyId (Q.SavedSearch.family saved) (O.RegistrationInfo.id (Scope.Target.registration selected))) ∧
    (does (C.compare Codecs.checkoutId (Q.SavedSearch.checkout saved) (O.CheckoutInfo.id (Scope.Target.checkout selected))) ∧
      does (C.compare Codecs.uuid (Q.SavedSearch.incarnation saved) (O.CheckoutInfo.incarnation (Scope.Target.checkout selected))))
  scopeProof : ∀ world saved (selected : Scope.Target world) → sameScope saved selected ≡ true → Scope.sameScope saved selected
  scopeProof world saved selected correct with
    C.compare Codecs.familyId (Q.SavedSearch.family saved) (O.RegistrationInfo.id (Scope.Target.registration selected)) |
    C.compare Codecs.checkoutId (Q.SavedSearch.checkout saved) (O.CheckoutInfo.id (Scope.Target.checkout selected)) |
    C.compare Codecs.uuid (Q.SavedSearch.incarnation saved) (O.CheckoutInfo.incarnation (Scope.Target.checkout selected))
  ... | yes familyId | yes checkoutId | yes incarnation = familyId , checkoutId , incarnation
  ... | no different | _ | _ with correct
  ...   | ()
  scopeProof world saved selected correct | yes familyId | no different | _ with correct
  ... | ()
  scopeProof world saved selected correct | yes familyId | yes checkoutId | no different with correct
  ... | ()

  receiptActive : O.World → I.OperationId → Bool
  receiptActive world id with L.find id world
  ... | just (L.found slot actualOwner (R.active input names progress)) = E.sameOwner actualOwner owner
  ... | _ = false
  sameCheckout : Q.SavedSearch → I.CheckoutJob → Bool
  sameCheckout saved input = does (C.compare Codecs.familyId (I.FamilyJob.family (I.CheckoutJob.parent input)) (Q.SavedSearch.family saved)) ∧
    does (C.compare Codecs.checkoutId (I.CheckoutJob.checkout input) (Q.SavedSearch.checkout saved))
  activeValue : O.World → Q.SavedSearch → O.Record → Bool
  activeValue world saved (O.recordOf actualOwner (O.acceptedWork versions (Q.work id parent I.reconcileCheckout input phase generation))) =
    E.sameOwner actualOwner owner ∧ (sameCheckout saved input ∧ (Q.runnable phase ∧ receiptActive world id))
  activeValue world saved value = false
  pausedValue : Q.SavedSearch → O.Record → Bool
  pausedValue saved (O.recordOf actualOwner (O.acceptedWork versions (Q.work id parent I.reconcileCheckout input Q.paused generation))) =
    E.sameOwner actualOwner owner ∧ (sameCheckout saved input ∧ does (L.sameId parent queryId))
  pausedValue saved value = false
  activeWork : O.World → Q.SavedSearch → Bool
  activeWork world saved = E.anyRow (λ key value → activeValue world saved value) world
  pausedWork : O.World → Q.SavedSearch → Bool
  pausedWork world saved = E.anyRow (λ key value → pausedValue saved value) world

  module Job (saved : Q.SavedSearch) where
    module Description = Start.Family family registrationSlot checkoutSlot (Q.SavedSearch.request saved) queryId jobId separateIds ctx observed
    workSlot : O.World → ℕ
    workSlot = Allocation.freshId
    workWorld : O.World → O.World
    workWorld world = DB.write (workSlot world) (Description.queue saved) world
    receiptSlot : O.World → ℕ
    receiptSlot world = Allocation.freshId (workWorld world)
    after : O.World → O.World
    after world = DB.write (receiptSlot world) (Description.receipt saved) (workWorld world)
    transaction : O.World → DB.Transaction Start.Reply
    transaction world = DB.put (workSlot world) (Description.queue saved)
      (DB.put (receiptSlot world) (Description.receipt saved) (DB.commit (Start.workArranged queryId saved)))

  available : ∀ {world} → Scope.Target world → Bool
  available {world} selected = Start.searchable owner world (Scope.Target.registration selected) (Scope.Target.checkout selected)

  prepare : ∀ world → Q.SavedSearch → Scope.Target world → DB.Transaction Start.Reply
  prepare world saved selected with Start.runnable owner world (Scope.Target.registration selected) (Scope.Target.checkout selected) | pausedWork world saved
  ... | false | _ = DB.commit (Start.saved queryId saved Start.authorizationNeeded)
  ... | true | true = DB.commit (Start.saved queryId saved Start.authorizationNeeded)
  ... | true | false with activeWork world saved
  ...   | true = DB.commit (Start.continueSaved queryId saved)
  ...   | false with L.find jobId world
  ...     | just original = DB.commit (Start.saved queryId saved Start.workContextNeeded)
  ...     | nothing = Job.transaction saved world

  selected : ∀ world → Q.SavedSearch → Maybe (Scope.Target world) → DB.Transaction Start.Reply
  selected world saved nothing = DB.commit (Start.resolveSaved queryId saved)
  selected world saved (just resolved) with sameScope saved resolved
  ... | false = DB.commit (Start.saved queryId saved differentScope)
  ... | true with available resolved | Published.observe world
  ...   | true | just view = DB.commit (Start.queryReady queryId saved)
  ...   | _ | _ = prepare world saved resolved
  snapshot : O.World → DB.Transaction Start.Reply
  snapshot world with Context.find world
  ... | nothing = DB.commit (Start.clarify lostQuery)
  ... | just saved = selected world saved (Scope.observe world)
  resume : DB.Transaction Start.Reply
  resume = DB.scan snapshot

  missingAsksForContext : ∀ world → Context.find world ≡ nothing → DB.execute resume world ≡ (Start.clarify lostQuery , world)
  missingAsksForContext world missing rewrite missing = refl
  wrongWorktreePreservesQuery : ∀ world saved resolved → Context.find world ≡ just saved → Scope.observe world ≡ just resolved → sameScope saved resolved ≡ false →
    DB.execute resume world ≡ (Start.saved queryId saved differentScope , world)
  wrongWorktreePreservesQuery world saved resolved captured found different rewrite captured | found | different = refl
  publicationResumesSearch : ∀ world saved resolved view → Context.find world ≡ just saved → Scope.observe world ≡ just resolved → sameScope saved resolved ≡ true →
    available resolved ≡ true → Published.observe world ≡ just view → DB.execute resume world ≡ (Start.queryReady queryId saved , world)
  publicationResumesSearch world saved resolved view captured found correct live published rewrite captured | found | correct | live | published = refl

  prepareDoesNotDuplicate : ∀ world saved resolved → activeWork world saved ≡ true →
    proj₂ (DB.execute (prepare world saved resolved) world) ≡ world
  prepareDoesNotDuplicate world saved resolved active with Start.runnable owner world (Scope.Target.registration resolved) (Scope.Target.checkout resolved) | pausedWork world saved
  ... | false | _ = refl
  ... | true | true = refl
  ... | true | false rewrite active = refl

  selectedDoesNotDuplicate : ∀ world saved resolved → activeWork world saved ≡ true →
    proj₂ (DB.execute (selected world saved resolved) world) ≡ world
  selectedDoesNotDuplicate world saved nothing active = refl
  selectedDoesNotDuplicate world saved (just resolved) active with sameScope saved resolved
  ... | false = refl
  ... | true with available resolved | Published.observe world
  ...   | true | just view = refl
  ...   | true | nothing = prepareDoesNotDuplicate world saved resolved active
  ...   | false | _ = prepareDoesNotDuplicate world saved resolved active

  activeWorkPreventsDuplicate : ∀ world saved → Context.find world ≡ just saved → activeWork world saved ≡ true →
    proj₂ (DB.execute resume world) ≡ world
  activeWorkPreventsDuplicate world saved found active rewrite found = selectedDoesNotDuplicate world saved (Scope.observe world) active

  startsWork : ∀ world saved resolved → Context.find world ≡ just saved → Scope.observe world ≡ just resolved →
    sameScope saved resolved ≡ true → Published.observe world ≡ nothing →
    Start.runnable owner world (Scope.Target.registration resolved) (Scope.Target.checkout resolved) ≡ true →
    pausedWork world saved ≡ false → activeWork world saved ≡ false → L.find jobId world ≡ nothing →
    DB.execute resume world ≡ (Start.workArranged queryId saved , Job.after saved world)
  startsWork world saved resolved found scope correct missing permission notPaused inactive noJob
    rewrite found | scope | correct | missing with available resolved
  ... | true rewrite permission | notPaused | inactive | noJob = refl
  ... | false rewrite permission | notPaused | inactive | noJob = refl

  sameValue : ∀ {A : Set} (codec : C.Codec A) value → does (C.compare codec value value) ≡ true
  sameValue codec value with C.compare codec value value
  ... | yes same = refl
  ... | no different = ⊥-elim (different refl)
  sameCheckoutSelf : ∀ saved → sameCheckout saved (record
    { parent = record { operationId = queryId; family = Q.SavedSearch.family saved }; checkout = Q.SavedSearch.checkout saved }) ≡ true
  sameCheckoutSelf saved rewrite sameValue Codecs.familyId (Q.SavedSearch.family saved) | sameValue Codecs.checkoutId (Q.SavedSearch.checkout saved) = refl

  anyHit : (world : O.World) (test : O.Record → Bool) → ∀ key value → (key , value) ∈ world → test value ≡ true → E.anyRow (λ key value → test value) world ≡ true
  anyHit ((key , value) ∷ rows) test .key .value (here refl) hit rewrite hit = refl
  anyHit ((first , stored) ∷ rows) test key value (there present) hit with test stored
  ... | true = refl
  ... | false = anyHit rows test key value present hit

  module NewWork (world : O.World) (valid : O.Admissible world) (saved : Q.SavedSearch) where
    module Work = Job saved
    module Description = Work.Description
    firstFresh = Allocation.fresh world
    secondFresh = Allocation.fresh (Work.workWorld world)
    workValid : O.Admissible (Work.workWorld world)
    workValid = Insert.insertAdmissible world (Work.workSlot world) (Description.queue saved) valid firstFresh O.local All.[] All.[]
    afterValid : O.Admissible (Work.after world)
    afterValid = Insert.insertAdmissible (Work.workWorld world) (Work.receiptSlot world) (Description.receipt saved) workValid secondFresh tt All.[] All.[]
    keepsContextAndData : ∀ key value → DB.lookup key world ≡ just value → DB.lookup key (Work.after world) ≡ just value
    keepsContextAndData key value found = Insert.oldLookup (Work.workWorld world) (Work.receiptSlot world) (Description.receipt saved) secondFresh key value
      (Insert.oldLookup world (Work.workSlot world) (Description.queue saved) firstFresh key value found)

    contextPreserved : Context.find world ≡ just saved → Context.find (Work.after world) ≡ just saved
    contextPreserved found = trans
      (Description.findFreshWrite (Work.workWorld world) (Work.receiptSlot world) (Description.receipt saved) secondFresh refl)
      (trans (Description.findFreshWrite world (Work.workSlot world) (Description.queue saved) firstFresh refl) found)
    queueAt : DB.lookup (Work.workSlot world) (Work.after world) ≡ just (Description.queue saved)
    queueAt = Insert.oldLookup (Work.workWorld world) (Work.receiptSlot world) (Description.receipt saved) secondFresh
      (Work.workSlot world) (Description.queue saved) (DB.writeVisible (Work.workSlot world) (Description.queue saved) world)
    receiptWritten : L.find jobId (Work.after world) ≡ just (L.found (Work.receiptSlot world) owner
      (R.active (Description.meaning saved) tt Description.progress))
    receiptWritten = L.writtenReceiptVisible jobId (Work.receiptSlot world) owner (R.active (Description.meaning saved) tt Description.progress) (Work.workWorld world)
    receiptReady : receiptActive (Work.after world) jobId ≡ true
    receiptReady rewrite receiptWritten with E.ownerEqual owner owner
    ... | yes same = refl
    ... | no different = ⊥-elim (different refl)
    queueActive : activeValue (Work.after world) saved (Description.queue saved) ≡ true
    queueActive rewrite sameCheckoutSelf saved | receiptReady with E.ownerEqual owner owner
    ... | yes same = refl
    ... | no different = ⊥-elim (different refl)
    workIsActive : activeWork (Work.after world) saved ≡ true
    workIsActive = anyHit (Work.after world) (activeValue (Work.after world) saved) (Work.workSlot world) (Description.queue saved)
      (Observations.lookupMember (Work.after world) (Work.workSlot world) (Description.queue saved) queueAt) queueActive
    retryDoesNotDuplicate : Context.find world ≡ just saved → proj₂ (DB.execute resume (Work.after world)) ≡ Work.after world
    retryDoesNotDuplicate found = activeWorkPreventsDuplicate (Work.after world) saved (contextPreserved found) workIsActive

    module Ready (captured : Context.find world ≡ just saved) (resolved : Scope.Target world)
      (scope : Scope.observe world ≡ just resolved) (correct : sameScope saved resolved ≡ true)
      (missing : Published.observe world ≡ nothing)
      (permission : Start.runnable owner world (Scope.Target.registration resolved) (Scope.Target.checkout resolved) ≡ true)
      (notPaused : pausedWork world saved ≡ false) (inactive : activeWork world saved ≡ false) (noJob : L.find jobId world ≡ nothing) where
      request = O.Execution.atomic resume O.Execution.done
      performed = startsWork world saved resolved captured scope correct missing permission notPaused inactive noJob
      boundary : ∀ observed → O.Execution.Interrupted request world observed → observed ≡ world ⊎ observed ≡ Work.after world
      boundary observed interrupted with L.atomicBoundary resume world observed interrupted
      ... | inj₁ same = inj₁ same
      ... | inj₂ same = inj₂ (trans same (cong proj₂ performed))
      completed : ∀ observed reply final → O.Execution.Completed request observed reply final → DB.execute resume observed ≡ (reply , final)
      completed observed reply final (O.Execution.committed O.Execution.stop) = refl
      converges : ∀ observed reply final → O.Execution.Interrupted request world observed → O.Execution.Completed request observed reply final → final ≡ Work.after world
      converges observed reply final interrupted done with boundary observed interrupted
      ... | inj₁ same = trans (sym (cong proj₂ (completed observed reply final done)))
        (trans (cong (λ observed → proj₂ (DB.execute resume observed)) same) (cong proj₂ performed))
      ... | inj₂ same = trans (sym (cong proj₂ (completed observed reply final done)))
        (trans (cong (λ observed → proj₂ (DB.execute resume observed)) same) (retryDoesNotDuplicate captured))
