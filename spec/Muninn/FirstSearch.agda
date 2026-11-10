{-# OPTIONS --safe #-}
-- Save a complete query and arrange authorized checkout work atomically.
module Muninn.FirstSearch where
import Muninn.OwnedState as O
import Muninn.WorkQueue as Q
import Muninn.SearchTarget as Target
import Muninn.SearchView as View
import Muninn.RepositoryIdentity as Identity
import Muninn.IndexControl as Control
import Muninn.CatalogInputs as I
import Muninn.RequestIdentity as N
import Muninn.ReceiptTypes as R
import Muninn.ReceiptLedger as L
import Muninn.RecordAllocation as Allocation
import Muninn.CleanupAdmissionStorage as Insert
import Muninn.ContentViews as Views
import Muninn.Dialogue as D
import Muninn.ExclusionOutcomes as E
open import Data.Nat using (ℕ; _≟_)
open import Data.Bool using (Bool; true; false; not; _∧_)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
module DB = O.DB
module Exec = O.Execution

deleteFresh : ∀ world slot → Insert.Fresh world slot → DB.delete slot world ≡ world
deleteFresh [] slot fresh = refl
deleteFresh ((key , value) ∷ rows) slot fresh with slot ≟ key
... | yes refl = ⊥-elim (fresh (here refl))
... | no different = cong ((key , value) ∷_) (deleteFresh rows slot
    (λ member → fresh (there (∈-++⁺ʳ (Insert.weakIds (O.body value)) member))))

data Reply : Set where
  clarify : D.Prompt → Reply
  resolveTarget : Q.Search → Reply
  resolveSaved : I.OperationId → Q.SavedSearch → Reply
  saved : I.OperationId → Q.SavedSearch → D.Prompt → Reply
  workArranged continueSaved queryReady : I.OperationId → Q.SavedSearch → Reply

authorizationNeeded : D.Prompt
authorizationNeeded = D.prompt (D.text 'T' "he query is saved, but indexing is not currently enabled and runnable for this worktree.")
  (D.text 'I' "nspect its setup and indexing status. Complete setup, explicitly Start indexing, Resume paused work, or restore the repository as appropriate; then continue this saved query. Saving a query does not grant indexing permission.") []
workContextNeeded : D.Prompt
workContextNeeded = D.prompt (D.text 'T' "his background-work identity already has a saved request.")
  (D.text 'C' "ontinue that request when it is the intended work, or arrange this search with a new background-work identity. The existing request is preserved.") []

runnable : O.Owner → O.World → O.RegistrationInfo → O.CheckoutInfo → Bool
runnable owner world registration checkout = Control.familyRunnable registration ∧
  (not (O.CheckoutInfo.paused checkout) ∧
    (not (O.CheckoutInfo.retired checkout) ∧ not (E.pendingRemovalFor owner world)))

searchable : O.Owner → O.World → O.RegistrationInfo → O.CheckoutInfo → Bool
searchable owner world registration checkout = not (O.RegistrationInfo.retired registration) ∧
  (not (O.CheckoutInfo.retired checkout) ∧ not (E.pendingRemovalFor owner world))

module Context (family : ℕ) (queryId : I.OperationId) where
  owner = O.family family
  select : O.Record → Maybe Q.SavedSearch
  select (O.recordOf actualOwner (O.continuation weak info)) with E.ownerEqual actualOwner owner
  ... | no other = nothing
  ... | yes sameOwner with L.sameId (Q.Continuation.parent info) queryId
  ...   | no different = nothing
  ...   | yes same = Q.Continuation.search info
  select value = nothing
  find : O.World → Maybe Q.SavedSearch
  find = Views.find select


module Family (family registrationSlot checkoutSlot : ℕ) (query : Q.Search)
  (queryId jobId : I.OperationId) (separateIds : queryId ≢ jobId)
  (ctx : D.Context) (observed : Identity.Observation) where
  module Scope = Target.Family family registrationSlot checkoutSlot (Q.location query) ctx observed
  owner = O.family family
  module Published = View.Family family checkoutSlot

  module SavedContext = Context family queryId
  open SavedContext using (select; find)

  continuation : Q.SavedSearch → O.Record
  continuation captured = O.recordOf owner (O.continuation (checkoutSlot ∷ []) (record
    { parent = queryId; payload = "Saved search: continue with the same query and selected worktree."
    ; search = just captured }))
  selectSaved : ∀ captured → select (continuation captured) ≡ just captured
  selectSaved captured with E.ownerEqual owner owner
  ... | no different = ⊥-elim (different refl)
  ... | yes sameOwner with L.sameId queryId queryId
  ...   | no different = ⊥-elim (different refl)
  ...   | yes same = refl

  allowed : ∀ {world} → Scope.Target world → Bool
  allowed {world} selected = runnable owner world (Scope.Target.registration selected) (Scope.Target.checkout selected)

  input : Q.SavedSearch → I.JobInput I.reconcileCheckout
  input captured = record { parent = record { operationId = queryId; family = Q.SavedSearch.family captured }
    ; checkout = Q.SavedSearch.checkout captured }
  meaning : Q.SavedSearch → N.Meaning
  meaning captured = N.durableJob I.reconcileCheckout (input captured)
  queue : Q.SavedSearch → O.Record
  queue captured = O.recordOf owner (O.acceptedWork [] (record
    { id = jobId; parent = queryId; job = I.reconcileCheckout; input = input captured
    ; phase = Q.queued; generation = 0 }))
  progress : R.Work
  progress = R.progressOf 0 [] "Authorized worktree reconciliation arranged for a saved search."
  receipt : Q.SavedSearch → O.Record
  receipt captured = L.recordAt {id = jobId} owner (R.active (meaning captured) tt progress)

  querySlot : O.World → ℕ
  querySlot = Allocation.freshId
  withQuery : O.World → Q.SavedSearch → O.World
  withQuery world captured = DB.write (querySlot world) (continuation captured) world
  workSlot : O.World → Q.SavedSearch → ℕ
  workSlot world captured = Allocation.freshId (withQuery world captured)
  withWork : O.World → Q.SavedSearch → O.World
  withWork world captured = DB.write (workSlot world captured) (queue captured) (withQuery world captured)
  receiptSlot : O.World → Q.SavedSearch → ℕ
  receiptSlot world captured = Allocation.freshId (withWork world captured)
  arranged : O.World → Q.SavedSearch → O.World
  arranged world captured = DB.write (receiptSlot world captured) (receipt captured) (withWork world captured)

  prepareNew : ∀ world → Scope.Target world → DB.Transaction Reply
  prepareNew world selected with allowed selected
  ... | false = DB.put (querySlot world) (continuation captured)
    (DB.commit (saved queryId captured authorizationNeeded))
    where captured = Scope.capture query refl selected
  ... | true = DB.put (querySlot world) (continuation captured)
    (DB.put (workSlot world captured) (queue captured)
      (DB.put (receiptSlot world captured) (receipt captured) (DB.commit (workArranged queryId captured))))
    where captured = Scope.capture query refl selected

  new : ∀ world → Scope.Target world → DB.Transaction Reply
  new world selected with Published.observe world
  ... | nothing = prepareNew world selected
  ... | just view with searchable owner world (Scope.Target.registration selected) (Scope.Target.checkout selected)
  ...   | true = DB.put (querySlot world) (continuation captured) (DB.commit (queryReady queryId captured))
    where captured = Scope.capture query refl selected
  ...   | false = prepareNew world selected

  snapshot : O.World → DB.Transaction Reply
  snapshot world with find world
  ... | just original = DB.commit (continueSaved queryId original)
  ... | nothing with L.find queryId world | L.find jobId world
  ...   | just stored | _ = DB.commit (clarify workContextNeeded)
  ...   | nothing | just stored = DB.commit (clarify workContextNeeded)
  ...   | nothing | nothing with Scope.observe world
  ...     | nothing = DB.commit (resolveTarget query)
  ...     | just selected = new world selected
  begin : DB.Transaction Reply
  begin = DB.scan snapshot

  repeatUsesOriginal : ∀ world captured → find world ≡ just captured →
    DB.execute begin world ≡ (continueSaved queryId captured , world)
  repeatUsesOriginal world captured found rewrite found = refl
  unresolvedTargetRequestsDiscovery : ∀ world → find world ≡ nothing → L.find queryId world ≡ nothing → L.find jobId world ≡ nothing → Scope.observe world ≡ nothing →
    DB.execute begin world ≡ (resolveTarget query , world)
  unresolvedTargetRequestsDiscovery world noQuery noQueryId noJob noScope rewrite noQuery | noQueryId | noJob | noScope = refl

  findFreshWrite : ∀ world slot value → Insert.Fresh world slot → select value ≡ nothing →
    find (DB.write slot value world) ≡ find world
  findFreshWrite world slot value fresh absent rewrite deleteFresh world slot fresh | absent = refl

  module Current (before : O.World) (valid : O.Admissible before) (selected : Scope.Target before)
    (seen : Scope.observe before ≡ just selected) (noQuery : find before ≡ nothing)
    (noQueryId : L.find queryId before ≡ nothing) (noJob : L.find jobId before ≡ nothing) where
    captured = Scope.capture query refl selected
    queryWorld = withQuery before captured
    workWorld = withWork before captured
    after = arranged before captured
    queryFresh = Allocation.fresh before
    workFresh = Allocation.fresh queryWorld
    receiptFresh = Allocation.fresh workWorld

    queryValid : O.Admissible queryWorld
    queryValid = Insert.insertAdmissible before (querySlot before) (continuation captured) valid queryFresh O.local All.[] All.[]
    workValid : O.Admissible workWorld
    workValid = Insert.insertAdmissible queryWorld (workSlot before captured) (queue captured) queryValid workFresh O.local All.[] All.[]
    afterValid : O.Admissible after
    afterValid = Insert.insertAdmissible workWorld (receiptSlot before captured) (receipt captured) workValid receiptFresh tt All.[] All.[]

    queryFound : find queryWorld ≡ just captured
    queryFound rewrite deleteFresh before (querySlot before) queryFresh | selectSaved captured = refl
    workFound : find workWorld ≡ just captured
    workFound = trans (findFreshWrite queryWorld (workSlot before captured) (queue captured) workFresh refl) queryFound
    afterFound : find after ≡ just captured
    afterFound = trans (findFreshWrite workWorld (receiptSlot before captured) (receipt captured) receiptFresh refl) workFound

    oldData : ∀ key value → DB.lookup key before ≡ just value → DB.lookup key after ≡ just value
    oldData key value found = Insert.oldLookup workWorld (receiptSlot before captured) (receipt captured) receiptFresh key value
      (Insert.oldLookup queryWorld (workSlot before captured) (queue captured) workFresh key value
        (Insert.oldLookup before (querySlot before) (continuation captured) queryFresh key value found))
    queryAt : DB.lookup (querySlot before) after ≡ just (continuation captured)
    queryAt = Insert.oldLookup workWorld (receiptSlot before captured) (receipt captured) receiptFresh (querySlot before) (continuation captured)
      (Insert.oldLookup queryWorld (workSlot before captured) (queue captured) workFresh (querySlot before) (continuation captured)
        (DB.writeVisible (querySlot before) (continuation captured) before))
    workAt : DB.lookup (workSlot before captured) after ≡ just (queue captured)
    workAt = Insert.oldLookup workWorld (receiptSlot before captured) (receipt captured) receiptFresh (workSlot before captured) (queue captured)
      (DB.writeVisible (workSlot before captured) (queue captured) queryWorld)
    receiptAt : DB.lookup (receiptSlot before captured) after ≡ just (receipt captured)
    receiptAt = DB.writeVisible (receiptSlot before captured) (receipt captured) workWorld

    authorized : allowed selected ≡ true → Published.observe before ≡ nothing → DB.execute begin before ≡ (workArranged queryId captured , after)
    authorized permission missing rewrite noQuery | noQueryId | noJob | seen | missing | permission = refl
    unauthorized : allowed selected ≡ false → Published.observe before ≡ nothing → DB.execute begin before ≡ (saved queryId captured authorizationNeeded , queryWorld)
    unauthorized stopped missing rewrite noQuery | noQueryId | noJob | seen | missing | stopped = refl
    noImplicitStart : DB.lookup registrationSlot after ≡ just (O.recordOf owner (O.registration (Scope.Target.registration selected)))
    noImplicitStart = oldData registrationSlot _ (Scope.Target.familyAt selected)
    unauthorizedKeepsRegistration : allowed selected ≡ false → Published.observe before ≡ nothing →
      DB.lookup registrationSlot (proj₂ (DB.execute begin before)) ≡ just (O.recordOf owner (O.registration (Scope.Target.registration selected)))
    unauthorizedKeepsRegistration stopped missing = trans
      (cong (DB.lookup registrationSlot) (cong proj₂ (unauthorized stopped missing)))
      (Insert.oldLookup before (querySlot before) (continuation captured) queryFresh registrationSlot _ (Scope.Target.familyAt selected))


    publishedAvoidsReindex : ∀ view → Published.observe before ≡ just view →
      searchable owner before (Scope.Target.registration selected) (Scope.Target.checkout selected) ≡ true →
      DB.execute begin before ≡ (queryReady queryId captured , queryWorld)
    publishedAvoidsReindex view published live rewrite noQuery | noQueryId | noJob | seen | published | live = refl

    retry : DB.execute begin after ≡ (continueSaved queryId captured , after)
    retry = repeatUsesOriginal after captured afterFound
    retryBeforeAuthorization : DB.execute begin queryWorld ≡ (continueSaved queryId captured , queryWorld)
    retryBeforeAuthorization = repeatUsesOriginal queryWorld captured queryFound

    module Ready (permission : allowed selected ≡ true) (missing : Published.observe before ≡ nothing) where
      request = Exec.atomic begin Exec.done
      boundary : ∀ observed → Exec.Interrupted request before observed → observed ≡ before ⊎ observed ≡ after
      boundary observed interrupted with L.atomicBoundary begin before observed interrupted
      ... | inj₁ same = inj₁ same
      ... | inj₂ same = inj₂ (trans same (cong proj₂ (authorized permission missing)))
      completed : ∀ world reply final → Exec.Completed request world reply final → DB.execute begin world ≡ (reply , final)
      completed world reply final (Exec.committed Exec.stop) = refl
      converges : ∀ observed reply final → Exec.Interrupted request before observed → Exec.Completed request observed reply final → final ≡ after
      converges observed reply final interrupted done with boundary observed interrupted
      ... | inj₁ same = trans (sym (cong proj₂ (completed observed reply final done)))
        (trans (cong (λ world → proj₂ (DB.execute begin world)) same) (cong proj₂ (authorized permission missing)))
      ... | inj₂ same = trans (sym (cong proj₂ (completed observed reply final done)))
        (trans (cong (λ world → proj₂ (DB.execute begin world)) same) (cong proj₂ retry))
