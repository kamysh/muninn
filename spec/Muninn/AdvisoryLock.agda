{-# OPTIONS --safe #-}
-- Index coordination and short publication transactions have distinct owners.
module Muninn.AdvisoryLock where
import Muninn.OwnedState as O
import Muninn.WorkQueue as Q
import Muninn.FairScheduling as Scheduling
import Muninn.CatalogInputs as I
import Muninn.RequestIdentity as Identity
import Muninn.ReceiptLedger as Ledger
import Muninn.ReceiptTypes as Receipt
import Muninn.Types as T
import Muninn.Canonical as C
import Muninn.RequestCodecs as Codec
open import Data.Nat using (ℕ; _≤_; z≤n; s≤s)
open import Data.String using (String)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (just)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
module DB = O.DB

data HolderKind : Set where Fg Bg : HolderKind
record Owner : Set where
  constructor owner
  field session : T.UUID
        operation : I.OperationId
        kind : HolderKind

data Lock : Set where
  Free : Lock
  Held : Owner → Lock

record TransactionOwner : Set where
  constructor transactionOwner
  field session transaction : T.UUID

data PublicationLock : Set where
  publicationFree : PublicationLock
  publicationHeld : TransactionOwner → PublicationLock

record Coord : Set where
  constructor coord
  field index : Lock
        waiting : List I.OperationId
        publication : PublicationLock
        store : O.World

-- A request already queued or holding the lock is reused, not duplicated.
notCurrent : Lock → I.OperationId → Set
notCurrent Free request = ⊤
notCurrent (Held holder) request = Owner.operation holder ≢ request

-- Session loss releases both locks belonging to that session. An interrupted
-- interactive owner returns to the head of its waiting queue; its stored work
-- stays intact. Background recovery uses the existing durable work record.
closePublication : T.UUID → PublicationLock → PublicationLock
closePublication session publicationFree = publicationFree
closePublication session (publicationHeld held) with C.compare Codec.uuid session (TransactionOwner.session held)
... | yes _ = publicationFree
... | no _ = publicationHeld held

closeIndex : T.UUID → Lock → Lock
closeIndex session Free = Free
closeIndex session (Held held) with C.compare Codec.uuid session (Owner.session held)
... | yes _ = Free
... | no _ = Held held

restoreWaiter : T.UUID → Lock → List I.OperationId → List I.OperationId
restoreWaiter session Free waiting = waiting
restoreWaiter session (Held held) waiting with C.compare Codec.uuid session (Owner.session held) | Owner.kind held
... | yes _ | Fg = Owner.operation held ∷ waiting
... | _ | _ = waiting

sessionEnded : T.UUID → Coord → Coord
sessionEnded session (coord index waiting publication store) =
  coord (closeIndex session index) (restoreWaiter session index waiting) (closePublication session publication) store

-- Notifications are hints; the durable queue is checked after either kind of
-- wakeup. The fallback interval is configurable, with the existing default.
fallbackDefaultSeconds : ℕ
fallbackDefaultSeconds = 10
record WakePolicy : Set where
  field fallbackSeconds : ℕ
        positive : 1 ≤ fallbackSeconds
defaultWakePolicy : WakePolicy
defaultWakePolicy = record { fallbackSeconds = fallbackDefaultSeconds; positive = s≤s z≤n }
-- One database-backed installation setting is shared by every family. The
-- configuration operation replaces this installation value, not each family.
record InstallationSettings : Set where
  field wakePolicy : WakePolicy

defaultInstallationSettings : InstallationSettings
defaultInstallationSettings = record { wakePolicy = defaultWakePolicy }
-- A poll is due only after the configured interval. Delivery and scheduler
-- availability are environmental conditions, never a hard completion bound.
data Wake (policy : WakePolicy) : Set where
  notification : Wake policy
  fallbackPoll : (elapsed : ℕ) → WakePolicy.fallbackSeconds policy ≤ elapsed → Wake policy

data Action (policy : WakePolicy) : Set where
  request cancel : I.OperationId → Action policy
  foregroundAcquire backgroundAcquire : T.UUID → I.OperationId → Action policy
  release : Owner → Action policy
  yield : Owner → Action policy
  recover : I.OperationId → Action policy
  wake : Wake policy → Action policy
  sessionLost : T.UUID → Action policy
  beginPublication commitPublication abortPublication : TransactionOwner → Action policy

-- Submitting a request emits a notification after the durable queue update.
-- Repeating that hint on a retry is harmless; the queue remains authoritative.
notifications : ∀ {policy} → Action policy → List I.OperationId
notifications (request requestId) = requestId ∷ []
notifications (cancel requestId) = []
notifications (foregroundAcquire session requestId) = []
notifications (backgroundAcquire session requestId) = []
notifications (release held) = []
notifications (yield held) = []
notifications (recover requestId) = []
notifications (wake event) = []
notifications (sessionLost session) = []
notifications (beginPublication transaction) = []
notifications (commitPublication transaction) = []
notifications (abortPublication transaction) = []

data Step (policy : WakePolicy) : Action policy → Coord → Coord → Set where
  requestOnce : ∀ {index waiting publication store} requestId meaning
    (names : Receipt.Names requestId meaning) work slot receiptOwner →
    Ledger.find requestId store ≡ just (Ledger.found slot receiptOwner (Receipt.active meaning names work)) →
    ¬ (requestId ∈ waiting) → notCurrent index requestId →
    Step policy (request requestId) (coord index waiting publication store) (coord index (waiting ++ (requestId ∷ [])) publication store)
  requestAlreadyWaiting : ∀ {index waiting publication store} requestId → requestId ∈ waiting →
    Step policy (request requestId) (coord index waiting publication store) (coord index waiting publication store)
  requestAlreadyRunning : ∀ {waiting publication store} held →
    Step policy (request (Owner.operation held)) (coord (Held held) waiting publication store) (coord (Held held) waiting publication store)
  cancelWaiting : ∀ {index publication store} prefix requestId suffix meaning
    (names : Receipt.Names requestId meaning) result slot receiptOwner →
    Ledger.find requestId store ≡ just (Ledger.found slot receiptOwner (Receipt.finished meaning names result)) →
    Step policy (cancel requestId) (coord index (prefix ++ (requestId ∷ suffix)) publication store)
      (coord index (prefix ++ suffix) publication store)
  acquireFirst : ∀ {publication store} session requestId rest →
    Step policy (foregroundAcquire session requestId) (coord Free (requestId ∷ rest) publication store)
      (coord (Held (owner session requestId Fg)) rest publication store)
  acquireBackground : ∀ {publication store} session requestId →
    Step policy (backgroundAcquire session requestId) (coord Free [] publication store)
      (coord (Held (owner session requestId Bg)) [] publication store)
  -- A completed request can release without requeueing only after its durable
  -- receipt records completion. Otherwise yield or crash recovery keeps it live.
  finished : ∀ {waiting publication store} held meaning
    (names : Receipt.Names (Owner.operation held) meaning) result slot receiptOwner →
    Ledger.find (Owner.operation held) store ≡ just (Ledger.found slot receiptOwner (Receipt.finished meaning names result)) →
    Step policy (release held) (coord (Held held) waiting publication store) (coord Free waiting publication store)
  yielded : ∀ {publication store} session requestId waiting slot ownerId versions info →
    DB.lookup slot store ≡ just (O.recordOf ownerId (O.acceptedWork versions info)) →
    Q.Info.id info ≡ requestId → Q.Info.phase info ≡ Q.running →
    Step policy (yield (owner session requestId Bg)) (coord (Held (owner session requestId Bg)) waiting publication store)
      (coord Free waiting publication (Scheduling.yield store slot ownerId versions info))
  -- If the owning session vanished, recover the actual running work as queued.
  recoverWork : ∀ {index waiting publication store} requestId slot ownerId versions info →
    notCurrent index requestId →
    DB.lookup slot store ≡ just (O.recordOf ownerId (O.acceptedWork versions info)) →
    Q.Info.id info ≡ requestId → Q.Info.phase info ≡ Q.running →
    Step policy (recover requestId) (coord index waiting publication store)
      (coord index waiting publication (Scheduling.yield store slot ownerId versions info))
  woken : ∀ kind state → Step policy (wake kind) state state
  lost : ∀ session state → Step policy (sessionLost session) state (sessionEnded session state)
  startPublication : ∀ {index waiting store} transaction →
    Step policy (beginPublication transaction) (coord index waiting publicationFree store)
      (coord index waiting (publicationHeld transaction) store)
  publish : ∀ {index waiting store after} transaction (operation : DB.Transaction ⊤) →
    DB.evaluate operation store ≡ DB.committed tt after →
    Ledger.ReceiptFrame store after → O.Admissible after →
    Step policy (commitPublication transaction) (coord index waiting (publicationHeld transaction) store)
      (coord index waiting publicationFree after)
  discard : ∀ {index waiting store} transaction (operation : DB.Transaction ⊤) →
    DB.evaluate operation store ≡ DB.aborted tt →
    Step policy (abortPublication transaction) (coord index waiting (publicationHeld transaction) store)
      (coord index waiting publicationFree store)

-- Every family selects transitions using the same installation value. The
-- runtime configuration adapter must obtain that value from the database.
module Installation (settings : InstallationSettings) where
  policy : WakePolicy
  policy = InstallationSettings.wakePolicy settings
  Transition : Action policy → Coord → Coord → Set
  Transition = Step policy

-- Single ownership, ordered interactive admission, and crash preservation are
-- independent of timing or of the choice of wakeup mechanism.
holds : Lock → Owner → Set
holds Free actor = ⊥
holds (Held current) actor = actor ≡ current
exclusive : ∀ lock first second → holds lock first → holds lock second → first ≡ second
exclusive Free first second () secondHolds
exclusive (Held holder) .holder .holder refl refl = refl

firstWaiterAcquires : ∀ {policy publication store session requestId first rest result} →
  Step policy (foregroundAcquire session requestId) (coord Free (first ∷ rest) publication store) result → requestId ≡ first
firstWaiterAcquires (acquireFirst session ._ rest) = refl

crashPreservesStore : ∀ session state → Coord.store (sessionEnded session state) ≡ Coord.store state
crashPreservesStore session (coord index waiting publication store) = refl

crashKeepsFirstWaiter : ∀ session operation waiting publication store →
  Coord.waiting (sessionEnded session (coord (Held (owner session operation Fg)) waiting publication store)) ≡ operation ∷ waiting
crashKeepsFirstWaiter session operation waiting publication store with C.compare Codec.uuid session session
... | yes _ = refl
... | no different = ⊥-elim (different refl)

-- Yield writes the existing queued work while retaining a distinct receipt.
yieldPreservesReceipt : ∀ world slot receiptSlot ownerId receiptOwner versions info receipt →
  DB.lookup slot world ≡ just (O.recordOf ownerId (O.acceptedWork versions info)) →
  DB.lookup receiptSlot world ≡ just (O.recordOf receiptOwner (O.receipt receipt)) →
  DB.lookup receiptSlot (Scheduling.yield world slot ownerId versions info) ≡ just (O.recordOf receiptOwner (O.receipt receipt))
yieldPreservesReceipt = Scheduling.yieldKeepsReceipt

-- Releasing a dead session does not remove committed work; a foreground
-- request is put back before later waiters, ready for a new session.
deadOwnerReleases : ∀ session requestId kind → closeIndex session (Held (owner session requestId kind)) ≡ Free
deadOwnerReleases session requestId kind with C.compare Codec.uuid session session
... | yes _ = refl
... | no different = ⊥-elim (different refl)

deadTransactionReleases : ∀ session transaction →
  closePublication session (publicationHeld (transactionOwner session transaction)) ≡ publicationFree
deadTransactionReleases session transaction with C.compare Codec.uuid session session
... | yes _ = refl
... | no different = ⊥-elim (different refl)

data Reach (policy : WakePolicy) : Coord → Coord → Set where
  done : ∀ {state} → Reach policy state state
  _∷_ : ∀ {before middle after action} → Step policy action before middle → Reach policy middle after → Reach policy before after
infixr 5 _∷_

-- When the background worker reaches a safe yield point, the first waiting
-- interactive request can acquire, with its earlier checkpoint retained.
handoffPossible : ∀ policy waiting publication store session requestId first slot ownerId versions info nextSession →
  DB.lookup slot store ≡ just (O.recordOf ownerId (O.acceptedWork versions info)) →
  Q.Info.id info ≡ requestId → Q.Info.phase info ≡ Q.running →
  Reach policy (coord (Held (owner session requestId Bg)) (first ∷ waiting) publication store)
    (coord (Held (owner nextSession first Fg)) waiting publication (Scheduling.yield store slot ownerId versions info))
handoffPossible policy waiting publication store session requestId first slot ownerId versions info nextSession located identity running =
  yielded session requestId (first ∷ waiting) slot ownerId versions info located identity running ∷
  acquireFirst nextSession first waiting ∷ done
