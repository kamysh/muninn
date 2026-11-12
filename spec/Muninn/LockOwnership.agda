{-# OPTIONS --safe #-}
-- Session ownership and handoff for indexing and publication are distinct.
module Muninn.LockOwnership where

import Muninn.Database as Database
import Muninn.AdvisoryLock as Legacy
import Muninn.CatalogInputs as Input
open import Muninn.Types using (UUID)
open import Data.Nat using (ℕ; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (proj₂)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

record Owner : Set where
  constructor owner
  field session : UUID
        request : Input.OperationId
        kind : Legacy.HolderKind

record TransactionOwner : Set where
  constructor transactionOwner
  field session transaction : UUID

-- Notification can wake earlier. Polling is a configurable fallback, not a
-- deadline: notification delivery, database availability and scheduling are
-- environmental conditions for progress.
record WakePolicy : Set where
  field fallbackSeconds : ℕ
        positive : 1 ≤ fallbackSeconds

defaultWakePolicy : WakePolicy
defaultWakePolicy = record { fallbackSeconds = 10; positive = s≤s z≤n }

data Wake (policy : WakePolicy) : Set where
  notification : Wake policy
  poll : (elapsed : ℕ) → WakePolicy.fallbackSeconds policy ≤ elapsed → Wake policy

module Model (Key Value : Set) (equal : (a b : Key) → Dec (a ≡ b))
  (sameSession : (a b : UUID) → Dec (a ≡ b)) where
  module DB = Database.Store Key Value equal

  record Coord : Set where
    constructor coord
    field indexOwner : Maybe Owner
          waiting : List Owner
          publicationOwner : Maybe TransactionOwner
          committed : DB.Rows

  -- A vanished session cannot retain queue positions and block later work.
  dropSession : UUID → List Owner → List Owner
  dropSession session [] = []
  dropSession session (held ∷ rest) with sameSession session (Owner.session held)
  ... | yes _ = dropSession session rest
  ... | no _ = held ∷ dropSession session rest

  data DoesNotOwnIndex (session : UUID) : Maybe Owner → Set where
    noIndex : DoesNotOwnIndex session nothing
    otherIndex : ∀ held → ¬ (session ≡ Owner.session held) → DoesNotOwnIndex session (just held)

  data DoesNotOwnPublication (session : UUID) : Maybe TransactionOwner → Set where
    noPublication : DoesNotOwnPublication session nothing
    otherPublication : ∀ held → ¬ (session ≡ TransactionOwner.session held) → DoesNotOwnPublication session (just held)

  data Event : Set where
    requestIndex acquireIndex releaseIndex preemptIndex : Owner → Event
    loseSession : UUID → Event
    beginTransaction finishTransaction : TransactionOwner → Event

  data Step : Event → Coord → Coord → Set₁ where
    request : ∀ {index waiting publication rows} session requestId →
      Step (requestIndex (owner session requestId Legacy.Fg))
        (coord index waiting publication rows)
        (coord index (waiting ++ (owner session requestId Legacy.Fg ∷ [])) publication rows)
    foregroundAcquire : ∀ {waiting publication rows} session requestId →
      Step (acquireIndex (owner session requestId Legacy.Fg))
        (coord nothing (owner session requestId Legacy.Fg ∷ waiting) publication rows)
        (coord (just (owner session requestId Legacy.Fg)) waiting publication rows)
    backgroundAcquire : ∀ {publication rows} session requestId →
      Step (acquireIndex (owner session requestId Legacy.Bg)) (coord nothing [] publication rows)
        (coord (just (owner session requestId Legacy.Bg)) [] publication rows)
    release : ∀ {waiting publication rows} held →
      Step (releaseIndex held) (coord (just held) waiting publication rows) (coord nothing waiting publication rows)
    preempt : ∀ {publication rows} session requestId first rest →
      Step (preemptIndex (owner session requestId Legacy.Bg))
        (coord (just (owner session requestId Legacy.Bg)) (first ∷ rest) publication rows)
        (coord nothing (first ∷ rest) publication rows)
    sessionLostIndex : ∀ {waiting rows} held →
      Step (loseSession (Owner.session held)) (coord (just held) waiting nothing rows) (coord nothing (dropSession (Owner.session held) waiting) nothing rows)
    sessionLostIndexOther : ∀ {waiting rows} held other →
      ¬ (Owner.session held ≡ TransactionOwner.session other) →
      Step (loseSession (Owner.session held)) (coord (just held) waiting (just other) rows)
        (coord nothing (dropSession (Owner.session held) waiting) (just other) rows)
    beginPublication : ∀ {index waiting rows} held →
      Step (beginTransaction held) (coord index waiting nothing rows) (coord index waiting (just held) rows)
    finishPublication : ∀ {index waiting rows A} held (transaction : DB.Transaction A) →
      Step (finishTransaction held) (coord index waiting (just held) rows)
        (coord index waiting nothing (proj₂ (DB.execute transaction rows)))
    sessionLostPublication : ∀ {waiting rows} held →
      Step (loseSession (TransactionOwner.session held)) (coord nothing waiting (just held) rows) (coord nothing (dropSession (TransactionOwner.session held) waiting) nothing rows)
    sessionLostPublicationOther : ∀ {waiting rows} held other →
      ¬ (TransactionOwner.session held ≡ Owner.session other) →
      Step (loseSession (TransactionOwner.session held)) (coord (just other) waiting (just held) rows)
        (coord (just other) (dropSession (TransactionOwner.session held) waiting) nothing rows)
    sessionLostBoth : ∀ {waiting rows} held publication →
      Owner.session held ≡ TransactionOwner.session publication →
      Step (loseSession (Owner.session held)) (coord (just held) waiting (just publication) rows)
        (coord nothing (dropSession (Owner.session held) waiting) nothing rows)
    sessionLostWaiter : ∀ {rows index publication} session waiting →
      DoesNotOwnIndex session index → DoesNotOwnPublication session publication →
      Step (loseSession session) (coord index waiting publication rows)
        (coord index (dropSession session waiting) publication rows)

  uniqueIndexOwner : ∀ state first second →
    Coord.indexOwner state ≡ just first → Coord.indexOwner state ≡ just second → first ≡ second
  uniqueIndexOwner state first .first refl refl = refl

  uniquePublicationOwner : ∀ state first second →
    Coord.publicationOwner state ≡ just first → Coord.publicationOwner state ≡ just second → first ≡ second
  uniquePublicationOwner state first .first refl refl = refl

  firstWaiterAcquires : ∀ {waiting publication rows after} session requestId candidate →
    Step (acquireIndex candidate) (coord nothing (owner session requestId Legacy.Fg ∷ waiting) publication rows) after →
    candidate ≡ owner session requestId Legacy.Fg
  firstWaiterAcquires session requestId .(owner session requestId Legacy.Fg) (foregroundAcquire .session .requestId) = refl

  data NoCommit : Event → Set where
    requestDoesNotCommit : ∀ held → NoCommit (requestIndex held)
    acquireDoesNotCommit : ∀ held → NoCommit (acquireIndex held)
    releaseDoesNotCommit : ∀ held → NoCommit (releaseIndex held)
    preemptDoesNotCommit : ∀ held → NoCommit (preemptIndex held)
    lossDoesNotCommit : ∀ session → NoCommit (loseSession session)
    beginDoesNotCommit : ∀ held → NoCommit (beginTransaction held)

  nonCommitPreservesStore : ∀ {event before after} → NoCommit event → Step event before after →
    Coord.committed after ≡ Coord.committed before
  nonCommitPreservesStore (requestDoesNotCommit held) (request session requestId) = refl
  nonCommitPreservesStore (acquireDoesNotCommit held) (foregroundAcquire session requestId) = refl
  nonCommitPreservesStore (acquireDoesNotCommit held) (backgroundAcquire session requestId) = refl
  nonCommitPreservesStore (releaseDoesNotCommit held) (release .held) = refl
  nonCommitPreservesStore (preemptDoesNotCommit held) (preempt session requestId first rest) = refl
  nonCommitPreservesStore (lossDoesNotCommit session) (sessionLostIndex held) = refl
  nonCommitPreservesStore (lossDoesNotCommit session) (sessionLostIndexOther held other different) = refl
  nonCommitPreservesStore (lossDoesNotCommit session) (sessionLostPublication held) = refl
  nonCommitPreservesStore (lossDoesNotCommit session) (sessionLostPublicationOther held other different) = refl
  nonCommitPreservesStore (lossDoesNotCommit session) (sessionLostBoth held publication same) = refl
  nonCommitPreservesStore (lossDoesNotCommit session) (sessionLostWaiter .session waiting indexEvidence publicationEvidence) = refl
  nonCommitPreservesStore (beginDoesNotCommit held) (beginPublication .held) = refl

  abortKeepsCommitted : ∀ {A} (transaction : DB.Transaction A) rows reply →
    DB.evaluate transaction rows ≡ DB.aborted reply → proj₂ (DB.execute transaction rows) ≡ rows
  abortKeepsCommitted = DB.abortKeepsStore

  -- Once the holder releases, the first queued interactive request can acquire.
  -- A scheduler must execute these transitions; polling alone supplies no bound.
  data Path : Coord → Coord → Set₁ where
    done : ∀ {state} → Path state state
    then : ∀ {event first middle last} → Step event first middle → Path middle last → Path first last

  queuedHandoff : ∀ held session requestId waiting publication rows →
    Path (coord (just held) (owner session requestId Legacy.Fg ∷ waiting) publication rows)
      (coord (just (owner session requestId Legacy.Fg)) waiting publication rows)
  queuedHandoff held session requestId waiting publication rows =
    then (release held) (then (foregroundAcquire session requestId) done)
