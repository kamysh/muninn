{-# OPTIONS --safe #-}
-- Registration is one atomic change. Its slot is a database identity, not a path.
module Muninn.RepositoryRegistration where

import Muninn.Database as Database
import Muninn.RepositoryIdentity as Identity
open import Data.Nat using (ℕ; _≟_)
open import Data.List using (List)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

record Registration : Set where
  constructor registration
  field family : Identity.FamilyBinding
        checkouts : List Identity.CheckoutBinding
        indexedWork : List ℕ

module DB = Database.Store ℕ Registration _≟_

data Reply : Set where
  created : Reply
  present : Registration → Reply

-- A retry sees the saved registration. An occupied identity is never overwritten.
register : ℕ → Registration → DB.Rows → Reply × DB.Rows
register id desired world with DB.lookup id world
... | nothing = created , DB.write id desired world
... | just saved = present saved , world

otherFamiliesUnchanged : ∀ id other desired world → ¬ (id ≡ other) →
  DB.lookup other (proj₂ (register id desired world)) ≡ DB.lookup other world
otherFamiliesUnchanged id other desired world different with DB.lookup id world
... | nothing = DB.writePreservesOther id other desired world different
... | just saved = refl

retryAfterCommit : ∀ id desired world →
  register id desired (DB.write id desired world) ≡ (present desired , DB.write id desired world)
retryAfterCommit id desired world rewrite DB.writeVisible id desired world = refl

-- Directory-to-Git conversion is explicit and retains the family identity and
-- already registered checkouts. Compatible indexed data is not changed here.
convert : Identity.GitObservation → Registration → Registration
convert observed (registration family checkouts indexedWork) = registration (Identity.convertBinding family observed) checkouts indexedWork

conversionKeepsCheckouts : ∀ observed before → Registration.checkouts (convert observed before) ≡ Registration.checkouts before
conversionKeepsCheckouts observed (registration family checkouts indexedWork) = refl

conversionKeepsFamily : ∀ observed before →
  Identity.FamilyBinding.id (Registration.family (convert observed before)) ≡
  Identity.FamilyBinding.id (Registration.family before)
conversionKeepsFamily observed (registration family checkouts indexedWork) = refl

-- Reuse follows external identity evidence; a path match alone is insufficient.
-- An inconclusive observation starts a dialogue instead of adopting a family.
data Discovery (saved : Identity.FamilyBinding) (observed : Identity.Observation) : Set where
  recognized : Identity.FamilyAssociation saved observed → Discovery saved observed
  needsContext : ¬ Identity.FamilyAssociation saved observed → Discovery saved observed

discover : (saved : Identity.FamilyBinding) → (observed : Identity.Observation) → Discovery saved observed
discover saved observed with Identity.familyAssociation? saved observed
... | Relation.Nullary.yes same = recognized same
... | Relation.Nullary.no missing = needsContext missing

conversionKeepsIndexedWork : ∀ observed before →
  Registration.indexedWork (convert observed before) ≡ Registration.indexedWork before
conversionKeepsIndexedWork observed (registration family checkouts indexedWork) = refl

-- The atomic statement either did not commit or committed its complete row.
data Interrupted (id : ℕ) (desired : Registration) (before : DB.Rows) : DB.Rows → Set where
  beforeCommit : Interrupted id desired before before
  afterCommit : Interrupted id desired before (DB.write id desired before)

retryConverges : ∀ id desired before observed → DB.lookup id before ≡ nothing →
  Interrupted id desired before observed →
  proj₂ (register id desired observed) ≡ DB.write id desired before
retryConverges id desired before .before absent beforeCommit rewrite absent = refl
retryConverges id desired before .(DB.write id desired before) absent afterCommit
  rewrite DB.writeVisible id desired before = refl

-- Worktrees have their own Git administration identity within the family.
data CheckoutDiscovery (kind : Identity.Kind) (saved : Identity.CheckoutBinding)
  (observed : Identity.Observation) : Set where
  recognizedCheckout : Identity.CheckoutAssociation kind saved observed → CheckoutDiscovery kind saved observed
  checkoutNeedsContext : ¬ Identity.CheckoutAssociation kind saved observed → CheckoutDiscovery kind saved observed

discoverCheckout : (kind : Identity.Kind) → (saved : Identity.CheckoutBinding) →
  (observed : Identity.Observation) → CheckoutDiscovery kind saved observed
discoverCheckout kind saved observed with Identity.checkoutAssociation? kind saved observed
... | Relation.Nullary.yes same = recognizedCheckout same
... | Relation.Nullary.no missing = checkoutNeedsContext missing

freshRegistrationVisible : ∀ id desired world → DB.lookup id world ≡ nothing →
  DB.lookup id (proj₂ (register id desired world)) ≡ just desired
freshRegistrationVisible id desired world empty rewrite empty = DB.writeVisible id desired world

-- The registration action is a database transaction with one commit boundary.
registrationTx : ℕ → Registration → DB.Transaction Reply
registrationTx id desired = DB.scan λ world → decide (DB.lookup id world)
  where
  decide : Data.Maybe.Maybe Registration → DB.Transaction Reply
  decide nothing = DB.put id desired (DB.commit created)
  decide (just saved) = DB.commit (present saved)

transactionMatchesRegistration : ∀ id desired world →
  DB.execute (registrationTx id desired) world ≡ register id desired world
transactionMatchesRegistration id desired world with DB.lookup id world
... | nothing = refl
... | just saved = refl

import Muninn.Recovery as Recovery
module Execution = Recovery.Protocol ℕ Registration _≟_

registrationScript : ℕ → Registration → Execution.Script Reply
registrationScript id desired = Execution.atomic (registrationTx id desired) Execution.done

-- The shared interruption semantics admits only the original world or the
-- completely committed registration, including an acknowledgement loss.
actualInterruption : ∀ id desired before observed → DB.lookup id before ≡ nothing →
  Execution.Interrupted (registrationScript id desired) before observed →
  Interrupted id desired before observed
actualInterruption id desired before .before absent (residual , Execution.stop) = beforeCommit
actualInterruption id desired before .(proj₂ (DB.execute (registrationTx id desired) before)) absent
  (residual , Execution.committed Execution.stop)
  rewrite absent = afterCommit

actualRetryConverges : ∀ id desired before observed → DB.lookup id before ≡ nothing →
  Execution.Interrupted (registrationScript id desired) before observed →
  proj₂ (DB.execute (registrationTx id desired) observed) ≡ DB.write id desired before
actualRetryConverges id desired before observed absent interrupted =
  trans (cong proj₂ (transactionMatchesRegistration id desired observed))
    (retryConverges id desired before observed absent (actualInterruption id desired before observed absent interrupted))
