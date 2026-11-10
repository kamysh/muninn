{-# OPTIONS --safe #-}
-- Durable finite traversal updates reuse the actual saved query and view.
module Muninn.PaginationAdvance where
import Muninn.PaginationData as P
import Muninn.Pagination as Page
import Muninn.PaginationTraversal as Traverse
import Muninn.PaginationStore as Store
import Muninn.PaginationCommit as Commit
import Muninn.OwnedState as O
import Muninn.ReceiptLedger as Ledger
import Muninn.WorkQueue as Q
import Muninn.CatalogInputs as I
import Muninn.Types as T
open import Data.Nat using (ℕ; _≟_; _<_; _≤_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Relation.Nullary using (yes; no)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
module DB = O.DB
module Exec = O.Execution

module Family (family : ℕ) (queryId : I.OperationId)
  (Match : O.World → P.Plan → P.Ref → P.Item → Set) where
  module Saved = Store.Family family
  module Query = Saved.Query queryId
  record Batch (world : O.World) (plan : P.Plan) : Set where
    module Source = Traverse.Source (Match world plan)
    field first rest : List P.Ref
          partition : P.Plan.pending plan ≡ first ++ rest
          advances : 0 < length first
          bounded : length first ≤ 1000
          classified : All Source.Classified first
          freshResults : ∀ result → result ∈ Source.found classified → ∀ previous → previous ∈ P.Plan.known plan →
            Traverse.identity (P.Item.ref result) ≢ Traverse.identity (P.Item.ref previous)
          uniqueResults : AllPairs (λ first second → Traverse.identity (P.Item.ref first) ≢ Traverse.identity (P.Item.ref second)) (Source.found classified)
    module Work = Source.Work plan
    step = Work.batch plan first rest partition advances bounded classified
    after = Page.State.extend plan plan step
    makesProgress : length (P.Plan.pending after) < length (P.Plan.pending plan)
    makesProgress = Page.State.decreases plan plan step
    sameQuery : P.Plan.query after ≡ P.Plan.query plan
    sameQuery = refl
    sameView : P.Plan.view after ≡ P.Plan.view plan
    sameView = refl
    recoveryContext : Commit.savedQuery after ≡ Commit.savedQuery plan
    recoveryContext = refl
    preservesPrefix : P.Plan.known after ≡ P.Plan.known plan ++ Source.found classified
    preservesPrefix = refl

  info : P.Plan → Q.Continuation
  info plan = record { parent = queryId; payload = Q.page (P.plan plan); search = Commit.savedQuery plan }
  row : P.Plan → O.Record
  row plan = Saved.newRow (info plan) (P.weakIds plan)
  advance : ℕ → (∀ world plan → Maybe (Batch world plan)) → DB.Transaction Commit.Reply
  advance expected prepare = DB.scan λ world → inspect world (Query.Plans.find world)
    where
    inspect : ∀ world → Maybe (Query.Plans.At world) → DB.Transaction Commit.Reply
    inspect world nothing = DB.commit (Commit.recover queryId Commit.recoverPrompt)
    inspect world (just found) with P.Plan.revision (Query.Plans.At.value found) ≟ expected
    ... | no newer = DB.commit Commit.continueWork
    ... | yes same with prepare world (Query.Plans.At.value found)
    ...   | nothing = DB.commit Commit.continueWork
    ...   | just batch = DB.put (Query.Plans.At.slot found) (row (Batch.after batch)) (DB.commit Commit.continueWork)

  noIdleHolds : ∀ plan → O.references (O.body (row plan)) ≡ []
  noIdleHolds plan = refl
  staleCheckpointDoesNotRepeat : ∀ expected prepare world (found : Query.Plans.At world) →
    Query.Plans.find world ≡ just found → P.Plan.revision (Query.Plans.At.value found) ≢ expected →
    DB.execute (advance expected prepare) world ≡ (Commit.continueWork , world)
  staleCheckpointDoesNotRepeat expected prepare world found located different rewrite located
    with P.Plan.revision (Query.Plans.At.value found) ≟ expected
  ... | yes same = ⊥-elim (different same)
  ... | no _ = refl
  atomicCheckpoint : ∀ expected prepare before observed →
    Exec.Interrupted (Exec.atomic (advance expected prepare) Exec.done) before observed →
    observed ≡ before ⊎ observed ≡ proj₂ (DB.execute (advance expected prepare) before)
  atomicCheckpoint expected prepare before observed = Ledger.atomicBoundary (advance expected prepare) before observed
