{-# OPTIONS --safe #-}
-- Checkout publication while individual files or Git operations need attention.
module Muninn.CheckoutState where

open import Muninn.Types using (FilePath)
open import Muninn.IndexFsm using (GitState; Settled; Operating; Conflicted)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module Model (Artifact : Set) where
  View : Set
  View = FilePath → Maybe Artifact

  data Observation : Set where
    unchanged removed unreadable : Observation
    indexed : Artifact → Observation

  record State : Set where
    constructor state
    field
      published : Maybe View
      pending : FilePath → Bool

  previous : Maybe View → View
  previous nothing path = nothing
  previous (just view) path = view path

  select : Bool → Maybe Artifact → Maybe Artifact
  select true value = value
  select false value = nothing

  apply : Observation → Maybe Artifact → Maybe Artifact
  apply unchanged old = old
  apply removed old = nothing
  apply unreadable old = nothing
  apply (indexed value) old = just value

  pendingAfter : Observation → Bool → Bool
  pendingAfter unchanged old = old
  pendingAfter removed old = false
  pendingAfter unreadable old = true
  pendingAfter (indexed value) old = false

  selectPending : Bool → Bool → Bool
  selectPending true value = value
  selectPending false value = false

  filterView : (FilePath → Bool) → Maybe View → Maybe View
  filterView policy nothing = nothing
  filterView policy (just view) = just (λ path → select (policy path) (view path))

  reconcile : (FilePath → Bool) → GitState → State → (FilePath → Observation) → State
  reconcile policy Settled before observations = state
    (just (λ path → select (policy path) (apply (observations path) (previous (State.published before) path))))
    (λ path → selectPending (policy path) (pendingAfter (observations path) (State.pending before path)))
  reconcile policy Operating before observations = state
    (filterView policy (State.published before))
    (λ path → selectPending (policy path) (State.pending before path))
  reconcile policy Conflicted before observations = state
    (filterView policy (State.published before))
    (λ path → selectPending (policy path) (State.pending before path))

  unreadableHidden : ∀ policy before observations path → observations path ≡ unreadable →
    previous (State.published (reconcile policy Settled before observations)) path ≡ nothing
  unreadableHidden policy before observations path observed rewrite observed with policy path
  ... | true = refl
  ... | false = refl

  unreadablePending : ∀ policy before observations path → observations path ≡ unreadable → policy path ≡ true →
    State.pending (reconcile policy Settled before observations) path ≡ true
  unreadablePending policy before observations path observed included rewrite observed | included = refl

  indexedVisible : ∀ policy before observations path value → observations path ≡ indexed value → policy path ≡ true →
    previous (State.published (reconcile policy Settled before observations)) path ≡ just value
  indexedVisible policy before observations path value observed included rewrite observed | included = refl

  suspendedOperating : ∀ policy before observations →
    State.published (reconcile policy Operating before observations) ≡ filterView policy (State.published before)
  suspendedOperating policy before observations = refl

  suspendedConflicted : ∀ policy before observations →
    State.published (reconcile policy Conflicted before observations) ≡ filterView policy (State.published before)
  suspendedConflicted policy before observations = refl

  excludedHidden : ∀ policy git before observations path → policy path ≡ false →
    previous (State.published (reconcile policy git before observations)) path ≡ nothing
  excludedHidden policy Settled before observations path excluded rewrite excluded = refl
  excludedHidden policy Operating (state nothing pending) observations path excluded = refl
  excludedHidden policy Operating (state (just view) pending) observations path excluded rewrite excluded = refl
  excludedHidden policy Conflicted (state nothing pending) observations path excluded = refl
  excludedHidden policy Conflicted (state (just view) pending) observations path excluded rewrite excluded = refl

  suspendedWithoutView : ∀ policy observations pending →
    State.published (reconcile policy Operating (state nothing pending) observations) ≡ nothing
  suspendedWithoutView policy observations pending = refl

  conflictedWithoutView : ∀ policy observations pending →
    State.published (reconcile policy Conflicted (state nothing pending) observations) ≡ nothing
  conflictedWithoutView policy observations pending = refl

  excludedNotPending : ∀ policy git before observations path → policy path ≡ false →
    State.pending (reconcile policy git before observations) path ≡ false
  excludedNotPending policy Settled before observations path excluded rewrite excluded = refl
  excludedNotPending policy Operating before observations path excluded rewrite excluded = refl
  excludedNotPending policy Conflicted before observations path excluded rewrite excluded = refl
