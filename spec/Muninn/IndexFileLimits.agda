{-# OPTIONS --safe #-}
-- The indexing admission batch schedules every ready selected file and retains
-- each unresolved size question. A question never blocks admission of a peer.
module Muninn.IndexFileLimits where

import Muninn.FileLimits as L
import Muninn.Config as C
import Muninn.Dialogue as D
open import Data.Nat using (ℕ)
open import Data.Nat.Show using (show)
open import Data.Bool using (Bool)
open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module Checkout (selected : String → Set) (policy : C.FamilyPolicy) where
  caps = C.FamilyPolicy.limits policy

  record File : Set where
    constructor file
    field path : String
          selectedFile : selected path
          contents : L.Contents
          parser : Bool

  Work : File → Set
  Work source = L.Work caps (File.contents source) (File.parser source)

  Ready : Set
  Ready = Σ File Work

  Waiting : Set
  Waiting = Σ File (λ source → ¬ L.TextAllowed caps (File.contents source))

  Batch : Set
  Batch = List Ready × List Waiting

  assess : ∀ source → L.Assessment caps (File.contents source) (File.parser source)
  assess source = L.assess caps (File.contents source) (File.parser source)

  plan : List File → Batch
  plan [] = [] , []
  plan (source ∷ rest) with assess source | plan rest
  ... | L.ask over | ready , waiting = ready , (source , over) ∷ waiting
  ... | L.run job | ready , waiting = (source , job) ∷ ready , waiting

  -- No premise about the other files: every allowed file has actual runnable
  -- work in the returned plan, even when any number of peers need a choice.
  readyScheduled : ∀ sources source → source ∈ sources → L.TextAllowed caps (File.contents source) →
    Σ (Work source) (λ job → (source , job) ∈ proj₁ (plan sources))
  readyScheduled (source ∷ rest) .source (here refl) allowed with assess source | plan rest
  ... | L.ask over | ready , waiting = ⊥-elim (over allowed)
  ... | L.run job | ready , waiting = job , here refl
  readyScheduled (first ∷ rest) source (there present) allowed
    with assess first | plan rest | readyScheduled rest source present allowed
  ... | L.ask over | ready , waiting | job , scheduled = job , scheduled
  ... | L.run firstJob | ready , waiting | job , scheduled = job , there scheduled

  waitingRecorded : ∀ sources source → source ∈ sources → ¬ L.TextAllowed caps (File.contents source) →
    Σ (¬ L.TextAllowed caps (File.contents source)) (λ over → (source , over) ∈ proj₂ (plan sources))
  waitingRecorded (source ∷ rest) .source (here refl) over with assess source | plan rest
  ... | L.ask blocked | ready , waiting = blocked , here refl
  ... | L.run job | ready , waiting = ⊥-elim (over (L.workFits job))
  waitingRecorded (first ∷ rest) source (there present) over
    with assess first | plan rest | waitingRecorded rest source present over
  ... | L.ask blocked | ready , waiting | proof , recorded = proof , there recorded
  ... | L.run firstJob | ready , waiting | proof , recorded = proof , recorded

  sizeQuestion : Waiting → D.Question
  sizeQuestion (source , over) = D.prerequisite
    (D.text 'F' ("ile " ++ File.path source ++ " contains " ++ show (length (File.contents source)) ++
      " raw bytes. The family file limit is " ++ show (C.FileLimits.selectedBytes caps) ++ " bytes."))
    (D.text 'C' "hoose how to continue: raise this family limit (all its worktrees), exclude this file through family selection rules, or reduce/split the file outside Muninn. Send the updated policy or file; other ready files continue indexing.")

  coverageMessage : ∀ source → Work source → D.Text
  coverageMessage source job with L.Work.coverage job
  ... | L.textAndStructure = D.text 'T' "ext and structural analysis are scheduled."
  ... | L.textOnly L.structuralSize = D.text 'T' ("ext indexing is scheduled for " ++ File.path source ++
      "; its " ++ show (length (File.contents source)) ++ " raw bytes exceed the structural limit of " ++
      show (C.FileLimits.structuralBytes caps) ++ " bytes. Raise the family structural limit to request structural analysis.")
  ... | L.textOnly L.noParser = D.text 'T' ("ext indexing is scheduled for " ++ File.path source ++
      "; structural analysis is unavailable because no parser supports this file. Structural queries cannot use it; text search remains available.")

  admittedFits : ∀ (ready : Ready) → L.TextAllowed caps (File.contents (proj₁ ready))
  admittedFits (source , job) = L.workFits job
