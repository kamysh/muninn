{-# OPTIONS --safe #-}
-- Reusable per-file structural analysis and checkout-wide name resolution.
module Muninn.IncrementalStructure where

import Muninn.ReusePolicy as Reuse
import Muninn.CompletedWork as Completed
import Muninn.Worktree as Worktree
import Muninn.IncrementalObservation as Observation
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_)
open import Data.Bool using (false)
open import Data.Maybe using (Maybe; just)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; subst)

-- Names and paths are abstract IDs. Candidate targets are retained even when
-- they have no match in the current checkout.
record Symbol : Set where
  constructor symbol
  field id path name : ℕ

record Candidate : Set where
  constructor mkCandidate
  field source sourcePath targetName : ℕ

record Analysis : Set where
  constructor analysis
  field symbols : List Symbol
        candidates : List Candidate

module Cache = Completed.For Reuse.AnalysisInput Analysis Reuse.analysisInput?

-- The validator denotes the parser/extractor contract for the exact bytes and
-- versioned settings in AnalysisInput. It is an adapter obligation, not a
-- claim that an arbitrary implementation conforms to that contract.
module Certified (Valid : Reuse.AnalysisInput → Analysis → Set) where
  module Stored = Cache.Certified Valid

  cachedAnalysisReused : ∀ input (before : Stored.Cache) value →
    Cache.Store.lookup input (Stored.Cache.rows before) ≡ just value →
    Cache.invokesProvider (Stored.nextAction input before) ≡ false
  cachedAnalysisReused input before value found =
    Cache.hitCannotCalculate input (Stored.Cache.rows before) value found (Stored.nextAction input before)

  reusedAnalysisValid : ∀ input (before : Stored.Cache) value →
    Cache.Store.lookup input (Stored.Cache.rows before) ≡ just value → Valid input value
  reusedAnalysisValid input before value found = Stored.reusedValueValid input before value found

  -- A saved entry can serve another observation only after exact input
  -- equality, including the family, bytes, and versioned analysis settings.
  compatibleCacheHit : ∀ saved current (before : Stored.Cache) value → saved ≡ current →
    Cache.Store.lookup saved (Stored.Cache.rows before) ≡ just value →
    Valid current value × (Cache.invokesProvider (Stored.nextAction current before) ≡ false)
  compatibleCacheHit saved .saved before value refl found =
    reusedAnalysisValid saved before value found , cachedAnalysisReused saved before value found

-- A name resolves to all local matches when any exist; otherwise it resolves
-- to all matching nonlocal symbols. The selected list is supplied by the
-- current checkout view, not by a process-global collection.
record Match (candidate : Candidate) (target : Symbol) : Set where
  constructor match
  field sameName : Symbol.name target ≡ Candidate.targetName candidate

Local : Candidate → Symbol → Set
Local candidate target = Symbol.path target ≡ Candidate.sourcePath candidate

NoLocal : Candidate → List Symbol → Set
NoLocal candidate selected = ∀ target → target ∈ selected → Match candidate target → Local candidate target → ⊥

data Resolves (candidate : Candidate) (selected : List Symbol) : Symbol → Set where
  local : ∀ {target} → target ∈ selected → Match candidate target → Local candidate target → Resolves candidate selected target
  external : ∀ {target} → target ∈ selected → Match candidate target → ¬ Local candidate target →
    NoLocal candidate selected → Resolves candidate selected target

endpointSelected : ∀ {candidate selected target} → Resolves candidate selected target → target ∈ selected
endpointSelected (local present same path) = present
endpointSelected (external present same outside noLocal) = present

endpointNameMatches : ∀ {candidate selected target} → Resolves candidate selected target →
  Symbol.name target ≡ Candidate.targetName candidate
endpointNameMatches (local present same path) = Match.sameName same
endpointNameMatches (external present same outside noLocal) = Match.sameName same

-- An available local target rules out every nonlocal target, even if a
-- nonlocal symbol with the same name is present.
localPreemptsExternal : ∀ {candidate selected localTarget target} →
  localTarget ∈ selected → Match candidate localTarget → Local candidate localTarget →
  ¬ Local candidate target → ¬ Resolves candidate selected target
localPreemptsExternal present matching localPath outside (local _ _ targetPath) = outside targetPath
localPreemptsExternal present matching localPath outside (external _ _ _ absent) = absent _ present matching localPath

-- A newly published local symbol can resolve a previously unresolved call
-- without recalculating the unchanged caller's retained candidate.
addedLocalResolves : ∀ candidate target selected → Match candidate target → Local candidate target →
  Resolves candidate (target ∷ selected) target
addedLocalResolves candidate target selected matching path = local (here refl) matching path

-- A new nonlocal target likewise resolves when no local match exists.
addedExternalResolves : ∀ candidate target selected → Match candidate target → ¬ Local candidate target →
  NoLocal candidate (target ∷ selected) → Resolves candidate (target ∷ selected) target
addedExternalResolves candidate target selected matching outside absent = external (here refl) matching outside absent

-- Replacing an analysis with the exact cached value preserves every candidate
-- and therefore its resolution against the current checkout's symbols.
reusePreservesResolution : ∀ {first second} → first ≡ second → ∀ candidate selected target →
  candidate ∈ Analysis.candidates first → Resolves candidate selected target →
  candidate ∈ Analysis.candidates second × Resolves candidate selected target
reusePreservesResolution refl candidate selected target present resolved = present , resolved

-- Every edge is anchored to a cached, valid analysis of a file in the actual
-- selected checkout. The adapter supplies the current file input map and the
-- selected symbol list; matching a hash alone cannot establish inputAt.
module SelectedEdges (Valid : Reuse.AnalysisInput → Analysis → Set)
  (family : Worktree.FamilyId) (current : Observation.Snapshot)
  (fileInput : ℕ → Maybe Reuse.AnalysisInput) (selected : List Symbol)
  (before : Certified.Stored.Cache Valid) where
  module Stored = Certified.Stored Valid

  record Edge : Set where
    field input : Reuse.AnalysisInput
          artifact : Analysis
          source target : Symbol
          reference : Candidate
          sourceFile targetFile : Observation.File
          targetInput : Reuse.AnalysisInput
          targetArtifact : Analysis
          inputFamily : Reuse.AnalysisInput.family input ≡ family
          inputAt : fileInput (Symbol.path source) ≡ just input
          sourceAt : current (Symbol.path source) ≡ Observation.present sourceFile
          sourceBytes : Observation.File.bytes sourceFile ≡ Worktree.AnalysisMeaning.bytes (Reuse.AnalysisInput.meaning input)
          cachedAt : Cache.Store.lookup input (Stored.Cache.rows before) ≡ just artifact
          sourceInArtifact : source ∈ Analysis.symbols artifact
          sourceSelected : source ∈ selected
          targetAt : current (Symbol.path target) ≡ Observation.present targetFile
          targetBytes : Observation.File.bytes targetFile ≡ Worktree.AnalysisMeaning.bytes (Reuse.AnalysisInput.meaning targetInput)
          targetInputAt : fileInput (Symbol.path target) ≡ just targetInput
          targetFamily : Reuse.AnalysisInput.family targetInput ≡ family
          targetCachedAt : Cache.Store.lookup targetInput (Stored.Cache.rows before) ≡ just targetArtifact
          targetInArtifact : target ∈ Analysis.symbols targetArtifact
          referenceInArtifact : reference ∈ Analysis.candidates artifact
          referenceSource : Candidate.source reference ≡ Symbol.id source
          referencePath : Candidate.sourcePath reference ≡ Symbol.path source
          targetResolved : Resolves reference selected target

  bothEndpointsSelected : ∀ edge → Edge.source edge ∈ selected × Edge.target edge ∈ selected
  bothEndpointsSelected edge = Edge.sourceSelected edge , endpointSelected (Edge.targetResolved edge)

  analysisIsValid : ∀ edge → Valid (Edge.input edge) (Edge.artifact edge)
  analysisIsValid edge = Stored.reusedValueValid (Edge.input edge) before (Edge.artifact edge) (Edge.cachedAt edge)

  targetAnalysisIsValid : ∀ edge → Valid (Edge.targetInput edge) (Edge.targetArtifact edge)
  targetAnalysisIsValid edge = Stored.reusedValueValid (Edge.targetInput edge) before (Edge.targetArtifact edge) (Edge.targetCachedAt edge)

  analysisBelongsToFamily : ∀ edge → Reuse.AnalysisInput.family (Edge.input edge) ≡ family
  analysisBelongsToFamily = Edge.inputFamily

  unchangedSourceNeedsNoProvider : ∀ edge →
    Cache.invokesProvider (Stored.nextAction (Edge.input edge) before) ≡ false
  unchangedSourceNeedsNoProvider edge =
    Cache.hitCannotCalculate (Edge.input edge) (Stored.Cache.rows before) (Edge.artifact edge)
      (Edge.cachedAt edge) (Stored.nextAction (Edge.input edge) before)
