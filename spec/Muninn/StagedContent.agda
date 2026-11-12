{-# OPTIONS --safe #-}
-- Text publication and vector preparation are independent state transitions.
module Muninn.StagedContent where

import Muninn.VectorData as V
import Muninn.Worktree as W
open import Muninn.Types using (Tier)
open import Data.Bool using (Bool; true; false)
open import Data.String using (String)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- A usable vector must belong to this exact input and embedding profile.
data VectorState (profile : W.EmbeddingKey) (source : String) : Set where
  pending : VectorState profile source
  unavailable : V.Guidance → VectorState profile source
  ready : (saved : V.Value) → V.Value.profile saved ≡ profile →
    V.Value.source saved ≡ source → VectorState profile source

-- The cache lookup is an observation of stored compatible data. Its link to
-- physical storage is checked separately; a hit always selects reuse.
record Compatible (profile : W.EmbeddingKey) (source : String) : Set where
  constructor compatible
  field saved : V.Value
        sameProfile : V.Value.profile saved ≡ profile
        sameSource : V.Value.source saved ≡ source

data VectorWork {profile source} : Maybe (Compatible profile source) → Set where
  reuse : (saved : Compatible profile source) → VectorWork (just saved)
  prepare : VectorWork nothing

chooseWork : ∀ {profile source} (cached : Maybe (Compatible profile source)) → VectorWork cached
chooseWork (just saved) = reuse saved
chooseWork nothing = prepare

reuseOnHit : ∀ {profile source} (saved : Compatible profile source) →
  chooseWork (just saved) ≡ reuse saved
reuseOnHit saved = refl

-- Logical stored content and its vector status for one selected source.
record State : Set where
  constructor state
  field tier : Tier
        source : String
        profile : W.EmbeddingKey
        textPublished : Bool
        symbolsPublished : Bool
        vector : VectorState profile source

publishText : State → State
publishText (state tier source profile text symbols vector) =
  state tier source profile true true vector

attach : (before : State) (saved : V.Value) →
  V.Value.profile saved ≡ State.profile before → V.Value.source saved ≡ State.source before → State
attach (state tier source profile text symbols vector) saved sameProfile sameSource =
  state tier source profile text symbols (ready saved sameProfile sameSource)

retry : State → State
retry (state tier source profile text symbols (unavailable guidance)) =
  state tier source profile text symbols pending
retry before = before

retryKeepsText : ∀ before → State.textPublished (retry before) ≡ State.textPublished before
retryKeepsText (state tier source profile text symbols pending) = refl
retryKeepsText (state tier source profile text symbols (unavailable guidance)) = refl
retryKeepsText (state tier source profile text symbols (ready saved sameProfile sameSource)) = refl

-- Coverage is read from this stored state; an unassociated cache entry alone
-- cannot make the vector for this source appear ready.
data Coverage : Set where
  textNotPublished vectorPending vectorUnavailable vectorReady : Coverage

coverage : State → Coverage
coverage (state tier source profile false symbols vector) = textNotPublished
coverage (state tier source profile true symbols pending) = vectorPending
coverage (state tier source profile true symbols (unavailable guidance)) = vectorUnavailable
coverage (state tier source profile true symbols (ready saved sameProfile sameSource)) = vectorReady

textCanPublish : ∀ before → State.textPublished (publishText before) ≡ true
textCanPublish (state tier source profile text symbols vector) = refl

vectorUpdateKeepsText : ∀ before saved sameProfile sameSource →
  State.textPublished (attach before saved sameProfile sameSource) ≡ State.textPublished before
vectorUpdateKeepsText (state tier source profile text symbols vector) saved sameProfile sameSource = refl

vectorUpdateKeepsSymbols : ∀ before saved sameProfile sameSource →
  State.symbolsPublished (attach before saved sameProfile sameSource) ≡ State.symbolsPublished before
vectorUpdateKeepsSymbols (state tier source profile text symbols vector) saved sameProfile sameSource = refl

usableReportsReady : ∀ tier source profile symbols saved sameProfile sameSource →
  coverage (state tier source profile true symbols (ready saved sameProfile sameSource)) ≡ vectorReady
usableReportsReady tier source profile symbols saved sameProfile sameSource = refl

-- A ready report has an actual associated valid vector, with matching source
-- and profile, rather than merely a cached candidate.
readyHasAssociatedVector : ∀ before → coverage before ≡ vectorReady →
  Σ V.Value (λ saved → (V.Value.profile saved ≡ State.profile before) ×
    (V.Value.source saved ≡ State.source before))
readyHasAssociatedVector (state tier source profile false symbols vector) ()
readyHasAssociatedVector (state tier source profile true symbols pending) ()
readyHasAssociatedVector (state tier source profile true symbols (unavailable guidance)) ()
readyHasAssociatedVector (state tier source profile true symbols (ready saved sameProfile sameSource)) _ =
  saved , sameProfile , sameSource
