{-# OPTIONS --safe #-}
-- Actual policy-entry admission retains original input and strict source evidence.
module Muninn.PolicyRuleAdmission where

import Muninn.RulePatterns as R
import Muninn.GlobBody as B
import Muninn.StrictGlob as S
open import Data.Char using (Char; isSpace; toℕ)
import Data.Nat as Nat
open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; reverse)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)

leftTrim : R.Word → R.Word
leftTrim [] = []
leftTrim (char ∷ rest) with isSpace char
... | true = leftTrim rest
... | false = char ∷ rest

normalize : R.Word → R.Word
normalize input = reverse (leftTrim (reverse (leftTrim input)))

NulFree : R.Word → Set
NulFree = All.All (λ char → toℕ char ≢ Nat.zero)

nulFree? : ∀ input → Dec (NulFree input)
nulFree? = All.all? (λ char → ¬? (toℕ char Nat.≟ Nat.zero))

record Entry (original : R.Word) : Set where
  constructor admitted
  field compiled : R.Compiled (normalize original)
        nulFree : NulFree (normalize original)
        strict : S.Strict (B.Parsed.source (R.Compiled.bodyInfo compiled))

admit : ∀ original → Maybe (Entry original)
admit original with R.compile (normalize original)
... | nothing = nothing
... | just candidate with nulFree? (normalize original)
...   | no absent = nothing
...   | yes clean with S.strict? (B.Parsed.source (R.Compiled.bodyInfo candidate))
...     | no absent = nothing
...     | yes strict = just (admitted candidate clean strict)

compiledStrictTransfer : ∀ {input} (first second : R.Compiled input) →
  S.Strict (B.Parsed.source (R.Compiled.bodyInfo first)) → S.Strict (B.Parsed.source (R.Compiled.bodyInfo second))
compiledStrictTransfer
  (R.compiled (R.header negated root directory body firstHeader) firstPresent (B.parsed firstGlob firstSource))
  (R.compiled (R.header otherNegated otherRoot otherDirectory otherBody secondHeader) secondPresent (B.parsed secondGlob secondSource)) valid
  with trans (sym (R.headerRecognized firstHeader)) (R.headerRecognized secondHeader)
... | refl with B.deterministic firstSource secondSource
...   | refl = S.transfer firstSource secondSource valid

admitComplete : ∀ {original} → Entry original → Σ (Entry original) (λ actual → admit original ≡ just actual)
admitComplete {original} entry with R.compile (normalize original) |
  R.recognized (R.Header.source (R.Compiled.headerInfo (Entry.compiled entry)))
    (R.Compiled.bodyPresent (Entry.compiled entry))
    (B.Parsed.source (R.Compiled.bodyInfo (Entry.compiled entry)))
... | nothing | ()
... | just candidate | known with nulFree? (normalize original)
...   | no absent = ⊥-elim (absent (Entry.nulFree entry))
...   | yes clean with S.strict? (B.Parsed.source (R.Compiled.bodyInfo candidate))
...     | no absent = ⊥-elim (absent (compiledStrictTransfer (Entry.compiled entry) candidate (Entry.strict entry)))
...     | yes strict = admitted candidate clean strict , refl

semanticUnique : ∀ {original} (first second : Entry original) → R.semantic (Entry.compiled first) ≡ R.semantic (Entry.compiled second)
semanticUnique first second = R.deterministic (Entry.compiled first) (Entry.compiled second)


data Entries : List R.Word → Set where
  none : Entries []
  more : ∀ {input inputs} → Entry input → Entries inputs → Entries (input ∷ inputs)

admitAll : ∀ inputs → Maybe (Entries inputs)
admitAll [] = just none
admitAll (input ∷ inputs) with admit input
... | nothing = nothing
... | just entry with admitAll inputs
...   | nothing = nothing
...   | just rest = just (more entry rest)

admitAllComplete : ∀ {inputs} → Entries inputs → Σ (Entries inputs) (λ actual → admitAll inputs ≡ just actual)
admitAllComplete none = none , refl
admitAllComplete (more entry rest) with admitComplete entry
... | actual , headKnown rewrite headKnown with admitAllComplete rest
...   | actualRest , tailKnown rewrite tailKnown = more actual actualRest , refl
