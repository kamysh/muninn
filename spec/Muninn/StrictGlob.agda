{-# OPTIONS --safe #-}
-- Strict policy syntax distinguishes unclosed raw brackets from quoted literals.
module Muninn.StrictGlob where

import Muninn.GlobTokens as T
import Muninn.GlobBody as B
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe.Properties using (just-injective)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans)

TokenOK : ∀ {boundary group input token suffix} → T.Source boundary group input token suffix → Set
TokenOK (T.bracketLiteral rest absent) = ⊥
TokenOK (T.literal char rest plain) = ⊤
TokenOK (T.escaped char rest) = ⊤
TokenOK (T.question rest) = ⊤
TokenOK (T.wildcard rest absent) = ⊤
TokenOK (T.recursive tail term suffix source) = ⊤
TokenOK (T.class result) = ⊤
TokenOK (T.openGroup rest) = ⊤
TokenOK (T.closeGroup rest) = ⊤
TokenOK (T.commaToken rest) = ⊤

token? : ∀ {boundary group input token suffix} (source : T.Source boundary group input token suffix) → Dec (TokenOK source)
token? (T.bracketLiteral rest absent) = no (λ impossible → impossible)
token? (T.literal char rest plain) = yes tt
token? (T.escaped char rest) = yes tt
token? (T.question rest) = yes tt
token? (T.wildcard rest absent) = yes tt
token? (T.recursive tail term suffix source) = yes tt
token? (T.class result) = yes tt
token? (T.openGroup rest) = yes tt
token? (T.closeGroup rest) = yes tt
token? (T.commaToken rest) = yes tt

tokenTransfer : ∀ {boundary group input token suffix}
  (first second : T.Source boundary group input token suffix) → TokenOK first → TokenOK second
tokenTransfer first (T.literal char rest plain) valid = tt
tokenTransfer first (T.escaped char rest) valid = tt
tokenTransfer first (T.question rest) valid = tt
tokenTransfer first (T.wildcard rest absent) valid = tt
tokenTransfer first (T.recursive tail term suffix source) valid = tt
tokenTransfer first (T.class result) valid = tt
tokenTransfer (T.literal char rest plain) (T.bracketLiteral .rest absent) valid = plain T.bracketMark refl
tokenTransfer (T.bracketLiteral rest firstAbsent) (T.bracketLiteral .rest secondAbsent) valid = valid
tokenTransfer first (T.openGroup rest) valid = tt
tokenTransfer first (T.closeGroup rest) valid = tt
tokenTransfer first (T.commaToken rest) valid = tt

Strict : ∀ {input before result} → B.Source input before result → Set
Strict (B.end current branches boundary) = ⊤
Strict (B.next token action rest) = TokenOK token × Strict rest

strict? : ∀ {input before result} (source : B.Source input before result) → Dec (Strict source)
strict? (B.end current branches boundary) = yes tt
strict? (B.next token action rest) with token? token
... | no absent = no (λ valid → absent (proj₁ valid))
... | yes allowed with strict? rest
...   | no absent = no (λ valid → absent (proj₂ valid))
...   | yes remainder = yes (allowed , remainder)

transfer : ∀ {input before result} (first second : B.Source input before result) → Strict first → Strict second
transfer (B.end current branches boundary) (B.end .current .branches .boundary) valid = tt
transfer (B.end current branches boundary) (B.next token action rest) valid = ⊥-elim (B.emptyToken token)
transfer (B.next token action rest) (B.end current branches boundary) valid = ⊥-elim (B.emptyToken token)
transfer (B.next token action rest) (B.next otherToken otherAction otherRest) (allowed , remainder)
  with T.deterministic token otherToken
... | refl with just-injective (trans (sym (B.stepRecognized action)) (B.stepRecognized otherAction))
...   | refl = tokenTransfer token otherToken allowed , transfer rest otherRest remainder
