{-# OPTIONS --safe #-}
-- Ordered resolution derives actual matches from certified compiled rules.
module Muninn.OrderedSelection where

import Muninn.RulePatterns as R
import Muninn.RuleScope as S
import Muninn.GlobBody as B
import Muninn.Config as C
open import Data.Bool using (Bool; true; false; not)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.String using (String; toList)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

data Rules : List R.Word → Set where
  empty : Rules []
  cons : ∀ {input inputs} → R.Compiled input → Rules inputs → Rules (input ∷ inputs)

compile : ∀ inputs → Maybe (Rules inputs)
compile [] = just empty
compile (input ∷ inputs) with R.compile input
... | nothing = nothing
... | just rule with compile inputs
...   | nothing = nothing
...   | just rules = just (cons rule rules)

compileComplete : ∀ {inputs} → Rules inputs → Σ (Rules inputs) (λ actual → compile inputs ≡ just actual)
compileComplete empty = empty , refl
compileComplete (cons {input} rule rules) with R.compile input |
  R.recognized (R.Header.source (R.Compiled.headerInfo rule)) (R.Compiled.bodyPresent rule)
    (B.Parsed.source (R.Compiled.bodyInfo rule))
... | nothing | ()
... | just actual | known with compileComplete rules
...   | actualRest , complete rewrite complete = cons actual actualRest , refl

step : Bool → Bool → Bool → Bool
step before false negative = before
step before true negative = not negative

resolve : ∀ {inputs} → Bool → Rules inputs → R.Word → Bool → Bool
resolve before empty word directory = before
resolve before (cons rule rules) word directory =
  resolve (step before (S.matches rule word directory) (R.negative rule)) rules word directory

data Resolution : ∀ {inputs} → Bool → Rules inputs → R.Word → Bool → Bool → Set where
  end : ∀ before word directory → Resolution before empty word directory before
  skip : ∀ {input inputs before word directory result} {rule : R.Compiled input} {rules : Rules inputs} →
    ¬ S.PathMatches rule word directory → Resolution before rules word directory result →
    Resolution before (cons rule rules) word directory result
  apply : ∀ {input inputs before word directory result} {rule : R.Compiled input} {rules : Rules inputs} →
    S.PathMatches rule word directory → Resolution (not (R.negative rule)) rules word directory result →
    Resolution before (cons rule rules) word directory result

resolveCorrect : ∀ {inputs} before (rules : Rules inputs) word directory →
  Resolution before rules word directory (resolve before rules word directory)
resolveCorrect before empty word directory = end before word directory
resolveCorrect before (cons rule rules) word directory with S.pathMatches? rule word directory
... | yes matched = apply matched (resolveCorrect (not (R.negative rule)) rules word directory)
... | no absent = skip absent (resolveCorrect before rules word directory)

recognized : ∀ {inputs before word directory result} {rules : Rules inputs} →
  Resolution before rules word directory result → resolve before rules word directory ≡ result
recognized (end before word directory) = refl
recognized {word = word} {directory} (skip {rule = rule} absent rest) with S.pathMatches? rule word directory
... | yes matched = ⊥-elim (absent matched)
... | no actual = recognized rest
recognized {word = word} {directory} (apply {rule = rule} matched rest) with S.pathMatches? rule word directory
... | yes actual = recognized rest
... | no absent = ⊥-elim (absent matched)

deterministic : ∀ {inputs before word directory first second} {rules : Rules inputs} →
  Resolution before rules word directory first → Resolution before rules word directory second → first ≡ second
deterministic first second = trans (sym (recognized first)) (recognized second)

resolveEquivalent : ∀ {inputs} before (first second : Rules inputs) word directory →
  resolve before first word directory ≡ resolve before second word directory
resolveEquivalent before empty empty word directory = refl
resolveEquivalent before (cons first rest) (cons second other) word directory = trans
  (resolveEquivalent (step before (S.matches first word directory) (R.negative first)) rest other word directory)
  (cong (λ current → resolve current other word directory) (cong₂ (step before)
    (S.matchesStable first second word directory (R.deterministic first second))
    (cong proj₁ (R.deterministic first second))))

append : ∀ {first second} → Rules first → Rules second → Rules (first ++ second)
append empty later = later
append (cons rule rules) later = cons rule (append rules later)

resolveAppend : ∀ {first second} before (earlier : Rules first) (later : Rules second) word directory →
  resolve before (append earlier later) word directory ≡ resolve (resolve before earlier word directory) later word directory
resolveAppend before empty later word directory = refl
resolveAppend before (cons rule rules) later word directory =
  resolveAppend (step before (S.matches rule word directory) (R.negative rule)) rules later word directory

lastMatchWins : ∀ {inputs input} before (earlier : Rules inputs) (rule : R.Compiled input) word directory →
  S.PathMatches rule word directory → resolve before (append earlier (cons rule empty)) word directory ≡ not (R.negative rule)
lastMatchWins before earlier rule word directory matched = trans
  (resolveAppend before earlier (cons rule empty) word directory)
  (recognized (apply matched (end (not (R.negative rule)) word directory)))

data Unmatched : ∀ {inputs} → Rules inputs → R.Word → Bool → Set where
  none : ∀ word directory → Unmatched empty word directory
  more : ∀ {input inputs word directory} {rule : R.Compiled input} {rules : Rules inputs} →
    ¬ S.PathMatches rule word directory → Unmatched rules word directory → Unmatched (cons rule rules) word directory

unmatchedResolution : ∀ {inputs word directory} {rules : Rules inputs} → Unmatched rules word directory →
  ∀ before → Resolution before rules word directory before
unmatchedResolution (none word directory) before = end before word directory
unmatchedResolution (more absent rest) before = skip absent (unmatchedResolution rest before)

unmatchedPreserves : ∀ {inputs word directory} {rules : Rules inputs} → Unmatched rules word directory →
  ∀ before → resolve before rules word directory ≡ before
unmatchedPreserves absent before = recognized (unmatchedResolution absent before)

record FamilyRules (policy : C.FamilyPolicy) : Set where
  field exclude : Rules (map toList (C.EffectiveConfig.exclude (C.familyConfig policy)))
        vendor : Rules (map toList (C.EffectiveConfig.vendor (C.familyConfig policy)))

classify : ∀ {excludeInputs vendorInputs} → Bool → Rules excludeInputs → Rules vendorInputs → R.Word → Bool → C.Decision
classify gitDefault exclude vendor word directory =
  C.classify (resolve gitDefault exclude word directory) (resolve false vendor word directory)

familyDecision : ∀ policy → FamilyRules policy → Bool → String → Bool → C.Decision
familyDecision policy rules gitDefault path directory =
  classify gitDefault (FamilyRules.exclude rules) (FamilyRules.vendor rules) (toList path) directory

included : C.Decision → Bool
included C.Drop = false
included C.T1 = true
included C.T2 = true

inclusion : ∀ excluded vendor → included (C.classify excluded vendor) ≡ not excluded
inclusion true vendor = refl
inclusion false true = refl
inclusion false false = refl

vendorCannotUnignore : ∀ {excludeInputs firstVendorInputs secondVendorInputs} gitDefault
  (exclude : Rules excludeInputs) (first : Rules firstVendorInputs) (second : Rules secondVendorInputs) word directory →
  included (classify gitDefault exclude first word directory) ≡ included (classify gitDefault exclude second word directory)
vendorCannotUnignore gitDefault exclude first second word directory = trans
  (inclusion (resolve gitDefault exclude word directory) (resolve false first word directory))
  (sym (inclusion (resolve gitDefault exclude word directory) (resolve false second word directory)))


explicitInclusionWins : ∀ {inputs input} gitDefault (earlier : Rules inputs) (rule : R.Compiled input) word directory →
  R.negative rule ≡ true → S.PathMatches rule word directory →
  resolve gitDefault (append earlier (cons rule empty)) word directory ≡ false
explicitInclusionWins gitDefault earlier rule word directory negative matched = trans
  (lastMatchWins gitDefault earlier rule word directory matched) (cong not negative)

explicitExclusionWins : ∀ {inputs input} gitDefault (earlier : Rules inputs) (rule : R.Compiled input) word directory →
  R.negative rule ≡ false → S.PathMatches rule word directory →
  resolve gitDefault (append earlier (cons rule empty)) word directory ≡ true
explicitExclusionWins gitDefault earlier rule word directory negative matched = trans
  (lastMatchWins gitDefault earlier rule word directory matched) (cong not negative)

familyDecisionUnique : ∀ policy (first second : FamilyRules policy) gitDefault path directory →
  familyDecision policy first gitDefault path directory ≡ familyDecision policy second gitDefault path directory
familyDecisionUnique policy first second gitDefault path directory = cong₂ C.classify
  (resolveEquivalent gitDefault (FamilyRules.exclude first) (FamilyRules.exclude second) (toList path) directory)
  (resolveEquivalent false (FamilyRules.vendor first) (FamilyRules.vendor second) (toList path) directory)
