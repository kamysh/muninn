{-# OPTIONS --safe #-}
-- Connect complete strict entry admission to the ordered family resolver.
module Muninn.AdmittedSelection where

import Muninn.PolicyRuleAdmission as A
import Muninn.OrderedSelection as O
import Muninn.Config as C
import Muninn.RulePatterns as R
open import Data.List using (List; []; _∷_; map)
open import Data.String using (String; toList)
open import Data.Bool using (Bool)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

compiledRules : ∀ {inputs} → A.Entries inputs → O.Rules (map A.normalize inputs)
compiledRules A.none = O.empty
compiledRules (A.more entry rest) = O.cons (A.Entry.compiled entry) (compiledRules rest)

record FamilyEntries (policy : C.FamilyPolicy) : Set where
  field exclude : A.Entries (map toList (C.EffectiveConfig.exclude (C.familyConfig policy)))
        vendor : A.Entries (map toList (C.EffectiveConfig.vendor (C.familyConfig policy)))

compiledStrings : ∀ texts → A.Entries (map toList texts) → O.Rules (map (λ text → A.normalize (toList text)) texts)
compiledStrings [] A.none = O.empty
compiledStrings (text ∷ rest) (A.more entry entries) = O.cons (A.Entry.compiled entry) (compiledStrings rest entries)

compiledFamily : ∀ policy → FamilyEntries policy → O.FamilyRules policy
compiledFamily policy entries = record
  { exclude = compiledStrings _ (FamilyEntries.exclude entries)
  ; vendor = compiledStrings _ (FamilyEntries.vendor entries) }

admitFamily : ∀ policy → Maybe (FamilyEntries policy)
admitFamily policy with A.admitAll (map toList (C.EffectiveConfig.exclude (C.familyConfig policy)))
... | nothing = nothing
... | just exclude with A.admitAll (map toList (C.EffectiveConfig.vendor (C.familyConfig policy)))
...   | nothing = nothing
...   | just vendor = just record { exclude = exclude; vendor = vendor }

familyComplete : ∀ policy → FamilyEntries policy → Σ (FamilyEntries policy) (λ actual → admitFamily policy ≡ just actual)
familyComplete policy entries with A.admitAllComplete (FamilyEntries.exclude entries)
... | exclude , knownExclude rewrite knownExclude with A.admitAllComplete (FamilyEntries.vendor entries)
...   | vendor , knownVendor rewrite knownVendor = record { exclude = exclude; vendor = vendor } , refl

classify : ∀ policy → FamilyEntries policy → Bool → String → Bool → C.Decision
classify policy entries gitDefault path directory = O.familyDecision policy (compiledFamily policy entries) gitDefault path directory

unique : ∀ policy (first second : FamilyEntries policy) gitDefault path directory →
  classify policy first gitDefault path directory ≡ classify policy second gitDefault path directory
unique policy first second gitDefault path directory = O.familyDecisionUnique policy
  (compiledFamily policy first) (compiledFamily policy second) gitDefault path directory
