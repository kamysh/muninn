{-# OPTIONS --safe #-}
-- Root/basename scope and directory ancestry use actual compiled rule meanings.
module Muninn.RuleScope where

import Muninn.RulePatterns as R
import Muninn.GlobMatching as G
import Muninn.FiniteClosure as F
open import Data.Char using (Char)
open import Data.Char.Properties using (_≟_)
open import Data.Bool using (Bool; true; false; T)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (map′; _×-dec_; does; toWitness; isYes≗does; dec-true)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

scopedGlob : ∀ {input} → R.Compiled input → G.Glob
scopedGlob rule with R.rooted rule
... | true = R.glob rule
... | false = G.part G.directories (R.glob rule)

data ScopeMatches {input} (rule : R.Compiled input) (word : R.Word) : Set where
  atRoot : R.rooted rule ≡ true → G.Matches (R.glob rule) word → ScopeMatches rule word
  atDepth : R.rooted rule ≡ false → ∀ prefix suffix → prefix ++ suffix ≡ word →
    G.AtomMatches G.directories prefix → G.Matches (R.glob rule) suffix → ScopeMatches rule word

scopeSound : ∀ {input} (rule : R.Compiled input) word → G.Matches (scopedGlob rule) word → ScopeMatches rule word
scopeSound rule word matched with R.rooted rule in observed
... | true = atRoot observed matched
... | false with matched
...   | G.chain prefix suffix joined directories rest = atDepth observed prefix suffix joined directories rest

scopeComplete : ∀ {input word} {rule : R.Compiled input} → ScopeMatches rule word → G.Matches (scopedGlob rule) word
scopeComplete {rule = rule} (atRoot root matched) with R.rooted rule | root
... | true | refl = matched
... | false | ()
scopeComplete {rule = rule} (atDepth root prefix suffix joined directories rest) with R.rooted rule | root
... | true | ()
... | false | refl = G.chain prefix suffix joined directories rest

data DirectoryOK : Bool → Bool → Set where
  unrestricted : ∀ directory → DirectoryOK false directory
  directoryEvidence : DirectoryOK true true

directory? : ∀ restriction actual → Dec (DirectoryOK restriction actual)
directory? false actual = yes (unrestricted actual)
directory? true true = yes directoryEvidence
directory? true false = no (λ ())

Direct : ∀ {input} → R.Compiled input → R.Word → Bool → Set
Direct rule word actualDirectory = DirectoryOK (R.directoryOnly rule) actualDirectory × ScopeMatches rule word

direct? : ∀ {input} (rule : R.Compiled input) word directory → Dec (Direct rule word directory)
direct? rule word directory = map′
  (λ { (allowed , matched) → allowed , scopeSound rule word matched })
  (λ { (allowed , matched) → allowed , scopeComplete matched })
  (directory? (R.directoryOnly rule) directory ×-dec G.matches? (scopedGlob rule) word)

data Parent {input} (rule : R.Compiled input) : R.Word × R.Word → Set where
  parent : ∀ prefix rest → Direct rule prefix true → Parent rule (prefix , '/' ∷ rest)

parent? : ∀ {input} (rule : R.Compiled input) pair → Dec (Parent rule pair)
parent? rule (prefix , []) = no (λ ())
parent? rule (prefix , char ∷ rest) with char ≟ '/'
... | yes refl = map′ (parent prefix rest) (λ { (parent _ _ matched) → matched }) (direct? rule prefix true)
... | no different = no (λ { (parent _ _ _) → different refl })

data PathMatches {input} (rule : R.Compiled input) (word : R.Word) (actualDirectory : Bool) : Set where
  current : Direct rule word actualDirectory → PathMatches rule word actualDirectory
  ancestor : ∀ prefix rest → prefix ++ ('/' ∷ rest) ≡ word →
    Direct rule prefix true → PathMatches rule word actualDirectory

pathMatches? : ∀ {input} (rule : R.Compiled input) word directory → Dec (PathMatches rule word directory)
pathMatches? rule word directory with direct? rule word directory
... | yes matched = yes (current matched)
... | no notCurrent with F.choose (Parent rule) (parent? rule) (G.splits word)
...   | yes ((prefix , _) , included , parent .prefix rest matched) =
    yes (ancestor prefix rest (G.splitSound word prefix ('/' ∷ rest) included) matched)
...   | no noParent = no (λ
    { (current matched) → notCurrent matched
    ; (ancestor prefix rest joined matched) → noParent
      ((prefix , '/' ∷ rest) ,
        subst (λ value → (prefix , '/' ∷ rest) ∈ G.splits value) joined (G.splitComplete prefix ('/' ∷ rest)) ,
        parent prefix rest matched) })

matches : ∀ {input} → R.Compiled input → R.Word → Bool → Bool
matches rule word directory = does (pathMatches? rule word directory)

matchSound : ∀ {input} (rule : R.Compiled input) word directory →
  matches rule word directory ≡ true → PathMatches rule word directory
matchSound rule word directory accepted = toWitness {a? = pathMatches? rule word directory}
  (subst T (sym (trans (isYes≗does (pathMatches? rule word directory)) accepted)) tt)

matchComplete : ∀ {input} (rule : R.Compiled input) word directory →
  PathMatches rule word directory → matches rule word directory ≡ true
matchComplete rule word directory matched = dec-true (pathMatches? rule word directory) matched
