{-# OPTIONS --safe #-}
-- Conservative prefix pruning cannot hide an explicitly re-included descendant.
module Muninn.InclusionTraversal where

import Muninn.GlobMatching as G
import Muninn.RulePatterns as R
import Muninn.RuleScope as S
import Muninn.OrderedSelection as O
open import Data.Char.Properties using (_≟_)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no; does)
open import Relation.Nullary.Decidable using (_⊎-dec_; dec-true)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

data Prefix : R.Word → R.Word → Set where
  emptyPrefix : ∀ {word} → Prefix [] word
  next : ∀ {char first second} → Prefix first second → Prefix (char ∷ first) (char ∷ second)

prefix? : ∀ first second → Dec (Prefix first second)
prefix? [] second = yes emptyPrefix
prefix? (_ ∷ _) [] = no (λ ())
prefix? (char ∷ first) (other ∷ second) with char ≟ other
... | no different = no (λ { (next prefix) → different refl })
... | yes refl with prefix? first second
...   | yes prefix = yes (next prefix)
...   | no absent = no (λ { (next prefix) → absent prefix })

prefixTrans : ∀ {first middle last} → Prefix first middle → Prefix middle last → Prefix first last
prefixTrans emptyPrefix second = emptyPrefix
prefixTrans (next first) (next second) = next (prefixTrans first second)

prefixAppend : ∀ first second → Prefix first (first ++ second)
prefixAppend [] second = emptyPrefix
prefixAppend (char ∷ first) second = next (prefixAppend first second)

commonComparable : ∀ {first second word} → Prefix first word → Prefix second word → Prefix first second ⊎ Prefix second first
commonComparable emptyPrefix second = inj₁ emptyPrefix
commonComparable (next first) emptyPrefix = inj₂ emptyPrefix
commonComparable (next first) (next second) with commonComparable first second
... | inj₁ prefix = inj₁ (next prefix)
... | inj₂ prefix = inj₂ (next prefix)

literalPrefix : G.Glob → R.Word
literalPrefix G.done = []
literalPrefix (G.part (G.literal char) rest) = char ∷ literalPrefix rest
literalPrefix (G.part G.one rest) = []
literalPrefix (G.part G.star rest) = []
literalPrefix (G.part G.path rest) = []
literalPrefix (G.part G.directories rest) = []
literalPrefix (G.part (G.characterClass negated ranges) rest) = []
literalPrefix (G.part (G.alternatives choices) rest) = []

literalLaw : ∀ {glob word} → G.Matches glob word → Prefix (literalPrefix glob) word
literalLaw {G.done} matched = emptyPrefix
literalLaw {G.part (G.literal char) rest} (G.chain .(char ∷ []) suffix joined (G.literalMatch .char) remaining) =
  subst (Prefix (char ∷ literalPrefix rest)) joined (next (literalLaw remaining))
literalLaw {G.part G.one rest} matched = emptyPrefix
literalLaw {G.part G.star rest} matched = emptyPrefix
literalLaw {G.part G.path rest} matched = emptyPrefix
literalLaw {G.part G.directories rest} matched = emptyPrefix
literalLaw {G.part (G.characterClass negated ranges) rest} matched = emptyPrefix
literalLaw {G.part (G.alternatives choices) rest} matched = emptyPrefix

hint : ∀ {input} → R.Compiled input → R.Word
hint rule with R.rooted rule
... | true = literalPrefix (R.glob rule)
... | false = []

scopeHint : ∀ {input word} {rule : R.Compiled input} → S.ScopeMatches rule word → Prefix (hint rule) word
scopeHint {rule = rule} (S.atRoot root matched) with R.rooted rule | root
... | true | refl = literalLaw matched
... | false | ()
scopeHint {rule = rule} (S.atDepth root prefix suffix joined directories matched) with R.rooted rule | root
... | true | ()
... | false | refl = emptyPrefix

pathHint : ∀ {input word directory} {rule : R.Compiled input} → S.PathMatches rule word directory → Prefix (hint rule) word
pathHint (S.current (allowed , matched)) = scopeHint matched
pathHint (S.ancestor prefix rest joined (allowed , matched)) = prefixTrans (scopeHint matched)
  (subst (Prefix prefix) joined (prefixAppend prefix ('/' ∷ rest)))

Comparable : R.Word → R.Word → Set
Comparable first second = Prefix first second ⊎ Prefix second first

comparable? : ∀ first second → Dec (Comparable first second)
comparable? first second = prefix? first second ⊎-dec prefix? second first

potential : ∀ {input} → R.Compiled input → R.Word → Bool
potential rule directory = does (comparable? (directory ++ ('/' ∷ [])) (hint rule))

potentialComplete : ∀ {input word actualDirectory} (rule : R.Compiled input) directory →
  Prefix (directory ++ ('/' ∷ [])) word → S.PathMatches rule word actualDirectory → potential rule directory ≡ true
potentialComplete rule directory ancestorPrefix matched =
  dec-true (comparable? (directory ++ ('/' ∷ [])) (hint rule)) (commonComparable ancestorPrefix (pathHint matched))

needsTraversal : ∀ {inputs} → O.Rules inputs → R.Word → Bool
needsTraversal O.empty directory = false
needsTraversal (O.cons rule rest) directory with R.negative rule ∧ potential rule directory
... | true = true
... | false = needsTraversal rest directory

data Override : ∀ {inputs} → O.Rules inputs → R.Word → Bool → Set where
  here : ∀ {input inputs word directory} {rule : R.Compiled input} {rest : O.Rules inputs} →
    R.negative rule ≡ true → S.PathMatches rule word directory → Override (O.cons rule rest) word directory
  later : ∀ {input inputs word directory} {rule : R.Compiled input} {rest : O.Rules inputs} →
    Override rest word directory → Override (O.cons rule rest) word directory

findOverride : ∀ {inputs} (rules : O.Rules inputs) word directory →
  O.resolve true rules word directory ≡ false → Override rules word directory
findOverride O.empty word directory ()
findOverride (O.cons rule rest) word directory kept with S.pathMatches? rule word directory
... | no absent = later (findOverride rest word directory kept)
... | yes matched with R.negative rule in negative
...   | true = here negative matched
...   | false = later (findOverride rest word directory kept)

witnessTraversal : ∀ {inputs word actualDirectory} {rules : O.Rules inputs} → Override rules word actualDirectory →
  ∀ directory → Prefix (directory ++ ('/' ∷ [])) word → needsTraversal rules directory ≡ true
witnessTraversal (here {rule = rule} negative matched) directory ancestorPrefix
  rewrite negative | potentialComplete rule directory ancestorPrefix matched = refl
witnessTraversal (later {rule = rule} witness) directory ancestorPrefix
  with R.negative rule ∧ potential rule directory
... | true = refl
... | false = witnessTraversal witness directory ancestorPrefix

-- The checkout root is always enumerated. Git-ignored directories are retained
-- exactly when an inclusion rule may need something beneath their prefix.
descend : ∀ {inputs} → Bool → O.Rules inputs → R.Word → Bool
descend ignored rules [] = true
descend false rules (_ ∷ _) = true
descend true rules directory@(_ ∷ _) = needsTraversal rules directory

reachesIncluded : ∀ {inputs word actualDirectory} (rules : O.Rules inputs) directory →
  Prefix (directory ++ ('/' ∷ [])) word → O.resolve true rules word actualDirectory ≡ false →
  descend true rules directory ≡ true
reachesIncluded rules [] ancestorPrefix kept = refl
reachesIncluded rules directory@(_ ∷ _) ancestorPrefix kept = witnessTraversal (findOverride rules _ _ kept) directory ancestorPrefix
