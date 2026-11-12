{-# OPTIONS --safe #-}
-- Ordered class interpretation connects source evidence to actual matcher atoms.
module Muninn.GlobRanges where

import Muninn.GlobLexing as L
import Muninn.GlobMatching as G
import Text.Regex.String as R
open import Data.Char using (Char; _≤_)
open import Data.Char.Properties using (_≟_; _≤?_)
open import Data.Bool using (Bool)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Nat using (_<_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

value : L.Unit → Char
value (L.raw char) = char
value (L.quoted char) = char

data Ahead : List L.Unit → Set where
  ahead : ∀ upper rest → Ahead (L.raw '-' ∷ upper ∷ rest)

data Ranges : List L.Unit → List R.Range → Set where
  end : Ranges [] []
  single : ∀ first rest ranges → ¬ Ahead rest → Ranges rest ranges →
    Ranges (first ∷ rest) (R.Range.[ value first ] ∷ ranges)
  interval : ∀ lower upper rest ranges → value lower ≤ value upper → Ranges rest ranges →
    Ranges (lower ∷ L.raw '-' ∷ upper ∷ rest) ((value lower R.─ value upper) ∷ ranges)

record Parsed (units : List L.Unit) : Set where
  constructor parsedRanges
  field ranges : List R.Range
        source : Ranges units ranges

addSingle : ∀ first rest → ¬ Ahead rest → Maybe (Parsed rest) → Maybe (Parsed (first ∷ rest))
addSingle first rest absent nothing = nothing
addSingle first rest absent (just (parsedRanges ranges source)) =
  just (parsedRanges (R.Range.[ value first ] ∷ ranges) (single first rest ranges absent source))

addInterval : ∀ lower upper rest → value lower ≤ value upper → Maybe (Parsed rest) →
  Maybe (Parsed (lower ∷ L.raw '-' ∷ upper ∷ rest))
addInterval lower upper rest ordered nothing = nothing
addInterval lower upper rest ordered (just (parsedRanges ranges source)) =
  just (parsedRanges ((value lower R.─ value upper) ∷ ranges) (interval lower upper rest ranges ordered source))

chooseRange : ∀ first char upper rest → Maybe (Parsed (L.raw char ∷ upper ∷ rest)) → Maybe (Parsed rest) →
  Maybe (Parsed (first ∷ L.raw char ∷ upper ∷ rest))
chooseRange first char upper rest tailResult restResult with char ≟ '-'
... | yes refl with value first ≤? value upper
...   | yes ordered = addInterval first upper rest ordered restResult
...   | no unordered = nothing
chooseRange first char upper rest tailResult restResult | no different = addSingle first (L.raw char ∷ upper ∷ rest)
  (λ { (ahead _ _) → different refl }) tailResult

parse : (units : List L.Unit) → Maybe (Parsed units)
parse [] = just (parsedRanges [] end)
parse (first ∷ []) = addSingle first [] (λ ()) (parse [])
parse (first ∷ second ∷ []) = addSingle first (second ∷ []) (λ ()) (parse (second ∷ []))
parse (first ∷ tail@(L.quoted char ∷ third ∷ rest)) = addSingle first tail (λ ()) (parse tail)
parse (first ∷ tail@(L.raw char ∷ upper ∷ rest)) = chooseRange first char upper rest (parse tail) (parse rest)

project : ∀ {units} → Maybe (Parsed units) → Maybe (List R.Range)
project nothing = nothing
project (just parsed) = just (Parsed.ranges parsed)

meaning : List L.Unit → Maybe (List R.Range)
meaning units = project (parse units)

singleProjection : ∀ first rest absent result → project (addSingle first rest absent result) ≡
  map (R.Range.[ value first ] ∷_) (project result)
singleProjection first rest absent nothing = refl
singleProjection first rest absent (just parsed) = refl

intervalProjection : ∀ lower upper rest ordered result → project (addInterval lower upper rest ordered result) ≡
  map ((value lower R.─ value upper) ∷_) (project result)
intervalProjection lower upper rest ordered nothing = refl
intervalProjection lower upper rest ordered (just parsed) = refl

singleStep : ∀ first rest → ¬ Ahead rest → meaning (first ∷ rest) ≡ map (R.Range.[ value first ] ∷_) (meaning rest)
singleStep first [] absent = refl
singleStep first (second ∷ []) absent = singleProjection first (second ∷ []) (λ ()) (parse (second ∷ []))
singleStep first tail@(L.quoted char ∷ upper ∷ rest) absent = singleProjection first tail (λ ()) (parse tail)
singleStep first tail@(L.raw char ∷ upper ∷ rest) absent with char ≟ '-'
... | yes refl = ⊥-elim (absent (ahead upper rest))
... | no different = singleProjection first tail (λ { (ahead _ _) → different refl }) (parse tail)

intervalStep : ∀ lower upper rest → value lower ≤ value upper →
  meaning (lower ∷ L.raw '-' ∷ upper ∷ rest) ≡ map ((value lower R.─ value upper) ∷_) (meaning rest)
intervalStep lower upper rest ordered with value lower ≤? value upper
... | yes verified = intervalProjection lower upper rest verified (parse rest)
... | no unordered = ⊥-elim (unordered ordered)

recognized : ∀ {units ranges} → Ranges units ranges → meaning units ≡ just ranges
recognized end = refl
recognized (single first rest ranges absent source) = trans (singleStep first rest absent)
  (cong (map (R.Range.[ value first ] ∷_)) (recognized source))
recognized (interval lower upper rest ranges ordered source) = trans (intervalStep lower upper rest ordered)
  (cong (map ((value lower R.─ value upper) ∷_)) (recognized source))

deterministic : ∀ {units first second} → Ranges units first → Ranges units second → first ≡ second
deterministic first second = just-injective (trans (sym (recognized first)) (recognized second))

record Compiled (input : L.Word) : Set where
  constructor compiled
  field lexical : L.Parsed input
        interpreted : Parsed (L.Parsed.units lexical)

atom : ∀ {input} → Compiled input → G.Atom
atom result = G.characterClass (L.Parsed.negated (Compiled.lexical result)) (Parsed.ranges (Compiled.interpreted result))

suffix : ∀ {input} → Compiled input → L.Word
suffix result = L.Parsed.suffix (Compiled.lexical result)

fromLexeme : ∀ input → Maybe (L.Parsed input) → Maybe (Compiled input)
fromLexeme input nothing = nothing
fromLexeme input (just lexical) with parse (L.Parsed.units lexical)
... | nothing = nothing
... | just interpreted = just (compiled lexical interpreted)

compile : (input : L.Word) → Maybe (Compiled input)
compile input = fromLexeme input (L.classValue input)

classMeaning : L.Word → Maybe (Bool × List R.Range × L.Word)
classMeaning input = map (λ result → L.Parsed.negated (Compiled.lexical result) ,
  Parsed.ranges (Compiled.interpreted result) , suffix result) (compile input)

classRecognized : ∀ {input negated units rest ranges} → L.Class input negated units rest → Ranges units ranges →
  classMeaning input ≡ just (negated , ranges , rest)
classRecognized {input} {negated} {units} {rest} {ranges} lexical interpreted
  with L.classValue input | L.classRecognized lexical
... | nothing | ()
... | just (L.parsed storedNegated storedUnits storedRest source) | same with just-injective same
...   | refl with parse units | recognized interpreted
...     | nothing | ()
...     | just (parsedRanges actualRanges rangeSource) | equal with just-injective equal
...       | refl = refl

classDeterministic : ∀ {input} (first second : Compiled input) → atom first ≡ atom second × suffix first ≡ suffix second
classDeterministic first second =
  cong (λ meaning → G.characterClass (proj₁ meaning) (proj₁ (proj₂ meaning))) same ,
  cong (λ meaning → proj₂ (proj₂ meaning)) same
  where
  same = just-injective (trans
    (sym (classRecognized (L.Parsed.source (Compiled.lexical first)) (Parsed.source (Compiled.interpreted first))))
    (classRecognized (L.Parsed.source (Compiled.lexical second)) (Parsed.source (Compiled.interpreted second))))

matches? : ∀ {input} (result : Compiled input) word → Dec (G.AtomMatches (atom result) word)
matches? result word = G.atomMatches? (atom result) word

consumption : ∀ {input} (result : Compiled input) → Σ L.Word (λ prefix → input ≡ prefix ++ suffix result)
consumption result = L.classConsumption (L.Parsed.source (Compiled.lexical result))

progress : ∀ {input} (result : Compiled input) → length (suffix result) < length input
progress result = L.classSuffixSmaller (L.Parsed.source (Compiled.lexical result))
