{-# OPTIONS --safe #-}
-- Certified source consumption for escaped units and bracketed classes.
module Muninn.GlobLexing where

open import Data.Char using (Char)
open import Data.Char.Properties using (_≟_)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (_<_)
open import Data.Nat.Properties using (≤-refl; m≤n⇒m≤1+n)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)

Word = List Char

data Unit : Set where
  raw quoted : Char → Unit

render : List Unit → Word
render [] = []
render (raw char ∷ units) = char ∷ render units
render (quoted char ∷ units) = '\\' ∷ char ∷ render units

Allowed : Bool → Char → Set
Allowed first char = char ≢ '\\' × (char ≢ ']' ⊎ first ≡ true)

-- ']' is literal only as the first unit; an escape always consumes two chars.
data Units : Bool → Word → List Unit → Word → Set where
  close : ∀ suffix → Units false (']' ∷ suffix) [] suffix
  plain : ∀ first char input units suffix → Allowed first char → Units false input units suffix →
    Units first (char ∷ input) (raw char ∷ units) suffix
  escape : ∀ first char input units suffix → Units false input units suffix →
    Units first ('\\' ∷ char ∷ input) (quoted char ∷ units) suffix

record Scanned (first : Bool) (input : Word) : Set where
  constructor scanned
  field units : List Unit
        suffix : Word
        source : Units first input units suffix

addPlain : ∀ first char input → Allowed first char → Maybe (Scanned false input) → Maybe (Scanned first (char ∷ input))
addPlain first char input allowed nothing = nothing
addPlain first char input allowed (just (scanned units suffix source)) =
  just (scanned (raw char ∷ units) suffix (plain first char input units suffix allowed source))

addEscape : ∀ first char input → Maybe (Scanned false input) → Maybe (Scanned first ('\\' ∷ char ∷ input))
addEscape first char input nothing = nothing
addEscape first char input (just (scanned units suffix source)) =
  just (scanned (quoted char ∷ units) suffix (escape first char input units suffix source))

scan : ∀ first input → Maybe (Scanned first input)
scan first [] = nothing
scan first (char ∷ input) with char ≟ '\\'
... | yes refl with input
...   | [] = nothing
...   | quotedChar ∷ rest = addEscape first quotedChar rest (scan false rest)
scan first (char ∷ input) | no notEscape with char ≟ ']'
... | yes refl with first
...   | false = just (scanned [] input (close input))
...   | true = addPlain true ']' input (notEscape , inj₂ refl) (scan false input)
scan first (char ∷ input) | no notEscape | no notClose =
  addPlain first char input (notEscape , inj₁ notClose) (scan false input)

project : ∀ {first input} → Maybe (Scanned first input) → Maybe (List Unit × Word)
project nothing = nothing
project (just result) = just (Scanned.units result , Scanned.suffix result)

meaning : Bool → Word → Maybe (List Unit × Word)
meaning first input = project (scan first input)

plainMeaning : ∀ first char input allowed result → project (addPlain first char input allowed result) ≡
  map (λ pair → raw char ∷ proj₁ pair , proj₂ pair) (project result)
plainMeaning first char input allowed nothing = refl
plainMeaning first char input allowed (just result) = refl

escapeMeaning : ∀ first char input result → project (addEscape first char input result) ≡
  map (λ pair → quoted char ∷ proj₁ pair , proj₂ pair) (project result)
escapeMeaning first char input nothing = refl
escapeMeaning first char input (just result) = refl

plainStep : ∀ first char input → Allowed first char → meaning first (char ∷ input) ≡
  map (λ pair → raw char ∷ proj₁ pair , proj₂ pair) (meaning false input)
plainStep first char input (notEscape , allowed) with char ≟ '\\'
... | yes refl = ⊥-elim (notEscape refl)
... | no different with char ≟ ']'
...   | yes refl with allowed
...     | inj₁ notClose = ⊥-elim (notClose refl)
...     | inj₂ refl = plainMeaning true ']' input (different , inj₂ refl) (scan false input)
plainStep first char input (notEscape , allowed) | no different | no notClose =
  plainMeaning first char input (different , inj₁ notClose) (scan false input)

escapeStep : ∀ first char input → meaning first ('\\' ∷ char ∷ input) ≡
  map (λ pair → quoted char ∷ proj₁ pair , proj₂ pair) (meaning false input)
escapeStep first char input = escapeMeaning first char input (scan false input)

recognized : ∀ {first input units suffix} → Units first input units suffix → meaning first input ≡ just (units , suffix)
recognized (close suffix) = refl
recognized (plain first char input units suffix allowed source) = trans (plainStep first char input allowed)
  (cong (map (λ pair → raw char ∷ proj₁ pair , proj₂ pair)) (recognized source))
recognized (escape first char input units suffix source) = trans (escapeStep first char input)
  (cong (map (λ pair → quoted char ∷ proj₁ pair , proj₂ pair)) (recognized source))

deterministic : ∀ {first input units suffix otherUnits otherSuffix} → Units first input units suffix →
  Units first input otherUnits otherSuffix → (units , suffix) ≡ (otherUnits , otherSuffix)
deterministic first second = just-injective (trans (sym (recognized first)) (recognized second))

consumption : ∀ {first input units suffix} → Units first input units suffix → input ≡ render units ++ (']' ∷ suffix)
consumption (close suffix) = refl
consumption (plain first char input units suffix allowed source) = cong (char ∷_) (consumption source)
consumption (escape first char input units suffix source) = cong ('\\' ∷_) (cong (char ∷_) (consumption source))

suffixSmaller : ∀ {first input units suffix} → Units first input units suffix → length suffix < length input
suffixSmaller (close suffix) = ≤-refl
suffixSmaller (plain first char input units suffix allowed source) = m≤n⇒m≤1+n (suffixSmaller source)
suffixSmaller (escape first char input units suffix source) = m≤n⇒m≤1+n (m≤n⇒m≤1+n (suffixSmaller source))

Positive : Word → Set
Positive [] = ⊤
Positive (char ∷ input) = char ≢ '!' × char ≢ '^'

data Class : Word → Bool → List Unit → Word → Set where
  positive : ∀ input units suffix → Positive input → Units true input units suffix →
    Class ('[' ∷ input) false units suffix
  bang : ∀ input units suffix → Units true input units suffix → Class ('[' ∷ '!' ∷ input) true units suffix
  caret : ∀ input units suffix → Units true input units suffix → Class ('[' ∷ '^' ∷ input) true units suffix

record Parsed (input : Word) : Set where
  constructor parsed
  field negated : Bool
        units : List Unit
        suffix : Word
        source : Class input negated units suffix

positiveValue : ∀ input → Positive input → Maybe (Scanned true input) → Maybe (Parsed ('[' ∷ input))
positiveValue input allowed nothing = nothing
positiveValue input allowed (just (scanned units suffix source)) = just (parsed false units suffix (positive input units suffix allowed source))

bangValue : ∀ input → Maybe (Scanned true input) → Maybe (Parsed ('[' ∷ '!' ∷ input))
bangValue input nothing = nothing
bangValue input (just (scanned units suffix source)) = just (parsed true units suffix (bang input units suffix source))

caretValue : ∀ input → Maybe (Scanned true input) → Maybe (Parsed ('[' ∷ '^' ∷ input))
caretValue input nothing = nothing
caretValue input (just (scanned units suffix source)) = just (parsed true units suffix (caret input units suffix source))

body : ∀ input → Maybe (Parsed ('[' ∷ input))
body [] = nothing
body (char ∷ input) with char ≟ '!'
... | yes refl = bangValue input (scan true input)
... | no notBang with char ≟ '^'
...   | yes refl = caretValue input (scan true input)
...   | no notCaret = positiveValue (char ∷ input) (notBang , notCaret) (scan true (char ∷ input))

classValue : ∀ input → Maybe (Parsed input)
classValue [] = nothing
classValue (char ∷ input) with char ≟ '['
... | yes refl = body input
... | no notOpen = nothing

classMeaning : Word → Maybe (Bool × List Unit × Word)
classMeaning input = map (λ result → Parsed.negated result , Parsed.units result , Parsed.suffix result) (classValue input)

tag : Bool → List Unit × Word → Bool × List Unit × Word
tag negated pair = negated , proj₁ pair , proj₂ pair

positiveProjection : ∀ input allowed result →
  map (λ parsed → Parsed.negated parsed , Parsed.units parsed , Parsed.suffix parsed) (positiveValue input allowed result) ≡
    map (tag false) (project result)
positiveProjection input allowed nothing = refl
positiveProjection input allowed (just result) = refl

bangProjection : ∀ input result →
  map (λ parsed → Parsed.negated parsed , Parsed.units parsed , Parsed.suffix parsed) (bangValue input result) ≡
    map (tag true) (project result)
bangProjection input nothing = refl
bangProjection input (just result) = refl

caretProjection : ∀ input result →
  map (λ parsed → Parsed.negated parsed , Parsed.units parsed , Parsed.suffix parsed) (caretValue input result) ≡
    map (tag true) (project result)
caretProjection input nothing = refl
caretProjection input (just result) = refl

positiveClassStep : ∀ char input → Positive (char ∷ input) →
  classMeaning ('[' ∷ char ∷ input) ≡ map (tag false) (meaning true (char ∷ input))
positiveClassStep char input (notBang , notCaret) with char ≟ '!'
... | yes refl = ⊥-elim (notBang refl)
... | no different with char ≟ '^'
...   | yes refl = ⊥-elim (notCaret refl)
...   | no distinct = positiveProjection (char ∷ input) (different , distinct) (scan true (char ∷ input))

bangClassStep : ∀ input → classMeaning ('[' ∷ '!' ∷ input) ≡ map (tag true) (meaning true input)
bangClassStep input = bangProjection input (scan true input)

caretClassStep : ∀ input → classMeaning ('[' ∷ '^' ∷ input) ≡ map (tag true) (meaning true input)
caretClassStep input = caretProjection input (scan true input)

classRecognized : ∀ {input negated units suffix} → Class input negated units suffix →
  classMeaning input ≡ just (negated , units , suffix)
classRecognized (positive [] units suffix allowed ())
classRecognized (positive (char ∷ input) units suffix allowed source) = trans (positiveClassStep char input allowed)
  (cong (map (tag false)) (recognized source))
classRecognized (bang input units suffix source) = trans (bangClassStep input) (cong (map (tag true)) (recognized source))
classRecognized (caret input units suffix source) = trans (caretClassStep input) (cong (map (tag true)) (recognized source))

classDeterministic : ∀ {input negated units suffix otherNegated otherUnits otherSuffix} → Class input negated units suffix →
  Class input otherNegated otherUnits otherSuffix → (negated , units , suffix) ≡ (otherNegated , otherUnits , otherSuffix)
classDeterministic first second = just-injective (trans (sym (classRecognized first)) (classRecognized second))

closedPrefix : ∀ units suffix → render units ++ (']' ∷ suffix) ≡ (render units ++ (']' ∷ [])) ++ suffix
closedPrefix units suffix = sym (++-assoc (render units) (']' ∷ []) suffix)

classConsumption : ∀ {input negated units suffix} → Class input negated units suffix → Σ Word (λ prefix → input ≡ prefix ++ suffix)
classConsumption (positive input units suffix allowed source) = ('[' ∷ render units ++ (']' ∷ [])) ,
  cong ('[' ∷_) (trans (consumption source) (closedPrefix units suffix))
classConsumption (bang input units suffix source) = ('[' ∷ '!' ∷ render units ++ (']' ∷ [])) ,
  cong (λ rest → '[' ∷ '!' ∷ rest) (trans (consumption source) (closedPrefix units suffix))
classConsumption (caret input units suffix source) = ('[' ∷ '^' ∷ render units ++ (']' ∷ [])) ,
  cong (λ rest → '[' ∷ '^' ∷ rest) (trans (consumption source) (closedPrefix units suffix))

classSuffixSmaller : ∀ {input negated units suffix} → Class input negated units suffix → length suffix < length input
classSuffixSmaller (positive input units suffix allowed source) = m≤n⇒m≤1+n (suffixSmaller source)
classSuffixSmaller (bang input units suffix source) = m≤n⇒m≤1+n (m≤n⇒m≤1+n (suffixSmaller source))
classSuffixSmaller (caret input units suffix source) = m≤n⇒m≤1+n (m≤n⇒m≤1+n (suffixSmaller source))

Claim : Word → Set
Claim input = Σ Bool (λ negated → Σ (List Unit) (λ units → Σ Word (λ suffix → Class input negated units suffix)))

classAbsent : ∀ input → classValue input ≡ nothing → ¬ Claim input
classAbsent input missing (negated , units , suffix , source) = impossible
  (trans (sym (cong (map (λ result → Parsed.negated result , Parsed.units result , Parsed.suffix result)) missing))
    (classRecognized source))
  where
  impossible : nothing ≡ just (negated , units , suffix) → Data.Empty.⊥
  impossible ()

class? : ∀ input → Dec (Claim input)
class? input with classValue input in observed
... | nothing = no (classAbsent input observed)
... | just (parsed negated units suffix source) = yes (negated , units , suffix , source)
