{-# OPTIONS --safe #-}
-- Raw token meanings, including explicit recursive-wildcard position context.
module Muninn.GlobTokens where

import Muninn.GlobLexing as L
import Muninn.GlobRanges as C
import Muninn.GlobMatching as G
import Muninn.FiniteClosure as F
open import Data.Char using (Char)
open import Data.Char.Properties using (_≟_)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Nat using (_<_; suc)
open import Data.Nat.Properties using (≤-refl; m≤n⇒m≤1+n)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂)

data Keyword : Set where
  escapeMark questionMark starMark bracketMark openMark closeMark commaMark : Keyword

glyph : Keyword → Char
glyph escapeMark = '\\'
glyph questionMark = '?'
glyph starMark = '*'
glyph bracketMark = '['
glyph openMark = '{'
glyph closeMark = '}'
glyph commaMark = ','

catalogue : List Keyword
catalogue = escapeMark ∷ questionMark ∷ starMark ∷ bracketMark ∷ openMark ∷ closeMark ∷ commaMark ∷ []

covered : ∀ key → key ∈ catalogue
covered escapeMark = here refl
covered questionMark = there (here refl)
covered starMark = there (there (here refl))
covered bracketMark = there (there (there (here refl)))
covered openMark = there (there (there (there (here refl))))
covered closeMark = there (there (there (there (there (here refl)))))
covered commaMark = there (there (there (there (there (there (here refl))))))

data Classified (char : Char) : Set where
  keyword : ∀ key → glyph key ≡ char → Classified char
  ordinary : (∀ key → glyph key ≢ char) → Classified char

classify : ∀ char → Classified char
classify char with F.choose (λ key → glyph key ≡ char) (λ key → glyph key ≟ char) catalogue
... | yes (key , included , same) = keyword key same
... | no absent = ordinary (λ key same → absent (key , covered key , same))

data Recursive : Bool → Bool → L.Word → G.Atom → L.Word → Set where
  directory : ∀ group rest → Recursive true group ('*' ∷ '/' ∷ rest) G.directories rest
  ending : ∀ group → Recursive true group ('*' ∷ []) G.path []
  comma : ∀ rest → Recursive true true ('*' ∷ ',' ∷ rest) G.path (',' ∷ rest)
  closing : ∀ rest → Recursive true true ('*' ∷ '}' ∷ rest) G.path ('}' ∷ rest)

RecursiveClaim : Bool → Bool → L.Word → Set
RecursiveClaim boundary group tail = Σ G.Atom (λ atom → Σ L.Word (λ suffix → Recursive boundary group tail atom suffix))

recursive? : ∀ boundary group tail → Dec (RecursiveClaim boundary group tail)
recursive? false group tail = no (λ { (_ , _ , ()) })
recursive? true group [] = no (λ { (_ , _ , ()) })
recursive? true group (char ∷ rest) with char ≟ '*'
... | no different = no (λ { (_ , _ , directory _ _) → different refl
                          ; (_ , _ , ending _) → different refl
                          ; (_ , _ , comma _) → different refl
                          ; (_ , _ , closing _) → different refl })
... | yes refl with rest
...   | [] = yes (G.path , [] , ending group)
...   | next ∷ tail with next ≟ '/'
...     | yes refl = yes (G.directories , tail , directory group tail)
...     | no notSlash with group
...       | false = no (λ { (_ , _ , directory _ _) → notSlash refl })
...       | true with next ≟ ','
...         | yes refl = yes (G.path , ',' ∷ tail , comma tail)
...         | no notComma with next ≟ '}'
...           | yes refl = yes (G.path , '}' ∷ tail , closing tail)
...           | no notClose = no (λ { (_ , _ , directory _ _) → notSlash refl
                                  ; (_ , _ , comma _) → notComma refl
                                  ; (_ , _ , closing _) → notClose refl })

recursiveDeterministic : ∀ {boundary group tail atom suffix otherAtom otherSuffix} → Recursive boundary group tail atom suffix →
  Recursive boundary group tail otherAtom otherSuffix → (atom , suffix) ≡ (otherAtom , otherSuffix)
recursiveDeterministic (directory group rest) (directory .group .rest) = refl
recursiveDeterministic (ending group) (ending .group) = refl
recursiveDeterministic (comma rest) (comma .rest) = refl
recursiveDeterministic (closing rest) (closing .rest) = refl

data Token : Set where
  atom : G.Atom → Token
  opening closingBracket separator : Token

data Source (boundary group : Bool) : L.Word → Token → L.Word → Set where
  literal : ∀ char rest → (∀ key → glyph key ≢ char) → Source boundary group (char ∷ rest) (atom (G.literal char)) rest
  escaped : ∀ char rest → Source boundary group ('\\' ∷ char ∷ rest) (atom (G.literal char)) rest
  question : ∀ rest → Source boundary group ('?' ∷ rest) (atom G.one) rest
  wildcard : ∀ rest → ¬ RecursiveClaim boundary group rest → Source boundary group ('*' ∷ rest) (atom G.star) rest
  recursive : ∀ tail atomValue suffix → Recursive boundary group tail atomValue suffix →
    Source boundary group ('*' ∷ tail) (atom atomValue) suffix
  class : ∀ {input} (result : C.Compiled input) → Source boundary group input (atom (C.atom result)) (C.suffix result)
  bracketLiteral : ∀ rest → ¬ L.Claim ('[' ∷ rest) → Source boundary group ('[' ∷ rest) (atom (G.literal '[')) rest
  openGroup : ∀ rest → Source boundary group ('{' ∷ rest) opening rest
  closeGroup : ∀ rest → Source boundary group ('}' ∷ rest) closingBracket rest
  commaToken : ∀ rest → Source boundary group (',' ∷ rest) separator rest

record Scanned (boundary group : Bool) (input : L.Word) : Set where
  constructor scanned
  field token : Token
        suffix : L.Word
        source : Source boundary group input token suffix

starValue : ∀ boundary group rest → Scanned boundary group ('*' ∷ rest)
starValue boundary group rest with recursive? boundary group rest
... | yes (atomValue , suffix , source) = scanned (atom atomValue) suffix (recursive rest atomValue suffix source)
... | no absent = scanned (atom G.star) rest (wildcard rest absent)

classValue : ∀ boundary group rest → Maybe (Scanned boundary group ('[' ∷ rest))
classValue boundary group rest with L.class? ('[' ∷ rest)
... | no absent = just (scanned (atom (G.literal '[')) rest (bracketLiteral rest absent))
... | yes exists with C.compile ('[' ∷ rest)
...   | nothing = nothing
...   | just result = just (scanned (atom (C.atom result)) (C.suffix result) (class result))

escapeValue : ∀ boundary group rest → Maybe (Scanned boundary group ('\\' ∷ rest))
escapeValue boundary group [] = nothing
escapeValue boundary group (char ∷ rest) = just (scanned (atom (G.literal char)) rest (escaped char rest))

emit : ∀ boundary group char rest → Classified char → Maybe (Scanned boundary group (char ∷ rest))
emit boundary group ._ rest (keyword escapeMark refl) = escapeValue boundary group rest
emit boundary group ._ rest (keyword questionMark refl) = just (scanned (atom G.one) rest (question rest))
emit boundary group ._ rest (keyword starMark refl) = just (starValue boundary group rest)
emit boundary group ._ rest (keyword bracketMark refl) = classValue boundary group rest
emit boundary group ._ rest (keyword openMark refl) = just (scanned opening rest (openGroup rest))
emit boundary group ._ rest (keyword closeMark refl) = just (scanned closingBracket rest (closeGroup rest))
emit boundary group ._ rest (keyword commaMark refl) = just (scanned separator rest (commaToken rest))
emit boundary group char rest (ordinary plain) = just (scanned (atom (G.literal char)) rest (literal char rest plain))

scan : ∀ boundary group input → Maybe (Scanned boundary group input)
scan boundary group [] = nothing
scan boundary group (char ∷ rest) = emit boundary group char rest (classify char)

meaning : Bool → Bool → L.Word → Maybe (Token × L.Word)
meaning boundary group input = map (λ result → Scanned.token result , Scanned.suffix result) (scan boundary group input)

classOpen : ∀ {input} (result : C.Compiled input) → Σ L.Word (λ rest → input ≡ '[' ∷ rest)
classOpen result with L.Parsed.source (C.Compiled.lexical result)
... | L.positive input units suffix allowed source = input , refl
... | L.bang input units suffix source = '!' ∷ input , refl
... | L.caret input units suffix source = '^' ∷ input , refl

recognized : ∀ {boundary group input token suffix} → Source boundary group input token suffix →
  meaning boundary group input ≡ just (token , suffix)
recognized (literal char rest plain) with classify char
... | keyword key same = ⊥-elim (plain key same)
... | ordinary actual = refl
recognized (escaped char rest) = refl
recognized (question rest) = refl
recognized {boundary} {group} (wildcard rest absent) with recursive? boundary group rest
... | yes found = ⊥-elim (absent found)
... | no actual = refl
recognized {boundary} {group} (recursive tail atomValue suffix source) with recursive? boundary group tail
... | no absent = ⊥-elim (absent (atomValue , suffix , source))
... | yes (actualAtom , actualSuffix , actual) with recursiveDeterministic actual source
...   | refl = refl
recognized {boundary} {group} (class result) with classOpen result
... | rest , refl with L.class? ('[' ∷ rest)
...   | no absent = ⊥-elim (absent (L.Parsed.negated (C.Compiled.lexical result) ,
      L.Parsed.units (C.Compiled.lexical result) , C.suffix result , L.Parsed.source (C.Compiled.lexical result)))
...   | yes lexical with C.compile ('[' ∷ rest) |
    C.classRecognized (L.Parsed.source (C.Compiled.lexical result)) (C.Parsed.source (C.Compiled.interpreted result))
...     | nothing | ()
...     | just actual | known with C.classDeterministic actual result
...       | sameAtom , sameSuffix = cong₂ (λ term suffix → just (atom term , suffix)) sameAtom sameSuffix
recognized {boundary} {group} (bracketLiteral rest absent) with L.class? ('[' ∷ rest)
... | yes found = ⊥-elim (absent found)
... | no actual = refl
recognized (openGroup rest) = refl
recognized (closeGroup rest) = refl
recognized (commaToken rest) = refl

recursiveProgress : ∀ {boundary group tail atom suffix} → Recursive boundary group tail atom suffix →
  length suffix < suc (length tail)
recursiveProgress (directory group rest) = m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl)
recursiveProgress (ending group) = m≤n⇒m≤1+n ≤-refl
recursiveProgress (comma rest) = m≤n⇒m≤1+n ≤-refl
recursiveProgress (closing rest) = m≤n⇒m≤1+n ≤-refl

progress : ∀ {boundary group input token suffix} → Source boundary group input token suffix → length suffix < length input
progress (literal char rest plain) = ≤-refl
progress (escaped char rest) = m≤n⇒m≤1+n ≤-refl
progress (question rest) = ≤-refl
progress (wildcard rest absent) = ≤-refl
progress (recursive tail atomValue suffix source) = recursiveProgress source
progress (class result) = C.progress result
progress (bracketLiteral rest absent) = ≤-refl
progress (openGroup rest) = ≤-refl
progress (closeGroup rest) = ≤-refl
progress (commaToken rest) = ≤-refl

recursiveConsumption : ∀ {boundary group tail atom suffix} → Recursive boundary group tail atom suffix →
  Σ L.Word (λ prefix → '*' ∷ tail ≡ prefix ++ suffix)
recursiveConsumption (directory group rest) = ('*' ∷ '*' ∷ '/' ∷ []) , refl
recursiveConsumption (ending group) = ('*' ∷ '*' ∷ []) , refl
recursiveConsumption (comma rest) = ('*' ∷ '*' ∷ []) , refl
recursiveConsumption (closing rest) = ('*' ∷ '*' ∷ []) , refl

consumption : ∀ {boundary group input token suffix} → Source boundary group input token suffix →
  Σ L.Word (λ prefix → input ≡ prefix ++ suffix)
consumption (literal char rest plain) = (char ∷ []) , refl
consumption (escaped char rest) = ('\\' ∷ char ∷ []) , refl
consumption (question rest) = ('?' ∷ []) , refl
consumption (wildcard rest absent) = ('*' ∷ []) , refl
consumption (recursive tail atomValue suffix source) = recursiveConsumption source
consumption (class result) = C.consumption result
consumption (bracketLiteral rest absent) = ('[' ∷ []) , refl
consumption (openGroup rest) = ('{' ∷ []) , refl
consumption (closeGroup rest) = ('}' ∷ []) , refl
consumption (commaToken rest) = (',' ∷ []) , refl

deterministic : ∀ {boundary group input token suffix otherToken otherSuffix} → Source boundary group input token suffix →
  Source boundary group input otherToken otherSuffix → (token , suffix) ≡ (otherToken , otherSuffix)
deterministic first second = just-injective (trans (sym (recognized first)) (recognized second))
