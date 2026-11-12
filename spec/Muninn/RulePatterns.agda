{-# OPTIONS --safe #-}
-- Source-certified negation, root and directory framing around actual bodies.
module Muninn.RulePatterns where

import Muninn.GlobBody as B
import Muninn.GlobMatching as G
open import Data.Char using (Char)
open import Data.Char.Properties using (_≟_)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.List using (List; []; _∷_; reverse)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)

Word : Set
Word = G.Word

data Peel (marker : Char) : Word → Bool → Word → Set where
  empty : Peel marker [] false []
  taken : ∀ rest → Peel marker (marker ∷ rest) true rest
  kept : ∀ first rest → marker ≢ first → Peel marker (first ∷ rest) false (first ∷ rest)

record Peeled (marker : Char) (input : Word) : Set where
  constructor peeled
  field present : Bool
        rest : Word
        source : Peel marker input present rest

peel : ∀ marker input → Peeled marker input
peel marker [] = peeled false [] empty
peel marker (first ∷ rest) with marker ≟ first
... | yes refl = peeled true rest (taken rest)
... | no different = peeled false (first ∷ rest) (kept first rest different)

peelMeaning : ∀ {marker input} → Peeled marker input → Bool × Word
peelMeaning result = Peeled.present result , Peeled.rest result

peelRecognized : ∀ {marker input present rest} → Peel marker input present rest →
  peelMeaning (peel marker input) ≡ (present , rest)
peelRecognized empty = refl
peelRecognized {marker} (taken rest) with marker ≟ marker
... | yes refl = refl
... | no different = ⊥-elim (different refl)
peelRecognized {marker} (kept first rest different) with marker ≟ first
... | yes same = ⊥-elim (different same)
... | no actual = refl

data HeaderSource (input : Word) : Bool → Bool → Bool → Word → Set where
  framed : ∀ {negated rooted directory front content backwards} →
    Peel '!' input negated front → Peel '/' front rooted content →
    Peel '/' (reverse content) directory backwards →
    HeaderSource input negated rooted directory (reverse backwards)

record Header (input : Word) : Set where
  constructor header
  field negated rooted directory : Bool
        body : Word
        source : HeaderSource input negated rooted directory body

scanHeader : ∀ input → Header input
scanHeader input with peel '!' input
... | peeled negated front negation with peel '/' front
...   | peeled rooted content root with peel '/' (reverse content)
...     | peeled directory backwards ending = header negated rooted directory (reverse backwards)
    (framed negation root ending)

headerMeaning : ∀ {input} → Header input → Bool × Bool × Bool × Word
headerMeaning result = Header.negated result , Header.rooted result , Header.directory result , Header.body result

headerRecognized : ∀ {input negated rooted directory body} → HeaderSource input negated rooted directory body →
  headerMeaning (scanHeader input) ≡ (negated , rooted , directory , body)
headerRecognized {input} (framed negation root ending) with peel '!' input | peelRecognized negation
... | peeled negated front actualNegation | same with same
...   | refl with peel '/' front | peelRecognized root
...     | peeled rooted content actualRoot | same with same
...       | refl with peel '/' (reverse content) | peelRecognized ending
...         | peeled directory backwards actualEnding | same with same
...           | refl = refl

containsSlash : Word → Bool
containsSlash [] = false
containsSlash (char ∷ rest) with char ≟ '/'
... | yes refl = true
... | no different = containsSlash rest

data Nonempty : Word → Set where
  nonempty : ∀ first rest → Nonempty (first ∷ rest)

record Compiled (input : Word) : Set where
  constructor compiled
  field headerInfo : Header input
        bodyPresent : Nonempty (Header.body headerInfo)
        bodyInfo : B.Parsed (Header.body headerInfo) B.initial

negative : ∀ {input} → Compiled input → Bool
negative result = Header.negated (Compiled.headerInfo result)

rooted : ∀ {input} → Compiled input → Bool
rooted result = Header.rooted (Compiled.headerInfo result) ∨ containsSlash (Header.body (Compiled.headerInfo result))

directoryOnly : ∀ {input} → Compiled input → Bool
directoryOnly result = Header.directory (Compiled.headerInfo result)

glob : ∀ {input} → Compiled input → G.Glob
glob result = B.Parsed.result (Compiled.bodyInfo result)

withBody : ∀ {input} (info : Header input) → Nonempty (Header.body info) →
  Maybe (B.Parsed (Header.body info) B.initial) → Maybe (Compiled input)
withBody info present nothing = nothing
withBody info present (just body) = just (compiled info present body)

compileHeader : ∀ {input} → Header input → Maybe (Compiled input)
compileHeader (header negated root directory [] source) = nothing
compileHeader info@(header negated root directory (first ∷ rest) source) =
  withBody info (nonempty first rest) (B.parse (first ∷ rest))

compile : ∀ input → Maybe (Compiled input)
compile input = compileHeader (scanHeader input)

Semantic : Set
Semantic = Bool × Bool × Bool × G.Glob

semantic : ∀ {input} → Compiled input → Semantic
semantic result = negative result , rooted result , directoryOnly result , glob result

meaning : Word → Maybe Semantic
meaning input = map semantic (compile input)

fromHeaderMeaning : ∀ {input negated root directory body result} (info : Header input) →
  headerMeaning info ≡ (negated , root , directory , body) → Nonempty body →
  B.Source body B.initial result → map semantic (compileHeader info) ≡
  just (negated , root ∨ containsSlash body , directory , result)
fromHeaderMeaning (header negated root directory body actualSource) refl (nonempty first rest) bodySource
  with B.parse (first ∷ rest) | B.recognized bodySource
... | nothing | ()
... | just actual | same with just-injective same
...   | refl = refl

recognized : ∀ {input negated root directory body result} → HeaderSource input negated root directory body →
  Nonempty body → B.Source body B.initial result →
  meaning input ≡ just (negated , root ∨ containsSlash body , directory , result)
recognized {input} framing present bodySource =
  fromHeaderMeaning (scanHeader input) (headerRecognized framing) present bodySource

deterministic : ∀ {input} (first second : Compiled input) → semantic first ≡ semantic second
deterministic first second = just-injective (trans
  (sym (recognized (Header.source (Compiled.headerInfo first)) (Compiled.bodyPresent first) (B.Parsed.source (Compiled.bodyInfo first))))
  (recognized (Header.source (Compiled.headerInfo second)) (Compiled.bodyPresent second) (B.Parsed.source (Compiled.bodyInfo second))))
