{-# OPTIONS --safe #-}
-- Independent glob languages and total matching over finite path splits.
module Muninn.GlobMatching where

import Muninn.FiniteClosure as Finite
import Text.Regex.String as R
open import Data.Char using (Char)
open import Data.Char.Properties using (_≟_)
open import Data.Bool using (Bool; true; false; T)
open import Data.Nat using (suc)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.List.Properties using (length-map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.All as All
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (map′; _×-dec_; does; toWitness; isYes≗does; dec-true)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans; sym; subst)

Word : Set
Word = List Char

NoSlash : Word → Set
NoSlash = All.All (_≢ '/')

noSlash? : ∀ word → Dec (NoSlash word)
noSlash? = All.all? (λ char → Relation.Nullary.Decidable.¬? (char ≟ '/'))

prepend : Char → Word × Word → Word × Word
prepend char (first , second) = char ∷ first , second

splits : Word → List (Word × Word)
splits [] = ([] , []) ∷ []
splits (char ∷ rest) = ([] , char ∷ rest) ∷ map (prepend char) (splits rest)

splitSound : ∀ word first second → (first , second) ∈ splits word → first ++ second ≡ word
splitSound [] .[] .[] (here refl) = refl
splitSound [] first second (there ())
splitSound (char ∷ rest) .[] .(char ∷ rest) (here refl) = refl
splitSound (char ∷ rest) first second (there present) with ∈-map⁻ (prepend char) present
... | (prefix , suffix) , included , refl = cong (char ∷_) (splitSound rest prefix suffix included)

splitComplete : ∀ first second → (first , second) ∈ splits (first ++ second)
splitComplete [] [] = here refl
splitComplete [] (char ∷ second) = here refl
splitComplete (char ∷ first) second = there (∈-map⁺ (prepend char) (splitComplete first second))

splitCount : ∀ word → length (splits word) ≡ suc (length word)
splitCount [] = refl
splitCount (char ∷ rest) = cong suc (trans (length-map (prepend char) (splits rest)) (splitCount rest))

-- Directory-prefix globstars consume either nothing or a prefix ending in '/'.
-- Repository-path normalization is a separate outer contract.
data EndsSlash : Word → Set where
  last : EndsSlash ('/' ∷ [])
  earlier : ∀ char rest → EndsSlash rest → EndsSlash (char ∷ rest)

endsSlash? : ∀ word → Dec (EndsSlash word)
endsSlash? [] = no (λ ())
endsSlash? (char ∷ []) with char ≟ '/'
... | yes refl = yes last
... | no different = no (λ { last → different refl; (earlier _ _ ()) })
endsSlash? (char ∷ next ∷ rest) with endsSlash? (next ∷ rest)
... | yes found = yes (earlier char (next ∷ rest) found)
... | no absent = no (λ { (earlier _ _ found) → absent found })

mutual
  data Glob : Set where
    done : Glob
    part : Atom → Glob → Glob

  data Atom : Set where
    literal : Char → Atom
    one star path directories : Atom
    characterClass : Bool → List R.Range → Atom -- true negates the class
    alternatives : List Glob → Atom

mutual
  data Matches : Glob → Word → Set where
    empty : Matches done []
    chain : ∀ {atom rest word} first second → first ++ second ≡ word →
      AtomMatches atom first → Matches rest second → Matches (part atom rest) word

  data AtomMatches : Atom → Word → Set where
    literalMatch : ∀ char → AtomMatches (literal char) (char ∷ [])
    oneMatch : ∀ char → char ≢ '/' → AtomMatches one (char ∷ [])
    starMatch : ∀ {word} → NoSlash word → AtomMatches star word
    pathMatch : ∀ word → AtomMatches path word
    noDirectories : AtomMatches directories []
    directoryPrefix : ∀ {word} → EndsSlash word → AtomMatches directories word
    classMatch : ∀ {ranges word} → NoSlash word → R._∈_ word R.Exp.[ ranges ] → AtomMatches (characterClass false ranges) word
    negatedClassMatch : ∀ {ranges word} → NoSlash word → R._∈_ word R.[^ ranges ] → AtomMatches (characterClass true ranges) word
    alternativeMatch : ∀ {choices word} glob → glob ∈ choices → Matches glob word → AtomMatches (alternatives choices) word

mutual
  matches? : ∀ glob word → Dec (Matches glob word)
  matches? done [] = yes empty
  matches? done (_ ∷ _) = no (λ ())
  matches? (part atom rest) word with Finite.choose
    (λ pair → AtomMatches atom (proj₁ pair) × Matches rest (proj₂ pair))
    (λ pair → atomMatches? atom (proj₁ pair) ×-dec matches? rest (proj₂ pair)) (splits word)
  ... | yes ((first , second) , included , firstMatch , restMatch) =
    yes (chain first second (splitSound word first second included) firstMatch restMatch)
  ... | no absent = no (λ { (chain first second joined firstMatch restMatch) →
    absent ((first , second) , subst (λ path → (first , second) ∈ splits path) joined (splitComplete first second) , firstMatch , restMatch) })

  atomMatches? : ∀ atom word → Dec (AtomMatches atom word)
  atomMatches? (literal char) [] = no (λ ())
  atomMatches? (literal char) (first ∷ []) with first ≟ char
  ... | yes refl = yes (literalMatch char)
  ... | no different = no (λ { (literalMatch _) → different refl })
  atomMatches? (literal char) (_ ∷ _ ∷ _) = no (λ ())
  atomMatches? one [] = no (λ ())
  atomMatches? one (char ∷ []) with char ≟ '/'
  ... | yes refl = no (λ { (oneMatch _ different) → different refl })
  ... | no different = yes (oneMatch char different)
  atomMatches? one (_ ∷ _ ∷ _) = no (λ ())
  atomMatches? star word = map′ starMatch (λ { (starMatch chars) → chars }) (noSlash? word)
  atomMatches? path word = yes (pathMatch word)
  atomMatches? directories [] = yes noDirectories
  atomMatches? directories word@(_ ∷ _) = map′ directoryPrefix
    (λ { (directoryPrefix ended) → ended }) (endsSlash? word)
  atomMatches? (characterClass false ranges) word = map′
    (λ { (chars , matched) → classMatch chars matched })
    (λ { (classMatch chars matched) → chars , matched })
    (noSlash? word ×-dec R._∈?_ word R.Exp.[ ranges ])
  atomMatches? (characterClass true ranges) word = map′
    (λ { (chars , matched) → negatedClassMatch chars matched })
    (λ { (negatedClassMatch chars matched) → chars , matched })
    (noSlash? word ×-dec R._∈?_ word R.[^ ranges ])
  atomMatches? (alternatives choices) word = map′
    (λ { (glob , included , matched) → alternativeMatch glob included matched })
    (λ { (alternativeMatch glob included matched) → glob , included , matched }) (choicesMatch? choices word)

  choicesMatch? : ∀ choices word → Dec (Σ Glob (λ glob → glob ∈ choices × Matches glob word))
  choicesMatch? [] word = no (λ { (_ , () , _) })
  choicesMatch? (glob ∷ rest) word with matches? glob word
  ... | yes matched = yes (glob , here refl , matched)
  ... | no absent with choicesMatch? rest word
  ...   | yes (other , included , matched) = yes (other , there included , matched)
  ...   | no none = no (λ { (_ , here refl , matched) → absent matched
                         ; (other , there included , matched) → none (other , included , matched) })

matches : Glob → Word → Bool
matches glob word = does (matches? glob word)

matchSound : ∀ glob word → matches glob word ≡ true → Matches glob word
matchSound glob word accepted = toWitness {a? = matches? glob word}
  (subst T (sym (trans (isYes≗does (matches? glob word)) accepted)) tt)

matchComplete : ∀ glob word → Matches glob word → matches glob word ≡ true
matchComplete glob word matched = dec-true (matches? glob word) matched
