{-# OPTIONS --safe #-}
-- Exact byte admission and independent text/structural coverage obligations.
module Muninn.FileLimits where

open import Data.Nat using (ℕ; _≤_; _≤?_; _<_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Fin using (Fin)
open import Data.List using (List; length)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

record Limits : Set where
  constructor limits
  field fileBytes structuralBytes : ℕ

-- Production defaults, in bytes (MiB = 1024 * 1024).
defaultLimits : Limits
defaultLimits = limits 10485760 1048576

resolve : Limits → Maybe Limits → Limits
resolve captured nothing = captured
resolve captured (just chosen) = chosen

initial : Maybe Limits → Limits
initial = resolve defaultLimits

Byte = Fin 256
Contents = List Byte

-- Contents is the logical raw byte sequence, before decoding, newline/BOM
-- normalization or parsing. It does not prescribe allocating a whole file.
TextAllowed : Limits → Contents → Set
TextAllowed caps bytes = length bytes ≤ Limits.fileBytes caps

StructureAllowed : Limits → Contents → Bool → Set
StructureAllowed caps bytes parser = TextAllowed caps bytes ×
  ((length bytes ≤ Limits.structuralBytes caps) × parser ≡ true)

data Limitation : Set where
  structuralSize noParser : Limitation

data Coverage : Set where
  textOnly : Limitation → Coverage
  textAndStructure : Coverage

-- This evidence is determined by the fixed intent predicates above.
data ValidWork (caps : Limits) (bytes : Contents) (parser : Bool) : Coverage → Set where
  limited : TextAllowed caps bytes → ¬ (length bytes ≤ Limits.structuralBytes caps) →
    ValidWork caps bytes parser (textOnly structuralSize)
  unsupported : TextAllowed caps bytes → length bytes ≤ Limits.structuralBytes caps → parser ≡ false →
    ValidWork caps bytes parser (textOnly noParser)
  structural : StructureAllowed caps bytes parser → ValidWork caps bytes parser textAndStructure

record Work (caps : Limits) (bytes : Contents) (parser : Bool) : Set where
  constructor work
  field coverage : Coverage
        valid : ValidWork caps bytes parser coverage

data Assessment (caps : Limits) (bytes : Contents) (parser : Bool) : Set where
  ask : ¬ TextAllowed caps bytes → Assessment caps bytes parser
  run : Work caps bytes parser → Assessment caps bytes parser

assess : ∀ caps bytes parser → Assessment caps bytes parser
assess caps bytes parser with length bytes ≤? Limits.fileBytes caps
... | no over = ask over
... | yes fits with length bytes ≤? Limits.structuralBytes caps
...   | no over = run (work (textOnly structuralSize) (limited fits over))
...   | yes small with parser
...     | false = run (work (textOnly noParser) (unsupported fits small refl))
...     | true = run (work textAndStructure (structural (fits , small , refl)))

workFits : ∀ {caps bytes parser} → Work caps bytes parser → TextAllowed caps bytes
workFits (work .(textOnly structuralSize) (limited fits over)) = fits
workFits (work .(textOnly noParser) (unsupported fits small absent)) = fits
workFits (work .textAndStructure (structural (fits , small , available))) = fits

textComplete : ∀ caps bytes parser → TextAllowed caps bytes →
  Σ (Work caps bytes parser) (λ job → assess caps bytes parser ≡ run job)
textComplete caps bytes parser fits with assess caps bytes parser
... | ask over = ⊥-elim (over fits)
... | run job = job , refl

structureSound : ∀ {caps bytes parser} (job : Work caps bytes parser) → Work.coverage job ≡ textAndStructure →
  StructureAllowed caps bytes parser
structureSound (work .(textOnly structuralSize) (limited fits over)) ()
structureSound (work .(textOnly noParser) (unsupported fits small absent)) ()
structureSound (work .textAndStructure (structural allowed)) chosen = allowed

structureComplete : ∀ {caps bytes parser} (job : Work caps bytes parser) → StructureAllowed caps bytes parser →
  Work.coverage job ≡ textAndStructure
structureComplete (work .(textOnly structuralSize) (limited fits over)) (allowed , small , available) = ⊥-elim (over small)
structureComplete (work .(textOnly noParser) (unsupported fits small ())) (allowed , bounded , refl)
structureComplete (work .textAndStructure (structural proof)) allowed = refl

atFileBoundary : ∀ caps bytes → length bytes ≡ Limits.fileBytes caps → TextAllowed caps bytes
atFileBoundary caps bytes same = subst (length bytes ≤_) same ≤-refl

atStructuralBoundary : ∀ caps bytes → TextAllowed caps bytes → length bytes ≡ Limits.structuralBytes caps →
  StructureAllowed caps bytes true
atStructuralBoundary caps bytes fits same = fits , subst (length bytes ≤_) same ≤-refl , refl
