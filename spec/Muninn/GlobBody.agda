{-# OPTIONS --safe #-}
-- Complete raw-body assembly over certified source tokens.
module Muninn.GlobBody where

import Muninn.GlobTokens as T
import Muninn.GlobMatching as G
open import Data.Char using (Char)
open import Data.Char.Properties using (_≟_)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Nullary using (yes; no)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

Word : Set
Word = G.Word

append : G.Glob → G.Atom → G.Glob
append G.done term = G.part term G.done
append (G.part first rest) term = G.part first (append rest term)

-- An empty rendered alternative is omitted by the existing syntax. A whole
-- group with no remaining branches is the empty expression, not an empty language.
mutual
  emptyExpression : G.Glob → Bool
  emptyExpression G.done = true
  emptyExpression (G.part term rest) = emptyAtom term ∧ emptyExpression rest

  emptyAtom : G.Atom → Bool
  emptyAtom (G.alternatives choices) = emptyChoices choices
  emptyAtom (G.literal char) = false
  emptyAtom G.one = false
  emptyAtom G.star = false
  emptyAtom G.path = false
  emptyAtom G.directories = false
  emptyAtom (G.characterClass negated ranges) = false

  emptyChoices : List G.Glob → Bool
  emptyChoices [] = true
  emptyChoices (first ∷ rest) = emptyExpression first ∧ emptyChoices rest

nonemptyChoices : List G.Glob → List G.Glob
nonemptyChoices [] = []
nonemptyChoices (first ∷ rest) with emptyExpression first
... | true = nonemptyChoices rest
... | false = first ∷ nonemptyChoices rest

choices : List G.Glob → List G.Glob
choices branches with nonemptyChoices branches
... | [] = G.done ∷ []
... | first ∷ rest = first ∷ rest

record Frame : Set where
  constructor frame
  field current : G.Glob
        branches : List G.Glob

record State : Set where
  constructor state
  field active : Frame
        parents : List Frame
        boundary : Bool

initial : State
initial = state (frame G.done []) [] true

inGroup : State → Bool
inGroup (state current [] boundary) = false
inGroup (state current (_ ∷ _) boundary) = true

atomBoundary : G.Atom → Bool
atomBoundary (G.literal char) with char ≟ '/'
... | yes refl = true
... | no different = false
atomBoundary G.directories = true
atomBoundary G.one = false
atomBoundary G.star = false
atomBoundary G.path = false
atomBoundary (G.characterClass negated ranges) = false
atomBoundary (G.alternatives branches) = false

add : G.Atom → Frame → Frame
add term (frame current branches) = frame (append current term) branches

branch : Frame → Frame
branch (frame current branches) = frame G.done (branches ++ (current ∷ []))

group : Frame → G.Atom
group (frame current branches) = G.alternatives (choices (branches ++ (current ∷ [])))

-- These source-assembly rules are independent of the executable step decision.
data Action : State → T.Token → State → Set where
  atom : ∀ current parents boundary term → Action (state current parents boundary)
    (T.atom term) (state (add term current) parents (atomBoundary term))
  opening : ∀ current parents boundary → Action (state current parents boundary)
    T.opening (state (frame G.done []) (current ∷ parents) true)
  commaOutside : ∀ current boundary → Action (state current [] boundary)
    T.separator (state (add (G.literal ',') current) [] false)
  commaInside : ∀ current parent parents boundary → Action (state current (parent ∷ parents) boundary)
    T.separator (state (branch current) (parent ∷ parents) true)
  closing : ∀ current parent parents boundary → Action (state current (parent ∷ parents) boundary)
    T.closingBracket (state (add (group current) parent) parents false)

record Stepped (before : State) (token : T.Token) : Set where
  constructor stepped
  field after : State
        action : Action before token after

step : ∀ before token → Maybe (Stepped before token)
step (state current parents boundary) (T.atom term) =
  just (stepped (state (add term current) parents (atomBoundary term)) (atom current parents boundary term))
step (state current parents boundary) T.opening =
  just (stepped (state (frame G.done []) (current ∷ parents) true) (opening current parents boundary))
step (state current [] boundary) T.separator =
  just (stepped (state (add (G.literal ',') current) [] false) (commaOutside current boundary))
step (state current (parent ∷ parents) boundary) T.separator =
  just (stepped (state (branch current) (parent ∷ parents) true) (commaInside current parent parents boundary))
step (state current [] boundary) T.closingBracket = nothing
step (state current (parent ∷ parents) boundary) T.closingBracket =
  just (stepped (state (add (group current) parent) parents false) (closing current parent parents boundary))

stepMeaning : State → T.Token → Maybe State
stepMeaning before token = map Stepped.after (step before token)

stepRecognized : ∀ {before token after} → Action before token after → stepMeaning before token ≡ just after
stepRecognized (atom current parents boundary term) = refl
stepRecognized (opening current parents boundary) = refl
stepRecognized (commaOutside current boundary) = refl
stepRecognized (commaInside current parent parents boundary) = refl
stepRecognized (closing current parent parents boundary) = refl

data Source : Word → State → G.Glob → Set where
  end : ∀ current branches boundary → Source [] (state (frame current branches) [] boundary) current
  next : ∀ {input before token suffix after result} →
    T.Source (State.boundary before) (inGroup before) input token suffix →
    Action before token after → Source suffix after result → Source input before result

record Parsed (input : Word) (before : State) : Set where
  constructor parsed
  field result : G.Glob
        source : Source input before result

attach : ∀ {input before token suffix after} →
  T.Source (State.boundary before) (inGroup before) input token suffix →
  Action before token after → Maybe (Parsed suffix after) → Maybe (Parsed input before)
attach token action nothing = nothing
attach token action (just (parsed result source)) = just (parsed result (next token action source))

parseWith : ∀ input before → Acc _<_ (length input) → Maybe (Parsed input before)
parseWith [] (state (frame current branches) [] boundary) accessible = just (parsed current (end current branches boundary))
parseWith [] (state current (_ ∷ _) boundary) accessible = nothing
parseWith input@(char ∷ rest) before (acc smaller) with T.scan (State.boundary before) (inGroup before) input
... | nothing = nothing
... | just token with step before (T.Scanned.token token)
...   | nothing = nothing
...   | just moved = attach (T.Scanned.source token) (Stepped.action moved)
    (parseWith (T.Scanned.suffix token) (Stepped.after moved)
      (smaller (T.progress (T.Scanned.source token))))

meaningWith : ∀ input before → Acc _<_ (length input) → Maybe G.Glob
meaningWith input before accessible = map Parsed.result (parseWith input before accessible)

emptyToken : ∀ {boundary group token suffix} → T.Source boundary group [] token suffix → ⊥
emptyToken source with T.recognized source
... | ()

recognizedWith : ∀ {input before result} → Source input before result →
  (accessible : Acc _<_ (length input)) → meaningWith input before accessible ≡ just result
recognizedWith (end current branches boundary) accessible = refl
recognizedWith {[]} (next token action rest) accessible = ⊥-elim (emptyToken token)
recognizedWith {input@(char ∷ tail)} {before} (next token action rest) (acc smaller)
  with T.scan (State.boundary before) (inGroup before) input | T.recognized token
... | nothing | ()
... | just (T.scanned actualToken suffix actualSource) | same with just-injective same
...   | refl with step before actualToken | stepRecognized action
...     | nothing | ()
...     | just (stepped after actualAction) | same with just-injective same
...       | refl with parseWith suffix after (smaller (T.progress actualSource)) |
    recognizedWith rest (smaller (T.progress actualSource))
...         | nothing | ()
...         | just (parsed result actual) | known = known

parse : ∀ input → Maybe (Parsed input initial)
parse input = parseWith input initial (<-wellFounded (length input))

meaning : Word → Maybe G.Glob
meaning input = map Parsed.result (parse input)

recognized : ∀ {input result} → Source input initial result → meaning input ≡ just result
recognized source = recognizedWith source (<-wellFounded _)

deterministic : ∀ {input before first second} → Source input before first → Source input before second → first ≡ second
deterministic first second = just-injective (trans
  (sym (recognizedWith first (<-wellFounded _))) (recognizedWith second (<-wellFounded _)))

steps : ∀ {input before result} → Source input before result → ℕ
steps (end current branches boundary) = zero
steps (next token action rest) = suc (steps rest)

bounded : ∀ {input before result} (source : Source input before result) → steps source ≤ length input
bounded (end current branches boundary) = z≤n
bounded (next token action rest) = ≤-trans (s≤s (bounded rest)) (T.progress token)

RawMatches : Word → Word → Set
RawMatches input word = Σ G.Glob (λ result → Source input initial result × G.Matches result word)

matches : Word → Word → Maybe Bool
matches input word = map (λ result → G.matches (Parsed.result result) word) (parse input)

matchSound : ∀ input word → matches input word ≡ just true → RawMatches input word
matchSound input word accepted with parse input
... | nothing = ⊥-elim (impossible accepted)
  where
  impossible : nothing ≡ just true → ⊥
  impossible ()
... | just result = Parsed.result result , Parsed.source result ,
  G.matchSound (Parsed.result result) word (just-injective accepted)

matchComplete : ∀ input word → RawMatches input word → matches input word ≡ just true
matchComplete input word (result , source , matched) with parse input | recognized source
... | nothing | ()
... | just actual | same with just-injective same
...   | refl = cong just (G.matchComplete (Parsed.result actual) word matched)
