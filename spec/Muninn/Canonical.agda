{-# OPTIONS --safe #-}
-- Internal typed content, not a wire format or a cryptographic digest.
module Muninn.Canonical where

open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Data.Bool using (Bool)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Relation.Nullary using (Dec; yes; no)
import Data.Nat.Properties as Nat
import Data.String.Properties as String
import Data.Bool.Properties as Bool

data Value : Set where
  text : String → Value
  natural : ℕ → Value
  boolean : Bool → Value
  sequence : List Value → Value

record Codec (A : Set) : Set where
  field
    encode : A → Value
    decode : Value → Maybe A
    roundTrip : ∀ a → decode (encode a) ≡ just a
open Codec public

just-injective : ∀ {A : Set} {a b : A} → just a ≡ just b → a ≡ b
just-injective refl = refl

faithful : ∀ {A} (c : Codec A) {a b} → encode c a ≡ encode c b → a ≡ b
faithful c {a} {b} same = just-injective
  (trans (sym (roundTrip c a)) (trans (cong (decode c) same) (roundTrip c b)))

-- The inverse obligation makes every field of a record significant. Adding a
-- field requires reconstructing it, and proving it was not lost in the view.
transport : ∀ {A B} → (view : A → B) → (build : B → A) →
  (∀ a → build (view a) ≡ a) → Codec B → Codec A
encode (transport view build inverse c) a = encode c (view a)
decode (transport view build inverse c) v = Maybe.map build (decode c v)
roundTrip (transport view build inverse c) a
  rewrite roundTrip c (view a) | inverse a = refl

string : Codec String
encode string = text
decode string (text x) = just x
decode string _ = nothing
roundTrip string x = refl

nat : Codec ℕ
encode nat = natural
decode nat (natural x) = just x
decode nat _ = nothing
roundTrip nat x = refl

bool : Codec Bool
encode bool = boolean
decode bool (boolean x) = just x
decode bool _ = nothing
roundTrip bool x = refl

unit : Codec ⊤
encode unit tt = sequence []
decode unit (sequence []) = just tt
decode unit _ = nothing
roundTrip unit tt = refl

pair : ∀ {A B} → Codec A → Codec B → Codec (A × B)
encode (pair a b) (x , y) = sequence (encode a x ∷ encode b y ∷ [])
decode (pair a b) (sequence (x ∷ y ∷ [])) with decode a x | decode b y
... | just u | just v = just (u , v)
... | _ | _ = nothing
decode (pair a b) _ = nothing
roundTrip (pair a b) (x , y) rewrite roundTrip a x | roundTrip b y = refl

optional : ∀ {A} → Codec A → Codec (Maybe A)
encode (optional c) nothing = sequence []
encode (optional c) (just a) = sequence (encode c a ∷ [])
decode (optional c) (sequence []) = just nothing
decode (optional c) (sequence (v ∷ [])) = Maybe.map just (decode c v)
decode (optional c) _ = nothing
roundTrip (optional c) nothing = refl
roundTrip (optional c) (just a) rewrite roundTrip c a = refl

decodeList : ∀ {A} → Codec A → List Value → Maybe (List A)
decodeList c [] = just []
decodeList c (x ∷ xs) with decode c x | decodeList c xs
... | just a | just as = just (a ∷ as)
... | _ | _ = nothing

listRoundTrip : ∀ {A} (c : Codec A) xs →
  decodeList c (map (encode c) xs) ≡ just xs
listRoundTrip c [] = refl
listRoundTrip c (x ∷ xs) rewrite roundTrip c x | listRoundTrip c xs = refl

list : ∀ {A} → Codec A → Codec (List A)
encode (list c) xs = sequence (map (encode c) xs)
decode (list c) (sequence xs) = decodeList c xs
decode (list c) _ = nothing
roundTrip (list c) = listRoundTrip c

-- A total comparison of full canonical content. A hash cannot substitute for
-- this equality. The mutually recursive cases preserve ordered lists.
mutual
  equal : (a b : Value) → Dec (a ≡ b)
  equal (text a) (text b) with a String.≟ b
  ... | yes refl = yes refl
  ... | no neq = no (λ { refl → neq refl })
  equal (natural a) (natural b) with a Nat.≟ b
  ... | yes refl = yes refl
  ... | no neq = no (λ { refl → neq refl })
  equal (boolean a) (boolean b) with a Bool.≟ b
  ... | yes refl = yes refl
  ... | no neq = no (λ { refl → neq refl })
  equal (sequence a) (sequence b) with equalList a b
  ... | yes refl = yes refl
  ... | no neq = no (λ { refl → neq refl })
  equal (text _) (natural _) = no (λ ())
  equal (text _) (boolean _) = no (λ ())
  equal (text _) (sequence _) = no (λ ())
  equal (natural _) (text _) = no (λ ())
  equal (natural _) (boolean _) = no (λ ())
  equal (natural _) (sequence _) = no (λ ())
  equal (boolean _) (text _) = no (λ ())
  equal (boolean _) (natural _) = no (λ ())
  equal (boolean _) (sequence _) = no (λ ())
  equal (sequence _) (text _) = no (λ ())
  equal (sequence _) (natural _) = no (λ ())
  equal (sequence _) (boolean _) = no (λ ())

  equalList : (a b : List Value) → Dec (a ≡ b)
  equalList [] [] = yes refl
  equalList [] (_ ∷ _) = no (λ ())
  equalList (_ ∷ _) [] = no (λ ())
  equalList (a ∷ as) (b ∷ bs) with equal a b | equalList as bs
  ... | yes refl | yes refl = yes refl
  ... | no neq | _ = no (λ { refl → neq refl })
  ... | _ | no neq = no (λ { refl → neq refl })

compare : ∀ {A} → Codec A → (a b : A) → Dec (a ≡ b)
compare c a b with equal (encode c a) (encode c b)
... | yes same = yes (faithful c same)
... | no different = no (λ same → different (cong (encode c) same))
