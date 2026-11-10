{-# OPTIONS --safe #-}
-- Authentication policy, independent of I/O. Runtime correspondence and
-- password-file grammar are documented in docs/database-connections.md.
module Muninn.Connection where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Used for passwords (config, nonempty environment, file lookup) and file
-- paths (config, environment, default). Values are never trimmed or decoded.
firstAvailable : ∀ {A : Set} → Maybe A → Maybe A → Maybe A → Maybe A
firstAvailable (just value) env fallback = just value
firstAvailable nothing (just value) fallback = just value
firstAvailable nothing nothing fallback = fallback

config-precedence : ∀ {A : Set} (value : A) env fallback →
  firstAvailable (just value) env fallback ≡ just value
config-precedence value env fallback = refl

environment-precedence : ∀ {A : Set} (value : A) fallback →
  firstAvailable nothing (just value) fallback ≡ just value
environment-precedence value fallback = refl

fallback-preserved : ∀ {A : Set} (fallback : Maybe A) →
  firstAvailable nothing nothing fallback ≡ fallback
fallback-preserved fallback = refl

data Mode : Set where
  disable allow prefer require verifyCa verifyFull : Mode

data Transport : Set where
  plaintext encrypted : Transport

-- trust and hostname are the independent results of certificate verification.
admissible : Mode → Transport → Bool → Bool → Bool
admissible disable plaintext trust hostname = true
admissible disable encrypted trust hostname = false
admissible allow transport trust hostname = true
admissible prefer transport trust hostname = true
admissible require plaintext trust hostname = false
admissible require encrypted trust hostname = true
admissible verifyCa plaintext trust hostname = false
admissible verifyCa encrypted trust hostname = trust
admissible verifyFull plaintext trust hostname = false
admissible verifyFull encrypted trust hostname = trust ∧ hostname

requiresTLS : Mode → Bool
requiresTLS require = true
requiresTLS verifyCa = true
requiresTLS verifyFull = true
requiresTLS _ = false

required-modes-refuse-plaintext : ∀ mode trust hostname →
  requiresTLS mode ≡ true → admissible mode plaintext trust hostname ≡ false
required-modes-refuse-plaintext require trust hostname required = refl
required-modes-refuse-plaintext verifyCa trust hostname required = refl
required-modes-refuse-plaintext verifyFull trust hostname required = refl

ca-verification-independent-of-hostname : ∀ trust hostname₁ hostname₂ →
  admissible verifyCa encrypted trust hostname₁ ≡
  admissible verifyCa encrypted trust hostname₂
ca-verification-independent-of-hostname trust hostname₁ hostname₂ = refl

full-verification-checks-hostname : ∀ hostname →
  admissible verifyFull encrypted true hostname ≡ hostname
full-verification-checks-hostname hostname = refl

untrusted-server-refused : ∀ hostname →
  admissible verifyFull encrypted false hostname ≡ false
untrusted-server-refused hostname = refl

validIdentity : Bool → Bool → Bool
validIdentity true true = true
validIdentity false false = true
validIdentity _ _ = false

-- Applies equally to query, migration, listener, lock, and cancellation paths:
-- no path may bypass the selected transport's admissibility condition.
data Path : Set where
  query migration listener lock preparation cancellation : Path

pathPolicy : Path → Mode → Transport → Bool → Bool → Bool
pathPolicy path = admissible

uniform-policy : ∀ path mode transport trust hostname →
  pathPolicy path mode transport trust hostname ≡
  admissible mode transport trust hostname
uniform-policy path mode transport trust hostname = refl

-- The configured mode selects the initial transport. Fallback is allowed only
-- for the cases explicitly defined by that mode, never for bad credentials or
-- a failed certificate verification.
data Observation : Set where
  serverDeclinedTls plaintextRejected authenticationRejected certificateRejected connectionLost : Observation

initial : Mode → Transport
initial disable = plaintext
initial allow = plaintext
initial prefer = encrypted
initial require = encrypted
initial verifyCa = encrypted
initial verifyFull = encrypted

fallback : Mode → Transport → Observation → Maybe Transport
fallback prefer encrypted serverDeclinedTls = just plaintext
fallback allow plaintext plaintextRejected = just encrypted
fallback _ _ _ = nothing

noCertificateDowngrade : ∀ mode transport → fallback mode transport certificateRejected ≡ nothing
noCertificateDowngrade disable transport = refl
noCertificateDowngrade allow plaintext = refl
noCertificateDowngrade allow encrypted = refl
noCertificateDowngrade prefer plaintext = refl
noCertificateDowngrade prefer encrypted = refl
noCertificateDowngrade require transport = refl
noCertificateDowngrade verifyCa transport = refl
noCertificateDowngrade verifyFull transport = refl

noAuthenticationDowngrade : ∀ mode transport → fallback mode transport authenticationRejected ≡ nothing
noAuthenticationDowngrade disable transport = refl
noAuthenticationDowngrade allow plaintext = refl
noAuthenticationDowngrade allow encrypted = refl
noAuthenticationDowngrade prefer plaintext = refl
noAuthenticationDowngrade prefer encrypted = refl
noAuthenticationDowngrade require transport = refl
noAuthenticationDowngrade verifyCa transport = refl
noAuthenticationDowngrade verifyFull transport = refl

credentialFor : ∀ {A : Set} → Path → Maybe A → Maybe A → Maybe A → Maybe A
credentialFor path configured environment file = firstAvailable configured environment file

allPathsUseSameCredential : ∀ {A : Set} (first second : Path) (configured environment file : Maybe A) →
  credentialFor first configured environment file ≡ credentialFor second configured environment file
allPathsUseSameCredential first second configured environment file = refl
