{-# OPTIONS --safe #-}
-- Usage and log observations retain the configured fields and retention.
module Muninn.UsageReports where

import Muninn.OwnedState as O
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤?_)
import Data.Empty
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_; proj₂)
open import Relation.Nullary using (yes; no)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

record Usage : Set where
  constructor usage
  field tool : String
        repositoryPath : Maybe String
        durationMilliseconds : ℕ
        resultCount : Maybe ℕ
        recordedAt : ℕ

record LogEvent : Set where
  constructor logEvent
  field tool : String
        repositoryPath : Maybe String
        query : Maybe String
        durationMilliseconds : ℕ
        resultCount : Maybe ℕ

record Settings : Set where
  constructor settings
  field recordUsage logEnabled : Bool
        logDirectory : String
        logRetentionDays pruneIntervalHours : ℕ

initialSettings : Settings
initialSettings = settings true true "~/.local/state/muninn/mcp" 7 24

-- The database stores usage separately from local log-file retention.
record Codec : Set where
  field encode : Usage → String
        decode : String → Maybe Usage
        roundTrip : ∀ item → decode (encode item) ≡ just item

recorded : Codec → Usage → O.Record
recorded codec item = O.recordOf O.installation (O.usage (Codec.encode codec item))


-- Count saved usage rows in a requested time window. Runtime correspondence
-- must establish that every actual usage row has a valid decoding.
countSince : Codec → ℕ → O.World → ℕ
countSince codec cutoff [] = zero
countSince codec cutoff ((slot , O.recordOf owner (O.usage payload)) ∷ rest) with Codec.decode codec payload
... | nothing = countSince codec cutoff rest
... | just item with cutoff ≤? Usage.recordedAt item
...   | yes _ = suc (countSince codec cutoff rest)
...   | no _ = countSince codec cutoff rest
countSince codec cutoff ((slot , O.recordOf owner other) ∷ rest) = countSince codec cutoff rest

inspect : Codec → ℕ → O.DB.Transaction ℕ
inspect codec cutoff = O.DB.scan (λ world → O.DB.commit (countSince codec cutoff world))
inspectionPreservesWorld : ∀ codec cutoff world → proj₂ (O.DB.execute (inspect codec cutoff) world) ≡ world
inspectionPreservesWorld codec cutoff world = refl

recentRowCounted : ∀ codec cutoff item slot rest → cutoff Data.Nat.≤ Usage.recordedAt item →
  countSince codec cutoff ((slot , recorded codec item) ∷ rest) ≡ suc (countSince codec cutoff rest)
recentRowCounted codec cutoff item slot rest within rewrite Codec.roundTrip codec item with cutoff ≤? Usage.recordedAt item
... | yes _ = refl
... | no outside = Data.Empty.⊥-elim (outside within)

-- Only identified Muninn log files are eligible for age-based pruning;
-- unknown or foreign files in the same directory are retained.
record LogFile : Set where
  constructor logFile
  field muninnOwned : Bool
        modifiedAt : ℕ

record LogCodec : Set where
  field decodeLog : String → Maybe LogFile

pruneLogs : LogCodec → ℕ → O.World → O.World
pruneLogs codec cutoff [] = []
pruneLogs codec cutoff ((slot , entry@(O.recordOf owner (O.logFile payload))) ∷ rest) with LogCodec.decodeLog codec payload
... | nothing = (slot , entry) ∷ pruneLogs codec cutoff rest
... | just file with LogFile.muninnOwned file
...   | false = (slot , entry) ∷ pruneLogs codec cutoff rest
...   | true with LogFile.modifiedAt file Data.Nat.<? cutoff
...     | yes _ = pruneLogs codec cutoff rest
...     | no _ = (slot , entry) ∷ pruneLogs codec cutoff rest
pruneLogs codec cutoff (entry ∷ rest) = entry ∷ pruneLogs codec cutoff rest

-- A zero retention setting disables pruning; the interval controls only the
-- periodic follow-up, not the initial prune.
pruneConfigured : Settings → LogCodec → ℕ → O.World → O.World
pruneConfigured (settings usageEnabled false dir retention interval) codec cutoff world = world
pruneConfigured (settings usageEnabled true dir zero interval) codec cutoff world = world
pruneConfigured (settings usageEnabled true dir (suc retention) interval) codec cutoff world = pruneLogs codec cutoff world

countToolSince : Codec → String → ℕ → O.World → ℕ
countToolSince codec selected cutoff [] = zero
countToolSince codec selected cutoff ((slot , O.recordOf owner (O.usage payload)) ∷ rest) with Codec.decode codec payload
... | nothing = countToolSince codec selected cutoff rest
... | just item with Usage.tool item Data.String.≟ selected | cutoff ≤? Usage.recordedAt item
...   | yes _ | yes _ = suc (countToolSince codec selected cutoff rest)
...   | _ | _ = countToolSince codec selected cutoff rest
countToolSince codec selected cutoff ((slot , O.recordOf owner other) ∷ rest) = countToolSince codec selected cutoff rest
