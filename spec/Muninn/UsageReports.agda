{-# OPTIONS --safe #-}
-- Usage and log observations retain the configured fields and retention.
module Muninn.UsageReports where

import Muninn.OwnedState as O
open import Muninn.UsageTypes public using (Usage; usage)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Nat using (ℕ; zero; suc; _≤?_)
import Data.Empty
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ; _×_; _,_; proj₂)
open import Relation.Nullary using (yes; no)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

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
recorded : Usage → O.Record
recorded item = O.recordOf O.installation (O.usage item)


classifyValue : ℕ → (ℕ × O.Record) → Bool
classifyValue cutoff (slot , O.recordOf owner (O.usage item)) with cutoff ≤? Usage.recordedAt item
... | yes _ = true
... | no _ = false
classifyValue cutoff (slot , O.recordOf owner other) = false

classify : ℕ → (ℕ × O.Record) → Maybe Bool
classify cutoff row = just (classifyValue cutoff row)

classifyPresent : ∀ cutoff row → Σ Bool (λ value → classify cutoff row ≡ just value)
classifyPresent cutoff row = classifyValue cutoff row , refl

countSince : ℕ → O.World → Maybe ℕ
countSince cutoff [] = just zero
countSince cutoff (row ∷ rest) with classify cutoff row
... | nothing = nothing
... | just false = countSince cutoff rest
... | just true = map suc (countSince cutoff rest)

countPresent : ∀ cutoff world → Σ ℕ (λ total → countSince cutoff world ≡ just total)
countPresent cutoff [] = zero , refl
countPresent cutoff (row ∷ rest) with classifyPresent cutoff row | countPresent cutoff rest
... | (true , headReady) | (total , tailReady) rewrite headReady | tailReady = suc total , refl
... | (false , headReady) | (total , tailReady) rewrite headReady | tailReady = total , refl

inspect : ℕ → O.DB.Transaction (Maybe ℕ)
inspect cutoff = O.DB.scan (λ world → O.DB.commit (countSince cutoff world))
inspectionPreservesWorld : ∀ cutoff world → proj₂ (O.DB.execute (inspect cutoff) world) ≡ world
inspectionPreservesWorld cutoff world = refl

recentRowCounted : ∀ cutoff item slot rest → cutoff Data.Nat.≤ Usage.recordedAt item →
  countSince cutoff ((slot , recorded item) ∷ rest) ≡ map suc (countSince cutoff rest)
recentRowCounted cutoff item slot rest within with cutoff ≤? Usage.recordedAt item
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

classifyTool : String → ℕ → (ℕ × O.Record) → Maybe Bool
classifyTool selected cutoff (slot , O.recordOf owner (O.usage item)) with Usage.tool item Data.String.≟ selected | cutoff ≤? Usage.recordedAt item
... | yes _ | yes _ = just true
... | _ | _ = just false
classifyTool selected cutoff (slot , O.recordOf owner other) = just false

countToolSince : String → ℕ → O.World → Maybe ℕ
countToolSince selected cutoff [] = just zero
countToolSince selected cutoff (row ∷ rest) with classifyTool selected cutoff row
... | nothing = nothing
... | just false = countToolSince selected cutoff rest
... | just true = map suc (countToolSince selected cutoff rest)
