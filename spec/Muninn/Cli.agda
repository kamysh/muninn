{-# OPTIONS --safe #-}
-- CLI intents for database-backed family configuration. Interactive TUI and
-- JSON clients present the same policy and preflight data. Only an explicit
-- start begins the first family index; linked worktrees then index automatically.
module Muninn.Cli where

open import Muninn.Types
open import Muninn.Worktree using (FamilyId)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (Σ; _×_)
open import Muninn.Config using (FamilyPolicy; BootstrapConfig)
open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Data.List using (List)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary using (¬_)

-- Explicit observed inputs replace empty records that were inhabited for
-- every path, including unregistered ones. Path lookup uses a canonical root.
Registry : Set
Registry = FilePath → Maybe FamilyId

PathExists : List FilePath → FilePath → Set
PathExists existing path = path ∈ existing

BootstrapExists : Maybe BootstrapConfig → Set
BootstrapExists nothing = ⊥
BootstrapExists (just _) = ⊤

RegisteredFamily : Registry → FilePath → Set
RegisteredFamily registry path = Σ FamilyId (λ family → registry path ≡ just family)

-- These are semantic intents, not a decision about concrete CLI flag spelling.
data RemovalScope : Set where
  CheckoutOnly EntireFamily : RemovalScope

-- Preflight is a cheap filesystem inventory: it does not parse or embed.
record DirectoryCost : Set where
  field path : FilePath
        files : ℕ
        bytes : ℕ
        concern : Maybe String

data Advice : Set where
  StartNow : Advice
  RefinePolicy : Advice

record Preflight : Set where
  field files : ℕ
        bytes : ℕ
        costlyDirectories : List DirectoryCost
        advice : Advice

-- Both clients can inspect and update the same versioned family policy.
-- The TUI displays an initial or current policy and asks whether to start.
-- JSON applies a complete, validated policy against an expected revision.
data Client : Set where
  Tui : Client
  Json : Client

data TuiChoice : Set where
  StartIndex : TuiChoice
  EditPolicy : TuiChoice
  AskAgent : TuiChoice
  LeaveUnindexed : TuiChoice

data Command : Set where
  CmdInit : Command
  CmdAdd : Client → FilePath → Command
  CmdConfig : Client → FilePath → Command
  CmdInspect : FilePath → Command
  CmdApply : FilePath → FamilyId → ℕ → FamilyPolicy → Command
  CmdStart : FilePath → Command
  CmdReindex : FilePath → Command
  CmdPause : FilePath → Command
  CmdResume : FilePath → Command
  CmdRemove : RemovalScope → FilePath → Command
  CmdStatus : Maybe FilePath → Command

IsBootstrap : Command → Set
IsBootstrap CmdInit = ⊤
IsBootstrap _ = ⊥

AddPre : List FilePath → FilePath → Set
AddPre = PathExists

AddPost : Registry → FilePath → Set
AddPost = RegisteredFamily

ConfigPre : Registry → FilePath → Set
ConfigPre = RegisteredFamily

-- Registration does not start indexing. The TUI's Start choice and CmdStart
-- are explicit user actions; JSON automation must issue CmdStart separately.
AddUnindexed : Bool → Set
AddUnindexed started = started ≡ false

-- Preflight does not change registration or indexing state.
PreflightReadOnly : ∀ {State : Set} → State → State → Set
PreflightReadOnly before after = before ≡ after

-- A family policy update is rejected when the supplied revision is stale.
ApplyPre : FamilyId → ℕ → FamilyPolicy → Set
ApplyPre expectedFamily expected current =
  (expectedFamily ≡ FamilyPolicy.family current) × (expected ≡ FamilyPolicy.revision current)

-- Directory removal affects its mapping. Explicit family removal affects all
-- mappings; Storage additionally requires reference safety before schema drop.
RemoveCheckoutPost : Registry → FilePath → Set
RemoveCheckoutPost registry path = registry path ≡ nothing

RemoveFamilyPost : Registry → FamilyId → Set
RemoveFamilyPost registry family = ∀ path → ¬ (registry path ≡ just family)
