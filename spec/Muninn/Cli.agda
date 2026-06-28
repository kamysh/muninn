{-# OPTIONS --safe #-}
-- Muninn/Cli.agda
-- Formal spec of the muninn CLI: command AST, config-scope model, argument
-- constraints, pre/postconditions, and the index-transition connection.
--
-- Redesigned surface (breaking; no back-compat). A single unified `config` verb
-- edits BOTH the global and any per-repo config with the same grammar:
--   config get/set/edit/unset  with scope = --global | <path>.
-- The repo scope is an EXPLICIT path — the CLI never resolves a repo from the
-- cwd (error-prone). `key=value` is always a positional assignment (never a
-- `--set` flag), and the same assignment grammar is reused by `init` and `add`.
-- Other verbs: `init` (bootstrap global config + migrate), `add` (register +
-- first index), `reindex`, `pause`/`resume` (daemon-skip without dropping data),
-- `remove`, `status` (fleet overview, merges the old `list`), `usage` (telemetry).
module Muninn.Cli where

open import Muninn.Types
open import Muninn.Index
open import Muninn.AdvisoryLock using (Fg)
open import Data.Nat     using (ℕ)
open import Data.String  using (String)
open import Data.List    using (List)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Bool    using (Bool; true; false)
open import Data.Product using (_×_)
open import Data.Unit    using (⊤)
open import Data.Empty   using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary using (¬_)

-- ─── Runtime predicates ──────────────────────────────────────────────────────
-- Abstract evidence types: inhabited iff the runtime filesystem confirms the fact.
record PathExists       (p : FilePath) : Set where
record HasDotMuninnToml (p : FilePath) : Set where
record GlobalConfigExists : Set where

-- ─── Config scope + assignments ──────────────────────────────────────────────
-- Exactly one scope per invocation — the old clap `conflicts_with` mutual
-- exclusion is structural here (a single Scope value). The repo scope takes an
-- EXPLICIT path: there is no cwd default (the CLI never guesses the repo from the
-- working directory — error-prone). A bare `config` with no scope is a usage
-- error (the AST always carries a Scope).
data Scope : Set where
  Global : Scope               -- --global
  AtRepo : FilePath → Scope    -- <path> (explicit; required)

-- A single `key=value` assignment: the unified set-grammar shared by
-- `config set`, `init`, and `add`. One syntax learned once.
record Assign : Set where
  field key   : String
        value : String

-- The unified config operation, identical across both scopes.
-- (`SetKeys`, not `Set` — `Set` is Agda's type universe.)
data ConfigOp : Set where
  Get     : ConfigOp               -- read (optionally one key)
  SetKeys : List Assign → ConfigOp  -- key=value … (non-interactive, scriptable)
  Edit    : ConfigOp               -- open $EDITOR (interactive)
  Unset   : ConfigOp

-- ─── Command AST ─────────────────────────────────────────────────────────────
-- Target for `reindex`: a specific repo (explicit path) or all repos.
-- OneRepo/AllRepos are structurally exclusive (no separate validity predicate).
data ReindexTarget : Set where
  OneRepo  : FilePath → ReindexTarget   -- explicit path
  AllRepos : ReindexTarget

-- Per-repo commands take an EXPLICIT FilePath — no cwd default. The sole
-- `Maybe FilePath` is `status`, where `nothing` means the FLEET overview (all
-- repos), not the cwd repo.
data Command : Set where
  CmdInit    : List Assign → Command                  -- muninn init [k=v…]
  CmdConfig  : Scope → ConfigOp → Command             -- muninn config <op> (--global | <path>)
  CmdAdd     : FilePath → List Assign → Bool → Command -- path, initial k=v…, noIndex
  CmdReindex : ReindexTarget → Bool → Command         -- target, detach
  CmdPause   : FilePath → Command
  CmdResume  : FilePath → Command
  CmdRemove  : FilePath → Bool → Command              -- path, skipConfirm (--yes)
  CmdStatus  : Maybe FilePath → Command               -- nothing = fleet overview; just p = detail
  CmdUsage   : Maybe ℕ → Command                     -- nothing = default window

-- ─── Bootstrap invariant ─────────────────────────────────────────────────────
-- `muninn init` is the only command that runs before the global config exists —
-- it creates it (and runs migrations). Everything else requires a loaded config.
IsBootstrap : Command → Set
IsBootstrap (CmdInit _) = ⊤
IsBootstrap _           = ⊥

RequiresGlobalConfig : Command → Set
RequiresGlobalConfig cmd = ¬ IsBootstrap cmd

-- ─── Preconditions ───────────────────────────────────────────────────────────

-- init: idempotent bootstrap (safe to rerun — writes config if absent, migrates).
InitPre : Set
InitPre = ⊤

-- add <path>: the path must name an existing directory.
AddPre : FilePath → Set
AddPre path = PathExists path

-- config: a repo scope requires the repo registered; the global scope requires
-- the global config to exist.
ConfigPre : Scope → Set
ConfigPre Global       = GlobalConfigExists
ConfigPre (AtRepo p)   = HasDotMuninnToml p

-- ─── Postconditions ──────────────────────────────────────────────────────────

InitPost : Set
InitPost = GlobalConfigExists

-- add: the repo is registered (has a .muninn.toml).
AddPost : FilePath → Set
AddPost path = HasDotMuninnToml path

-- add without --no-index leaves the repo indexed; with --no-index, registered
-- but owed an index.
AddIndexed : Bool → Repo → Set
AddIndexed false repo = Repo.indexedAt repo ≢ nothing
AddIndexed true  repo = Repo.indexedAt repo ≡ nothing

-- remove: the .muninn.toml is gone and all index data dropped.
RemovePost : FilePath → Set
RemovePost path = ¬ HasDotMuninnToml path

-- pause / resume toggle the daemon-skip flag without dropping data.
PausePost : Repo → Set
PausePost repo = Repo.paused repo ≡ true

ResumePost : Repo → Set
ResumePost repo = Repo.paused repo ≡ false

-- reindex: a foreground run (detach = false) leaves the repo indexed; a detached
-- run, and `--all`, reset indexedAt = nothing for the daemon to pick up.
ReindexPost : Bool → Repo → Set
ReindexPost false repo = Repo.indexedAt repo ≢ nothing
ReindexPost true  repo = Repo.indexedAt repo ≡ nothing

-- ─── Config-edit reindex side-effect ──────────────────────────────────────────
-- A `config set`/`edit` on a repo scope reindexes per Muninn.IndexFsm: reindex
-- iff content changed OR the index is owed (configureAction, re-exported via
-- Muninn.Index). A `--global` set/edit runs migrations instead. The shared
-- --no-apply flag suppresses the side-effect; not modelled here.

-- ─── State-machine connection ─────────────────────────────────────────────────
-- `add`/`reindex` drive a foreground index: Unindexed → Indexing Fg → Indexed,
-- and Indexed → Indexing Fg. See Muninn.IndexFsm.Step.
IndexTransitionsCorrect : Set
IndexTransitionsCorrect =
  (Step Unindexed (Indexing Fg) × Step (Indexing Fg) Indexed) ×
  Step Indexed (Indexing Fg)

-- ─── Per-command specification bundle ─────────────────────────────────────────
record CommandSpec : Set₁ where
  field pre  : Set
        post : Set

initSpec : CommandSpec
initSpec = record { pre = InitPre ; post = InitPost }

addSpec : FilePath → CommandSpec
addSpec path = record { pre = AddPre path ; post = AddPost path }

configSpec : Scope → CommandSpec
configSpec sc = record { pre = ConfigPre sc ; post = ⊤ }

reindexSpec : Bool → Repo → CommandSpec
reindexSpec detach repo = record { pre = ⊤ ; post = ReindexPost detach repo }

pauseSpec : Repo → CommandSpec
pauseSpec repo = record { pre = ⊤ ; post = PausePost repo }

resumeSpec : Repo → CommandSpec
resumeSpec repo = record { pre = ⊤ ; post = ResumePost repo }

removeSpec : FilePath → CommandSpec
removeSpec path = record { pre = ⊤ ; post = RemovePost path }

statusSpec : CommandSpec
statusSpec = record { pre = ⊤ ; post = ⊤ }

usageSpec : CommandSpec
usageSpec = record { pre = ⊤ ; post = ⊤ }
