-- Muninn/Cli.agda
-- Formal specification of the muninn CLI (crate: muninn).
-- Covers command syntax, argument constraints, preconditions, postconditions,
-- and the ordering invariant that separates the bootstrap command (config init)
-- from all commands that require a loaded GlobalConfig.
module Muninn.Cli where

open import Muninn.Types
open import Muninn.Config
open import Muninn.Index
open import Data.Nat     using (ℕ)
open import Data.String  using (String)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Product using (_×_)
open import Data.Sum     using (_⊎_)
open import Data.Unit    using (⊤; tt)
open import Data.Empty   using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary using (¬_)

-- ─── Runtime predicates (postulated; truth determined at runtime) ─────────────

-- Abstract evidence types: inhabited iff the runtime filesystem confirms the fact.
record PathExists         (p : FilePath) : Set where
record HasMuninnToml      (p : FilePath) : Set where
record GlobalConfigExists : Set where
record GlobalConfigAbsent : Set where

-- ─── Command AST ─────────────────────────────────────────────────────────────

-- The subcommand under `muninn config`.
data ConfigSubCmd : Set where
  Init : ConfigSubCmd   -- create ~/.config/muninn/config.toml

-- Target for `muninn reindex`: either a specific repo path or all repos.
data ReindexTarget : Set where
  OneRepo : FilePath → ReindexTarget   -- muninn reindex <path>
  AllRepos : ReindexTarget             -- muninn reindex --all

-- The full set of top-level CLI commands.
data Command : Set where
  CmdConfig     : ConfigSubCmd  → Command        -- muninn config <subcmd>
  CmdRegister   : FilePath → Maybe String → Command  -- muninn register <path> [--name <n>]
  CmdIndex      : FilePath → Command             -- muninn index <path>
  CmdUnregister : FilePath → Command             -- muninn unregister <path>
  CmdList       : Command                        -- muninn list
  CmdReindex    : ReindexTarget → Command        -- muninn reindex (<path>|--all)
  CmdStatus     : Command                        -- muninn status
  CmdStats      : Maybe ℕ → Command             -- muninn stats [--days N]; nothing = default (30)

-- ─── Bootstrap invariant ─────────────────────────────────────────────────────
-- `muninn config init` is the only command that runs before GlobalConfig is
-- loaded — it is the command that creates the config.  All other commands
-- require a successfully loaded GlobalConfig.

IsBootstrap : Command → Set
IsBootstrap (CmdConfig Init) = ⊤
IsBootstrap _                = ⊥

RequiresGlobalConfig : Command → Set
RequiresGlobalConfig cmd with IsBootstrap cmd
... | _ = ¬ IsBootstrap cmd

-- ─── Argument constraints ─────────────────────────────────────────────────────

-- `reindex` accepts exactly one of: a path argument, or the --all flag.
-- This is the mutual-exclusion invariant enforced by clap's `conflicts_with`.
data ReindexArgValid : ReindexTarget → Set where
  reindexOnePath : ∀ (p : FilePath)  → ReindexArgValid (OneRepo p)
  reindexAll     :                      ReindexArgValid AllRepos

-- ─── Preconditions ───────────────────────────────────────────────────────────

-- config init: global config must not already exist.
ConfigInitPre : Set
ConfigInitPre = GlobalConfigAbsent

-- register <path> [--name]: path must name an existing directory.
RegisterPre : FilePath → Set
RegisterPre path = PathExists path

-- index <path>: path must exist AND contain muninn.toml (i.e. be registered).
IndexPre : FilePath → Set
IndexPre path = PathExists path × HasMuninnToml path

-- unregister, list, reindex, status: no per-argument path constraints beyond
-- the GlobalConfig requirement captured by RequiresGlobalConfig.

-- ─── Postconditions ──────────────────────────────────────────────────────────

-- After `config init` the global config file exists.
ConfigInitPost : Set
ConfigInitPost = GlobalConfigExists

-- After `register <path>` the path has a muninn.toml.
RegisterPost : FilePath → Set
RegisterPost path = HasMuninnToml path

-- After `index <path>` the repo's indexedAt field is set (not nothing).
-- Encoded as: the resulting Repo has indexedAt ≢ nothing.
IndexPost : Repo → Set
IndexPost repo = Repo.indexedAt repo ≢ nothing

-- After `unregister <path>` (confirmed) the muninn.toml is gone.
UnregisterPost : FilePath → Set
UnregisterPost path = ¬ HasMuninnToml path

-- After `reindex AllRepos` every repo in the DB has indexedAt = nothing
-- (daemon will re-index on next run).
ReindexAllPost : Repo → Set
ReindexAllPost repo = Repo.indexedAt repo ≡ nothing

-- After `reindex (OneRepo p)` the specific repo has indexedAt = nothing.
ReindexOnePost : Repo → Set
ReindexOnePost repo = Repo.indexedAt repo ≡ nothing

-- ─── State-machine connection ─────────────────────────────────────────────────
-- `muninn index` drives the repo through: Unindexed → Indexing → Indexed.
-- `muninn reindex` resets indexedAt, moving the repo back to Unindexed so
-- the daemon can perform startIndex / startReindex on its next scan.

IndexTransitionsCorrect : Set
IndexTransitionsCorrect =
  -- index moves an unindexed repo to Indexed via Indexing
  (IndexTransition Unindexed Indexing × IndexTransition Indexing Indexed) ×
  -- reindex resets a previously-indexed repo so it can be re-driven to Indexing
  IndexTransition Indexed Indexing

-- ─── Register idempotency ────────────────────────────────────────────────────
-- Running `register` on a path that already has a muninn.toml is a no-op:
-- the file is not overwritten (create_template returns the existing path).
-- Postcondition is the same whether or not the file pre-existed.
RegisterIdempotent : FilePath → Set
RegisterIdempotent path = HasMuninnToml path → RegisterPost path

-- ─── Summary: per-command specification bundle ───────────────────────────────

record CommandSpec : Set₁ where
  field
    pre  : Set    -- precondition (⊤ if unconditional)
    post : Set    -- postcondition (⊤ if side-effect free / display only)

configInitSpec : CommandSpec
configInitSpec = record { pre = ConfigInitPre ; post = ConfigInitPost }

registerSpec : FilePath → CommandSpec
registerSpec path = record { pre = RegisterPre path ; post = RegisterPost path }

indexSpec : FilePath → Repo → CommandSpec
indexSpec path repo = record { pre = IndexPre path ; post = IndexPost repo }

unregisterSpec : FilePath → CommandSpec
unregisterSpec path = record { pre = ⊤ ; post = UnregisterPost path }

listSpec : CommandSpec
listSpec = record { pre = ⊤ ; post = ⊤ }

reindexSpec : ReindexTarget → Repo → CommandSpec
reindexSpec (OneRepo _) repo = record { pre = ⊤ ; post = ReindexOnePost repo }
reindexSpec AllRepos    repo = record { pre = ⊤ ; post = ReindexAllPost  repo }

statusSpec : CommandSpec
statusSpec = record { pre = ⊤ ; post = ⊤ }

-- stats [--days N]: read-only diagnostic; no preconditions or postconditions.
statsSpec : CommandSpec
statsSpec = record { pre = ⊤ ; post = ⊤ }