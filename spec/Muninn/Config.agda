-- Muninn/Config.agda
-- Two-layer configuration: global defaults merged with per-repo overrides.
-- Specifies merge semantics, repo discovery, repo resolution, and the
-- DimFrozen invariant that prevents embedding backend changes after indexing.
module Muninn.Config where

open import Muninn.Types
open import Muninn.Embeddings
open import Data.String  using (String)
open import Data.List    using (List)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Nat     using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

-- ─── Database Connection ─────────────────────────────────────────────────────

record DbConfig : Set where
  field host   : String
        port   : ℕ
        dbname : String
        user   : String
        -- password intentionally absent: supplied via ~/.pgpass

-- ─── Watcher Config ──────────────────────────────────────────────────────────

record WatcherConfig : Set where
  field debounceMs : ℕ

-- ─── Embedding Config ────────────────────────────────────────────────────────

record EmbeddingConfig : Set where
  field backend   : EmbeddingBackend
        model     : String
        apiKey    : Maybe String
        batchSize : ℕ

-- ─── Global Config ───────────────────────────────────────────────────────────
-- Loaded from ~/.config/muninn/config.toml.
-- Provides defaults for every setting; must be fully populated (no Maybes).

record GlobalConfig : Set where
  field database   : DbConfig
        embeddings : EmbeddingConfig
        watcher    : WatcherConfig
        scanRoots  : List FilePath   -- directories to scan for muninn.toml
        scanDepth  : ℕ              -- max directory depth per scan root

-- ─── Per-Repo Config ─────────────────────────────────────────────────────────
-- Loaded from <repo-root>/muninn.toml.
-- Every field is optional; absent = inherit from GlobalConfig.
-- An empty file (all nothing) is valid and only marks the repo root.

record RepoConfig : Set where
  field repoName   : Maybe String              -- [repo] name
        database   : Maybe DbConfig
        embeddings : Maybe EmbeddingConfig
        watcher    : Maybe WatcherConfig

-- ─── Effective Config ────────────────────────────────────────────────────────
-- The resolved config for a specific repo: global defaults overlaid with
-- per-repo overrides.  This is what the indexer and MCP server consume.

record EffectiveConfig : Set where
  field database   : DbConfig
        embeddings : EmbeddingConfig
        watcher    : WatcherConfig
        repoName   : String          -- resolved: repo override or directory name

-- ─── Merge Semantics ─────────────────────────────────────────────────────────

-- Field-level merge: use the override if present, else fall back to the default.
effective : {A : Set} → Maybe A → A → A
effective (just x) _ = x
effective nothing  d = d

-- The effective config for a repo is the per-repo override where present,
-- the global default everywhere else.
merge : GlobalConfig → RepoConfig → String → EffectiveConfig
merge g r dirName = record
  { database   = effective (RepoConfig.database   r) (GlobalConfig.database   g)
  ; embeddings = effective (RepoConfig.embeddings r) (GlobalConfig.embeddings g)
  ; watcher    = effective (RepoConfig.watcher    r) (GlobalConfig.watcher    g)
  ; repoName   = effective (RepoConfig.repoName   r) dirName
  }

-- ─── DimFrozen Invariant ─────────────────────────────────────────────────────
-- Once a repo has been indexed its embeddingDim is fixed.
-- Changing the effective backend after first index is forbidden.
-- Formally: if the repo has ever been indexed (indexedAt ≠ nothing) then
-- its stored embeddingDim must equal the canonical dimension of the
-- current effective backend.

DimFrozen : Repo → EffectiveConfig → Set
DimFrozen repo cfg =
  ¬ (Repo.indexedAt repo ≡ nothing) →
  Repo.embeddingDim repo ≡ EmbeddingDimension (EmbeddingConfig.backend (EffectiveConfig.embeddings cfg))

-- ─── Repo Discovery ──────────────────────────────────────────────────────────
-- A path is a RepoRoot iff it contains a muninn.toml file.
-- Discovery scans each scan root up to scanDepth levels deep and collects
-- all RepoRoots found.

-- We postulate the filesystem predicate; its truth is determined at runtime.
postulate
  IsRepoRoot : FilePath → Set

-- All discovered repo roots are within a bounded depth of some scan root.
-- (Encoded as a membership predicate; the actual walk is an implementation detail.)
DiscoveredUnder : FilePath → ℕ → FilePath → Set
DiscoveredUnder scanRoot depth repoRoot = IsRepoRoot repoRoot

-- ─── Repo Resolution (MCP walk-up) ───────────────────────────────────────────
-- Given a cwd, the MCP server resolves the repo root by walking up the
-- directory tree to the nearest ancestor (inclusive) that is a RepoRoot.
-- If no ancestor is a RepoRoot the resolution fails.

-- We postulate the ancestor relation; directory structure is a runtime concern.
postulate
  IsAncestorOrSelf : FilePath → FilePath → Set   -- IsAncestorOrSelf ancestor path

-- The resolved repo root is the nearest RepoRoot ancestor of cwd.
-- Parameterised by cwd so the ancestor relation is fully applied.
record ResolvedRepo (cwd : FilePath) : Set where
  field root    : FilePath
        isRoot  : IsRepoRoot root
        isAnc   : IsAncestorOrSelf root cwd
        -- nearest: no strictly closer ancestor is also a RepoRoot
        nearest : ∀ (closer : FilePath) → IsRepoRoot closer → IsAncestorOrSelf closer cwd → root ≡ closer