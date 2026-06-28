{-# OPTIONS --safe #-}
-- Muninn/Config.agda
-- Two-layer configuration: global defaults merged with per-repo overrides.
-- Specifies merge semantics, repo resolution, and the DimFrozen invariant
-- that prevents embedding backend changes after indexing.
-- Repo discovery is database-driven: the indexer daemon watches all repos
-- registered in the DB, notified via PostgreSQL LISTEN/NOTIFY with a 60s
-- fallback poll (implementation detail; not a config-level invariant).
module Muninn.Config where

open import Muninn.Types
open import Muninn.Embeddings
open import Data.Bool    using (Bool)
open import Data.String  using (String)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Nat     using (ℕ)
open import Data.Unit    using (⊤; tt)
open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

-- ─── Database Connection ─────────────────────────────────────────────────────

data SslMode : Set where
  Disable    : SslMode   -- never use TLS
  Allow      : SslMode   -- use TLS if server offers it
  Prefer     : SslMode   -- try TLS, fall back to plain (libpq default)
  Require    : SslMode   -- TLS required, no certificate verification
  VerifyCa   : SslMode   -- TLS + verify CA chain
  VerifyFull : SslMode   -- TLS + verify CA chain + hostname

record DbConfig : Set where
  field
    -- Required: must be present in every config layer that provides a DbConfig.
    host   : String
    port   : ℕ
    dbname : String
    user   : String
    -- password intentionally absent: supplied via ~/.pgpass
    -- Optional: absent means use the driver or pool default.
    dsnOverride     : Maybe String    -- if present, used verbatim; other fields ignored
    sslMode         : Maybe SslMode
    sslRootCert     : Maybe FilePath  -- path to CA bundle
    sslClientCert   : Maybe FilePath  -- path to client certificate
    sslClientKey    : Maybe FilePath  -- path to client private key
    maxConnections  : Maybe ℕ         -- connection pool size
    connectTimeout  : Maybe ℕ         -- seconds; nothing = no timeout
    applicationName : Maybe String    -- shown in pg_stat_activity

-- ─── Watcher Config ──────────────────────────────────────────────────────────

record WatcherConfig : Set where
  field debounceMs : ℕ

-- ─── Embedding Config ────────────────────────────────────────────────────────

record EmbeddingConfig : Set where
  field backend   : EmbeddingBackend
        -- Required for voyage/openai; absent for local (uses a hardcoded
        -- bundled model). Matches the impl's Option<String> (config.rs).
        model     : Maybe String
        apiKey    : Maybe String
        cacheDir  : Maybe String
        batchSize : ℕ

-- ─── MCP Config ──────────────────────────────────────────────────────────────

record McpLogConfig : Set where
  field enabled : Bool
        dir : String
        retentionDays : ℕ
        pruneIntervalHours : ℕ

record McpConfig : Set where
  field recordUsage : Bool
        logging : McpLogConfig

-- ─── Global Config ──────────────────────────────────────────────────────────
-- Loaded from ~/.config/muninn/config.toml.
-- Provides defaults for every setting; must be fully populated (no Maybes).

record GlobalConfig : Set where
  field database   : DbConfig
        embeddings : EmbeddingConfig
        watcher    : WatcherConfig
        mcp        : McpConfig

-- ─── Per-Repo Config ─────────────────────────────────────────────────────────
-- Loaded from <repo-root>/.muninn.toml.
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
-- Changing the effective backend is forbidden once a repo is registered.
-- Formally (UNCONDITIONAL): a repo's stored embeddingDim must always equal the
-- canonical dimension of its current effective backend — not only after first
-- index. The implementation enforces this on every daemon scan and CLI path
-- (indexer/main.rs DimFrozen check, before the indexed_at branch; cli
-- validate_repo_cfg / run_foreground_index), so the spec states the stronger,
-- always-true invariant the code actually guarantees. (embeddingDim is set from
-- the backend at registration, so for an unindexed repo the equality holds by
-- construction unless the configured backend was changed after registration —
-- exactly the case this rejects.)

DimFrozen : Repo → EffectiveConfig → Set
DimFrozen repo cfg =
  Repo.embeddingDim repo ≡ EmbeddingDimension (EmbeddingConfig.backend (EffectiveConfig.embeddings cfg))

-- ─── Repo Root Predicate ─────────────────────────────────────────────────────
-- A path is a RepoRoot iff it contains a .muninn.toml file.
-- Used by both `muninn register` and the MCP server's cwd walk-up.

-- Abstract evidence type: inhabited iff the runtime filesystem confirms the fact.
record IsRepoRoot (p : FilePath) : Set where

-- ─── Repo Resolution (MCP walk-up) ───────────────────────────────────────────
-- Given a cwd, the MCP server resolves the repo root by walking up the
-- directory tree to the nearest ancestor (inclusive) that is a RepoRoot.
-- If no ancestor is a RepoRoot the resolution fails.

-- Abstract evidence type: inhabited iff the runtime filesystem confirms ancestry.
record IsAncestorOrSelf (ancestor path : FilePath) : Set where

-- The resolved repo root is the nearest RepoRoot ancestor of cwd.
-- Parameterised by cwd so the ancestor relation is fully applied.
record ResolvedRepo (cwd : FilePath) : Set where
  field root    : FilePath
        isRoot  : IsRepoRoot root
        isAnc   : IsAncestorOrSelf root cwd
        -- nearest: no strictly closer ancestor is also a RepoRoot
        nearest : ∀ (closer : FilePath) → IsRepoRoot closer → IsAncestorOrSelf closer cwd → root ≡ closer
