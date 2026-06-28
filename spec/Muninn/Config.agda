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
open import Data.Bool    using (Bool; true; false)
open import Data.String  using (String)
open import Data.List    using (List; []; _∷_; _++_; foldl)
open import Data.Maybe   using (Maybe; just; nothing; map)
open import Data.Nat     using (ℕ)
open import Data.Unit    using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
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

-- ─── Index Config ────────────────────────────────────────────────────────────
-- Two glob axes, each a list of patterns (globs relative to the repo root):
--   exclude — paths to DROP entirely (never indexed).
--   vendor  — paths to index as Tier 2 (down-weighted in search, embedded
--             lazily). Applied to whatever survives `exclude`.
-- A leading '!' on a pattern negates a prior match (un-sets it). Both axes
-- resolve the same way (see resolveAxis below): the effective pattern list is
-- shipped-defaults ++ global ++ repo, matched LAST-WINS.
record IndexConfig : Set where
  field exclude : List String
        vendor  : List String

-- ─── Axis resolution (last-match-wins fold with negation) ────────────────────
-- The engine matches a path against the ordered pattern list and the LAST
-- matching pattern decides membership: a bare pattern sets membership true, a
-- '!'-pattern sets it false. We model this as a left fold over the per-pattern
-- outcomes `(matched , negated)` already computed by the glob engine for a given
-- path: only matching patterns move the accumulator; the last one wins.
--   matched = does this glob match the path
--   negated = was the pattern '!'-prefixed
resolveStep : Bool → (Bool × Bool) → Bool
resolveStep acc (false , _)       = acc          -- no match: unchanged
resolveStep _   (true  , negated) = neg negated  -- match: set per polarity
  where
    neg : Bool → Bool
    neg true  = false   -- '!pattern' un-sets
    neg false = true    -- bare pattern sets

-- Whether a path is in the axis, given the per-pattern (matched, negated)
-- outcomes for the ordered effective list. Default (no match) is false.
resolveAxis : List (Bool × Bool) → Bool
resolveAxis = foldl resolveStep false

-- ─── Classification ──────────────────────────────────────────────────────────
-- exclude wins over vendor; unmatched survivors are Tier 1.
data Decision : Set where
  Drop : Decision
  T1   : Decision
  T2   : Decision

classify : (excluded vendored : Bool) → Decision
classify true  _     = Drop
classify false true  = T2
classify false false = T1

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
        index      : IndexConfig
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
        index      : Maybe IndexConfig

-- ─── Effective Config ────────────────────────────────────────────────────────
-- The resolved config for a specific repo: global defaults overlaid with
-- per-repo overrides.  This is what the indexer and MCP server consume.

record EffectiveConfig : Set where
  field database   : DbConfig
        embeddings : EmbeddingConfig
        watcher    : WatcherConfig
        exclude    : List String     -- resolved exclude globs (defaults++global++repo)
        vendor     : List String     -- resolved vendor globs (defaults++global++repo)
        repoName   : String          -- resolved: repo override or directory name

-- ─── Merge Semantics ─────────────────────────────────────────────────────────

-- Field-level merge: use the override if present, else fall back to the default.
effective : {A : Set} → Maybe A → A → A
effective (just x) _ = x
effective nothing  d = d

-- Shipped defaults for each axis. The authoritative lists live in config.rs
-- (EXCLUDE_DEFAULTS / VENDOR_DEFAULTS); these mirror them. Only the LAYERING
-- (defaults ++ global ++ repo) is the spec-level invariant — the specific
-- patterns are kept here so spec and impl agree, not because the proofs depend
-- on them. (Concrete, not postulated: --safe forbids postulates.)
excludeDefaults : List String
excludeDefaults =
  ".git/" ∷ "**/*.min.js" ∷ "**/*.min.css" ∷ "**/*.map" ∷ "**/*.snap" ∷
  "**/package-lock.json" ∷ "**/yarn.lock" ∷ "**/pnpm-lock.yaml" ∷
  "**/Cargo.lock" ∷ "**/poetry.lock" ∷ "**/Gemfile.lock" ∷ "**/composer.lock" ∷ []

vendorDefaults : List String
vendorDefaults =
  "**/node_modules/**" ∷ "**/vendor/**" ∷ "vendor/" ∷
  "**/.venv/**" ∷ "**/venv/**" ∷ "**/site-packages/**" ∷
  "**/target/**" ∷ "**/dist/**" ∷ "**/build/**" ∷ "**/.tox/**" ∷ "**/__pycache__/**" ∷ []

-- The repo's axis list (empty when the repo has no [index] section).
repoAxis : (IndexConfig → List String) → Maybe IndexConfig → List String
repoAxis f (just ic) = f ic
repoAxis _ nothing   = []

-- Layered resolution: defaults ++ global ++ repo, IN THIS ORDER. The engine then
-- matches a path against the concatenated list LAST-WINS with '!' negation (see
-- resolveAxis). This SUPERSEDES the earlier whole-list-replace exclude merge: a
-- repo now writes only its delta and inherits the rest, and '!p' can subtract a
-- default or inherited entry. (Matches impl EffectiveConfig::merge in config.rs.)
layerAxis : (IndexConfig → List String) → List String → GlobalConfig → RepoConfig → List String
layerAxis f defaults g r =
  defaults ++ f (GlobalConfig.index g) ++ repoAxis f (RepoConfig.index r)

-- The effective config for a repo is the per-repo override where present,
-- the global default everywhere else; the two glob axes use the layered fold.
merge : GlobalConfig → RepoConfig → String → EffectiveConfig
merge g r dirName = record
  { database   = effective (RepoConfig.database   r) (GlobalConfig.database   g)
  ; embeddings = effective (RepoConfig.embeddings r) (GlobalConfig.embeddings g)
  ; watcher    = effective (RepoConfig.watcher    r) (GlobalConfig.watcher    g)
  ; exclude    = layerAxis IndexConfig.exclude excludeDefaults g r
  ; vendor     = layerAxis IndexConfig.vendor  vendorDefaults  g r
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
