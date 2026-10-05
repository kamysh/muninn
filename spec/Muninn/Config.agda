{-# OPTIONS --safe #-}
-- Muninn/Config.agda
-- One local bootstrap connection plus database-backed family policy.
-- Every checkout in a Git family uses the same policy. The daemon discovers
-- checkouts from the registered family; no repository marker is required.
module Muninn.Config where

open import Muninn.Types
open import Muninn.Worktree using (Checkout; FamilyId)
open import Muninn.Embeddings
open import Data.Bool    using (Bool; true; false)
open import Data.String  using (String)
open import Data.List    using (List; []; _∷_; _++_; foldl)
open import Data.Maybe   using (Maybe; just; nothing; map)
open import Data.Nat     using (ℕ; _<_)
open import Data.List.Membership.Propositional using (_∈_)
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
    -- Required in the one local bootstrap connection.
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

record EmbeddingSelection : Set where
  field backend   : EmbeddingBackend
        model     : Maybe String
        batchSize : ℕ

-- ─── Index Config ────────────────────────────────────────────────────────────
-- Two glob axes, each a list of patterns (globs relative to the repo root):
--   exclude — paths to DROP entirely (never indexed).
--   vendor  — paths to index as Tier 2 (down-weighted in search, embedded
--             lazily). Applied to whatever survives `exclude`.
-- A leading '!' on a pattern negates a prior match (un-sets it). Both axes
-- resolve the same way (see resolveAxis below): the effective pattern list is
-- shipped-defaults ++ family policy, matched LAST-WINS.
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

-- ─── Bootstrap and database-backed family policy ────────────────────────────
-- The bootstrap file is local and supplies one database connection, secrets,
-- and machine-local paths. No per-repository file can override the connection.
record BootstrapConfig : Set where
  field database : DbConfig
        embeddingApiKey : Maybe String
        embeddingCacheDir : Maybe FilePath
        mcp : McpConfig

-- One database row per registered family. A non-Git directory is a family
-- with one checkout. Credentials and connection details do not belong here.
record PolicyDefaults : Set where
  field defaultsRevision : String
        rules : IndexConfig

record FamilyPolicy : Set where
  field family : FamilyId
        name : String
        watcher : WatcherConfig
        index : IndexConfig
        embeddings : EmbeddingSelection
        revision : ℕ
        defaults : PolicyDefaults

record EffectiveConfig : Set where
  field embeddings : EmbeddingSelection
        watcher : WatcherConfig
        exclude : List String
        vendor : List String
        repoName : String

-- Defaults are immutable inputs to policy creation. A stored family policy is
-- authoritative afterward, and its globs apply to all linked checkouts.
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

familyConfig : FamilyPolicy → EffectiveConfig
familyConfig p = record
  { embeddings = FamilyPolicy.embeddings p
  ; watcher = FamilyPolicy.watcher p
  ; exclude = IndexConfig.exclude (PolicyDefaults.rules (FamilyPolicy.defaults p)) ++ IndexConfig.exclude (FamilyPolicy.index p)
  ; vendor = IndexConfig.vendor (PolicyDefaults.rules (FamilyPolicy.defaults p)) ++ IndexConfig.vendor (FamilyPolicy.index p)
  ; repoName = FamilyPolicy.name p
  }

-- A checkout cannot select a different family policy.
CheckoutUsesFamilyPolicy : Checkout → FamilyPolicy → Set
CheckoutUsesFamilyPolicy c p = Checkout.family c ≡ FamilyPolicy.family p

-- Dimension stays fixed for a registered family until a deliberate migration.
DimFrozen : ℕ → FamilyPolicy → Set
DimFrozen schemaDimension policy =
  schemaDimension ≡ EmbeddingDimension (EmbeddingSelection.backend (FamilyPolicy.embeddings policy))

-- DB revisions allow JSON and TUI clients to reject stale writes atomically.
-- A successful update strictly advances the stored revision.
record PolicyUpdate (before after : FamilyPolicy) : Set where
  field sameFamily : FamilyPolicy.family before ≡ FamilyPolicy.family after
        newer : FamilyPolicy.revision before < FamilyPolicy.revision after

-- Resolution is a registry lookup from a path in a checkout, independent of
-- .muninn.toml. The runtime must establish the ancestor and registered-family
-- evidence; the selected checkout determines returned paths and visibility.
-- Canonical-path containment is an external relation supplied by the resolver;
-- it is not an empty, universally inhabited record asserting every path matches.
record ResolvedCheckout (ancestorOrSelf : FilePath → FilePath → Set)
                        (registered : List Checkout) (cwd : FilePath) : Set where
  field checkout : Checkout
        registeredCheckout : checkout ∈ registered
        isAnc : ancestorOrSelf (Checkout.root checkout) cwd
