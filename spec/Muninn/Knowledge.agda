-- Muninn/Knowledge.agda
-- Knowledge item storage: free-text notes and lessons attached to a repo.
-- Knowledge items are distinct from code chunks: they are manually curated,
-- not derived from source files, and searched independently of code.
module Muninn.Knowledge where

open import Muninn.Float
open import Muninn.Types
open import Data.String  using (String)
open import Data.List    using (List; length)
open import Data.Nat     using (ℕ; _≤_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary                      using (¬_)
open import Data.List.Membership.Propositional    using (_∈_)

record KnowledgeId : Set where
  field value : UUID

-- A single curated note or lesson attached to a repo.
record KnowledgeItem : Set where
  field id           : KnowledgeId
        repoPath     : String          -- file-system path of the owning repo
        title        : String
        body         : String
        tags         : List String
        relatedFiles : List FilePath   -- code files this item describes
        -- embedding is intentionally absent: it is stored in the database for
        -- semantic search but is never returned to callers (large, opaque, internal).

-- ─── Validity Invariants ──────────────────────────────────────────────────────

NonEmptyTitle : KnowledgeItem → Set
NonEmptyTitle item = ¬ (KnowledgeItem.title item ≡ "")

NonEmptyBody : KnowledgeItem → Set
NonEmptyBody item = ¬ (KnowledgeItem.body item ≡ "")

record ValidKnowledgeItem (item : KnowledgeItem) : Set where
  field titleOk : NonEmptyTitle item
        bodyOk  : NonEmptyBody  item

-- ─── Search ───────────────────────────────────────────────────────────────────

record KnowledgeResult : Set where
  field item  : KnowledgeItem
        score : Float

-- Search results must not exceed the requested limit.
KnowledgeResultBound : (limit : ℕ) → List KnowledgeResult → Set
KnowledgeResultBound limit results = length results ≤ limit

-- ─── Repo Scoping ────────────────────────────────────────────────────────────

-- All knowledge items returned for a repo path must belong to that repo.
ScopedToRepo : String → List KnowledgeItem → Set
ScopedToRepo repoPath items =
  ∀ (item : KnowledgeItem) →
    item ∈ items →
    KnowledgeItem.repoPath item ≡ repoPath