{-# OPTIONS --safe #-}
-- Muninn/Knowledge.agda
-- Knowledge item storage: free-text notes and lessons attached to a repo.
-- Knowledge items are distinct from code chunks: they are manually curated,
-- not derived from source files, and searched independently of code.
module Muninn.Knowledge where

open import Muninn.Float
open import Muninn.Worktree using (FamilyId)
open import Muninn.Types
open import Data.String  using (String)
open import Data.List    using (List; length)
open import Data.Maybe   using (Maybe)
open import Data.Nat     using (ℕ; _≤_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary                      using (¬_)
open import Data.List.Membership.Propositional    using (_∈_)

record KnowledgeId : Set where
  field value : UUID

-- A curated note belongs to the registered family and is visible from every
-- checkout. Related file paths are advisory references, not search visibility.
record KnowledgeItem : Set where
  field id           : KnowledgeId
        family       : FamilyId
        origin       : Maybe FilePath   -- optional checkout where it was written
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

-- ─── Family Scoping ──────────────────────────────────────────────────────────

-- All knowledge items returned from any checkout belong to its family.
ScopedToFamily : FamilyId → List KnowledgeItem → Set
ScopedToFamily family items =
  ∀ (item : KnowledgeItem) →
    item ∈ items →
    KnowledgeItem.family item ≡ family
