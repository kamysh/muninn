{-# OPTIONS --safe #-}
-- Application migrations belong to Kryzhen; graph lifecycle belongs to AGE.
-- Both kinds of evidence are abstract observations supplied by the runtime.
module Muninn.Schema where

open import Muninn.Worktree using (SchemaId)
open import Data.List using (List)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim)

-- These are namespace identities, not the common family UUID from which
-- runtime names are derived. AGE owns the second namespace in the pair.
record SchemaPair : Set where
  field application graph : SchemaId
        graphName : String
        distinct : ¬ (application ≡ graph)

data SchemaRole : Set where
  Application Graph : SchemaRole

schemaAt : SchemaPair → SchemaRole → SchemaId
schemaAt pair Application = SchemaPair.application pair
schemaAt pair Graph = SchemaPair.graph pair

schemaRoleInjective : ∀ pair a b → schemaAt pair a ≡ schemaAt pair b → a ≡ b
schemaRoleInjective pair Application Application same = refl
schemaRoleInjective pair Application Graph same = ⊥-elim (SchemaPair.distinct pair same)
schemaRoleInjective pair Graph Application same = ⊥-elim (SchemaPair.distinct pair (sym same))
schemaRoleInjective pair Graph Graph same = refl

record Migration : Set where
  field name body : String

Template : Set
Template = List Migration

Ledger : Set
Ledger = SchemaId → List Migration

-- Completion in another schema cannot supply this evidence. Full body
-- identity also matters; a reused name with a changed body is insufficient.
AppliedTemplate : Template → Ledger → SchemaId → Set
AppliedTemplate required ledger schema =
  ∀ m → m ∈ required → m ∈ ledger schema

record FamilyTemplate : Set where
  field applicationMigrations : Template

-- Abstract observed catalog evidence; the runtime must establish it from AGE.
-- This model does not prove that a supplied observation matches the database.
record GraphMapping (pair : SchemaPair) : Set where
  field observedName : String
        observedNamespace : SchemaId
        nameMatches : observedName ≡ SchemaPair.graphName pair
        namespaceMatches : observedNamespace ≡ SchemaPair.graph pair

-- AGE owns the graph and its internal schema. Neither route depends on a
-- Kryzhen template or ledger. Existing graph data need not be recreated.
-- These constructors describe verified outcomes, not implementations of API calls.
data GraphReady (pair : SchemaPair) : Set where
  createdByAge : GraphMapping pair → GraphReady pair
  existingValidatedByAge : GraphMapping pair → GraphReady pair

graphReadinessMatchesPair : ∀ {pair} → GraphReady pair → GraphMapping pair
graphReadinessMatchesPair (createdByAge mapping) = mapping
graphReadinessMatchesPair (existingValidatedByAge mapping) = mapping

data SchemaState : Set where
  Missing Migrating Ready : SchemaState

-- SchemaState is the readiness of the whole family pair. Muninn coordinates
-- independent Kryzhen and AGE operations; it may report Ready only with both.
data SchemaStep (required : FamilyTemplate) (ledger : Ledger) (pair : SchemaPair)
                : SchemaState → SchemaState → Set where
  beginPreparation : SchemaStep required ledger pair Missing Migrating
  familyReady : AppliedTemplate (FamilyTemplate.applicationMigrations required) ledger (SchemaPair.application pair) →
                GraphReady pair → SchemaStep required ledger pair Migrating Ready

noDirectReadiness : ∀ required ledger pair →
  ¬ SchemaStep required ledger pair Missing Ready
noDirectReadiness required ledger pair ()

readinessRequiresOwnTemplate : ∀ {required ledger pair before} →
  SchemaStep required ledger pair before Ready →
  AppliedTemplate (FamilyTemplate.applicationMigrations required) ledger (SchemaPair.application pair)
readinessRequiresOwnTemplate (familyReady applied graph) = applied

readinessRequiresGraph : ∀ {required ledger pair before} →
  SchemaStep required ledger pair before Ready → GraphReady pair
readinessRequiresGraph (familyReady applied graph) = graph

noReadinessWithoutGraph : ∀ {required ledger pair before} →
  ¬ GraphReady pair → ¬ SchemaStep required ledger pair before Ready
noReadinessWithoutGraph absent ready = absent (readinessRequiresGraph ready)

readinessRequiresGraphMapping : ∀ {required ledger pair before} →
  SchemaStep required ledger pair before Ready → GraphMapping pair
readinessRequiresGraphMapping ready =
  graphReadinessMatchesPair (readinessRequiresGraph ready)

noReadinessWithoutApplication : ∀ {required ledger pair before} →
  ¬ AppliedTemplate (FamilyTemplate.applicationMigrations required) ledger (SchemaPair.application pair) →
  ¬ SchemaStep required ledger pair before Ready
noReadinessWithoutApplication absent ready = absent (readinessRequiresOwnTemplate ready)
