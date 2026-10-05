{-# OPTIONS --safe #-}
-- Extensional membership and graph-visibility contract. Physical storage and
-- the SQL/AGE observation boundary are not proved here.
module Muninn.GraphMembership where

open import Muninn.Types using (UUID; FilePath)
open import Muninn.Worktree using (FamilyId; VersionRef; Manifest; FileEntry)
open import Muninn.Graph using (Relation)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Empty using (⊥-elim)

record EdgeId : Set where
  field value : UUID

record EdgeRef : Set where
  field family : FamilyId
        id : EdgeId

record SymbolKey : Set where
  field version : VersionRef
        ordinal : ℕ

record SymbolOccurrence : Set where
  field symbol : SymbolKey
        path : FilePath

record GraphEdge : Set where
  field source target : SymbolOccurrence
        relation : Relation
        referenceOrdinal : ℕ
        resolverIdentity : UUID

EdgeStore : Set
EdgeStore = EdgeRef → Maybe GraphEdge

Membership : Set
Membership = EdgeRef → Bool

Member : Membership → EdgeRef → Set
Member members ref = members ref ≡ true

setMember : ((a b : EdgeRef) → Dec (a ≡ b)) →
  EdgeRef → Bool → Membership → Membership
setMember eq target value members ref with eq target ref
... | yes _ = value
... | no _ = members ref

setMemberAtTarget : ∀ eq target value members →
  setMember eq target value members target ≡ value
setMemberAtTarget eq target value members with eq target target
... | yes _ = refl
... | no different = ⊥-elim (different refl)

otherMembershipUnchanged : ∀ eq target other value members →
  ¬ (target ≡ other) → setMember eq target value members other ≡ members other
otherMembershipUnchanged eq target other value members distinct with eq target other
... | yes same = ⊥-elim (distinct same)
... | no _ = refl

insertSelectsEdge : ∀ eq target members → Member (setMember eq target true members) target
insertSelectsEdge eq target members = setMemberAtTarget eq target true members

deleteExcludesEdge : ∀ eq target members → ¬ Member (setMember eq target false members) target
deleteExcludesEdge eq target members selected =
  subst (λ b → ¬ (b ≡ true)) (sym (setMemberAtTarget eq target false members))
    (λ ()) selected

OccurrenceVisible : Manifest → SymbolOccurrence → Set
OccurrenceVisible manifest occurrence = Σ FileEntry (λ entry →
  manifest (SymbolOccurrence.path occurrence) ≡ just entry ×
  FileEntry.version entry ≡ SymbolKey.version (SymbolOccurrence.symbol occurrence))

EndpointsVisible : Manifest → GraphEdge → Set
EndpointsVisible manifest edge =
  OccurrenceVisible manifest (GraphEdge.source edge) ×
  OccurrenceVisible manifest (GraphEdge.target edge)

EndpointsInFamily : FamilyId → GraphEdge → Set
EndpointsInFamily family edge =
  VersionRef.family (SymbolKey.version (SymbolOccurrence.symbol (GraphEdge.source edge))) ≡ family ×
  VersionRef.family (SymbolKey.version (SymbolOccurrence.symbol (GraphEdge.target edge))) ≡ family

-- A query result carries independent membership and endpoint evidence.
-- Resolver correctness/symbol-ordinal validity still require parsed facts.
record SelectedEdge (store : EdgeStore) (members : Membership)
                    (family : FamilyId) (manifest : Manifest) (ref : EdgeRef) : Set where
  field selected : Member members ref
        referenceFamily : EdgeRef.family ref ≡ family
        edge : GraphEdge
        stored : store ref ≡ just edge
        visible : EndpointsVisible manifest edge
        inFamily : EndpointsInFamily family edge

unselectedCannotReturn : ∀ {store members family manifest ref} →
  ¬ Member members ref → ¬ SelectedEdge store members family manifest ref
unselectedCannotReturn absent result = absent (SelectedEdge.selected result)

-- Even a stored edge with two visible endpoints is excluded if not selected.
visibleEndpointsDoNotBypassMembership : ∀ store members family manifest ref edge →
  store ref ≡ just edge → EndpointsVisible manifest edge →
  ¬ Member members ref → ¬ SelectedEdge store members family manifest ref
visibleEndpointsDoNotBypassMembership store members family manifest ref edge stored visible absent =
  unselectedCannotReturn absent

foreignFamilyCannotReturn : ∀ {store members family manifest ref} →
  ¬ (EdgeRef.family ref ≡ family) → ¬ SelectedEdge store members family manifest ref
foreignFamilyCannotReturn different result = different (SelectedEdge.referenceFamily result)

GraphExtends : EdgeStore → EdgeStore → Set
GraphExtends before after = ∀ ref edge → before ref ≡ just edge → after ref ≡ just edge

extensionPreservesSelectedEdge : ∀ {before after members family manifest ref} →
  GraphExtends before after → SelectedEdge before members family manifest ref →
  SelectedEdge after members family manifest ref
extensionPreservesSelectedEdge extends result = record
  { selected = SelectedEdge.selected result
  ; referenceFamily = SelectedEdge.referenceFamily result
  ; edge = SelectedEdge.edge result
  ; stored = extends _ _ (SelectedEdge.stored result)
  ; visible = SelectedEdge.visible result
  ; inFamily = SelectedEdge.inFamily result
  }

-- Logical references to shared immutable objects, not a requirement to store
-- a full edge list or expand membership rows per snapshot.
record GraphView (manifest : Manifest) : Set where
  field family : FamilyId
        store : EdgeStore
        members : Membership
        membersValid : ∀ ref → Member members ref → SelectedEdge store members family manifest ref

viewMemberHasVisibleEndpoints : ∀ {manifest} (view : GraphView manifest) ref →
  (selected : Member (GraphView.members view) ref) →
  EndpointsVisible manifest (SelectedEdge.edge (GraphView.membersValid view ref selected))
viewMemberHasVisibleEndpoints view ref selected =
  SelectedEdge.visible (GraphView.membersValid view ref selected)
