{-# OPTIONS --safe #-}
-- Whole-store laws used by the bounded cleanup transactions.
module Muninn.CleanupStorage where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
open import Data.Nat using (ℕ; _≟_)
open import Data.Bool using (Bool; true; false)
open import Data.String using (String)
open import Data.List using (List; []; _∷_; map; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.All as All
open All using (All; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans; subst)
module DB = O.DB

lookupAll : ∀ {P : ℕ × O.Record → Set} world key value → All P world →
  DB.lookup key world ≡ just value → P (key , value)
lookupAll [] key value proofs ()
lookupAll ((other , stored) ∷ rows) key value (proof ∷ proofs) found with key ≟ other
... | yes refl with just-injective found
...   | refl = proof
lookupAll ((other , stored) ∷ rows) key value (proof ∷ proofs) found | no different =
  lookupAll rows key value proofs found

writeUnique : ∀ key value world → O.Unique world → O.Unique (DB.write key value world)
writeUnique key value world unique = DB.deleteAbsent key world , O.deleteUnique key world unique

writeResolves : ∀ world key old new source ref → DB.lookup key world ≡ just old →
  O.owner new ≡ O.owner old → O.kind (O.body new) ≡ O.kind (O.body old) →
  O.Resolves world source ref → O.Resolves (DB.write key new world) source ref
writeResolves world key old new source ref found sameOwner sameKind resolved with O.target ref ≟ key
... | yes refl = record
  { value = new; found = DB.writeVisible key new world
  ; rightKind = trans sameKind (trans (cong (λ value → O.kind (O.body value)) sameValue) (O.Resolves.rightKind resolved))
  ; rightOwner = subst (O.MayReference source)
      (trans (sym (cong O.owner sameValue)) (sym sameOwner)) (O.Resolves.rightOwner resolved) }
  where
  sameValue : old ≡ O.Resolves.value resolved
  sameValue = just-injective (trans (sym found) (O.Resolves.found resolved))
... | no different = record
  { value = O.Resolves.value resolved
  ; found = trans (DB.writePreservesOther key (O.target ref) new world (λ same → different (sym same))) (O.Resolves.found resolved)
  ; rightKind = O.Resolves.rightKind resolved; rightOwner = O.Resolves.rightOwner resolved }

writeAdmissible : ∀ world key old new → O.Admissible world → DB.lookup key world ≡ just old →
  O.owner new ≡ O.owner old → O.kind (O.body new) ≡ O.kind (O.body old) → O.Placed new →
  (∀ ref → ref ∈ O.references (O.body new) → ref ∈ O.references (O.body old)) →
  O.Admissible (DB.write key new world)
writeAdmissible world key old new valid found sameOwner sameKind placed subset = record
  { unique = writeUnique key new world (O.Admissible.unique valid)
  ; placed = placed ∷ O.deleteAll key world (O.Admissible.placed valid)
  ; sound = newSound ∷ O.deleteAll key world shifted
  ; privateBookkeeping = All.tabulate (λ {ref} present → All.lookup
      (lookupAll world key old (O.Admissible.privateBookkeeping valid) found) (subset ref present)) ∷
      O.deleteAll key world (O.Admissible.privateBookkeeping valid) }
  where
  oldSound : All (O.Resolves world (O.owner old)) (O.references (O.body old))
  oldSound = lookupAll world key old (O.Admissible.sound valid) found
  newBefore : All (O.Resolves world (O.owner new)) (O.references (O.body new))
  newBefore = subst (λ owner → All (O.Resolves world owner) (O.references (O.body new))) (sym sameOwner)
    (All.tabulate (λ present → All.lookup oldSound (subset _ present)))
  newSound : All (O.Resolves (DB.write key new world) (O.owner new)) (O.references (O.body new))
  newSound = All.map (λ {ref} → writeResolves world key old new (O.owner new) ref found sameOwner sameKind) newBefore
  shifted : All (O.SoundReferences (DB.write key new world)) world
  shifted = All.map (λ {row} refs → All.map
    (λ {ref} → writeResolves world key old new (O.owner (proj₂ row)) ref found sameOwner sameKind) refs)
    (O.Admissible.sound valid)

-- Replacing a control record may change its outgoing references. Every new
-- reference is resolved and private-safe; incoming references keep kind/owner.
writeResolvedAdmissible : ∀ world key old new → O.Admissible world →
  DB.lookup key world ≡ just old → O.owner new ≡ O.owner old →
  O.kind (O.body new) ≡ O.kind (O.body old) → O.Placed new →
  All (O.Resolves world (O.owner new)) (O.references (O.body new)) →
  O.PrivateBookkeepingReferences new → O.Admissible (DB.write key new world)
writeResolvedAdmissible world key old new valid found sameOwner sameKind placed resolved privateRefs = record
  { unique = writeUnique key new world (O.Admissible.unique valid)
  ; placed = placed ∷ O.deleteAll key world (O.Admissible.placed valid)
  ; sound = All.map (λ {ref} proof → writeResolves world key old new (O.owner new) ref found sameOwner sameKind proof) resolved ∷
      O.deleteAll key world shifted
  ; privateBookkeeping = privateRefs ∷ O.deleteAll key world (O.Admissible.privateBookkeeping valid) }
  where
  shifted : All (O.SoundReferences (DB.write key new world)) world
  shifted = All.map (λ {row} refs → All.map
    (λ {ref} proof → writeResolves world key old new (O.owner (proj₂ row)) ref found sameOwner sameKind proof) refs)
    (O.Admissible.sound valid)

filterSubset : ∀ keep keys key → key ∈ E.filterKeys keep keys → key ∈ keys
filterSubset keep [] key ()
filterSubset keep (first ∷ rest) key present with keep first
... | true with present
...   | here same = here same
...   | there later = there (filterSubset keep rest key later)
filterSubset keep (first ∷ rest) key present | false = there (filterSubset keep rest key present)

mapFilterSubset : ∀ {A : Set} (f : ℕ → A) keep keys value →
  value ∈ map f (E.filterKeys keep keys) → value ∈ map f keys
mapFilterSubset f keep keys value present with ∈-map⁻ f present
... | key , included , refl = ∈-map⁺ f (filterSubset keep keys key included)

module Model (excluded : List String → String → Bool) where
  module M = E.Model excluded

  data Shape (selection : E.Rule) (world : O.World) : O.Record → Set where
    plain : ∀ {value} → M.project selection world value ≡ value → Shape selection world value
    snapshot : ∀ owner selected nodes edges payload → Shape selection world
      (O.recordOf owner (O.structuralSnapshot selected nodes edges payload))

  shape : ∀ selection world value → Shape selection world value
  shape selection world (O.recordOf owner (O.structuralSnapshot selected nodes edges payload)) = snapshot owner selected nodes edges payload
  shape selection world value@(O.recordOf owner (O.registration _)) = plain refl
  shape selection world value@(O.recordOf owner (O.checkout _)) = plain refl
  shape selection world value@(O.recordOf owner (O.creationIntent _)) = plain refl
  shape selection world value@(O.recordOf owner (O.defaults _)) = plain refl
  shape selection world value@(O.recordOf owner (O.policyVersion _ _)) = plain refl
  shape selection world value@(O.recordOf owner (O.currentPolicy _)) = plain refl
  shape selection world value@(O.recordOf owner (O.note _)) = plain refl
  shape selection world value@(O.recordOf owner (O.notePosting _ _)) = plain refl
  shape selection world value@(O.recordOf owner (O.noteVector _ _)) = plain refl
  shape selection world value@(O.recordOf owner (O.fileVersion _)) = plain refl
  shape selection world value@(O.recordOf owner (O.baseBinding _ _)) = plain refl
  shape selection world value@(O.recordOf owner (O.deltaBinding _ _ _)) = plain refl
  shape selection world value@(O.recordOf owner (O.basePointer _)) = plain refl
  shape selection world value@(O.recordOf owner (O.chunk _ _)) = plain refl
  shape selection world value@(O.recordOf owner (O.posting _ _)) = plain refl
  shape selection world value@(O.recordOf owner (O.vector _ _)) = plain refl
  shape selection world value@(O.recordOf owner (O.symbol _ _ _)) = plain refl
  shape selection world value@(O.recordOf owner (O.edge _ _ _)) = plain refl
  shape selection world value@(O.recordOf owner (O.legacy _ _)) = plain refl
  shape selection world value@(O.recordOf owner (O.staging _ _)) = plain refl
  shape selection world value@(O.recordOf owner (O.acceptedWork _ _)) = plain refl
  shape selection world value@(O.recordOf owner (O.cleanupWork _ _ _)) = plain refl
  shape selection world value@(O.recordOf owner (O.activeReader _ _)) = plain refl
  shape selection world value@(O.recordOf owner (O.continuation _ _)) = plain refl
  shape selection world value@(O.recordOf owner (O.receipt _)) = plain refl
  shape selection world value@(O.recordOf owner (O.migration _)) = plain refl
  shape selection world value@(O.recordOf owner (O.usage _)) = plain refl
  shape selection world value@(O.recordOf owner (O.bootstrap _)) = plain refl
  shape selection world value@(O.recordOf owner (O.modelCache _)) = plain refl
  shape selection world value@(O.recordOf owner (O.coordination _)) = plain refl
  shape selection world value@(O.recordOf owner (O.schemaResource _)) = plain refl
  shape selection world value@(O.recordOf owner (O.graphResource _ _ _)) = plain refl
  shape selection world value@(O.recordOf owner (O.publishedView _ _)) = plain refl
  shape selection world value@(O.recordOf owner (O.logFile _)) = plain refl
  shape selection world value@(O.recordOf owner (O.bootstrapStage _)) = plain refl

  projectOwner : ∀ selection world value → O.owner (M.project selection world value) ≡ O.owner value
  projectOwner selection world value with shape selection world value
  ... | plain equal = cong O.owner equal
  ... | snapshot owner selected nodes edges payload with E.ownerEqual owner (E.targetOwner selection)
  ...   | yes _ = refl
  ...   | no _ = refl

  projectKind : ∀ selection world value → O.kind (O.body (M.project selection world value)) ≡ O.kind (O.body value)
  projectKind selection world value with shape selection world value
  ... | plain equal = cong (λ v → O.kind (O.body v)) equal
  ... | snapshot owner selected nodes edges payload with E.ownerEqual owner (E.targetOwner selection)
  ...   | yes _ = refl
  ...   | no _ = refl

  projectPlaced : ∀ selection world value → O.Placed value → O.Placed (M.project selection world value)
  projectPlaced selection world value placed with shape selection world value
  ... | plain equal = subst O.Placed (sym equal) placed
  ... | snapshot owner selected nodes edges payload with E.ownerEqual owner (E.targetOwner selection)
  ...   | yes _ = placed
  ...   | no _ = placed

  projectReferences : ∀ selection world value ref →
    ref ∈ O.references (O.body (M.project selection world value)) → ref ∈ O.references (O.body value)
  projectReferences selection world value ref present with shape selection world value
  ... | plain equal = subst (λ v → ref ∈ O.references (O.body v)) equal present
  ... | snapshot owner selected nodes edges payload with E.ownerEqual owner (E.targetOwner selection)
  ...   | no _ = present
  ...   | yes _ with present
  ...     | here same = here same
  ...     | there later with ∈-++⁻ (map (λ key → O.reference key O.symbolK)
          (E.filterKeys (M.symbolVisible selection world owner selected) nodes)) later
  ...       | inj₁ node = there (∈-++⁺ˡ (mapFilterSubset (λ key → O.reference key O.symbolK) _ nodes ref node))
  ...       | inj₂ edge = there (∈-++⁺ʳ (map (λ key → O.reference key O.symbolK) nodes)
          (mapFilterSubset (λ key → O.reference key O.edgeK) _ edges ref edge))

  projectNodesSubset : ∀ selection world value key →
    key ∈ E.snapshotNodes (M.project selection world value) → key ∈ E.snapshotNodes value
  projectNodesSubset selection world value key present with shape selection world value
  ... | plain equal = subst (λ v → key ∈ E.snapshotNodes v) equal present
  ... | snapshot owner selected nodes edges payload with E.ownerEqual owner (E.targetOwner selection)
  ...   | no _ = present
  ...   | yes _ = filterSubset _ nodes key present

  projectEdgesSubset : ∀ selection world value key →
    key ∈ E.snapshotEdges (M.project selection world value) → key ∈ E.snapshotEdges value
  projectEdgesSubset selection world value key present with shape selection world value
  ... | plain equal = subst (λ v → key ∈ E.snapshotEdges v) equal present
  ... | snapshot owner selected nodes edges payload with E.ownerEqual owner (E.targetOwner selection)
  ...   | no _ = present
  ...   | yes _ = filterSubset _ edges key present

  projectIdempotent : ∀ selection world value → M.project selection world (M.project selection world value) ≡ M.project selection world value
  projectIdempotent selection world value with shape selection world value
  ... | plain equal = cong (M.project selection world) equal
  ... | snapshot owner selected nodes edges payload with E.ownerEqual owner (E.targetOwner selection) in decision
  ...   | no _ rewrite decision = refl
  ...   | yes _ rewrite decision | E.filterKeysIdempotent (M.symbolVisible selection world owner selected) nodes
        | E.filterKeysIdempotent (M.edgeVisible selection world owner selected) edges = refl

  projectAdmissible : ∀ selection world key value → O.Admissible world → DB.lookup key world ≡ just value →
    O.Admissible (DB.write key (M.project selection world value) world)
  projectAdmissible selection world key value valid found = writeAdmissible world key value (M.project selection world value)
    valid found (projectOwner selection world value) (projectKind selection world value)
    (projectPlaced selection world value (lookupAll world key value (O.Admissible.placed valid) found))
    (projectReferences selection world value)


  projectCheckout : ∀ selection world value →
    E.snapshotCheckout (M.project selection world value) ≡ E.snapshotCheckout value
  projectCheckout selection world value with shape selection world value
  ... | plain same = cong E.snapshotCheckout same
  ... | snapshot owner selected nodes edges payload with E.ownerEqual owner (E.targetOwner selection)
  ...   | yes same = refl
  ...   | no different = refl
