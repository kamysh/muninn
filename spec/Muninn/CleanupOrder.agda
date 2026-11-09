{-# OPTIONS --safe #-}
-- Raw strong-reference ordering for indexed records, independent of a worker.
module Muninn.CleanupOrder where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.ReceiptTypes as Receipt
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _≟_; _≤?_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; <-trans; <-irrefl; <⇒≤; ≰⇒>)
open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.All as All
open All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst; subst₂)
module DB = O.DB

lookupExists : ∀ world key value → (key , value) ∈ world → Σ O.Record (λ stored → DB.lookup key world ≡ just stored)
lookupExists ((key , value) ∷ world) .key .value (here refl) = value , DB.lookupHead key value world
lookupExists ((other , stored) ∷ world) key value (there present) with key ≟ other
... | yes _ = stored , refl
... | no _ = lookupExists world key value present

memberLookup : ∀ world key value → O.Unique world → (key , value) ∈ world → DB.lookup key world ≡ just value
memberLookup ((key , value) ∷ world) .key .value unique (here refl) = DB.lookupHead key value world
memberLookup ((other , stored) ∷ world) key value (absent , unique) (there present) with key ≟ other
... | no _ = memberLookup world key value unique present
... | yes refl with trans (sym absent) (memberLookup world key value unique present)
...   | ()

rank : O.Kind → ℕ
rank O.registrationK = 0
rank O.checkoutK = 0
rank O.creationIntentK = 0
rank O.defaultsK = 0
rank O.policyVersionK = 0
rank O.currentPolicyK = 0
rank O.noteK = 0
rank O.notePostingK = 0
rank O.noteVectorK = 0
rank O.fileVersionK = 0
rank O.baseBindingK = 1
rank O.deltaBindingK = 1
rank O.basePointerK = 1
rank O.chunkK = 1
rank O.postingK = 2
rank O.vectorK = 2
rank O.symbolK = 1
rank O.edgeK = 2
rank O.structuralSnapshotK = 3
rank O.legacyK = 0
rank O.stagingK = 1
rank O.acceptedWorkK = 0
rank O.cleanupWorkK = 0
rank O.activeReaderK = 0
rank O.continuationK = 0
rank O.receiptK = 0
rank O.migrationK = 0
rank O.usageK = 0
rank O.bootstrapK = 0
rank O.modelCacheK = 0
rank O.coordinationK = 0
rank O.schemaResourceK = 0
rank O.graphResourceK = 0
rank O.logFileK = 0
rank O.bootstrapStageK = 0

join : ∀ {A : Set} {P : A → Set} {xs ys} → All P xs → All P ys → All P (xs ++ ys)
join [] right = right
join (proof ∷ left) right = proof ∷ join left right

constantLower : ∀ keys kind upper → rank kind < upper →
  All (λ ref → rank (O.expected ref) < upper) (map (λ key → O.reference key kind) keys)
constantLower [] kind upper smaller = []
constantLower (_ ∷ keys) kind upper smaller = smaller ∷ constantLower keys kind upper smaller

indexedReferencesLower : ∀ value → E.indexed value ≡ true →
  All (λ ref → rank (O.expected ref) < rank (O.kind (O.body value))) (O.references (O.body value))

indexedReferencesLower (O.recordOf owner (O.registration _)) ()
indexedReferencesLower (O.recordOf owner (O.checkout _)) ()
indexedReferencesLower (O.recordOf owner (O.creationIntent _)) ()
indexedReferencesLower (O.recordOf owner (O.defaults _)) ()
indexedReferencesLower (O.recordOf owner (O.policyVersion _ _)) ()
indexedReferencesLower (O.recordOf owner (O.currentPolicy _)) ()
indexedReferencesLower (O.recordOf owner (O.note _)) ()
indexedReferencesLower (O.recordOf owner (O.notePosting _ _)) ()
indexedReferencesLower (O.recordOf owner (O.noteVector _ _)) ()
indexedReferencesLower (O.recordOf owner (O.acceptedWork _ _)) ()
indexedReferencesLower (O.recordOf owner (O.cleanupWork _ _ _)) ()
indexedReferencesLower (O.recordOf owner (O.activeReader _ _)) ()
indexedReferencesLower (O.recordOf owner (O.continuation _ _)) ()
indexedReferencesLower (O.recordOf owner (O.receipt (Receipt.entry id (Receipt.active input names work)))) ()
indexedReferencesLower (O.recordOf owner (O.receipt (Receipt.entry id (Receipt.finished input names reply)))) ()
indexedReferencesLower (O.recordOf owner (O.receipt (Receipt.entry id (Receipt.used)))) ()
indexedReferencesLower (O.recordOf owner (O.migration _)) ()
indexedReferencesLower (O.recordOf owner (O.usage _)) ()
indexedReferencesLower (O.recordOf owner (O.bootstrap _)) ()
indexedReferencesLower (O.recordOf owner (O.modelCache _)) ()
indexedReferencesLower (O.recordOf owner (O.coordination _)) ()
indexedReferencesLower (O.recordOf owner (O.schemaResource _)) ()
indexedReferencesLower (O.recordOf owner (O.logFile _)) ()
indexedReferencesLower (O.recordOf owner (O.bootstrapStage _)) ()
indexedReferencesLower (O.recordOf owner (O.fileVersion _)) proof = []
indexedReferencesLower (O.recordOf owner (O.baseBinding _ _)) proof = s≤s z≤n ∷ []
indexedReferencesLower (O.recordOf owner (O.deltaBinding _ nothing _)) proof = s≤s z≤n ∷ []
indexedReferencesLower (O.recordOf owner (O.deltaBinding _ (just _) _)) proof = s≤s z≤n ∷ s≤s z≤n ∷ []
indexedReferencesLower (O.recordOf owner (O.basePointer _)) proof = s≤s z≤n ∷ []
indexedReferencesLower (O.recordOf owner (O.chunk _ _)) proof = s≤s z≤n ∷ []
indexedReferencesLower (O.recordOf owner (O.posting _ _)) proof = s≤s (s≤s z≤n) ∷ []
indexedReferencesLower (O.recordOf owner (O.vector _ _)) proof = s≤s (s≤s z≤n) ∷ []
indexedReferencesLower (O.recordOf owner (O.symbol _ _ _)) proof = s≤s z≤n ∷ []
indexedReferencesLower (O.recordOf owner (O.edge _ _ _)) proof = s≤s (s≤s z≤n) ∷ s≤s (s≤s z≤n) ∷ []
indexedReferencesLower (O.recordOf owner (O.structuralSnapshot selected nodes edges payload)) proof =
  s≤s z≤n ∷ join (constantLower nodes O.symbolK 3 (s≤s (s≤s z≤n)))
    (constantLower edges O.edgeK 3 (s≤s (s≤s (s≤s z≤n))))
indexedReferencesLower (O.recordOf owner (O.legacy _ _)) proof = []
indexedReferencesLower (O.recordOf owner (O.staging _ _)) proof = s≤s z≤n ∷ []
indexedReferencesLower (O.recordOf owner (O.graphResource _ _ _)) proof = []

rankMaybe : Maybe O.Record → ℕ
rankMaybe nothing = zero
rankMaybe (just value) = rank (O.kind (O.body value))

rankAt : ℕ → O.World → ℕ
rankAt key world = rankMaybe (DB.lookup key world)

rankFound : ∀ key world value → DB.lookup key world ≡ just value → rankAt key world ≡ rank (O.kind (O.body value))
rankFound key world value found = cong rankMaybe found

data Down (world : O.World) : ℕ → ℕ → Set where
  link : ∀ source value ref → DB.lookup source world ≡ just value → E.indexed value ≡ true →
    ref ∈ O.references (O.body value) → O.Resolves world (O.owner value) ref → Down world source (O.target ref)

downDecreases : ∀ world {source target} → Down world source target → rankAt target world < rankAt source world
downDecreases world (link source value ref found indexed present resolved) = subst₂ _<_
  (sym (rankFound (O.target ref) world (O.Resolves.value resolved) (O.Resolves.found resolved)))
  (sym (rankFound source world value found))
  (subst (λ kind → rank kind < rank (O.kind (O.body value))) (sym (O.Resolves.rightKind resolved))
    (All.lookup (indexedReferencesLower value indexed) present))

data Chain (world : O.World) : ℕ → ℕ → Set where
  one : ∀ {source target} → Down world source target → Chain world source target
  more : ∀ {source middle target} → Down world source middle → Chain world middle target → Chain world source target

chainDecreases : ∀ world {source target} → Chain world source target → rankAt target world < rankAt source world
chainDecreases world (one edge) = downDecreases world edge
chainDecreases world (more edge rest) = <-trans (chainDecreases world rest) (downDecreases world edge)

noIndexedReferenceCycle : ∀ world key → ¬ Chain world key key
noIndexedReferenceCycle world key cycle = <-irrefl refl (chainDecreases world cycle)

-- A finite maximum supplies an actual ordering witness; progress will not be
-- an assumption that a desired cleanup edit is available.
maximum : ∀ world first rest → Σ ℕ (λ chosen → chosen ∈ (first ∷ rest) ×
  (∀ other → other ∈ (first ∷ rest) → rankAt other world ≤ rankAt chosen world))
maximum world first [] = first , here refl , λ { other (here refl) → ≤-refl }
maximum world first (second ∷ rest) with maximum world second rest
... | chosen , present , greatest with rankAt first world ≤? rankAt chosen world
...   | yes firstBelow = chosen , there present , λ { other (here refl) → firstBelow; other (there later) → greatest other later }
...   | no firstAbove = first , here refl , λ { other (here refl) → ≤-refl
      ; other (there later) → ≤-trans (greatest other later) (<⇒≤ (≰⇒> firstAbove)) }
