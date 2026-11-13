{-# OPTIONS --safe #-}
-- The effective rule comes from the actual current pointer, version and defaults.
module Muninn.StoredPolicy where

import Muninn.OwnedState as O
import Muninn.Config as Config
import Muninn.PolicyRuleAdmission as Admission
import Muninn.AdmittedSelection as Admitted
import Muninn.CatalogInputs as I
import Muninn.ExclusionOutcomes as E
open import Data.Nat using (ℕ; _≟_)
open import Data.String using (String)
open import Data.List using (_++_)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
module DB = O.DB

applyObserved : ∀ {A B : Set} (observed : A) (use : (value : A) → observed ≡ value → B)
  {value : A} (seen : observed ≡ value) → use observed refl ≡ use value seen
applyObserved observed use refl = refl

policyFrom : O.PolicyVersionInfo → O.DefaultsInfo → Config.FamilyPolicy
policyFrom info frozen = record
  { family = O.PolicyVersionInfo.familyId info
  ; name = I.PolicyDraft.name (O.PolicyVersionInfo.contents info)
  ; index = I.PolicyDraft.index (O.PolicyVersionInfo.contents info)
  ; limits = I.PolicyDraft.limits (O.PolicyVersionInfo.contents info)
  ; watcher = I.PolicyDraft.watcher (O.PolicyVersionInfo.contents info)
  ; embeddings = I.PolicyDraft.embeddings (O.PolicyVersionInfo.contents info)
  ; revision = O.PolicyVersionInfo.revision info
  ; defaults = O.DefaultsInfo.value frozen }

validFrom : ∀ info frozen → Admitted.FamilyEntries (policyFrom info frozen)
validFrom info frozen = record
  { exclude = Admission.appendStrings _ _ (O.DefaultsInfo.excludeValid frozen) (O.PolicyVersionInfo.excludeValid info)
  ; vendor = Admission.appendStrings _ _ (O.DefaultsInfo.vendorValid frozen) (O.PolicyVersionInfo.vendorValid info) }

module Family (family pointer : ℕ) where
  owner = O.family family

  record Saved (world : O.World) : Set where
    constructor saved
    field version defaultsSlot : ℕ
          info : O.PolicyVersionInfo
          frozen : O.DefaultsInfo
          pointerAt : DB.lookup pointer world ≡ just (O.recordOf owner (O.currentPolicy version))
          versionAt : DB.lookup version world ≡ just (O.recordOf owner (O.policyVersion defaultsSlot info))
          defaultsAt : DB.lookup defaultsSlot world ≡ just (O.recordOf owner (O.defaults frozen))

  policy : ∀ {world} → Saved world → Config.FamilyPolicy
  policy current = policyFrom (Saved.info current) (Saved.frozen current)

  rule : ∀ {world} → Saved world → E.Rule
  rule current = E.fromStoredPolicy family (policy current) (validFrom (Saved.info current) (Saved.frozen current))

  defaultsValue : ∀ world version initial info →
    DB.lookup pointer world ≡ just (O.recordOf owner (O.currentPolicy version)) →
    DB.lookup version world ≡ just (O.recordOf owner (O.policyVersion initial info)) →
    (value : Maybe O.Record) → DB.lookup initial world ≡ value → Maybe (Saved world)
  defaultsValue world version initial info pointerAt versionAt (just (O.recordOf actualOwner (O.defaults frozen))) defaultsAt
    with E.ownerEqual actualOwner owner
  ... | yes refl = just (saved version initial info frozen pointerAt versionAt defaultsAt)
  ... | no different = nothing
  defaultsValue world version initial info pointerAt versionAt value defaultsAt = nothing

  versionValue : ∀ world version → DB.lookup pointer world ≡ just (O.recordOf owner (O.currentPolicy version)) →
    (value : Maybe O.Record) → DB.lookup version world ≡ value → Maybe (Saved world)
  versionValue world version pointerAt (just (O.recordOf actualOwner (O.policyVersion initial info))) versionAt
    with E.ownerEqual actualOwner owner
  ... | yes refl = defaultsValue world version initial info pointerAt versionAt (DB.lookup initial world) refl
  ... | no different = nothing
  versionValue world version pointerAt value versionAt = nothing

  pointerValue : ∀ world → (value : Maybe O.Record) → DB.lookup pointer world ≡ value → Maybe (Saved world)
  pointerValue world (just (O.recordOf actualOwner (O.currentPolicy version))) pointerAt with E.ownerEqual actualOwner owner
  ... | yes refl = versionValue world version pointerAt (DB.lookup version world) refl
  ... | no different = nothing
  pointerValue world value pointerAt = nothing

  observe : (world : O.World) → Maybe (Saved world)
  observe world = pointerValue world (DB.lookup pointer world) refl

  selectedPolicy : O.World → Maybe Config.FamilyPolicy
  selectedPolicy world = map policy (observe world)

  deterministic : ∀ world (first second : Saved world) → policy first ≡ policy second
  deterministic world (saved version initial info frozen pointerAt versionAt defaultsAt)
    (saved otherVersion otherInitial otherInfo otherFrozen otherPointer otherAt otherDefaults)
    with just-injective (trans (sym pointerAt) otherPointer)
  ... | refl with just-injective (trans (sym versionAt) otherAt)
  ...   | refl with just-injective (trans (sym defaultsAt) otherDefaults)
  ...     | refl = refl

  defaultsExact : ∀ world version initial info frozen pointerAt versionAt defaultsAt →
    map policy (defaultsValue world version initial info pointerAt versionAt (just (O.recordOf owner (O.defaults frozen))) defaultsAt) ≡
      just (policyFrom info frozen)
  defaultsExact world version initial info frozen pointerAt versionAt defaultsAt with E.ownerEqual owner owner
  ... | yes refl = refl
  ... | no different = ⊥-elim (different refl)

  versionExact : ∀ world version initial info frozen pointerAt versionAt →
    DB.lookup initial world ≡ just (O.recordOf owner (O.defaults frozen)) →
    map policy (versionValue world version pointerAt (just (O.recordOf owner (O.policyVersion initial info))) versionAt) ≡
      just (policyFrom info frozen)
  versionExact world version initial info frozen pointerAt versionAt defaultsAt with E.ownerEqual owner owner
  ... | yes refl = trans
    (cong (map policy) (applyObserved (DB.lookup initial world) (defaultsValue world version initial info pointerAt versionAt) defaultsAt))
    (defaultsExact world version initial info frozen pointerAt versionAt defaultsAt)
  ... | no different = ⊥-elim (different refl)

  pointerExact : ∀ world version initial info frozen pointerAt →
    DB.lookup version world ≡ just (O.recordOf owner (O.policyVersion initial info)) →
    DB.lookup initial world ≡ just (O.recordOf owner (O.defaults frozen)) →
    map policy (pointerValue world (just (O.recordOf owner (O.currentPolicy version))) pointerAt) ≡ just (policyFrom info frozen)
  pointerExact world version initial info frozen pointerAt versionAt defaultsAt with E.ownerEqual owner owner
  ... | yes refl = trans
    (cong (map policy) (applyObserved (DB.lookup version world) (versionValue world version pointerAt) versionAt))
    (versionExact world version initial info frozen pointerAt versionAt defaultsAt)
  ... | no different = ⊥-elim (different refl)

  selectsKnown : ∀ world version initial info frozen →
    DB.lookup pointer world ≡ just (O.recordOf owner (O.currentPolicy version)) →
    DB.lookup version world ≡ just (O.recordOf owner (O.policyVersion initial info)) →
    DB.lookup initial world ≡ just (O.recordOf owner (O.defaults frozen)) →
    selectedPolicy world ≡ just (policyFrom info frozen)
  selectsKnown world version initial info frozen pointerAt versionAt defaultsAt = trans
    (cong (map policy) (applyObserved (DB.lookup pointer world) (pointerValue world) pointerAt))
    (pointerExact world version initial info frozen pointerAt versionAt defaultsAt)

  effectiveExclusions : ∀ world (current : Saved world) → E.exclusions (rule current) ≡
    Config.IndexConfig.exclude (Config.PolicyDefaults.rules (O.DefaultsInfo.value (Saved.frozen current))) ++
    Config.IndexConfig.exclude (I.PolicyDraft.index (O.PolicyVersionInfo.contents (Saved.info current)))
  effectiveExclusions world current = refl

  dispatch : ∀ {A : Set} (world : O.World) → Maybe (Saved world) →
    (E.Rule → DB.Transaction A) → (O.World → DB.Transaction A) → DB.Transaction A
  dispatch world nothing next replan = replan world
  dispatch world (just current) next replan = next (rule current)

  withCurrent : ∀ {A : Set} → (E.Rule → DB.Transaction A) → (O.World → DB.Transaction A) → DB.Transaction A
  withCurrent next replan = DB.scan (λ world → dispatch world (observe world) next replan)

  usesCurrent : ∀ {A : Set} world (current : Saved world) (next : E.Rule → DB.Transaction A) replan →
    observe world ≡ just current → DB.evaluate (withCurrent next replan) world ≡ DB.evaluate (next (rule current)) world
  usesCurrent world current next replan observed rewrite observed = refl

  needsContext : ∀ {A : Set} world (next : E.Rule → DB.Transaction A) replan → observe world ≡ nothing →
    DB.evaluate (withCurrent next replan) world ≡ DB.evaluate (replan world) world
  needsContext world next replan missing rewrite missing = refl

  missingKeepsWorld : ∀ {A : Set} world (next : E.Rule → DB.Transaction A) continuation → observe world ≡ nothing →
    DB.execute (withCurrent next (λ current → DB.abort continuation)) world ≡ (continuation , world)
  missingKeepsWorld world next continuation missing =
    cong (λ outcome → DB.reply outcome , DB.publish world outcome)
      (needsContext world next (λ current → DB.abort continuation) missing)

  retainedValue : ∀ {A : Set} (world : O.World) → Maybe (Saved world) → ℕ → ℕ →
    (E.Rule → DB.Transaction A) → (E.Rule → DB.Transaction A) → (O.World → DB.Transaction A) → DB.Transaction A
  retainedValue world nothing expected revision next reconsider replan = replan world
  retainedValue world (just current) expected revision next reconsider replan
    with expected ≟ Saved.version current | revision ≟ O.PolicyVersionInfo.revision (Saved.info current)
  ... | yes same | yes matched = next (rule current)
  ... | _ | _ = reconsider (rule current)

  withRetained : ∀ {A : Set} → ℕ → ℕ → (E.Rule → DB.Transaction A) →
    (E.Rule → DB.Transaction A) → (O.World → DB.Transaction A) → DB.Transaction A
  withRetained expected revision next reconsider replan = DB.scan (λ world → retainedValue world (observe world) expected revision next reconsider replan)

  staleVersion : ∀ {A : Set} world (current : Saved world) expected revision (next reconsider : E.Rule → DB.Transaction A) replan →
    observe world ≡ just current → expected ≢ Saved.version current →
    DB.evaluate (withRetained expected revision next reconsider replan) world ≡ DB.evaluate (reconsider (rule current)) world
  staleVersion world current expected revision next reconsider replan observed stale rewrite observed
    with expected ≟ Saved.version current | revision ≟ O.PolicyVersionInfo.revision (Saved.info current)
  ... | yes same | _ = ⊥-elim (stale same)
  ... | no different | _ = refl

  staleRevision : ∀ {A : Set} world (current : Saved world) expected revision (next reconsider : E.Rule → DB.Transaction A) replan →
    observe world ≡ just current → revision ≢ O.PolicyVersionInfo.revision (Saved.info current) →
    DB.evaluate (withRetained expected revision next reconsider replan) world ≡ DB.evaluate (reconsider (rule current)) world
  staleRevision world current expected revision next reconsider replan observed stale rewrite observed
    with expected ≟ Saved.version current | revision ≟ O.PolicyVersionInfo.revision (Saved.info current)
  ... | yes same | yes matched = ⊥-elim (stale matched)
  ... | yes same | no different = refl
  ... | no different | _ = refl

  retainedCurrent : ∀ {A : Set} world (current : Saved world) (next reconsider : E.Rule → DB.Transaction A) replan →
    observe world ≡ just current →
    DB.evaluate (withRetained (Saved.version current) (O.PolicyVersionInfo.revision (Saved.info current)) next reconsider replan) world ≡
      DB.evaluate (next (rule current)) world
  retainedCurrent world current next reconsider replan observed rewrite observed
    with Saved.version current ≟ Saved.version current | O.PolicyVersionInfo.revision (Saved.info current) ≟ O.PolicyVersionInfo.revision (Saved.info current)
  ... | yes same | yes matched = refl
  ... | no different | _ = ⊥-elim (different refl)
  ... | _ | no different = ⊥-elim (different refl)
