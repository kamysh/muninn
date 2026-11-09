{-# OPTIONS --safe #-}
-- Identity is the complete typed meaning, independent of its transport.
module Muninn.RequestIdentity where

open import Muninn.CatalogInputs
import Muninn.Catalog as Catalog
open import Muninn.RequestCodecs
open import Muninn.Canonical
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
import Relation.Nullary

data MutationKind : Set where
  kReplaceGlobal kApplyPolicy kRegister kStart kReindex kPause kResume kCancel kUnregister kForget kRecreateIndex kConvertDirectory kWriteNote kDeleteNote : MutationKind

intent : MutationKind → Intent
intent kReplaceGlobal = replaceGlobal
intent kApplyPolicy = applyPolicy
intent kRegister = register
intent kStart = start
intent kReindex = reindex
intent kPause = pause
intent kResume = resume
intent kCancel = cancel
intent kUnregister = unregister
intent kForget = forget
intent kRecreateIndex = recreateIndex
intent kConvertDirectory = convertDirectory
intent kWriteNote = writeNote
intent kDeleteNote = deleteNote

data Meaning : Set where
  mutation : (kind : MutationKind) → IntentInput (intent kind) → Meaning
  durableJob : (job : Job) → JobInput job → Meaning

-- Each mutation constructor carries its entire existing typed payload.
userMeaning : (i : Intent) → IntentInput i → Maybe Meaning
userMeaning inspectGlobal input = nothing
userMeaning replaceGlobal input = just (mutation kReplaceGlobal input)
userMeaning inspectPolicy input = nothing
userMeaning checkPolicy input = nothing
userMeaning applyPolicy input = just (mutation kApplyPolicy input)
userMeaning preflight input = nothing
userMeaning register input = just (mutation kRegister input)
userMeaning start input = just (mutation kStart input)
userMeaning reindex input = just (mutation kReindex input)
userMeaning pause input = just (mutation kPause input)
userMeaning resume input = just (mutation kResume input)
userMeaning cancel input = just (mutation kCancel input)
userMeaning unregister input = just (mutation kUnregister input)
userMeaning forget input = just (mutation kForget input)
userMeaning recreateIndex input = just (mutation kRecreateIndex input)
userMeaning convertDirectory input = just (mutation kConvertDirectory input)
userMeaning status input = nothing
userMeaning usage input = nothing
userMeaning (searchCode mode) input = nothing
userMeaning searchStructure input = nothing
userMeaning writeNote input = just (mutation kWriteNote input)
userMeaning searchNotes input = nothing
userMeaning deleteNote input = just (mutation kDeleteNote input)
userMeaning listNotes input = nothing
userMeaning continueRequest input = nothing

-- Reconstruct the independent typed input; encoding does not define sameness.
originalPublic : Meaning → Maybe (Σ Intent IntentInput)
originalPublic (mutation kind input) = just (intent kind , input)
originalPublic (durableJob job input) = nothing

preservesPublicInput : ∀ kind input →
  originalPublic (mutation kind input) ≡ just (intent kind , input)
preservesPublicInput kind input = refl

classifiedWithoutLoss : ∀ kind input →
  userMeaning (intent kind) input ≡ just (mutation kind input)
classifiedWithoutLoss kReplaceGlobal input = refl
classifiedWithoutLoss kApplyPolicy input = refl
classifiedWithoutLoss kRegister input = refl
classifiedWithoutLoss kStart input = refl
classifiedWithoutLoss kReindex input = refl
classifiedWithoutLoss kPause input = refl
classifiedWithoutLoss kResume input = refl
classifiedWithoutLoss kCancel input = refl
classifiedWithoutLoss kUnregister input = refl
classifiedWithoutLoss kForget input = refl
classifiedWithoutLoss kRecreateIndex input = refl
classifiedWithoutLoss kConvertDirectory input = refl
classifiedWithoutLoss kWriteNote input = refl
classifiedWithoutLoss kDeleteNote input = refl

normalize : Catalog.Request → Maybe Meaning
normalize (Catalog.user adapter input) = userMeaning (Catalog.canonicalIntent adapter) input
normalize (Catalog.background job input) = just (durableJob job input)
normalize (Catalog.control event input) = nothing
normalize (Catalog.localUi input) = nothing

-- Read/control/UI requests do not acquire permanent used-ID markers.
-- Work arranged by those requests has a separately registered job identity.
sameTransportMeaning : ∀ first second firstInput secondInput →
  (Catalog.canonicalIntent first , firstInput) ≡
    (Catalog.canonicalIntent second , secondInput) →
  normalize (Catalog.user first firstInput) ≡
    normalize (Catalog.user second secondInput)
sameTransportMeaning first second firstInput secondInput same =
  cong (λ { (i , input) → userMeaning i input }) same

meaning : Codec Meaning
encode meaning (mutation kReplaceGlobal x0) = sequence (text "mutation kReplaceGlobal" ∷ encode (mutationInput globalSettings) x0 ∷ [])
encode meaning (mutation kApplyPolicy x0) = sequence (text "mutation kApplyPolicy" ∷ encode (mutationInput (pair policyTarget policyDraft)) x0 ∷ [])
encode meaning (mutation kRegister x0) = sequence (text "mutation kRegister" ∷ encode (mutationInput (pair locator policyDraft)) x0 ∷ [])
encode meaning (mutation kStart x0) = sequence (text "mutation kStart" ∷ encode (mutationInput policyTarget) x0 ∷ [])
encode meaning (mutation kReindex x0) = sequence (text "mutation kReindex" ∷ encode (mutationInput reindexTarget) x0 ∷ [])
encode meaning (mutation kPause x0) = sequence (text "mutation kPause" ∷ encode (mutationInput familyTarget) x0 ∷ [])
encode meaning (mutation kResume x0) = sequence (text "mutation kResume" ∷ encode (mutationInput familyTarget) x0 ∷ [])
encode meaning (mutation kCancel x0) = sequence (text "mutation kCancel" ∷ encode (mutationInput (pair familyTarget operationId)) x0 ∷ [])
encode meaning (mutation kUnregister x0) = sequence (text "mutation kUnregister" ∷ encode (mutationInput familyTarget) x0 ∷ [])
encode meaning (mutation kForget x0) = sequence (text "mutation kForget" ∷ encode (mutationInput familyTarget) x0 ∷ [])
encode meaning (mutation kRecreateIndex x0) = sequence (text "mutation kRecreateIndex" ∷ encode (mutationInput (pair familyTarget embedding)) x0 ∷ [])
encode meaning (mutation kConvertDirectory x0) = sequence (text "mutation kConvertDirectory" ∷ encode (mutationInput familyTarget) x0 ∷ [])
encode meaning (mutation kWriteNote x0) = sequence (text "mutation kWriteNote" ∷ encode (mutationInput noteInput) x0 ∷ [])
encode meaning (mutation kDeleteNote x0) = sequence (text "mutation kDeleteNote" ∷ encode (mutationInput (pair familyTarget knowledgeId)) x0 ∷ [])
encode meaning (durableJob preparePublic x0) = sequence (text "durableJob preparePublic" ∷ encode bootstrap x0 ∷ [])
encode meaning (durableJob prepareFamily x0) = sequence (text "durableJob prepareFamily" ∷ encode familyJob x0 ∷ [])
encode meaning (durableJob prepareGraph x0) = sequence (text "durableJob prepareGraph" ∷ encode (pair familyJob (optional checkoutId)) x0 ∷ [])
encode meaning (durableJob fleetScan x0) = sequence (text "durableJob fleetScan" ∷ encode operationId x0 ∷ [])
encode meaning (durableJob discoverCheckouts x0) = sequence (text "durableJob discoverCheckouts" ∷ encode familyJob x0 ∷ [])
encode meaning (durableJob observeCheckout x0) = sequence (text "durableJob observeCheckout" ∷ encode checkoutJob x0 ∷ [])
encode meaning (durableJob reconcileFamily x0) = sequence (text "durableJob reconcileFamily" ∷ encode familyJob x0 ∷ [])
encode meaning (durableJob reconcileCheckout x0) = sequence (text "durableJob reconcileCheckout" ∷ encode checkoutJob x0 ∷ [])
encode meaning (durableJob watchBatch x0) = sequence (text "durableJob watchBatch" ∷ encode (pair familyJob (optional (list path))) x0 ∷ [])
encode meaning (durableJob analyzeFile x0) = sequence (text "durableJob analyzeFile" ∷ encode fileJob x0 ∷ [])
encode meaning (durableJob publishCheckout x0) = sequence (text "durableJob publishCheckout" ∷ encode checkoutJob x0 ∷ [])
encode meaning (durableJob embedCode x0) = sequence (text "durableJob embedCode" ∷ encode (pair familyJob versionId) x0 ∷ [])
encode meaning (durableJob embedNote x0) = sequence (text "durableJob embedNote" ∷ encode (pair familyJob knowledgeId) x0 ∷ [])
encode meaning (durableJob reclaimExcluded x0) = sequence (text "durableJob reclaimExcluded" ∷ encode familyJob x0 ∷ [])
encode meaning (durableJob reclaimRetired x0) = sequence (text "durableJob reclaimRetired" ∷ encode familyJob x0 ∷ [])
encode meaning (durableJob handoff x0) = sequence (text "durableJob handoff" ∷ encode familyJob x0 ∷ [])
encode meaning (durableJob recoverOperation x0) = sequence (text "durableJob recoverOperation" ∷ encode operationId x0 ∷ [])
encode meaning (durableJob recordUsage x0) = sequence (text "durableJob recordUsage" ∷ encode usageInput x0 ∷ [])
encode meaning (durableJob appendLog x0) = sequence (text "durableJob appendLog" ∷ encode string x0 ∷ [])
encode meaning (durableJob pruneLogs x0) = sequence (text "durableJob pruneLogs" ∷ encode nat x0 ∷ [])
encode meaning (durableJob flushDiagnostics x0) = sequence (text "durableJob flushDiagnostics" ∷ encode unit x0 ∷ [])
decode meaning (sequence (text "mutation kReplaceGlobal" ∷ v0 ∷ [])) = Maybe.map (mutation kReplaceGlobal) (decode (mutationInput globalSettings) v0)
decode meaning (sequence (text "mutation kApplyPolicy" ∷ v0 ∷ [])) = Maybe.map (mutation kApplyPolicy) (decode (mutationInput (pair policyTarget policyDraft)) v0)
decode meaning (sequence (text "mutation kRegister" ∷ v0 ∷ [])) = Maybe.map (mutation kRegister) (decode (mutationInput (pair locator policyDraft)) v0)
decode meaning (sequence (text "mutation kStart" ∷ v0 ∷ [])) = Maybe.map (mutation kStart) (decode (mutationInput policyTarget) v0)
decode meaning (sequence (text "mutation kReindex" ∷ v0 ∷ [])) = Maybe.map (mutation kReindex) (decode (mutationInput reindexTarget) v0)
decode meaning (sequence (text "mutation kPause" ∷ v0 ∷ [])) = Maybe.map (mutation kPause) (decode (mutationInput familyTarget) v0)
decode meaning (sequence (text "mutation kResume" ∷ v0 ∷ [])) = Maybe.map (mutation kResume) (decode (mutationInput familyTarget) v0)
decode meaning (sequence (text "mutation kCancel" ∷ v0 ∷ [])) = Maybe.map (mutation kCancel) (decode (mutationInput (pair familyTarget operationId)) v0)
decode meaning (sequence (text "mutation kUnregister" ∷ v0 ∷ [])) = Maybe.map (mutation kUnregister) (decode (mutationInput familyTarget) v0)
decode meaning (sequence (text "mutation kForget" ∷ v0 ∷ [])) = Maybe.map (mutation kForget) (decode (mutationInput familyTarget) v0)
decode meaning (sequence (text "mutation kRecreateIndex" ∷ v0 ∷ [])) = Maybe.map (mutation kRecreateIndex) (decode (mutationInput (pair familyTarget embedding)) v0)
decode meaning (sequence (text "mutation kConvertDirectory" ∷ v0 ∷ [])) = Maybe.map (mutation kConvertDirectory) (decode (mutationInput familyTarget) v0)
decode meaning (sequence (text "mutation kWriteNote" ∷ v0 ∷ [])) = Maybe.map (mutation kWriteNote) (decode (mutationInput noteInput) v0)
decode meaning (sequence (text "mutation kDeleteNote" ∷ v0 ∷ [])) = Maybe.map (mutation kDeleteNote) (decode (mutationInput (pair familyTarget knowledgeId)) v0)
decode meaning (sequence (text "durableJob preparePublic" ∷ v0 ∷ [])) = Maybe.map (durableJob preparePublic) (decode bootstrap v0)
decode meaning (sequence (text "durableJob prepareFamily" ∷ v0 ∷ [])) = Maybe.map (durableJob prepareFamily) (decode familyJob v0)
decode meaning (sequence (text "durableJob prepareGraph" ∷ v0 ∷ [])) = Maybe.map (durableJob prepareGraph) (decode (pair familyJob (optional checkoutId)) v0)
decode meaning (sequence (text "durableJob fleetScan" ∷ v0 ∷ [])) = Maybe.map (durableJob fleetScan) (decode operationId v0)
decode meaning (sequence (text "durableJob discoverCheckouts" ∷ v0 ∷ [])) = Maybe.map (durableJob discoverCheckouts) (decode familyJob v0)
decode meaning (sequence (text "durableJob observeCheckout" ∷ v0 ∷ [])) = Maybe.map (durableJob observeCheckout) (decode checkoutJob v0)
decode meaning (sequence (text "durableJob reconcileFamily" ∷ v0 ∷ [])) = Maybe.map (durableJob reconcileFamily) (decode familyJob v0)
decode meaning (sequence (text "durableJob reconcileCheckout" ∷ v0 ∷ [])) = Maybe.map (durableJob reconcileCheckout) (decode checkoutJob v0)
decode meaning (sequence (text "durableJob watchBatch" ∷ v0 ∷ [])) = Maybe.map (durableJob watchBatch) (decode (pair familyJob (optional (list path))) v0)
decode meaning (sequence (text "durableJob analyzeFile" ∷ v0 ∷ [])) = Maybe.map (durableJob analyzeFile) (decode fileJob v0)
decode meaning (sequence (text "durableJob publishCheckout" ∷ v0 ∷ [])) = Maybe.map (durableJob publishCheckout) (decode checkoutJob v0)
decode meaning (sequence (text "durableJob embedCode" ∷ v0 ∷ [])) = Maybe.map (durableJob embedCode) (decode (pair familyJob versionId) v0)
decode meaning (sequence (text "durableJob embedNote" ∷ v0 ∷ [])) = Maybe.map (durableJob embedNote) (decode (pair familyJob knowledgeId) v0)
decode meaning (sequence (text "durableJob reclaimExcluded" ∷ v0 ∷ [])) = Maybe.map (durableJob reclaimExcluded) (decode familyJob v0)
decode meaning (sequence (text "durableJob reclaimRetired" ∷ v0 ∷ [])) = Maybe.map (durableJob reclaimRetired) (decode familyJob v0)
decode meaning (sequence (text "durableJob handoff" ∷ v0 ∷ [])) = Maybe.map (durableJob handoff) (decode familyJob v0)
decode meaning (sequence (text "durableJob recoverOperation" ∷ v0 ∷ [])) = Maybe.map (durableJob recoverOperation) (decode operationId v0)
decode meaning (sequence (text "durableJob recordUsage" ∷ v0 ∷ [])) = Maybe.map (durableJob recordUsage) (decode usageInput v0)
decode meaning (sequence (text "durableJob appendLog" ∷ v0 ∷ [])) = Maybe.map (durableJob appendLog) (decode string v0)
decode meaning (sequence (text "durableJob pruneLogs" ∷ v0 ∷ [])) = Maybe.map (durableJob pruneLogs) (decode nat v0)
decode meaning (sequence (text "durableJob flushDiagnostics" ∷ v0 ∷ [])) = Maybe.map (durableJob flushDiagnostics) (decode unit v0)
decode meaning _ = nothing
roundTrip meaning (mutation kReplaceGlobal x0) rewrite roundTrip (mutationInput globalSettings) x0 = refl
roundTrip meaning (mutation kApplyPolicy x0) rewrite roundTrip (mutationInput (pair policyTarget policyDraft)) x0 = refl
roundTrip meaning (mutation kRegister x0) rewrite roundTrip (mutationInput (pair locator policyDraft)) x0 = refl
roundTrip meaning (mutation kStart x0) rewrite roundTrip (mutationInput policyTarget) x0 = refl
roundTrip meaning (mutation kReindex x0) rewrite roundTrip (mutationInput reindexTarget) x0 = refl
roundTrip meaning (mutation kPause x0) rewrite roundTrip (mutationInput familyTarget) x0 = refl
roundTrip meaning (mutation kResume x0) rewrite roundTrip (mutationInput familyTarget) x0 = refl
roundTrip meaning (mutation kCancel x0) rewrite roundTrip (mutationInput (pair familyTarget operationId)) x0 = refl
roundTrip meaning (mutation kUnregister x0) rewrite roundTrip (mutationInput familyTarget) x0 = refl
roundTrip meaning (mutation kForget x0) rewrite roundTrip (mutationInput familyTarget) x0 = refl
roundTrip meaning (mutation kRecreateIndex x0) rewrite roundTrip (mutationInput (pair familyTarget embedding)) x0 = refl
roundTrip meaning (mutation kConvertDirectory x0) rewrite roundTrip (mutationInput familyTarget) x0 = refl
roundTrip meaning (mutation kWriteNote x0) rewrite roundTrip (mutationInput noteInput) x0 = refl
roundTrip meaning (mutation kDeleteNote x0) rewrite roundTrip (mutationInput (pair familyTarget knowledgeId)) x0 = refl
roundTrip meaning (durableJob preparePublic x0) rewrite roundTrip bootstrap x0 = refl
roundTrip meaning (durableJob prepareFamily x0) rewrite roundTrip familyJob x0 = refl
roundTrip meaning (durableJob prepareGraph x0) rewrite roundTrip (pair familyJob (optional checkoutId)) x0 = refl
roundTrip meaning (durableJob fleetScan x0) rewrite roundTrip operationId x0 = refl
roundTrip meaning (durableJob discoverCheckouts x0) rewrite roundTrip familyJob x0 = refl
roundTrip meaning (durableJob observeCheckout x0) rewrite roundTrip checkoutJob x0 = refl
roundTrip meaning (durableJob reconcileFamily x0) rewrite roundTrip familyJob x0 = refl
roundTrip meaning (durableJob reconcileCheckout x0) rewrite roundTrip checkoutJob x0 = refl
roundTrip meaning (durableJob watchBatch x0) rewrite roundTrip (pair familyJob (optional (list path))) x0 = refl
roundTrip meaning (durableJob analyzeFile x0) rewrite roundTrip fileJob x0 = refl
roundTrip meaning (durableJob publishCheckout x0) rewrite roundTrip checkoutJob x0 = refl
roundTrip meaning (durableJob embedCode x0) rewrite roundTrip (pair familyJob versionId) x0 = refl
roundTrip meaning (durableJob embedNote x0) rewrite roundTrip (pair familyJob knowledgeId) x0 = refl
roundTrip meaning (durableJob reclaimExcluded x0) rewrite roundTrip familyJob x0 = refl
roundTrip meaning (durableJob reclaimRetired x0) rewrite roundTrip familyJob x0 = refl
roundTrip meaning (durableJob handoff x0) rewrite roundTrip familyJob x0 = refl
roundTrip meaning (durableJob recoverOperation x0) rewrite roundTrip operationId x0 = refl
roundTrip meaning (durableJob recordUsage x0) rewrite roundTrip usageInput x0 = refl
roundTrip meaning (durableJob appendLog x0) rewrite roundTrip string x0 = refl
roundTrip meaning (durableJob pruneLogs x0) rewrite roundTrip nat x0 = refl
roundTrip meaning (durableJob flushDiagnostics x0) rewrite roundTrip unit x0 = refl

-- Equality of canonical content implies equality of the complete typed input.
contentFaithful : ∀ {first second} →
  encode meaning first ≡ encode meaning second → first ≡ second
contentFaithful = faithful meaning

sameRequest : (first second : Meaning) → Relation.Nullary.Dec (first ≡ second)
sameRequest = compare meaning
