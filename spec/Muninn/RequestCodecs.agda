{-# OPTIONS --safe #-}
-- Complete typed payload codecs. Each record transport must prove its inverse.
module Muninn.RequestCodecs where

import Muninn.FileLimits as FileLimits

open import Muninn.Canonical
open import Muninn.CatalogInputs
open import Muninn.Types using (UUID; FilePath)
open import Muninn.Worktree using (FamilyId; CheckoutId; VersionId)
open import Muninn.Knowledge using (KnowledgeId)
open import Muninn.Config using (SslMode; Disable; Allow; Prefer; Require; VerifyCa; VerifyFull; DbConfig; WatcherConfig; EmbeddingSelection; IndexConfig; McpLogConfig; McpConfig; BootstrapConfig)
open import Muninn.Embeddings using (EmbeddingBackend; Voyage; OpenAI; Local)
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (just; nothing)
import Data.Maybe as Maybe
open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (refl)

sslMode : Codec SslMode
encode sslMode (Disable) = sequence (natural 0 ∷ [])
encode sslMode (Allow) = sequence (natural 1 ∷ [])
encode sslMode (Prefer) = sequence (natural 2 ∷ [])
encode sslMode (Require) = sequence (natural 3 ∷ [])
encode sslMode (VerifyCa) = sequence (natural 4 ∷ [])
encode sslMode (VerifyFull) = sequence (natural 5 ∷ [])
decode sslMode (sequence (natural 0 ∷ [])) = just (Disable)
decode sslMode (sequence (natural 1 ∷ [])) = just (Allow)
decode sslMode (sequence (natural 2 ∷ [])) = just (Prefer)
decode sslMode (sequence (natural 3 ∷ [])) = just (Require)
decode sslMode (sequence (natural 4 ∷ [])) = just (VerifyCa)
decode sslMode (sequence (natural 5 ∷ [])) = just (VerifyFull)
decode sslMode _ = nothing
roundTrip sslMode (Disable) = refl
roundTrip sslMode (Allow) = refl
roundTrip sslMode (Prefer) = refl
roundTrip sslMode (Require) = refl
roundTrip sslMode (VerifyCa) = refl
roundTrip sslMode (VerifyFull) = refl

backend : Codec EmbeddingBackend
encode backend (Voyage) = sequence (natural 0 ∷ [])
encode backend (OpenAI) = sequence (natural 1 ∷ [])
encode backend (Local) = sequence (natural 2 ∷ [])
decode backend (sequence (natural 0 ∷ [])) = just (Voyage)
decode backend (sequence (natural 1 ∷ [])) = just (OpenAI)
decode backend (sequence (natural 2 ∷ [])) = just (Local)
decode backend _ = nothing
roundTrip backend (Voyage) = refl
roundTrip backend (OpenAI) = refl
roundTrip backend (Local) = refl

uuid : Codec (UUID)
uuid = transport
  (λ r → UUID.value r)
  (λ x0 → record { value = x0 })
  (λ r → refl) string

path : Codec (FilePath)
path = transport
  (λ r → FilePath.value r)
  (λ x0 → record { value = x0 })
  (λ r → refl) string

familyId : Codec (FamilyId)
familyId = transport
  (λ r → FamilyId.value r)
  (λ x0 → record { value = x0 })
  (λ r → refl) uuid

checkoutId : Codec (CheckoutId)
checkoutId = transport
  (λ r → CheckoutId.value r)
  (λ x0 → record { value = x0 })
  (λ r → refl) uuid

versionId : Codec (VersionId)
versionId = transport
  (λ r → VersionId.value r)
  (λ x0 → record { value = x0 })
  (λ r → refl) uuid

knowledgeId : Codec (KnowledgeId)
knowledgeId = transport
  (λ r → KnowledgeId.value r)
  (λ x0 → record { value = x0 })
  (λ r → refl) uuid

operationId : Codec (OperationId)
operationId = transport
  (λ r → OperationId.value r)
  (λ x0 → record { value = x0 })
  (λ r → refl) uuid

locator : Codec Locator
encode locator (repository x0) = sequence (natural 0 ∷ encode path x0 ∷ [])
encode locator (cwd x0) = sequence (natural 1 ∷ encode path x0 ∷ [])
decode locator (sequence (natural 0 ∷ v0 ∷ [])) = Maybe.map (repository) (decode path v0)
decode locator (sequence (natural 1 ∷ v0 ∷ [])) = Maybe.map (cwd) (decode path v0)
decode locator _ = nothing
roundTrip locator (repository x0) rewrite roundTrip path x0 = refl
roundTrip locator (cwd x0) rewrite roundTrip path x0 = refl

dbConfig : Codec (DbConfig)
dbConfig = transport
  (λ r → (DbConfig.host r , (DbConfig.port r , (DbConfig.dbname r , (DbConfig.user r , (DbConfig.password r , (DbConfig.pgpassfile r , (DbConfig.dsnOverride r , (DbConfig.sslMode r , (DbConfig.sslRootCert r , (DbConfig.sslClientCert r , (DbConfig.sslClientKey r , (DbConfig.maxConnections r , (DbConfig.connectTimeout r , DbConfig.applicationName r))))))))))))))
  (λ (x0 , (x1 , (x2 , (x3 , (x4 , (x5 , (x6 , (x7 , (x8 , (x9 , (x10 , (x11 , (x12 , x13))))))))))))) → record { host = x0; port = x1; dbname = x2; user = x3; password = x4; pgpassfile = x5; dsnOverride = x6; sslMode = x7; sslRootCert = x8; sslClientCert = x9; sslClientKey = x10; maxConnections = x11; connectTimeout = x12; applicationName = x13 })
  (λ r → refl) (pair string (pair nat (pair string (pair string (pair (optional string) (pair (optional path) (pair (optional string) (pair (optional sslMode) (pair (optional path) (pair (optional path) (pair (optional path) (pair (optional nat) (pair (optional nat) (optional string))))))))))))))

watcher : Codec (WatcherConfig)
watcher = transport
  (λ r → WatcherConfig.debounceMs r)
  (λ x0 → record { debounceMs = x0 })
  (λ r → refl) nat

embedding : Codec (EmbeddingSelection)
embedding = transport
  (λ r → (EmbeddingSelection.backend r , (EmbeddingSelection.model r , EmbeddingSelection.batchSize r)))
  (λ (x0 , (x1 , x2)) → record { backend = x0; model = x1; batchSize = x2 })
  (λ r → refl) (pair backend (pair (optional string) nat))

fileLimits : Codec FileLimits.Limits
fileLimits = transport
  (λ r → FileLimits.Limits.fileBytes r , FileLimits.Limits.structuralBytes r)
  (λ (file , structural) → FileLimits.limits file structural)
  (λ r → refl) (pair nat nat)

index : Codec (IndexConfig)
index = transport
  (λ r → (IndexConfig.exclude r , (IndexConfig.vendor r , IndexConfig.limits r)))
  (λ (x0 , (x1 , x2)) → record { exclude = x0; vendor = x1; limits = x2 })
  (λ r → refl) (pair (list string) (pair (list string) (optional fileLimits)))

logging : Codec (McpLogConfig)
logging = transport
  (λ r → (McpLogConfig.enabled r , (McpLogConfig.dir r , (McpLogConfig.retentionDays r , McpLogConfig.pruneIntervalHours r))))
  (λ (x0 , (x1 , (x2 , x3))) → record { enabled = x0; dir = x1; retentionDays = x2; pruneIntervalHours = x3 })
  (λ r → refl) (pair bool (pair string (pair nat nat)))

mcpSettings : Codec (McpConfig)
mcpSettings = transport
  (λ r → (McpConfig.recordUsage r , McpConfig.logging r))
  (λ (x0 , x1) → record { recordUsage = x0; logging = x1 })
  (λ r → refl) (pair bool logging)

bootstrap : Codec (BootstrapConfig)
bootstrap = transport
  (λ r → (BootstrapConfig.database r , (BootstrapConfig.embeddingApiKey r , (BootstrapConfig.embeddingCacheDir r , BootstrapConfig.mcp r))))
  (λ (x0 , (x1 , (x2 , x3))) → record { database = x0; embeddingApiKey = x1; embeddingCacheDir = x2; mcp = x3 })
  (λ r → refl) (pair dbConfig (pair (optional string) (pair (optional path) mcpSettings)))

familyTarget : Codec (FamilyTarget)
familyTarget = transport
  (λ r → (FamilyTarget.location r , FamilyTarget.expectedFamily r))
  (λ (x0 , x1) → record { location = x0; expectedFamily = x1 })
  (λ r → refl) (pair locator familyId)

policyTarget : Codec (PolicyTarget)
policyTarget = transport
  (λ r → (PolicyTarget.target r , PolicyTarget.expectedRevision r))
  (λ (x0 , x1) → record { target = x0; expectedRevision = x1 })
  (λ r → refl) (pair familyTarget nat)

policyDraft : Codec (PolicyDraft)
policyDraft = transport
  (λ r → (PolicyDraft.name r , (PolicyDraft.index r , (PolicyDraft.watcher r , PolicyDraft.embeddings r))))
  (λ (x0 , (x1 , (x2 , x3))) → record { name = x0; index = x1; watcher = x2; embeddings = x3 })
  (λ r → refl) (pair string (pair index (pair watcher embedding)))

globalSettings : Codec (GlobalSettings)
globalSettings = transport
  (λ r → (GlobalSettings.bootstrap r , (GlobalSettings.defaultIndex r , (GlobalSettings.defaultWatcher r , GlobalSettings.defaultEmbeddings r))))
  (λ (x0 , (x1 , (x2 , x3))) → record { bootstrap = x0; defaultIndex = x1; defaultWatcher = x2; defaultEmbeddings = x3 })
  (λ r → refl) (pair bootstrap (pair index (pair watcher embedding)))

noteInput : Codec (NoteInput)
noteInput = transport
  (λ r → (NoteInput.target r , (NoteInput.id r , (NoteInput.origin r , (NoteInput.title r , (NoteInput.body r , (NoteInput.tags r , NoteInput.relatedFiles r)))))))
  (λ (x0 , (x1 , (x2 , (x3 , (x4 , (x5 , x6)))))) → record { target = x0; id = x1; origin = x2; title = x3; body = x4; tags = x5; relatedFiles = x6 })
  (λ r → refl) (pair familyTarget (pair (optional knowledgeId) (pair (optional path) (pair string (pair string (pair (list string) (list path)))))))

reindexTarget : Codec ReindexTarget
encode reindexTarget (foregroundIndex x0) = sequence (natural 0 ∷ encode familyTarget x0 ∷ [])
encode reindexTarget (detachedIndex x0) = sequence (natural 1 ∷ encode familyTarget x0 ∷ [])
encode reindexTarget (allRegistered) = sequence (natural 2 ∷ [])
decode reindexTarget (sequence (natural 0 ∷ v0 ∷ [])) = Maybe.map (foregroundIndex) (decode familyTarget v0)
decode reindexTarget (sequence (natural 1 ∷ v0 ∷ [])) = Maybe.map (detachedIndex) (decode familyTarget v0)
decode reindexTarget (sequence (natural 2 ∷ [])) = just (allRegistered)
decode reindexTarget _ = nothing
roundTrip reindexTarget (foregroundIndex x0) rewrite roundTrip familyTarget x0 = refl
roundTrip reindexTarget (detachedIndex x0) rewrite roundTrip familyTarget x0 = refl
roundTrip reindexTarget (allRegistered) = refl

familyJob : Codec (FamilyJob)
familyJob = transport
  (λ r → (FamilyJob.operationId r , FamilyJob.family r))
  (λ (x0 , x1) → record { operationId = x0; family = x1 })
  (λ r → refl) (pair operationId familyId)

checkoutJob : Codec (CheckoutJob)
checkoutJob = transport
  (λ r → (CheckoutJob.parent r , CheckoutJob.checkout r))
  (λ (x0 , x1) → record { parent = x0; checkout = x1 })
  (λ r → refl) (pair familyJob checkoutId)

fileJob : Codec (FileJob)
fileJob = transport
  (λ r → (FileJob.parent r , (FileJob.path r , FileJob.version r)))
  (λ (x0 , (x1 , x2)) → record { parent = x0; path = x1; version = x2 })
  (λ r → refl) (pair checkoutJob (pair path (optional versionId)))

usageInput : Codec (UsageInput)
usageInput = transport
  (λ r → (UsageInput.tool r , (UsageInput.family r , (UsageInput.durationMilliseconds r , UsageInput.resultCount r))))
  (λ (x0 , (x1 , (x2 , x3))) → record { tool = x0; family = x1; durationMilliseconds = x2; resultCount = x3 })
  (λ r → refl) (pair string (pair (optional familyId) (pair nat (optional nat))))

mutationInput : ∀ {A} → Codec A → Codec (Mutation A)
mutationInput c = transport
  (λ r → Mutation.operationId r , Mutation.input r)
  (λ { (id , input) → record { operationId = id; input = input } })
  (λ r → refl) (pair operationId c)
