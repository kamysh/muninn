{-# OPTIONS --safe #-}
-- One Kryzhen block and its ledger row share a database transaction.
module Muninn.MigrationBlock where
import Muninn.OwnedState as O
import Muninn.Schema as Schema
import Muninn.Worktree as W
import Muninn.ExclusionOutcomes as E
import Muninn.ReceiptLedger as Ledger
import Muninn.Dialogue as D
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false)
open import Data.List using ([])
open import Data.String using (String)
import Data.String as String
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
module DB = O.DB
module Exec = O.Execution

-- The codec is lossless for the actual schema and complete migration identity.
-- The runtime adapter must bind it to Kryzhen ledger rows and catalog evidence.
record LedgerCodec : Set where
  field encode : W.SchemaId → Schema.Migration → String
        decode : String → Maybe (W.SchemaId × Schema.Migration)
        roundTrip : ∀ schema migration → decode (encode schema migration) ≡ just (schema , migration)

ledgerIdentity : ∀ codec schema₁ migration₁ schema₂ migration₂ →
  LedgerCodec.encode codec schema₁ migration₁ ≡ LedgerCodec.encode codec schema₂ migration₂ →
  (schema₁ ≡ schema₂) × (migration₁ ≡ migration₂)
ledgerIdentity codec schema₁ migration₁ schema₂ migration₂ same =
  cong proj₁ pairEqual , cong proj₂ pairEqual
  where
  pairEqual : (schema₁ , migration₁) ≡ (schema₂ , migration₂)
  pairEqual = just-injective (trans (sym (LedgerCodec.roundTrip codec schema₁ migration₁))
    (trans (cong (LedgerCodec.decode codec) same) (LedgerCodec.roundTrip codec schema₂ migration₂)))

data Scope : Set where
  shared : Scope
  family : ℕ → Scope
owner : Scope → O.Owner
owner shared = O.installation
owner (family id) = O.family id
catalog : Scope → String → O.Record
catalog shared payload = O.recordOf O.installation (O.coordination payload)
catalog (family id) payload = O.recordOf (O.family id) (O.schemaResource payload)

record Block : Set where
  field scope : Scope
        schema : W.SchemaId
        migration : Schema.Migration
        catalogSlot markerSlot : ℕ
        distinct : markerSlot ≢ catalogSlot
        beforeCatalog : Maybe String
        afterCatalog : String

record Outcome (codec : LedgerCodec) (block : Block) (before after : O.World) : Set where
  field schemaReady : DB.lookup (Block.catalogSlot block) after ≡ just (catalog (Block.scope block) (Block.afterCatalog block))
        ledgerRecorded : DB.lookup (Block.markerSlot block) after ≡ just (O.recordOf (owner (Block.scope block))
          (O.migration (LedgerCodec.encode codec (Block.schema block) (Block.migration block))))
        othersPreserved : ∀ key → Block.markerSlot block ≢ key → Block.catalogSlot block ≢ key →
          DB.lookup key after ≡ DB.lookup key before

data Reply : Set where prepared : Reply; ask : D.Prompt → Reply

module Apply (codec : LedgerCodec) (block : Block) where
  scope = Block.scope block
  original = Maybe.map (catalog scope) (Block.beforeCatalog block)
  updated = catalog scope (Block.afterCatalog block)
  ledger = O.recordOf (owner scope) (O.migration (LedgerCodec.encode codec (Block.schema block) (Block.migration block)))
  prompt : D.Prompt
  prompt = D.prompt (D.text 'I' " cannot prepare this database with the saved migration information.")
    (D.text 'C' "heck the configured database and migration history, then continue. Existing data is unchanged.") []

  markerMatches : O.Record → Bool
  markerMatches (O.recordOf actual (O.migration payload)) with E.ownerEqual actual (owner scope) | payload String.≟ LedgerCodec.encode codec (Block.schema block) (Block.migration block)
  ... | yes _ | yes _ = true
  ... | _ | _ = false
  markerMatches _ = false
  catalogMatchesExisting : Scope → String → O.Record → Bool
  catalogMatchesExisting shared expected (O.recordOf actual (O.coordination payload)) with E.ownerEqual actual O.installation | payload String.≟ expected
  ... | yes _ | yes _ = true
  ... | _ | _ = false
  catalogMatchesExisting (family id) expected (O.recordOf actual (O.schemaResource payload)) with E.ownerEqual actual (O.family id) | payload String.≟ expected
  ... | yes _ | yes _ = true
  ... | _ | _ = false
  catalogMatchesExisting _ _ _ = false
  catalogAccepts : Maybe O.Record → Bool
  catalogAccepts nothing with Block.beforeCatalog block
  ... | nothing = true
  ... | just _ = false
  catalogAccepts (just row) with Block.beforeCatalog block
  ... | nothing = false
  ... | just expected = catalogMatchesExisting scope expected row

  transaction : DB.Transaction Reply
  transaction = DB.read (Block.markerSlot block) inspectMarker
    where
    apply : DB.Transaction Reply
    apply = DB.put (Block.catalogSlot block) updated (DB.put (Block.markerSlot block) ledger (DB.commit prepared))
    inspectCatalog : Maybe O.Record → DB.Transaction Reply
    inspectCatalog value with catalogAccepts value
    ... | true = apply
    ... | false = DB.abort (ask prompt)
    inspectMarker : Maybe O.Record → DB.Transaction Reply
    inspectMarker (just row) with markerMatches row
    ... | true = DB.commit prepared
    ... | false = DB.abort (ask prompt)
    inspectMarker nothing = DB.read (Block.catalogSlot block) inspectCatalog

  changed : O.World → O.World
  changed world = DB.write (Block.markerSlot block) ledger (DB.write (Block.catalogSlot block) updated world)
  markerMatchesSelf : markerMatches ledger ≡ true
  markerMatchesSelf with E.ownerEqual (owner scope) (owner scope) | LedgerCodec.encode codec (Block.schema block) (Block.migration block) String.≟ LedgerCodec.encode codec (Block.schema block) (Block.migration block)
  ... | yes _ | yes _ = refl
  ... | no different | _ = ⊥-elim (different refl)
  ... | _ | no different = ⊥-elim (different refl)
  matchesExistingSelf : ∀ selected payload → catalogMatchesExisting selected payload (catalog selected payload) ≡ true
  matchesExistingSelf shared payload with E.ownerEqual O.installation O.installation | payload String.≟ payload
  ... | yes _ | yes _ = refl
  ... | no different | _ = ⊥-elim (different refl)
  ... | _ | no different = ⊥-elim (different refl)
  matchesExistingSelf (family id) payload with E.ownerEqual (O.family id) (O.family id) | payload String.≟ payload
  ... | yes _ | yes _ = refl
  ... | no different | _ = ⊥-elim (different refl)
  ... | _ | no different = ⊥-elim (different refl)
  catalogAcceptsOriginal : catalogAccepts original ≡ true
  catalogAcceptsOriginal with Block.beforeCatalog block in beforeEq
  ... | nothing rewrite beforeEq = refl
  ... | just payload rewrite beforeEq = matchesExistingSelf scope payload

  commits : ∀ world → DB.lookup (Block.markerSlot block) world ≡ nothing →
    DB.lookup (Block.catalogSlot block) world ≡ original → DB.execute transaction world ≡ (prepared , changed world)
  commits world missing found rewrite missing | found | catalogAcceptsOriginal = refl

  markerSaved : ∀ world → DB.lookup (Block.markerSlot block) (changed world) ≡ just ledger
  markerSaved world = DB.writeVisible (Block.markerSlot block) ledger _
  schemaSaved : ∀ world → DB.lookup (Block.catalogSlot block) (changed world) ≡ just updated
  schemaSaved world = trans (DB.writePreservesOther (Block.markerSlot block) (Block.catalogSlot block) ledger _ (Block.distinct block))
    (DB.writeVisible (Block.catalogSlot block) updated world)
  replay : ∀ world → DB.lookup (Block.markerSlot block) world ≡ just ledger → DB.execute transaction world ≡ (prepared , world)
  replay world saved rewrite saved | markerMatchesSelf = refl
  otherPreserved : ∀ world key → Block.markerSlot block ≢ key → Block.catalogSlot block ≢ key →
    DB.lookup key (changed world) ≡ DB.lookup key world
  otherPreserved world key markerDifferent catalogDifferent = trans
    (DB.writePreservesOther (Block.markerSlot block) key ledger _ markerDifferent)
    (DB.writePreservesOther (Block.catalogSlot block) key updated world catalogDifferent)
  -- Existing notes and AGE graph records cannot occupy either migration slot.
  preservesNote : ∀ world key noteOwner payload →
    DB.lookup (Block.markerSlot block) world ≡ nothing → DB.lookup (Block.catalogSlot block) world ≡ original →
    DB.lookup key world ≡ just (O.recordOf noteOwner (O.note payload)) →
    DB.lookup key (changed world) ≡ just (O.recordOf noteOwner (O.note payload))
  preservesNote world key noteOwner payload missing found noteAt = trans (otherPreserved world key markerDifferent catalogDifferent) noteAt
    where
    markerDifferent : Block.markerSlot block ≢ key
    markerDifferent refl with trans (sym missing) noteAt
    ... | ()
    catalogDifferent : Block.catalogSlot block ≢ key
    catalogDifferent refl with Block.beforeCatalog block | scope | trans (sym found) noteAt
    ... | nothing | selected | ()
    ... | just payload | shared | ()
    ... | just payload | family id | ()
  preservesGraph : ∀ world key graphOwner checkout inUse payload →
    DB.lookup (Block.markerSlot block) world ≡ nothing → DB.lookup (Block.catalogSlot block) world ≡ original →
    DB.lookup key world ≡ just (O.recordOf graphOwner (O.graphResource checkout inUse payload)) →
    DB.lookup key (changed world) ≡ just (O.recordOf graphOwner (O.graphResource checkout inUse payload))
  preservesGraph world key graphOwner checkout inUse payload missing found graphAt = trans (otherPreserved world key markerDifferent catalogDifferent) graphAt
    where
    markerDifferent : Block.markerSlot block ≢ key
    markerDifferent refl with trans (sym missing) graphAt
    ... | ()
    catalogDifferent : Block.catalogSlot block ≢ key
    catalogDifferent refl with Block.beforeCatalog block | scope | trans (sym found) graphAt
    ... | nothing | selected | ()
    ... | just payload | shared | ()
    ... | just payload | family id | ()

  -- Every existing record other than the migration catalog itself is retained.
  preservesRecord : ∀ world key value →
    DB.lookup (Block.markerSlot block) world ≡ nothing → DB.lookup (Block.catalogSlot block) world ≡ original →
    DB.lookup key world ≡ just value → O.kind (O.body value) ≢ O.coordinationK → O.kind (O.body value) ≢ O.schemaResourceK →
    DB.lookup key (changed world) ≡ just value
  preservesRecord world key value missing found valueAt notCoordination notSchema =
    trans (otherPreserved world key markerDifferent catalogDifferent) valueAt
    where
    markerDifferent : Block.markerSlot block ≢ key
    markerDifferent refl with trans (sym missing) valueAt
    ... | ()
    catalogDifferent : Block.catalogSlot block ≢ key
    catalogDifferent refl with Block.beforeCatalog block | scope
    ... | nothing | selected with trans (sym found) valueAt
    ...   | ()
    catalogDifferent refl | just payload | shared = notCoordination (sym (cong (λ row → O.kind (O.body row)) (just-injective (trans (sym found) valueAt))))
    catalogDifferent refl | just payload | family id = notSchema (sym (cong (λ row → O.kind (O.body row)) (just-injective (trans (sym found) valueAt))))

  outcome : ∀ world → Outcome codec block world (changed world)
  outcome world = record { schemaReady = schemaSaved world; ledgerRecorded = markerSaved world; othersPreserved = otherPreserved world }

  script : Exec.Script Reply
  script = Exec.atomic transaction Exec.done
  module InterruptedBlock (before : O.World) (missing : DB.lookup (Block.markerSlot block) before ≡ nothing)
    (found : DB.lookup (Block.catalogSlot block) before ≡ original) where
    after = changed before
    first : DB.execute transaction before ≡ (prepared , after)
    first = commits before missing found
    retry : DB.execute transaction after ≡ (prepared , after)
    retry = replay after (markerSaved before)
    boundary : ∀ observed → Exec.Interrupted script before observed → observed ≡ before ⊎ observed ≡ after
    boundary observed (residual , Exec.stop) = inj₁ refl
    boundary observed (residual , Exec.committed Exec.stop) = inj₂ (cong proj₂ first)
    completedAtomic : ∀ observed reply final → Exec.Completed script observed reply final → DB.execute transaction observed ≡ (reply , final)
    completedAtomic observed reply final (Exec.committed Exec.stop) = refl
    converges : ∀ observed reply final → Exec.Interrupted script before observed → Exec.Completed script observed reply final → final ≡ after
    converges observed reply final interrupted complete with boundary observed interrupted
    ... | inj₁ same = trans (sym (cong proj₂ (completedAtomic observed reply final complete)))
      (trans (cong (λ world → proj₂ (DB.execute transaction world)) same) (cong proj₂ first))
    ... | inj₂ same = trans (sym (cong proj₂ (completedAtomic observed reply final complete)))
      (trans (cong (λ world → proj₂ (DB.execute transaction world)) same) (cong proj₂ retry))
    retryAchievesOutcome : ∀ observed reply final → Exec.Interrupted script before observed → Exec.Completed script observed reply final → Outcome codec block before final
    retryAchievesOutcome observed reply final interrupted complete =
      subst (Outcome codec block before) (sym (converges observed reply final interrupted complete)) (outcome before)
