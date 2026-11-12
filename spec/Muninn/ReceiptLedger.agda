{-# OPTIONS --safe #-}
-- Receipt operations read and write the COMPLETE owned world. There is no
-- independent ledger map and no operation-specific atomic-effect relation.
module Muninn.ReceiptLedger where

import Muninn.OwnedState as O
import Muninn.Dialogue as Dialogue
import Muninn.ReceiptTypes as R
import Muninn.RequestCodecs as Codecs
import Muninn.Canonical as Canonical
open import Muninn.CatalogInputs using (OperationId)
open import Muninn.RequestIdentity using (Meaning; sameRequest)
open import Data.Nat using (ℕ; zero; suc; pred; _≟_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans; sym)

module DB = O.DB
module E = O.Execution

sameId : (first second : OperationId) → Relation.Nullary.Dec (first ≡ second)
sameId = Canonical.compare Codecs.operationId

record Found (id : OperationId) : Set where
  constructor found
  field slot : ℕ
        owner : O.Owner
        state : R.State id
open Found public

inRecord : ∀ id → ℕ → O.Record → Maybe (Found id)
inRecord id slot (O.recordOf owner (O.receipt (R.entry stored state))) with sameId id stored
... | yes refl = just (found slot owner state)
... | no _ = nothing
inRecord id slot _ = nothing

find : ∀ id → O.World → Maybe (Found id)
find id [] = nothing
find id ((slot , stored) ∷ rest) with inRecord id slot stored
... | just value = just value
... | nothing = find id rest

data Advice : Set where
  differentRequest historyReclaimed unknownId : Advice

message : Advice → String
message differentRequest = "This ID belongs to a different request. Its saved work is unchanged. Use a new ID for the new request."
message historyReclaimed = "This ID was already used. Its details were removed, so I will not run it again. Inspect the current state before deciding whether you need a new operation."
message unknownId = "I cannot find work for this ID. Tell me what you were trying to do so we can recover the context."

data Reply : Set where
  fresh : Reply
  accepted : ℕ → Reply
  resume : ℕ → R.Work → Reply
  saved : String → Reply
  explain : Advice → Reply
  allocateSlot : Reply -- internal allocator continuation, never a wire error
  continueDialogue : ℕ → R.Work → Dialogue.Prompt → Reply

existing : ∀ {id} → Meaning → Found id → Reply
existing input (found slot owner (R.active original names work)) with sameRequest input original
... | yes _ = resume slot work
... | no _ = explain differentRequest
existing input (found slot owner (R.finished original names result)) with sameRequest input original
... | yes _ = saved result
... | no _ = explain differentRequest
existing input (found slot owner R.used) = explain historyReclaimed

inspect : ∀ id → Meaning → O.World → Reply
inspect id input world with find id world
... | nothing = fresh
... | just value = existing input value

recordAt : ∀ {id} → O.Owner → R.State id → O.Record
recordAt {id} owner state = O.recordOf owner (O.receipt (R.entry id state))

markerAt : OperationId → O.Record
markerAt id = O.recordOf O.installation (O.receipt (R.marker id))

-- The scan/check/write are inside ONE shared transaction, not a check followed
-- by a separately committed insert. Runtime adapters owe serialization and
-- uniqueness of operation IDs, not only uniqueness of physical row keys.
acceptSnapshot : ∀ id input → R.Names id input → ℕ → O.Owner → R.Work →
  O.World → DB.Transaction Reply
acceptSnapshot id input names slot owner work world with find id world
... | just value = DB.commit (existing input value)
... | nothing with DB.lookup slot world
...   | just _ = DB.commit allocateSlot
...   | nothing = DB.put slot (recordAt owner (R.active input names work)) (DB.commit (accepted slot))

accept : ∀ id input → R.Names id input → ℕ → O.Owner → R.Work → DB.Transaction Reply
accept id input names slot owner work = DB.scan (acceptSnapshot id input names slot owner work)

-- Seal EVERY commit of a shared transaction with the checkpoint/receipt write.
-- An abort retains the original store, including its prior checkpoint. No
-- filesystem or third-party effect is asserted to participate in this commit.
seal : ∀ {A B : Set} → ℕ → (A → O.Record) → (A → B) → (A → B) →
  DB.Transaction A → DB.Transaction B
seal key value success waiting (DB.commit result) = DB.put key (value result) (DB.commit (success result))
seal key value success waiting (DB.abort result) = DB.abort (waiting result)
seal key value success waiting (DB.scan next) = DB.scan (λ rows → seal key value success waiting (next rows))
seal key value success waiting (DB.read slot next) = DB.read slot (λ result → seal key value success waiting (next result))
seal key value success waiting (DB.put slot stored next) = DB.put slot stored (seal key value success waiting next)
seal key value success waiting (DB.remove slot next) = DB.remove slot (seal key value success waiting next)
seal key value success waiting (DB.eraseRows bound keep next) = DB.eraseRows bound keep (seal key value success waiting next)

sealCommitted : ∀ {A B} key value (success waiting : A → B) transaction before result after →
  DB.evaluate transaction before ≡ DB.committed result after →
  DB.evaluate (seal key value success waiting transaction) before ≡
    DB.committed (success result) (DB.write key (value result) after)
sealCommitted key value success waiting (DB.commit result) before .result .before refl = refl
sealCommitted key value success waiting (DB.abort result) before observed after ()
sealCommitted key value success waiting (DB.scan next) before result after committed =
  sealCommitted key value success waiting (next before) before result after committed
sealCommitted key value success waiting (DB.read slot next) before result after committed =
  sealCommitted key value success waiting (next (DB.lookup slot before)) before result after committed
sealCommitted key value success waiting (DB.put slot stored next) before result after committed =
  sealCommitted key value success waiting next (DB.write slot stored before) result after committed
sealCommitted key value success waiting (DB.remove slot next) before result after committed =
  sealCommitted key value success waiting next (DB.delete slot before) result after committed
sealCommitted key value success waiting (DB.eraseRows bound keep next) before result after committed =
  sealCommitted key value success waiting next (DB.erase bound keep before) result after committed

sealAborted : ∀ {A B} key value (success waiting : A → B) transaction before result →
  DB.evaluate transaction before ≡ DB.aborted result →
  DB.evaluate (seal key value success waiting transaction) before ≡ DB.aborted (waiting result)
sealAborted key value success waiting (DB.commit result) before observed ()
sealAborted key value success waiting (DB.abort result) before .result refl = refl
sealAborted key value success waiting (DB.scan next) before result aborted =
  sealAborted key value success waiting (next before) before result aborted
sealAborted key value success waiting (DB.read slot next) before result aborted =
  sealAborted key value success waiting (next (DB.lookup slot before)) before result aborted
sealAborted key value success waiting (DB.put slot stored next) before result aborted =
  sealAborted key value success waiting next (DB.write slot stored before) result aborted
sealAborted key value success waiting (DB.remove slot next) before result aborted =
  sealAborted key value success waiting next (DB.delete slot before) result aborted
sealAborted key value success waiting (DB.eraseRows bound keep next) before result aborted =
  sealAborted key value success waiting next (DB.erase bound keep before) result aborted

-- Business effects cannot create, delete or alter a receipt. Only the
-- receipt protocol may change one, after checking identity and generation.
-- This predicate is fixed here; an operation cannot supply a weaker frame.
ReceiptFrame : O.World → O.World → Set
ReceiptFrame before after = ∀ key owner receiptData →
  ((DB.lookup key before ≡ just (O.recordOf owner (O.receipt receiptData))) →
    DB.lookup key after ≡ just (O.recordOf owner (O.receipt receiptData))) ×
  ((DB.lookup key after ≡ just (O.recordOf owner (O.receipt receiptData))) →
    DB.lookup key before ≡ just (O.recordOf owner (O.receipt receiptData)))

record Effect : Set where
  field
    transaction : DB.Transaction String
    guidance : String → Dialogue.Prompt
    isolates : ∀ before result after →
      DB.evaluate transaction before ≡ DB.committed result after → ReceiptFrame before after

sealedOtherReceipt : ∀ {B : Set} key value (success waiting : String → B) (effect : Effect) before result after →
  DB.evaluate (Effect.transaction effect) before ≡ DB.committed result after →
  ∀ other owner receiptData → key ≢ other →
  DB.lookup other before ≡ just (O.recordOf owner (O.receipt receiptData)) →
  DB.lookup other (proj₂ (DB.execute
    (seal key value success waiting (Effect.transaction effect)) before)) ≡
      just (O.recordOf owner (O.receipt receiptData))
sealedOtherReceipt key value success waiting effect before result after committed other owner receiptData distinct present
  rewrite sealCommitted key value success waiting (Effect.transaction effect) before result after committed =
  trans (DB.writePreservesOther key other (value result) after distinct)
    (proj₁ (Effect.isolates effect before result after committed other owner receiptData) present)

sealedAbortKeepsWork : ∀ {B : Set} key value (success waiting : String → B) (effect : Effect) before result →
  DB.evaluate (Effect.transaction effect) before ≡ DB.aborted result →
  proj₂ (DB.execute (seal key value success waiting (Effect.transaction effect)) before) ≡ before
sealedAbortKeepsWork key value success waiting effect before result aborted
  rewrite sealAborted key value success waiting (Effect.transaction effect) before result aborted = refl


data Update : Set where
  checkpoint : List ℕ → Update
  complete : Update

updatedState : ∀ {id} → Update → (input : Meaning) → R.Names id input → R.Work → String → R.State id
updatedState (checkpoint retained) input names work result = R.active input names (R.nextWork work retained result)
updatedState complete input names work result = R.finished input names result

updatedReply : Update → ℕ → R.Work → String → Reply
updatedReply (checkpoint retained) slot work result = resume slot (R.nextWork work retained result)
updatedReply complete slot work result = saved result

-- A stale worker resumes the current checkpoint; it cannot replay its old
-- database effect after a lost acknowledgement or a competing committed step.
updateExisting : ∀ {id} → Meaning → ℕ → Update → Effect → Found id → DB.Transaction Reply
updateExisting input expected update effect value@(found slot owner (R.active original names work))
  with sameRequest input original
... | no _ = DB.commit (explain differentRequest)
... | yes _ with R.generation work ≟ expected
...   | no _ = DB.commit (resume slot work)
...   | yes _ = seal slot (λ result → recordAt owner (updatedState update original names work result))
    (updatedReply update slot work)
    (λ reason → continueDialogue slot work (Effect.guidance effect reason)) (Effect.transaction effect)
updateExisting input expected update effect value@(found slot owner (R.finished original names result)) =
  DB.commit (existing input value)
updateExisting input expected update effect (found slot owner R.used) = DB.commit (explain historyReclaimed)

updateSnapshot : ∀ id → Meaning → ℕ → Update → Effect → O.World → DB.Transaction Reply
updateSnapshot id input expected update effect world with find id world
... | nothing = DB.commit (explain unknownId)
... | just value = updateExisting input expected update effect value

update : ∀ id → Meaning → ℕ → Update → Effect → DB.Transaction Reply
update id input expected change effect = DB.scan (updateSnapshot id input expected change effect)

reclaimSnapshot : ∀ id → O.World → DB.Transaction Reply
reclaimSnapshot id world with find id world
... | nothing = DB.commit (explain unknownId)
... | just (found slot owner (R.active input names work)) = DB.commit (resume slot work)
... | just (found slot owner (R.finished input names result)) =
  DB.put slot (markerAt id) (DB.commit (explain historyReclaimed))
... | just (found slot owner R.used) = DB.commit (explain historyReclaimed)

reclaim : OperationId → DB.Transaction Reply
reclaim id = DB.scan (reclaimSnapshot id)

-- General boundary law: every crash in a one-transaction script leaves either
-- the old world or the committed world, including loss of the final reply.
atomicBoundary : ∀ {A : Set} (transaction : DB.Transaction A) before after →
  E.Interrupted (E.atomic transaction E.done) before after →
  (after ≡ before) ⊎ (after ≡ proj₂ (DB.execute transaction before))
atomicBoundary transaction before after (residual , E.stop) = inj₁ refl
atomicBoundary transaction before after (residual , E.committed E.stop) = inj₂ refl

writtenReceiptVisible : ∀ id slot owner state world →
  find id (DB.write slot (recordAt owner state) world) ≡ just (found slot owner state)
writtenReceiptVisible id slot owner state world with sameId id id
... | yes refl = refl
... | no different = ⊥-elim (different refl)

existingNeverFresh : ∀ {id} input (value : Found id) → existing input value ≢ fresh
existingNeverFresh input (found slot owner (R.active original names work)) with sameRequest input original
... | yes _ = λ ()
... | no _ = λ ()
existingNeverFresh input (found slot owner (R.finished original names result)) with sameRequest input original
... | yes _ = λ ()
... | no _ = λ ()
existingNeverFresh input (found slot owner R.used) = λ ()

-- Applies to accepted work, completed results AND ID-only markers. A lost
-- acknowledgement cannot turn any of them into a fresh acceptance.
lostReplyNeverFresh : ∀ id input slot owner state world →
  inspect id input (DB.write slot (recordAt owner state) world) ≢ fresh
lostReplyNeverFresh id input slot owner state world
  rewrite writtenReceiptVisible id slot owner state world = existingNeverFresh input (found slot owner state)

sameRetryResumes : ∀ id input names slot owner work world →
  inspect id input (DB.write slot (recordAt owner (R.active input names work)) world) ≡ resume slot work
sameRetryResumes id input names slot owner work world
  rewrite writtenReceiptVisible id slot owner (R.active input names work) world with sameRequest input input
... | yes _ = refl
... | no different = ⊥-elim (different refl)

sameRetryReplays : ∀ id input names slot owner result world →
  inspect id input (DB.write slot (recordAt owner (R.finished input names result)) world) ≡ saved result
sameRetryReplays id input names slot owner result world
  rewrite writtenReceiptVisible id slot owner (R.finished input names result) world with sameRequest input input
... | yes _ = refl
... | no different = ⊥-elim (different refl)

receiptWriteIsolated : ∀ slot other owner id state world → slot ≢ other →
  DB.lookup other (DB.write slot (recordAt {id} owner state) world) ≡ DB.lookup other world
receiptWriteIsolated slot other owner id state world distinct =
  DB.writePreservesOther slot other (recordAt owner state) world distinct

markerOwner : ∀ id → O.owner (markerAt id) ≡ O.installation
markerOwner id = refl

markerNoReferences : ∀ id → O.references (O.body (markerAt id)) ≡ []
markerNoReferences id = refl

reclaimKeepsActiveWork : ∀ id world slot owner input names work →
  find id world ≡ just (found slot owner (R.active input names work)) →
  proj₂ (DB.execute (reclaim id) world) ≡ world
reclaimKeepsActiveWork id world slot owner input names work foundHere rewrite foundHere = refl

reclaimRetainsId : ∀ id world slot owner input names result →
  find id world ≡ just (found slot owner (R.finished input names result)) →
  find id (proj₂ (DB.execute (reclaim id) world)) ≡ just (found slot O.installation R.used)
reclaimRetainsId id world slot owner input names result foundHere rewrite foundHere =
  writtenReceiptVisible id slot O.installation R.used world

differentInputKeepsWorld : ∀ id input names slot owner initial world value →
  find id world ≡ just value → existing input value ≡ explain differentRequest →
  DB.execute (accept id input names slot owner initial) world ≡ (explain differentRequest , world)
differentInputKeepsWorld id input names slot owner initial world value foundHere mismatched
  rewrite foundHere | mismatched = refl

acceptPreservesExisting : ∀ id input names slot owner initial world other retained →
  DB.lookup other world ≡ just retained →
  DB.lookup other (proj₂ (DB.execute (accept id input names slot owner initial) world)) ≡ just retained
acceptPreservesExisting id input names slot owner initial world other retained present
  with find id world
... | just value = present
... | nothing with DB.lookup slot world in allocated
...   | just value = present
...   | nothing with slot ≟ other
...     | yes refl = ⊥-elim (absentNotPresent (trans (sym allocated) present))
  where
  absentNotPresent : ∀ {A : Set} {a : A} → nothing ≡ just a → Data.Empty.⊥
  absentNotPresent ()
...     | no distinct = trans
  (DB.writePreservesOther slot other (recordAt owner (R.active input names initial)) world distinct) present

-- No expired/used-ID request can enter the caller's effect transaction.
usedSkipsEffect : ∀ id input expected change effect slot owner world →
  find id world ≡ just (found slot owner R.used) →
  DB.execute (update id input expected change effect) world ≡ (explain historyReclaimed , world)
usedSkipsEffect id input expected change effect slot owner world foundHere rewrite foundHere = refl

staleStepSkipsEffect : ∀ id input names expected change effect slot owner progress world →
  find id world ≡ just (found slot owner (R.active input names progress)) →
  R.generation progress ≢ expected →
  DB.execute (update id input expected change effect) world ≡ (resume slot progress , world)
staleStepSkipsEffect id input names expected change effect slot owner progress world foundHere stale
  rewrite foundHere with sameRequest input input
... | no different = ⊥-elim (different refl)
... | yes _ with R.generation progress ≟ expected
...   | yes same = ⊥-elim (stale same)
...   | no _ = refl

nextGenerationDifferent : ∀ n → suc n ≢ n
nextGenerationDifferent zero ()
nextGenerationDifferent (suc n) same = nextGenerationDifferent n (cong pred same)

-- The exact old step is suppressed after its checkpoint was committed, even
-- if its acknowledgement was lost. Any retained versions and result apply.
lostCheckpointReplySkipsEffect : ∀ id input names change effect slot owner progress retained result world →
  DB.execute (update id input (R.generation progress) change effect)
    (DB.write slot (recordAt owner (R.active input names (R.nextWork progress retained result))) world) ≡
  (resume slot (R.nextWork progress retained result) ,
    DB.write slot (recordAt owner (R.active input names (R.nextWork progress retained result))) world)
lostCheckpointReplySkipsEffect id input names change effect slot owner progress retained result world =
  staleStepSkipsEffect id input names (R.generation progress) change effect slot owner
    (R.nextWork progress retained result)
    (DB.write slot (recordAt owner (R.active input names (R.nextWork progress retained result))) world)
    (writtenReceiptVisible id slot owner (R.active input names (R.nextWork progress retained result)) world)
    (nextGenerationDifferent (R.generation progress))

finishedSkipsEffect : ∀ id input names expected change effect slot owner result world →
  find id world ≡ just (found slot owner (R.finished input names result)) →
  DB.execute (update id input expected change effect) world ≡ (saved result , world)
finishedSkipsEffect id input names expected change effect slot owner result world foundHere
  rewrite foundHere with sameRequest input input
... | yes _ = refl
... | no different = ⊥-elim (different refl)

acceptedReceiptVisible : ∀ id input names slot owner initial world →
  find id world ≡ nothing → DB.lookup slot world ≡ nothing →
  find id (proj₂ (DB.execute (accept id input names slot owner initial) world)) ≡
    just (found slot owner (R.active input names initial))
acceptedReceiptVisible id input names slot owner initial world absent free
  rewrite absent | free = writtenReceiptVisible id slot owner (R.active input names initial) world

sealedCommitNeverFresh : ∀ id input slot owner (next : String → R.State id)
  (success waiting : String → Reply) effect before result after →
  DB.evaluate (Effect.transaction effect) before ≡ DB.committed result after →
  inspect id input (proj₂ (DB.execute
    (seal slot (λ r → recordAt owner (next r)) success waiting (Effect.transaction effect)) before)) ≢ fresh
sealedCommitNeverFresh id input slot owner next success waiting effect before result after committed
  rewrite sealCommitted slot (λ r → recordAt owner (next r)) success waiting
    (Effect.transaction effect) before result after committed =
  lostReplyNeverFresh id input slot owner (next result) after

wrongInputSkipsEffect : ∀ id input original names expected change effect slot owner progress world →
  find id world ≡ just (found slot owner (R.active original names progress)) → input ≢ original →
  DB.execute (update id input expected change effect) world ≡ (explain differentRequest , world)
wrongInputSkipsEffect id input original names expected change effect slot owner progress world foundHere different
  rewrite foundHere with sameRequest input original
... | yes same = ⊥-elim (different same)
... | no _ = refl

committedUpdate : ∀ id input names change effect slot owner progress world result after →
  find id world ≡ just (found slot owner (R.active input names progress)) →
  DB.evaluate (Effect.transaction effect) world ≡ DB.committed result after →
  DB.execute (update id input (R.generation progress) change effect) world ≡
    (updatedReply change slot progress result ,
      DB.write slot (recordAt owner (updatedState change input names progress result)) after)
committedUpdate id input names change effect slot owner progress world result after foundHere committed
  rewrite foundHere with sameRequest input input
... | no different = ⊥-elim (different refl)
... | yes _ with R.generation progress ≟ R.generation progress
...   | no different = ⊥-elim (different refl)
...   | yes _ rewrite sealCommitted slot
  (λ r → recordAt owner (updatedState change input names progress r))
  (updatedReply change slot progress)
  (λ reason → continueDialogue slot progress (Effect.guidance effect reason))
  (Effect.transaction effect) world result after committed = refl

markerPlaced : ∀ id → O.Placed (markerAt id)
markerPlaced id = O.shared

existingAcceptanceReadOnly : ∀ id input names slot owner initial world value →
  find id world ≡ just value →
  DB.execute (accept id input names slot owner initial) world ≡ (existing input value , world)
existingAcceptanceReadOnly id input names slot owner initial world value foundHere rewrite foundHere = refl

lostAcceptanceReplyReadOnly : ∀ id input names slot owner initial previousSlot previousOwner previousState world →
  DB.execute (accept id input names slot owner initial)
    (DB.write previousSlot (recordAt previousOwner previousState) world) ≡
    (existing input (found previousSlot previousOwner previousState) ,
      DB.write previousSlot (recordAt previousOwner previousState) world)
lostAcceptanceReplyReadOnly id input names slot owner initial previousSlot previousOwner previousState world =
  existingAcceptanceReadOnly id input names slot owner initial
    (DB.write previousSlot (recordAt previousOwner previousState) world)
    (found previousSlot previousOwner previousState)
    (writtenReceiptVisible id previousSlot previousOwner previousState world)

usedReclaimKeepsWorld : ∀ id world slot owner →
  find id world ≡ just (found slot owner R.used) →
  DB.execute (reclaim id) world ≡ (explain historyReclaimed , world)
usedReclaimKeepsWorld id world slot owner foundHere rewrite foundHere = refl
