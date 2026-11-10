{-# OPTIONS --safe #-}
-- Delete one family note and its derived rows in a single receipt-sealed commit.
module Muninn.KnowledgeDelete where
import Muninn.OwnedState as O
import Muninn.Knowledge as K
import Muninn.KnowledgeViews as Views
import Muninn.KnowledgeLookup as Lookup
import Muninn.KnowledgeRead as Read
import Muninn.KnowledgeErase as Erase
import Muninn.StoredPolicy as Policy
import Muninn.RecreationStore as Store
import Muninn.CleanupStorage as Storage
import Muninn.CleanupOrder as Order
import Muninn.ViewPublication as Frames
import Muninn.IdentityCheckpoint as Checkpoint
import Muninn.SearchTarget as Target
import Muninn.RepositoryIdentity as Repository
import Muninn.ExclusionOutcomes as E
import Muninn.CatalogInputs as I
import Muninn.RequestIdentity as Identity
import Muninn.RequestCodecs as Codecs
import Muninn.Canonical as Canonical
import Muninn.ReceiptLedger as Ledger
import Muninn.ReceiptTypes as Receipt
import Muninn.Dialogue as D
open import Data.Nat using (ℕ; zero; suc; _≟_; _≤_; _≤?_)
import Data.Nat.Properties as Nat
open import Data.Bool using (Bool; true; false; not; _∧_; T)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; _++_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
module DB = O.DB
module Exec = O.Execution

isTrue : ∀ {value} → T value → value ≡ true
isTrue {true} proof = refl
isTrue {false} ()

module Family (family registrationSlot pointer selected : ℕ) (codec : Views.Codec)
  (request : I.Mutation (I.FamilyTarget × K.KnowledgeId)) (context : D.Context) (observed : Repository.Observation) where
  owner = O.family family
  input = I.Mutation.input request
  target = proj₁ input
  id = proj₂ input
  module Notes = Lookup.Family family codec id
  module Saved = Policy.Family family pointer
  module Access = Read.Family family pointer codec
  module Requested = Target.Family family registrationSlot selected (I.FamilyTarget.location target) context observed

  -- Only this note and its own posting/vector associations are removed.
  localKeep : ℕ → ℕ → O.Body → Bool
  localKeep targetKey key (O.note payload) = not (does (key ≟ targetKey))
  localKeep targetKey key (O.notePosting source payload) = not (does (source ≟ targetKey))
  localKeep targetKey key (O.noteVector source value) = not (does (source ≟ targetKey))
  localKeep targetKey key body = true
  keep : ℕ → ℕ → O.Record → Bool
  keep targetKey key (O.recordOf actualOwner body) with E.ownerEqual actualOwner owner
  ... | no _ = true
  ... | yes _ = localKeep targetKey key body
  keepsReceipt : ∀ targetKey key receiptOwner receipt → keep targetKey key (O.recordOf receiptOwner (O.receipt receipt)) ≡ true
  keepsReceipt targetKey key receiptOwner receipt with E.ownerEqual receiptOwner owner
  ... | no _ = refl
  ... | yes _ = refl
  keepsOtherFamily : ∀ targetKey key value → O.owner value ≢ owner → keep targetKey key value ≡ true
  keepsOtherFamily targetKey key (O.recordOf actualOwner body) different with E.ownerEqual actualOwner owner
  ... | no _ = refl
  ... | yes same = ⊥-elim (different same)

  otherFamilyPreserved : ∀ world targetKey key value → DB.lookup key world ≡ just value → O.owner value ≢ owner →
    DB.lookup key (DB.erase (length world) (keep targetKey) world) ≡ just value
  otherFamilyPreserved world targetKey key value found different =
    Erase.retains (length world) (keep targetKey) world key value found (keepsOtherFamily targetKey key value different)

  dropsNote : ∀ key payload → keep key key (O.recordOf owner (O.note payload)) ≡ false
  dropsNote key payload with E.ownerEqual owner owner | key ≟ key
  ... | no different | _ = ⊥-elim (different refl)
  ... | yes _ | no different = ⊥-elim (different refl)
  ... | yes _ | yes _ rewrite isTrue (Nat.≡⇒≡ᵇ key key refl) = refl
  dropsPosting : ∀ key slot payload → keep key slot (O.recordOf owner (O.notePosting key payload)) ≡ false
  dropsPosting key slot payload with E.ownerEqual owner owner | key ≟ key
  ... | no different | _ = ⊥-elim (different refl)
  ... | yes _ | no different = ⊥-elim (different refl)
  ... | yes _ | yes _ rewrite isTrue (Nat.≡⇒≡ᵇ key key refl) = refl
  dropsVector : ∀ key slot value → keep key slot (O.recordOf owner (O.noteVector key value)) ≡ false
  dropsVector key slot value with E.ownerEqual owner owner | key ≟ key
  ... | no different | _ = ⊥-elim (different refl)
  ... | yes _ | no different = ⊥-elim (different refl)
  ... | yes _ | yes _ rewrite isTrue (Nat.≡⇒≡ᵇ key key refl) = refl

  noteRemoved : ∀ world (found : Notes.Located world) → O.Unique world →
    DB.lookup (Notes.Located.slot found) (DB.erase (length world) (keep (Notes.Located.slot found)) world) ≡ nothing
  noteRemoved world found unique = Erase.removed (keep (Notes.Located.slot found)) world
    (Notes.Located.slot found) _ unique (Notes.Located.stored found) (dropsNote (Notes.Located.slot found) (Notes.Located.oldPayload found))
  postingRemoved : ∀ world targetKey slot payload → O.Unique world →
    DB.lookup slot world ≡ just (O.recordOf owner (O.notePosting targetKey payload)) →
    DB.lookup slot (DB.erase (length world) (keep targetKey) world) ≡ nothing
  postingRemoved world targetKey slot payload unique found =
    Erase.removed (keep targetKey) world slot _ unique found (dropsPosting targetKey slot payload)
  vectorRemoved : ∀ world targetKey slot value → O.Unique world →
    DB.lookup slot world ≡ just (O.recordOf owner (O.noteVector targetKey value)) →
    DB.lookup slot (DB.erase (length world) (keep targetKey) world) ≡ nothing
  vectorRemoved world targetKey slot value unique found =
    Erase.removed (keep targetKey) world slot _ unique found (dropsVector targetKey slot value)

  targetKept : O.World → ℕ → O.Reference → Bool
  targetKept world targetKey ref with DB.lookup (O.target ref) world
  ... | nothing = false
  ... | just row = keep targetKey (O.target ref) row
  referencesKept : O.World → ℕ → List O.Reference → Bool
  referencesKept world targetKey [] = true
  referencesKept world targetKey (ref ∷ refs) = targetKept world targetKey ref ∧ referencesKept world targetKey refs
  checks : O.World → ℕ → O.World → Bool
  checks world targetKey [] = true
  checks world targetKey ((key , row) ∷ rows) with keep targetKey key row
  ... | false = checks world targetKey rows
  ... | true = referencesKept world targetKey (O.references (O.body row)) ∧ checks world targetKey rows
  safe : O.World → ℕ → Bool
  safe world targetKey = checks world targetKey world

  refsSound : ∀ world targetKey refs → referencesKept world targetKey refs ≡ true → All.All (λ ref → targetKept world targetKey ref ≡ true) refs
  refsSound world targetKey [] proof = All.[]
  refsSound world targetKey (ref ∷ refs) proof = Store.andLeft _ _ proof All.∷ refsSound world targetKey refs (Store.andRight _ _ proof)
  checksSound : ∀ world targetKey rows → checks world targetKey rows ≡ true →
    All.All (λ row → keep targetKey (proj₁ row) (proj₂ row) ≡ true →
      All.All (λ ref → targetKept world targetKey ref ≡ true) (O.references (O.body (proj₂ row)))) rows
  checksSound world targetKey [] proof = All.[]
  checksSound world targetKey ((key , value) ∷ rows) proof with keep targetKey key value in retained
  ... | false = (λ claimed → ⊥-elim (impossible (trans (sym retained) claimed))) All.∷ checksSound world targetKey rows proof
    where impossible : false ≢ true
          impossible ()
  ... | true = (λ claimed → refsSound world targetKey (O.references (O.body value)) (Store.andLeft _ _ proof)) All.∷
    checksSound world targetKey rows (Store.andRight _ _ proof)

  module Valid (before : O.World) (valid : O.Admissible before) (targetKey : ℕ) (released : safe before targetKey ≡ true) where
    predicate = keep targetKey
    after = DB.erase (length before) predicate before
    unique = O.Admissible.unique valid
    uniqueAfter : O.Unique after
    uniqueAfter = Erase.afterUnique predicate before unique
    source : ∀ {row} → row ∈ after → Erase.Source predicate before (proj₁ row) (proj₂ row)
    source {row} present = Erase.source predicate before _ _ unique (Order.memberLookup after _ _ uniqueAfter present)
    sound : ∀ {row} → row ∈ after → O.SoundReferences after row
    sound {row} present = All.tabulate resolve
      where
      origin = source present
      oldSound = Storage.lookupAll before (proj₁ row) (proj₂ row) (O.Admissible.sound valid) (Erase.Source.found origin)
      checked = Storage.lookupAll before (proj₁ row) (proj₂ row) (checksSound before targetKey before released) (Erase.Source.found origin)
      resolve : ∀ {ref} → ref ∈ O.references (O.body (proj₂ row)) → O.Resolves after (O.owner (proj₂ row)) ref
      resolve {ref} included = record
        { value = O.Resolves.value old
        ; found = Erase.retains (length before) predicate before (O.target ref) (O.Resolves.value old) (O.Resolves.found old) kept
        ; rightKind = O.Resolves.rightKind old; rightOwner = O.Resolves.rightOwner old }
        where
        old = All.lookup oldSound included
        kept : predicate (O.target ref) (O.Resolves.value old) ≡ true
        kept with DB.lookup (O.target ref) before | O.Resolves.found old | All.lookup (checked (Erase.Source.retained origin)) included
        ... | .(just (O.Resolves.value old)) | refl | proof = proof
    admissible : O.Admissible after
    admissible = record
      { unique = uniqueAfter
      ; placed = All.tabulate (λ {row} present → Storage.lookupAll before _ _ (O.Admissible.placed valid) (Erase.Source.found (source present)))
      ; sound = All.tabulate sound
      ; privateBookkeeping = All.tabulate (λ {row} present → Storage.lookupAll before _ _ (O.Admissible.privateBookkeeping valid) (Erase.Source.found (source present))) }

  count : O.World → ℕ
  count [] = zero
  count ((key , O.recordOf actualOwner (O.note payload)) ∷ rows) with E.ownerEqual actualOwner owner | Views.Codec.decode codec payload
  ... | yes _ | just item with Canonical.compare Codecs.knowledgeId (K.KnowledgeItem.id item) id
  ...   | yes _ = suc (count rows)
  ...   | no _ = count rows
  count ((key , O.recordOf actualOwner (O.note payload)) ∷ rows) | _ | _ = count rows
  count (row ∷ rows) = count rows

  data Plan (world : O.World) : Set where
    absent : Notes.find world ≡ nothing → Plan world
    remove : (found : Notes.Located world) → O.Unique world → count world ≤ 1 → safe world (Notes.Located.slot found) ≡ true → Plan world
  makePlan : (world : O.World) → Maybe (Plan world)
  makePlan world with Saved.observe world | Requested.observe world
  ... | just current | just resolved with
    Canonical.compare Codecs.familyId (I.FamilyTarget.expectedFamily target) (O.PolicyVersionInfo.familyId (Saved.Saved.info current)) |
    Canonical.compare Codecs.familyId (I.FamilyTarget.expectedFamily target) (O.RegistrationInfo.id (Requested.Target.registration resolved)) |
    O.CheckoutInfo.retired (Requested.Target.checkout resolved)
  ...   | yes _ | yes _ | false with Notes.find world in found
  ...     | nothing = just (absent found)
  ...     | just note with Access.allowed (Notes.Located.oldItem note) (Requested.Target.checkout resolved) | Store.unique? world | count world ≤? 1 | safe world (Notes.Located.slot note) in ready | Canonical.compare Codecs.familyId (K.KnowledgeItem.family (Notes.Located.oldItem note)) (O.PolicyVersionInfo.familyId (Saved.Saved.info current))
  ...       | just permitted | yes unique | yes one | true | yes _ = just (remove note unique one ready)
  ...       | _ | _ | _ | _ | _ = nothing
  makePlan world | just current | just resolved | _ | _ | _ = nothing
  makePlan world | _ | _ = nothing

  message : String
  message = "The note and its derived search records have been removed."
  guidance : String → D.Prompt
  guidance reason = D.prompt (D.text 'I' (" cannot finish the note request yet: " ++ reason))
    (D.text 'C' "heck the repository and worktree or let an active search finish, then continue this saved request.") []
  apply : ∀ world → Maybe (Plan world) → DB.Transaction String
  apply world nothing = DB.abort "The repository or worktree needs attention, or a search is still using this note."
  apply world (just (absent missing)) = DB.commit message
  apply world (just (remove found unique one ready)) = DB.eraseRows (length world) (keep (Notes.Located.slot found)) (DB.commit message)
  transaction : DB.Transaction String
  transaction = DB.scan (λ world → apply world (makePlan world))
  frame : ∀ before plan answer after → DB.evaluate (apply before plan) before ≡ DB.committed answer after → Ledger.ReceiptFrame before after
  frame before nothing answer after ()
  frame before (just (absent missing)) .message .before refl key receiptOwner receipt = (λ found → found) , (λ found → found)
  frame before (just (remove found unique one ready)) .message .(DB.erase (length before) (keep (Notes.Located.slot found)) before) refl =
    Erase.frame (length before) (keep (Notes.Located.slot found)) before unique (keepsReceipt (Notes.Located.slot found))
  effect : Ledger.Effect
  effect = record { transaction = transaction; guidance = guidance
    ; isolates = λ before answer after committed → frame before (makePlan before) answer after committed }
  delete : ℕ → DB.Transaction Ledger.Reply
  delete expected = Ledger.update (I.Mutation.operationId request) (Identity.mutation Identity.kDeleteNote request) expected Ledger.complete effect
  completedRetry : ∀ names expected receiptSlot receiptOwner answer world →
    Ledger.find (I.Mutation.operationId request) world ≡ just (Ledger.found receiptSlot receiptOwner
      (Receipt.finished (Identity.mutation Identity.kDeleteNote request) names answer)) →
    DB.execute (delete expected) world ≡ (Ledger.saved answer , world)
  completedRetry names expected receiptSlot receiptOwner answer world =
    Ledger.finishedSkipsEffect (I.Mutation.operationId request) (Identity.mutation Identity.kDeleteNote request)
      names expected Ledger.complete effect receiptSlot receiptOwner answer world
  atomicBoundary : ∀ expected before observed → Exec.Interrupted (Exec.atomic (delete expected) Exec.done) before observed →
    observed ≡ before ⊎ observed ≡ proj₂ (DB.execute (delete expected) before)
  atomicBoundary expected before observed = Ledger.atomicBoundary (delete expected) before observed

  -- A committed delete and its completed receipt share one transaction.
  -- Any interruption followed by a completed retry reaches the same world.
  module Completed (before : O.World) (valid : O.Admissible before) (found : Notes.Located before)
    (one : count before ≤ 1) (released : safe before (Notes.Located.slot found) ≡ true)
    (selectedPlan : makePlan before ≡ just (remove found (O.Admissible.unique valid) one released))
    (names : Receipt.Names (I.Mutation.operationId request) (Identity.mutation Identity.kDeleteNote request))
    (receiptSlot : ℕ) (receiptOwner : O.Owner) (sameOwner : receiptOwner ≡ owner) (work : Receipt.Work)
    (receiptFound : Ledger.find (I.Mutation.operationId request) before ≡ just (Ledger.found receiptSlot receiptOwner
      (Receipt.active (Identity.mutation Identity.kDeleteNote request) names work)))
    (receiptAt : DB.lookup receiptSlot before ≡ just (Ledger.recordAt receiptOwner
      (Receipt.active (Identity.mutation Identity.kDeleteNote request) names work))) where
    idRequest = I.Mutation.operationId request
    meaning = Identity.mutation Identity.kDeleteNote request
    changed = DB.erase (length before) (keep (Notes.Located.slot found)) before
    oldReceipt = Ledger.recordAt {id = idRequest} receiptOwner (Receipt.active meaning names work)
    finalReceipt = Ledger.recordAt {id = idRequest} receiptOwner (Receipt.finished meaning names message)
    after = DB.write receiptSlot finalReceipt changed
    performed : DB.evaluate transaction before ≡ DB.committed message changed
    performed rewrite selectedPlan = refl
    commits : DB.execute (delete (Receipt.generation work)) before ≡ (Ledger.saved message , after)
    commits = Ledger.committedUpdate idRequest meaning names Ledger.complete effect receiptSlot receiptOwner work before message changed receiptFound performed
    receiptInChanged : DB.lookup receiptSlot changed ≡ just oldReceipt
    receiptInChanged = Erase.retains (length before) (keep (Notes.Located.slot found)) before receiptSlot oldReceipt receiptAt
      (keepsReceipt (Notes.Located.slot found) receiptSlot receiptOwner (Receipt.entry idRequest (Receipt.active meaning names work)))
    changedValid : O.Admissible changed
    changedValid = Valid.admissible before valid (Notes.Located.slot found) released
    afterValid : O.Admissible after
    afterValid = Storage.writeAdmissible changed receiptSlot oldReceipt finalReceipt changedValid receiptInChanged refl refl tt (λ ref ())
    distinct : receiptSlot ≢ Notes.Located.slot found
    distinct = Frames.lookupDistinct before receiptSlot oldReceipt (Notes.Located.slot found)
      (O.recordOf owner (O.note (Notes.Located.oldPayload found))) receiptAt (Notes.Located.stored found) (λ ())
    noteAbsent : DB.lookup (Notes.Located.slot found) after ≡ nothing
    noteAbsent = trans (DB.writePreservesOther receiptSlot (Notes.Located.slot found) finalReceipt changed distinct)
      (noteRemoved before found (O.Admissible.unique valid))
    foreignPreserved : ∀ key value → DB.lookup key before ≡ just value → O.owner value ≢ owner → DB.lookup key after ≡ just value
    foreignPreserved key value present different = trans
      (DB.writePreservesOther receiptSlot key finalReceipt changed
        (Checkpoint.ownerDistinct before receiptSlot oldReceipt key value receiptAt present
          (λ same → different (trans (sym same) sameOwner))))
      (otherFamilyPreserved before (Notes.Located.slot found) key value present different)
    retry : DB.execute (delete (Receipt.generation work)) after ≡ (Ledger.saved message , after)
    retry = completedRetry names (Receipt.generation work) receiptSlot receiptOwner message after
      (Ledger.writtenReceiptVisible idRequest receiptSlot receiptOwner (Receipt.finished meaning names message) changed)
    boundary : ∀ observed → Exec.Interrupted (Exec.atomic (delete (Receipt.generation work)) Exec.done) before observed →
      observed ≡ before ⊎ observed ≡ after
    boundary observed interrupted with atomicBoundary (Receipt.generation work) before observed interrupted
    ... | inj₁ same = inj₁ same
    ... | inj₂ same = inj₂ (trans same (cong proj₂ commits))
    completedAtomic : ∀ observed reply final → Exec.Completed (Exec.atomic (delete (Receipt.generation work)) Exec.done) observed reply final →
      DB.execute (delete (Receipt.generation work)) observed ≡ (reply , final)
    completedAtomic observed reply final (Exec.committed Exec.stop) = refl
    converges : ∀ observed reply final → Exec.Interrupted (Exec.atomic (delete (Receipt.generation work)) Exec.done) before observed →
      Exec.Completed (Exec.atomic (delete (Receipt.generation work)) Exec.done) observed reply final → final ≡ after
    converges observed reply final interrupted completed with boundary observed interrupted
    ... | inj₁ same = trans (sym (cong proj₂ (completedAtomic observed reply final completed)))
      (trans (cong (λ world → proj₂ (DB.execute (delete (Receipt.generation work)) world)) same) (cong proj₂ commits))
    ... | inj₂ same = trans (sym (cong proj₂ (completedAtomic observed reply final completed)))
      (trans (cong (λ world → proj₂ (DB.execute (delete (Receipt.generation work)) world)) same) (cong proj₂ retry))
    retryAchievesDeletion : ∀ observed reply final → Exec.Interrupted (Exec.atomic (delete (Receipt.generation work)) Exec.done) before observed →
      Exec.Completed (Exec.atomic (delete (Receipt.generation work)) Exec.done) observed reply final →
      DB.lookup (Notes.Located.slot found) final ≡ nothing
    retryAchievesDeletion observed reply final interrupted completed =
      subst (λ world → DB.lookup (Notes.Located.slot found) world ≡ nothing) (sym (converges observed reply final interrupted completed)) noteAbsent
