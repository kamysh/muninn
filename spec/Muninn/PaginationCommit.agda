{-# OPTIONS --safe #-}
-- A page and its traversal checkpoint are published in one shared transaction.
-- Private continuations carry no strong references to indexed content.
module Muninn.PaginationCommit where
import Muninn.PaginationData as P
import Muninn.Pagination as Page
import Muninn.PaginationStore as Store
import Muninn.OwnedState as O
import Muninn.WorkQueue as Q
import Muninn.RecordAllocation as Allocation
import Muninn.ReceiptLedger as Ledger
import Muninn.CatalogInputs as I
import Muninn.Types as T
open import Data.Nat using (ℕ; _≟_; _≤?_; _≤_; _<_)
open import Data.List using (List; []; length; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String)
open import Data.Bool using (false)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
module DB = O.DB
module Exec = O.Execution

data Reply : Set where
  served : P.Token → Reply
  queued : P.Token → Reply
  continueWork : Reply
  explain : String → Reply

module Family (family : ℕ) (queryId : I.OperationId) (tokenId : T.UUID) where
  module Saved = Store.Family family
  module Query = Saved.Query queryId
  module Token = Query.Token tokenId
  owner = O.family family

  info : P.Payload → Q.Continuation
  info payload = record { parent = queryId; payload = Q.page payload; search = nothing }
  planRow : P.Plan → O.Record
  planRow plan = Saved.newRow (info (P.plan plan)) (P.weakIds plan)
  tokenRow : P.Token → O.Record
  tokenRow token = Saved.newRow (info (P.token token)) []

  -- Admission never overwrites another query or repeats its initial capture.
  -- A caller has to provide the independent source/ranking capture first.
  capture : P.Plan → DB.Transaction Reply
  capture plan = DB.scan λ world → existing world (Query.Plans.find world)
    where
    first : P.Token
    first = record { id = tokenId; query = queryId; start = 0; served = nothing }
    existing : ∀ world → Maybe (Query.Plans.At world) → DB.Transaction Reply
    existing world (just previous) = DB.commit (explain "This search ID already has saved work. Continue that search, or use a fresh ID for a different query.")
    existing world nothing with Ledger.sameId (P.Plan.id plan) queryId | Store.tokenReserved tokenId world
    ... | no _ | _ = DB.commit (explain "The search ID does not match the saved query. Use its original ID or start a new search.")
    ... | _ | Data.Bool.true = DB.commit (explain "This continuation ID is already in use. Choose a fresh ID for the new search.")
    ... | yes _ | false = DB.put (Allocation.freshId world) (planRow plan)
      (DB.scan (λ tentative → DB.put (Allocation.freshId tentative) (tokenRow first) (DB.commit (queued first))))

  module Initial (before : O.World) (valid : O.Admissible before) (plan : P.Plan) where
    first : P.Token
    first = record { id = tokenId; query = queryId; start = 0; served = nothing }
    middle = DB.write (Allocation.freshId before) (planRow plan) before
    middleValid : O.Admissible middle
    middleValid = Saved.insertAdmissible before valid (info (P.plan plan)) (P.weakIds plan)
    after = DB.write (Allocation.freshId middle) (tokenRow first) middle
    afterValid : O.Admissible after
    afterValid = Saved.insertAdmissible middle middleValid (info (P.token first)) []
    commits : Query.Plans.find before ≡ nothing → Store.tokenReserved tokenId before ≡ false → P.Plan.id plan ≡ queryId →
      DB.execute (capture plan) before ≡ (queued first , after)
    commits absent unused same rewrite absent | unused with Ledger.sameId (P.Plan.id plan) queryId
    ... | yes _ = refl
    ... | no different = ⊥-elim (different same)

  -- Each concrete query adapter checks source ownership, current eligibility,
  -- scope, profile and saved identities in this exact transaction snapshot.
  -- A false check arranges the existing explanation/restart conversation.
  module Checked (Eligible : O.World → P.Plan → List P.Item → Set)
    (eligible? : ∀ world plan rows → Maybe (Eligible world plan rows)) where
    replayPage : ∀ world plan token → P.Receipt (P.Token.start token) → I.Page → DB.Transaction Reply
    replayPage world plan token receipt page with I.Page.size page ≟ P.Receipt.size receipt
    ... | no different = DB.commit (explain "This page was already returned with a different page size. Reuse that size, or start a new search.")
    ... | yes same with eligible? world plan (P.Receipt.rows receipt)
    ...   | nothing = DB.commit (explain "The saved search view is no longer available. Continue with the saved query in a new view.")
    ...   | just checked = DB.commit (served token)
    replaySnapshot : ∀ world plan token receipt page (checked : Eligible world plan (P.Receipt.rows receipt)) →
      I.Page.size page ≡ P.Receipt.size receipt → eligible? world plan (P.Receipt.rows receipt) ≡ just checked →
      DB.execute (replayPage world plan token receipt page) world ≡ (served token , world)
    replaySnapshot world plan token receipt page checked same accepted with I.Page.size page ≟ P.Receipt.size receipt
    ... | no different = ⊥-elim (different same)
    ... | yes equal rewrite accepted = refl
    record Ready (world : O.World) (plan : P.Plan) (token : P.Token) (page : I.Page) : Set where
      field next : Page.Next plan token page
            source : Eligible world plan (Page.slice (P.Token.start token) (I.Page.size page) (P.Plan.known plan))
            offsetValid : P.Token.start token ≤ length (P.Plan.known plan)
            nonemptyOrFinished : 0 < length (Page.slice (P.Token.start token) (I.Page.size page) (P.Plan.known plan)) ⊎ P.Plan.pending plan ≡ []
            freshNext : ∀ id → Page.nextId next ≡ just id →
              Store.tokenReserved id world ≡ false
    -- The source adapter supplies a Next only after arranging more work when
    -- required. It cannot say done while any captured source remains pending.
    seal : (world : O.World) → (planAt : Query.Plans.At world) → (tokenAt : Token.Tokens.At world) →
      (page : I.Page) → Ready world (Query.Plans.At.value planAt) (Token.Tokens.At.value tokenAt) page → DB.Transaction Reply
    seal world planAt tokenAt page ready with P.Token.served token
      where token = Token.Tokens.At.value tokenAt
    ... | just receipt = replayPage world (Query.Plans.At.value planAt) (Token.Tokens.At.value tokenAt) receipt page
    seal world planAt tokenAt page ready | nothing = DB.put (Token.Tokens.At.slot tokenAt) (tokenRow frozen) following
      where
      plan = Query.Plans.At.value planAt
      token = Token.Tokens.At.value tokenAt
      frozen = Page.freeze plan token page (Ready.next ready)
      -- Successor storage is in the same transaction as the old page receipt.
      -- Its offset is the end of that exact page, never the later plan length.
      following : DB.Transaction Reply
      following with P.Token.served frozen
      ... | nothing = DB.commit continueWork
      ... | just receipt with P.Receipt.next receipt
      ...   | nothing = DB.commit (served frozen)
      ...   | just id = DB.scan (λ tentative →
          DB.put (Allocation.freshId tentative) (tokenRow (Page.successor queryId receipt id)) (DB.commit (served frozen)))

    -- Preparation reads actual cursor rows, never a caller-supplied fake world.
    call : (page : I.Page) →
      (∀ world (planAt : Query.Plans.At world) (tokenAt : Token.Tokens.At world) →
        Maybe (Ready world (Query.Plans.At.value planAt) (Token.Tokens.At.value tokenAt) page)) → DB.Transaction Reply
    call page prepare = DB.scan λ world → inspect world (Query.Plans.find world) (Token.Tokens.find world)
      where
      inspect : ∀ world → Maybe (Query.Plans.At world) → Maybe (Token.Tokens.At world) → DB.Transaction Reply
      inspect world (just planAt) (just tokenAt) with P.Token.served (Token.Tokens.At.value tokenAt)
      ... | just receipt = replayPage world (Query.Plans.At.value planAt) (Token.Tokens.At.value tokenAt) receipt page
      ... | nothing with prepare world planAt tokenAt
      ...   | nothing = DB.commit continueWork
      ...   | just ready = seal world planAt tokenAt page ready
      inspect world _ _ = DB.commit (explain "I no longer have this search continuation. I can use the query from our conversation to start it again; otherwise please give me the query and repository.")

    callReplay : ∀ page prepare world (planAt : Query.Plans.At world) (tokenAt : Token.Tokens.At world)
      (receipt : P.Receipt (P.Token.start (Token.Tokens.At.value tokenAt)))
      (checked : Eligible world (Query.Plans.At.value planAt) (P.Receipt.rows receipt)) →
      Query.Plans.find world ≡ just planAt → Token.Tokens.find world ≡ just tokenAt →
      P.Token.served (Token.Tokens.At.value tokenAt) ≡ just receipt →
      I.Page.size page ≡ P.Receipt.size receipt →
      eligible? world (Query.Plans.At.value planAt) (P.Receipt.rows receipt) ≡ just checked →
      DB.execute (call page prepare) world ≡ (served (Token.Tokens.At.value tokenAt) , world)
    callReplay page prepare world planAt tokenAt receipt checked planFound tokenFound recorded same accepted
      rewrite planFound | tokenFound | recorded = replaySnapshot world (Query.Plans.At.value planAt) (Token.Tokens.At.value tokenAt) receipt page checked same accepted

    atomicPage : ∀ page prepare before observed →
      Exec.Interrupted (Exec.atomic (call page prepare) Exec.done) before observed →
      observed ≡ before ⊎ observed ≡ proj₂ (DB.execute (call page prepare) before)
    atomicPage page prepare before observed = Ledger.atomicBoundary (call page prepare) before observed

  idlePlanHasNoHolds : ∀ plan → O.references (O.body (planRow plan)) ≡ []
  idlePlanHasNoHolds plan = refl
  idleTokenHasNoHolds : ∀ token → O.references (O.body (tokenRow token)) ≡ []
  idleTokenHasNoHolds token = refl
