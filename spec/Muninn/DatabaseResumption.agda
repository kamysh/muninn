{-# OPTIONS --safe #-}
-- Responsive waiting and receipt-first continuation when database access returns.
module Muninn.DatabaseResumption where

import Muninn.OwnedState as O
import Muninn.Config as Config
import Muninn.Dialogue as D
import Muninn.RequestAdmission as Admission
import Muninn.ReceiptLedger as Ledger
import Muninn.ReceiptTypes as R
import Muninn.RequestIdentity as Identity
import Muninn.IdentityDialogue as Guidance
open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂; trans)
module DB = O.DB

-- The enclosing connection/preparation adapter supplies these observations.
-- Usable means access to the shared receipt store is ready, not TCP reachability.
data Access : Set where
  waiting usable : Access

record Session : Set where
  constructor session
  field bootstrap : Config.BootstrapConfig
        context : D.Context
        access : Access

observe : Access → Session → Session
observe access before = session (Session.bootstrap before) (Session.context before) access

observeAll : List Access → Session → Session
observeAll [] before = before
observeAll (access ∷ rest) before = observeAll rest (observe access before)

keepsContext : ∀ observations before → Session.context (observeAll observations before) ≡ Session.context before
keepsContext [] before = refl
keepsContext (access ∷ rest) before = keepsContext rest (observe access before)

keepsBootstrap : ∀ observations before → Session.bootstrap (observeAll observations before) ≡ Session.bootstrap before
keepsBootstrap [] before = refl
keepsBootstrap (access ∷ rest) before = keepsBootstrap rest (observe access before)

keepsRequestId : ∀ observations before → D.Context.id (Session.context (observeAll observations before)) ≡ D.Context.id (Session.context before)
keepsRequestId observations before = cong D.Context.id (keepsContext observations before)

observationKeepsSession : ∀ observations access before → observe access (observeAll observations before) ≡ observe access before
observationKeepsSession observations access before = cong₂ (λ bootstrap ctx → session bootstrap ctx access)
  (keepsBootstrap observations before) (keepsContext observations before)

waitingPrompt : D.Prompt
waitingPrompt = D.prompt
  (D.text 'I' " cannot reach the database right now, so I cannot check the saved work for this request.")
  (D.text 'R' "estore database access, then continue with the same request ID. I will check its saved work before continuing.") []

module Protocol
  (Environment : Set)
  (Fields : List String)
  (Prerequisites : Identity.Meaning → O.World → Environment → Set)
  (Result : Identity.Meaning → Set)
  (Achieved : (subject : Identity.Meaning) → O.World → Result subject → Set)
  where
  module Adapter = Admission.Protocol Environment Fields Prerequisites Result Achieved

  -- A pure MCP response can be produced without opening a DB transaction.
  Step : Set
  Step = Adapter.Reply ⊎ DB.Transaction Adapter.Reply

  inspect : Identity.Meaning → D.Context → DB.Transaction Adapter.Reply
  inspect subject ctx = DB.scan (λ world → DB.commit
    (Adapter.ledgerReply ctx subject (Ledger.inspect (D.Context.id ctx) subject world)))

  step : Identity.Meaning → Session → Step
  step subject (session bootstrap ctx waiting) = inj₁ (Adapter.ask (just ctx) waitingPrompt)
  step subject (session bootstrap ctx usable) = inj₂ (inspect subject ctx)

  perform : Step → O.World → Adapter.Reply × O.World
  perform (inj₁ reply) world = reply , world
  perform (inj₂ transaction) world = DB.execute transaction world

  serve : Identity.Meaning → Session → O.World → Adapter.Reply × O.World
  serve subject current = perform (step subject current)

  waitingIsPure : ∀ subject bootstrap ctx → step subject (session bootstrap ctx waiting) ≡ inj₁ (Adapter.ask (just ctx) waitingPrompt)
  waitingIsPure subject bootstrap ctx = refl

  waitingResponds : ∀ subject bootstrap ctx world →
    serve subject (session bootstrap ctx waiting) world ≡ (Adapter.ask (just ctx) waitingPrompt , world)
  waitingResponds subject bootstrap ctx world = refl

  preservesWorld : ∀ subject current world → proj₂ (serve subject current world) ≡ world
  preservesWorld subject (session bootstrap ctx waiting) world = refl
  preservesWorld subject (session bootstrap ctx usable) world = refl

  bootstrapNotInReply : ∀ subject first second ctx access world →
    serve subject (session first ctx access) world ≡ serve subject (session second ctx access) world
  bootstrapNotInReply subject first second ctx waiting world = refl
  bootstrapNotInReply subject first second ctx usable world = refl

  currentReceiptFirst : ∀ subject current world →
    serve subject (observe usable current) world ≡
      (Adapter.ledgerReply (Session.context current) subject
        (Ledger.inspect (D.Context.id (Session.context current)) subject world) , world)
  currentReceiptFirst subject current world = refl

  resumesActive : ∀ subject bootstrap ctx access slot owner (names : R.Names (D.Context.id ctx) subject) progress world →
    Ledger.find (D.Context.id ctx) world ≡ just (Ledger.found slot owner (R.active subject names progress)) →
    serve subject (observe usable (session bootstrap ctx access)) world ≡
      (Adapter.knownWork (D.Context.id ctx) subject slot progress , world)
  resumesActive subject bootstrap ctx access slot owner names progress world found
    rewrite found with Identity.sameRequest subject subject
  ... | yes same = refl
  ... | no different = ⊥-elim (different refl)

  replaysCompleted : ∀ subject bootstrap ctx access slot owner (names : R.Names (D.Context.id ctx) subject) result world →
    Ledger.find (D.Context.id ctx) world ≡ just (Ledger.found slot owner (R.finished subject names result)) →
    serve subject (observe usable (session bootstrap ctx access)) world ≡
      (Adapter.historicalResult (D.Context.id ctx) result , world)
  replaysCompleted subject bootstrap ctx access slot owner names result world found
    rewrite found with Identity.sameRequest subject subject
  ... | yes same = refl
  ... | no different = ⊥-elim (different refl)

  reclaimedHistoryContinuesDialogue : ∀ subject bootstrap ctx access slot owner world →
    Ledger.find (D.Context.id ctx) world ≡ just (Ledger.found slot owner R.used) →
    serve subject (observe usable (session bootstrap ctx access)) world ≡
      (Adapter.ask (just ctx) (Guidance.advicePrompt Ledger.historyReclaimed) , world)
  reclaimedHistoryContinuesDialogue subject bootstrap ctx access slot owner world found rewrite found = refl

  changedRequestContinuesDialogue : ∀ subject original bootstrap ctx access slot owner (names : R.Names (D.Context.id ctx) original) progress world →
    Ledger.find (D.Context.id ctx) world ≡ just (Ledger.found slot owner (R.active original names progress)) → subject ≢ original →
    serve subject (observe usable (session bootstrap ctx access)) world ≡
      (Adapter.ask (just ctx) (Guidance.advicePrompt Ledger.differentRequest) , world)
  changedRequestContinuesDialogue subject original bootstrap ctx access slot owner names progress world found different
    rewrite found with Identity.sameRequest subject original
  ... | yes same = ⊥-elim (different same)
  ... | no mismatch = refl

  missingWorkContinuesDialogue : ∀ subject bootstrap ctx access world → Ledger.find (D.Context.id ctx) world ≡ Data.Maybe.nothing →
    serve subject (observe usable (session bootstrap ctx access)) world ≡
      (Adapter.ask (just ctx) (Guidance.advicePrompt Ledger.unknownId) , world)
  missingWorkContinuesDialogue subject bootstrap ctx access world found rewrite found = refl

  resumesAfterObservations : ∀ subject observations current slot owner
    (names : R.Names (D.Context.id (Session.context current)) subject) progress world →
    Ledger.find (D.Context.id (Session.context current)) world ≡ just (Ledger.found slot owner (R.active subject names progress)) →
    serve subject (observe usable (observeAll observations current)) world ≡
      (Adapter.knownWork (D.Context.id (Session.context current)) subject slot progress , world)
  resumesAfterObservations subject observations current slot owner names progress world found = trans
    (cong (λ state → serve subject state world) (observationKeepsSession observations usable current))
    (resumesActive subject (Session.bootstrap current) (Session.context current) (Session.access current) slot owner names progress world found)
