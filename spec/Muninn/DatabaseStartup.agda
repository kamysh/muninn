{-# OPTIONS --safe #-}
-- Database-dependent work waits for a usable connection and starts again
-- after unfinished transactional preparation has been rolled back.
module Muninn.DatabaseStartup where

import Muninn.Config as Config
import Muninn.Connection as Connection
import Muninn.Database as Database
import Muninn.Schema as Schema
import Muninn.Worktree as W
import Muninn.Dialogue as D
open import Data.List using (List; [])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true)
open import Data.String using (String)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Relation.Nullary using (Dec; ¬_)

configuredMode : Maybe Config.SslMode → Connection.Mode
configuredMode nothing = Connection.prefer
configuredMode (just Config.Disable) = Connection.disable
configuredMode (just Config.Allow) = Connection.allow
configuredMode (just Config.Prefer) = Connection.prefer
configuredMode (just Config.Require) = Connection.require
configuredMode (just Config.VerifyCa) = Connection.verifyCa
configuredMode (just Config.VerifyFull) = Connection.verifyFull

-- Every connection path uses the configured TLS mode and credential sources.
-- In particular, prefer retains its configured plaintext fallback behavior.
record Connected (bootstrap : Config.BootstrapConfig) : Set where
  field transport : Connection.Transport
        trusted hostnameMatches : Bool
        environmentPassword filePassword selectedPassword : Maybe String
        selectedCredential : selectedPassword ≡ Connection.firstAvailable
          (Config.DbConfig.password (Config.BootstrapConfig.database bootstrap)) environmentPassword filePassword
        transportAllowed : Connection.admissible
          (configuredMode (Config.DbConfig.sslMode (Config.BootstrapConfig.database bootstrap)))
          transport trusted hostnameMatches ≡ true

connectionPolicy : ∀ bootstrap (connected : Connected bootstrap) path →
  Connection.pathPolicy path
    (configuredMode (Config.DbConfig.sslMode (Config.BootstrapConfig.database bootstrap)))
    (Connected.transport connected) (Connected.trusted connected) (Connected.hostnameMatches connected) ≡ true
connectionPolicy bootstrap connected path = Connected.transportAllowed connected

-- Readiness comes from the application migration ledger and AGE separately.
record Ready (required : Schema.FamilyTemplate) (ledger : Schema.Ledger) (pair : Schema.SchemaPair) : Set where
  field application : Schema.AppliedTemplate (Schema.FamilyTemplate.applicationMigrations required) ledger (Schema.SchemaPair.application pair)
        graph : Schema.GraphReady pair

-- An outage does not require a process restart, a manual retry, or a database
-- write to record a failed attempt. The operation input remains in the session.
data Access (bootstrap : Config.BootstrapConfig) (required : Schema.FamilyTemplate) (ledger : Schema.Ledger) (pair : Schema.SchemaPair) : Set where
  unavailable preparing : Access bootstrap required ledger pair
  available : Connected bootstrap → Ready required ledger pair → Access bootstrap required ledger pair

record Session (Operation : Set) (required : Schema.FamilyTemplate) (ledger : Schema.Ledger) (pair : Schema.SchemaPair) : Set where
  constructor session
  field bootstrap : Config.BootstrapConfig
        operation : Operation
        access : Access bootstrap required ledger pair

data Action : Set where
  reconnect prepare runOperation : Action

next : ∀ {Operation required ledger pair} → Session Operation required ledger pair → Action
next (session bootstrap operation unavailable) = reconnect
next (session bootstrap operation preparing) = prepare
next (session bootstrap operation (available connected ready)) = runOperation

observe : ∀ {Operation required ledger pair} (before : Session Operation required ledger pair) → Access (Session.bootstrap before) required ledger pair → Session Operation required ledger pair
observe (session bootstrap operation _) access = session bootstrap operation access

keepsOperation : ∀ {Operation required ledger pair} (before : Session Operation required ledger pair) (access : Access (Session.bootstrap before) required ledger pair) →
  Session.operation (observe before access) ≡ Session.operation before
keepsOperation (session bootstrap operation previous) access = refl

keepsBootstrap : ∀ {Operation required ledger pair} (before : Session Operation required ledger pair) (access : Access (Session.bootstrap before) required ledger pair) →
  Session.bootstrap (observe before access) ≡ Session.bootstrap before
keepsBootstrap (session bootstrap operation previous) access = refl

automaticReconnect : ∀ {Operation required ledger pair} bootstrap (operation : Operation) →
  next (session {Operation} {required} {ledger} {pair} bootstrap operation unavailable) ≡ reconnect
automaticReconnect bootstrap operation = refl

runsWhenAvailable : ∀ {Operation required ledger pair} bootstrap (operation : Operation) (connected : Connected bootstrap) (ready : Ready required ledger pair) →
  next (observe (session bootstrap operation unavailable) (available connected ready)) ≡ runOperation
runsWhenAvailable bootstrap operation connected ready = refl

unavailableMessage : D.Prompt
unavailableMessage = D.prompt
  (D.text 'I' " cannot reach the database, so this operation cannot proceed yet.")
  (D.text 'I' " will reconnect automatically and continue the operation when access returns. Check the database connection if it remains unavailable.") []

-- When automatic recovery cannot resolve the problem, the caller supplies
-- specific plain-language guidance and a practical next step.
needsHelp : D.Text → D.Text → D.Prompt
needsHelp explanation nextStep = D.prompt explanation nextStep []

module Transactions (Key Value : Set) (equal : (a b : Key) → Dec (a ≡ b)) where
  module DB = Database.Store Key Value equal

  -- The transaction interpreter restores the original rows on abort. Retrying
  -- the operation from those rows is therefore the same as a fresh execution.
  retryAfterRollback : ∀ {A} (transaction : DB.Transaction A) original result →
    DB.evaluate transaction original ≡ DB.aborted result →
    DB.execute transaction (proj₂ (DB.execute transaction original)) ≡ DB.execute transaction original
  retryAfterRollback transaction original result aborted =
    cong (DB.execute transaction) (DB.abortKeepsStore transaction original result aborted)


  -- Schema changes and the ordinary migration ledger entry commit together.
  migration : Key → Value → Key → Value → DB.Transaction ⊤
  migration schemaKey schemaValue ledgerKey ledgerValue =
    DB.put schemaKey schemaValue (DB.put ledgerKey ledgerValue (DB.commit tt))

  migrationLedgerVisible : ∀ schemaKey schemaValue ledgerKey ledgerValue rows →
    DB.lookup ledgerKey (proj₂ (DB.execute (migration schemaKey schemaValue ledgerKey ledgerValue) rows)) ≡ just ledgerValue
  migrationLedgerVisible schemaKey schemaValue ledgerKey ledgerValue rows =
    DB.writeVisible ledgerKey ledgerValue (DB.write schemaKey schemaValue rows)

  migrationSchemaVisible : ∀ schemaKey schemaValue ledgerKey ledgerValue rows →
    ¬ (ledgerKey ≡ schemaKey) →
    DB.lookup schemaKey (proj₂ (DB.execute (migration schemaKey schemaValue ledgerKey ledgerValue) rows)) ≡ just schemaValue
  migrationSchemaVisible schemaKey schemaValue ledgerKey ledgerValue rows distinct =
    trans (DB.writePreservesOther ledgerKey schemaKey ledgerValue (DB.write schemaKey schemaValue rows) distinct)
      (DB.writeVisible schemaKey schemaValue rows)

  -- An aborted transaction leaves no failed-operation record; the same
  -- migration may be executed again on the unchanged store.
  retryMigration : ∀ schemaKey schemaValue ledgerKey ledgerValue original (interruptedResult : ⊤) →
    DB.evaluate (DB.put schemaKey schemaValue (DB.put ledgerKey ledgerValue (DB.abort interruptedResult))) original ≡ DB.aborted interruptedResult →
    DB.execute (migration schemaKey schemaValue ledgerKey ledgerValue)
      (proj₂ (DB.execute (DB.put schemaKey schemaValue (DB.put ledgerKey ledgerValue (DB.abort interruptedResult))) original)) ≡
    DB.execute (migration schemaKey schemaValue ledgerKey ledgerValue) original
  retryMigration schemaKey schemaValue ledgerKey ledgerValue original interruptedResult interrupted =
    cong (DB.execute (migration schemaKey schemaValue ledgerKey ledgerValue))
      (DB.abortKeepsStore (DB.put schemaKey schemaValue (DB.put ledgerKey ledgerValue (DB.abort interruptedResult))) original interruptedResult interrupted)
