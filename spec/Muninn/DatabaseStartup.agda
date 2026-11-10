{-# OPTIONS --safe #-}
-- Startup keeps the connection conversation responsive until public readiness.
module Muninn.DatabaseStartup where
import Muninn.OwnedState as O
import Muninn.Config as Config
import Muninn.Connection as Connection
import Muninn.Dialogue as D
import Muninn.DatabaseResumption as Resume
import Muninn.MigrationBlock as Block
import Muninn.MigrationSequence as Migration
import Muninn.Schema as Schema
import Muninn.Worktree as W
import Muninn.Types as T
open import Data.List using (List; [])
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String)
open import Data.Unit using (⊤)
open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

configuredMode : Maybe Config.SslMode → Connection.Mode
configuredMode nothing = Connection.prefer
configuredMode (just Config.Disable) = Connection.disable
configuredMode (just Config.Allow) = Connection.allow
configuredMode (just Config.Prefer) = Connection.prefer
configuredMode (just Config.Require) = Connection.require
configuredMode (just Config.VerifyCa) = Connection.verifyCa
configuredMode (just Config.VerifyFull) = Connection.verifyFull

present : ∀ {A : Set} → Maybe A → Bool
present nothing = false
present (just _) = true

-- The observed transport must follow the configured initial choice or its
-- specifically permitted fallback; certificate and authentication failures
-- cannot be presented as a server declining TLS.
data Negotiated (mode : Connection.Mode) : Connection.Transport → Set where
  initialTransport : Negotiated mode (Connection.initial mode)
  permittedFallback : ∀ observation transport →
    Connection.fallback mode (Connection.initial mode) observation ≡ just transport → Negotiated mode transport

tlsOptions : Connection.Mode → Config.DbConfig → Set
tlsOptions Connection.disable config =
  (Config.DbConfig.sslRootCert config ≡ nothing) × (Config.DbConfig.sslClientCert config ≡ nothing) × (Config.DbConfig.sslClientKey config ≡ nothing)
tlsOptions Connection.allow config = ⊤
tlsOptions Connection.prefer config = ⊤
tlsOptions Connection.require config = ⊤
tlsOptions Connection.verifyCa config = ⊤
tlsOptions Connection.verifyFull config = ⊤

-- Runtime connection observations must satisfy the selected transport and use
-- the documented credential-source order; they cannot replace the bootstrap.
record Connected (bootstrap : Config.BootstrapConfig) : Set where
  field transport : Connection.Transport
        trusted hostnameMatches : Bool
        environmentPassword filePassword selectedPassword : Maybe String
        environmentPasswordFile defaultPasswordFile selectedPasswordFile : Maybe T.FilePath
        passwordFileSelection : selectedPasswordFile ≡ Connection.firstAvailable
          (Config.DbConfig.pgpassfile (Config.BootstrapConfig.database bootstrap)) environmentPasswordFile defaultPasswordFile
        nonemptyEnvironment : ∀ password → environmentPassword ≡ just password → password ≢ ""
        credential : selectedPassword ≡ Connection.firstAvailable
          (Config.DbConfig.password (Config.BootstrapConfig.database bootstrap)) environmentPassword filePassword
        negotiated : Negotiated (configuredMode (Config.DbConfig.sslMode (Config.BootstrapConfig.database bootstrap))) transport
        permittedOptions : tlsOptions (configuredMode (Config.DbConfig.sslMode (Config.BootstrapConfig.database bootstrap)))
          (Config.BootstrapConfig.database bootstrap)
        secureMode : Connection.admissible
          (configuredMode (Config.DbConfig.sslMode (Config.BootstrapConfig.database bootstrap)))
          transport trusted hostnameMatches ≡ true
        clientIdentity : Connection.validIdentity
          (present (Config.DbConfig.sslClientCert (Config.BootstrapConfig.database bootstrap)))
          (present (Config.DbConfig.sslClientKey (Config.BootstrapConfig.database bootstrap))) ≡ true

connectedPolicyAllPaths : ∀ bootstrap (connected : Connected bootstrap) path →
  Connection.pathPolicy path (configuredMode (Config.DbConfig.sslMode (Config.BootstrapConfig.database bootstrap)))
    (Connected.transport connected) (Connected.trusted connected) (Connected.hostnameMatches connected) ≡ true
connectedPolicyAllPaths bootstrap connected path = Connected.secureMode connected

module Installation (codec : Block.LedgerCodec) (required : Schema.Template) (schema : W.SchemaId)
  (requirements : List Migration.Requirement) (blocks : List Block.Block) where
  module M = Migration.Sequence codec
  data Status (bootstrap : Config.BootstrapConfig) (world : O.World) : Set where
    unavailable preparing : Status bootstrap world
    available : Connected bootstrap → M.PublicReady required schema requirements blocks world → Status bootstrap world

  record Session (world : O.World) : Set where
    constructor session
    field bootstrap : Config.BootstrapConfig
          context : D.Context
          status : Status bootstrap world

  -- Connection observations do not replace credentials or conversation state.
  observe : ∀ {before after} (previous : Session before) → Status (Session.bootstrap previous) after → Session after
  observe previous status = session (Session.bootstrap previous) (Session.context previous) status
  keepsBootstrap : ∀ {before after} (previous : Session before) (status : Status (Session.bootstrap previous) after) →
    Session.bootstrap (observe previous status) ≡ Session.bootstrap previous
  keepsBootstrap previous status = refl
  keepsContext : ∀ {before after} (previous : Session before) (status : Status (Session.bootstrap previous) after) →
    Session.context (observe previous status) ≡ Session.context previous
  keepsContext previous status = refl

  preparingPrompt : D.Prompt
  preparingPrompt = D.prompt (D.text 'I' " am preparing the database for use.")
    (D.text 'I' " will continue the saved request when preparation is complete.") []
  data Next (bootstrap : Config.BootstrapConfig) (world : O.World) : Set where
    explain : D.Prompt → Next bootstrap world
    continue : Connected bootstrap → M.PublicReady required schema requirements blocks world → Next bootstrap world
  next : ∀ {world} (current : Session world) → Next (Session.bootstrap current) world
  next (session bootstrap ctx unavailable) = explain Resume.waitingPrompt
  next (session bootstrap ctx preparing) = explain preparingPrompt
  next (session bootstrap ctx (available connected ready)) = continue connected ready

  unavailableNeedsNoTransaction : ∀ {world} bootstrap ctx →
    next (session {world} bootstrap ctx unavailable) ≡ explain Resume.waitingPrompt
  unavailableNeedsNoTransaction bootstrap ctx = refl
  preparingDoesNotRunRequest : ∀ {world} bootstrap ctx →
    next (session {world} bootstrap ctx preparing) ≡ explain preparingPrompt
  preparingDoesNotRunRequest bootstrap ctx = refl
  proceedsOnlyWhenReady : ∀ {world} (ready : M.PublicReady required schema requirements blocks world) bootstrap ctx (connected : Connected bootstrap) →
    next (session {world} bootstrap ctx (available connected ready)) ≡ continue connected ready
  proceedsOnlyWhenReady ready bootstrap ctx connected = refl

  -- Connection details are internal evidence and are never rendered in the
  -- startup dialogue, including while waiting for the database.
  visiblePrompt : ∀ {bootstrap world} → Next bootstrap world → Maybe D.Prompt
  visiblePrompt (explain guidance) = just guidance
  visiblePrompt (continue connected ready) = nothing
  waitingDoesNotExposeBootstrap : ∀ {world} first second ctx →
    visiblePrompt (next (session {world} first ctx unavailable)) ≡
    visiblePrompt (next (session {world} second ctx unavailable))
  waitingDoesNotExposeBootstrap first second ctx = refl
  preparingDoesNotExposeBootstrap : ∀ {world} first second ctx →
    visiblePrompt (next (session {world} first ctx preparing)) ≡
    visiblePrompt (next (session {world} second ctx preparing))
  preparingDoesNotExposeBootstrap first second ctx = refl
