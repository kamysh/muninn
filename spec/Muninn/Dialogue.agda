{-# OPTIONS --safe #-}
-- A finite dialogue turn around the fixed operation catalog. Context is
-- transient here; identity-checked persistence/recovery belongs to receipts.
module Muninn.Dialogue where

open import Data.Char using (Char)
open import Data.String as String using (String; _≟_; _++_)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans)
open import Muninn.Catalog using (Request)
open import Muninn.CatalogInputs using (OperationId)
import Muninn.Database
import Muninn.OwnedState as Owned

-- Nonempty guidance is structural; plain-language quality remains reviewable.
record Text : Set where
  constructor text
  field first : Char
        rest : String

render : Text → String
render (text first rest) = String.fromList (first ∷ String.toList rest)

module Facts = Muninn.Database.Store String String _≟_

record Context : Set where
  constructor context
  field id : OperationId
        originalIntent : String
        facts : Facts.Rows
        workRefs : List OperationId

fresh : OperationId → String → Context
fresh id intent = context id intent [] []

repair : String → String → Context → Context
repair key value ctx = context (Context.id ctx) (Context.originalIntent ctx)
  (Facts.write key value (Context.facts ctx)) (Context.workRefs ctx)

repairKeepsIntent : ∀ key value ctx →
  Context.originalIntent (repair key value ctx) ≡ Context.originalIntent ctx
repairKeepsIntent key value ctx = refl

repairKeepsIdentity : ∀ key value ctx → Context.id (repair key value ctx) ≡ Context.id ctx
repairKeepsIdentity key value ctx = refl

repairKeepsWork : ∀ key value ctx → Context.workRefs (repair key value ctx) ≡ Context.workRefs ctx
repairKeepsWork key value ctx = refl

repairKeepsOtherFacts : ∀ key other value ctx → key ≢ other →
  Facts.lookup other (Context.facts (repair key value ctx)) ≡ Facts.lookup other (Context.facts ctx)
repairKeepsOtherFacts key other value ctx distinct =
  Facts.writePreservesOther key other value (Context.facts ctx) distinct

repairMany : List (String × String) → Context → Context
repairMany [] ctx = ctx
repairMany ((key , value) ∷ updates) ctx = repairMany updates (repair key value ctx)

repairManyKeepsIntent : ∀ updates ctx →
  Context.originalIntent (repairMany updates ctx) ≡ Context.originalIntent ctx
repairManyKeepsIntent [] ctx = refl
repairManyKeepsIntent ((key , value) ∷ updates) ctx =
  trans (repairManyKeepsIntent updates (repair key value ctx)) (repairKeepsIntent key value ctx)

repairManyKeepsIdentity : ∀ updates ctx → Context.id (repairMany updates ctx) ≡ Context.id ctx
repairManyKeepsIdentity [] ctx = refl
repairManyKeepsIdentity ((key , value) ∷ updates) ctx =
  trans (repairManyKeepsIdentity updates (repair key value ctx)) (repairKeepsIdentity key value ctx)

repairManyKeepsWork : ∀ updates ctx → Context.workRefs (repairMany updates ctx) ≡ Context.workRefs ctx
repairManyKeepsWork [] ctx = refl
repairManyKeepsWork ((key , value) ∷ updates) ctx =
  trans (repairManyKeepsWork updates (repair key value ctx)) (repairKeepsWork key value ctx)

repairManyKeepsOtherFacts : ∀ updates ctx other →
  All (λ update → Data.Product.proj₁ update ≢ other) updates →
  Facts.lookup other (Context.facts (repairMany updates ctx)) ≡ Facts.lookup other (Context.facts ctx)
repairManyKeepsOtherFacts [] ctx other [] = refl
repairManyKeepsOtherFacts ((key , value) ∷ updates) ctx other (distinct ∷ rest) =
  trans (repairManyKeepsOtherFacts updates (repair key value ctx) other rest)
    (repairKeepsOtherFacts key other value ctx distinct)

record Option : Set where
  constructor option
  field label : Text
        consequences : Text
        updates : List (String × String)

-- Context recovery has its own generic prompt. An existing Context can only
-- ask for a specific detail, correction, prerequisite or explicit choice.
data Question : Set where
  detail : Text → Question
  correction : Text → Text → Question
  alternatives : Option → List Option → Question
  prerequisite : Text → Text → Question

lostExplanation : Text
lostExplanation = text 'I' " no longer have the earlier context."

lostAction : Text
lostAction = text 'S' "end the original request again, including the details you already supplied."

explanation : Question → Text
explanation (detail requested) = text 'I' (" need " ++ render requested ++ " to continue.")
explanation (correction requested reason) = reason
explanation (alternatives first rest) = text 'T' "here are several ways to continue; each option explains what would change."
explanation (prerequisite reason action) = reason

nextAction : Question → Text
nextAction (detail requested) = text 'P' ("rovide " ++ render requested ++ ".")
nextAction (correction requested reason) = text 'S' ("end a corrected value for " ++ render requested ++ ".")
nextAction (alternatives first rest) = text 'C' "hoose one of the listed options."
nextAction (prerequisite reason action) = action

record Prompt : Set where
  constructor prompt
  field reason : Text
        action : Text
        choices : List (Text × Text)

questionPrompt : Question → Prompt
questionPrompt q@(detail requested) = prompt (explanation q) (nextAction q) []
questionPrompt q@(correction requested reason) = prompt (explanation q) (nextAction q) []
questionPrompt q@(alternatives first rest) = prompt (explanation q) (nextAction q)
  (map (λ choice → Option.label choice , Option.consequences choice) (first ∷ rest))
questionPrompt q@(prerequisite reason action) = prompt (explanation q) (nextAction q) []

-- These parameters belong to the independent catalog/schema/outcome model,
-- not to individual handlers. A handler cannot supply weaker prerequisites
-- or manufacture a successful result by selecting its own completion test.
module Protocol
  (Environment : Set)
  (Fields : List String)
  (Matches : Context → Request → Set)
  (Prerequisites : Request → Owned.World → Environment → Set)
  (Result : Request → Set)
  (Achieved : (request : Request) → Owned.World → Result request → Set)
  where

  record Permission (ctx : Context) (world : Owned.World) (env : Environment) : Set where
    field request : Request
          matches : Matches ctx request
          prerequisites : Prerequisites request world env

  record Answer (ctx : Context) (world : Owned.World) : Set where
    field request : Request
          result : Result request
          matches : Matches ctx request
          achieved : Achieved request world result

  -- A valid admission cannot be ignored in favour of another question.
  -- Available completed answers are selected before the checker runs.
  data Assessment (ctx : Context) (world : Owned.World) (env : Environment) : Set where
    ready : Permission ctx world env → Assessment ctx world env
    done : Answer ctx world → Assessment ctx world env
    needs : ¬ (Permission ctx world env) → Question → Assessment ctx world env

  record Checker : Set where
    field assess : ∀ ctx world env → Assessment ctx world env

  assessWithCache : Checker → ∀ ctx world env → Maybe (Answer ctx world) → Assessment ctx world env
  assessWithCache checker ctx world env (just answer) = done answer
  assessWithCache checker ctx world env nothing = Checker.assess checker ctx world env

  cachedResultIsReused : ∀ checker ctx world env answer →
    assessWithCache checker ctx world env (just answer) ≡ done answer
  cachedResultIsReused checker ctx world env answer = refl

  data Phase (world : Owned.World) (env : Environment) : Set where
    noContext : Phase world env
    examining : (ctx : Context) → Maybe (Answer ctx world) → Phase world env
    responded : (ctx : Context) → Assessment ctx world env → Phase world env

  promptFor : ∀ {world env} → Phase world env → Maybe Prompt
  promptFor noContext = just (prompt lostExplanation lostAction [])
  promptFor (examining ctx cached) = nothing
  promptFor (responded ctx (ready permission)) = nothing
  promptFor (responded ctx (done answer)) = nothing
  promptFor (responded ctx (needs blocked question)) = just (questionPrompt question)

  contextOf : ∀ {world env} → Phase world env → Maybe Context
  contextOf noContext = nothing
  contextOf (examining ctx cached) = just ctx
  contextOf (responded ctx assessment) = just ctx

  record Recovered (world : Owned.World) : Set where
    constructor recovered
    field ctx : Context
          cached : Maybe (Answer ctx world)

  resume : ∀ {world env} → Maybe (Recovered world) → Phase world env
  resume nothing = noContext
  resume (just (recovered ctx cached)) = examining ctx cached

  reconnect : ∀ {world env} → Phase world env → Maybe (Recovered world) → Phase world env
  reconnect noContext available = resume available
  reconnect (examining ctx cached) available = examining ctx cached
  reconnect (responded ctx assessment) available = responded ctx assessment

  reconnectKeepsKnownState : ∀ {world env} ctx assessment available →
    reconnect {world} {env} (responded ctx assessment) available ≡ responded ctx assessment
  reconnectKeepsKnownState ctx assessment available = refl

  resumeReusesAvailableContext : ∀ {world env} ctx cached →
    contextOf (resume {world} {env} (just (recovered ctx cached))) ≡ just ctx
  resumeReusesAvailableContext ctx cached = refl

  resumeWithoutContextAsksAgain : ∀ {world env} → resume {world} {env} nothing ≡ noContext
  resumeWithoutContextAsksAgain = refl

  -- One total assessment ends the local turn. No server-generated agent reply,
  -- generative-model call or operation execution is an internal transition.
  data Internal : ∀ {world env} → Phase world env → Phase world env → Set where
    evaluate : ∀ {world env} checker ctx cached →
      Internal {world} {env} (examining ctx cached)
        (responded ctx (assessWithCache checker ctx world env cached))

  noTwoInternalSteps : ∀ {world env} {a b c : Phase world env} →
    Internal a b → Internal b c → ⊥
  noTwoInternalSteps (evaluate checker ctx cached) ()

  internalKeepsContext : ∀ {world env} {a b : Phase world env} →
    Internal a b → contextOf a ≡ contextOf b
  internalKeepsContext (evaluate checker ctx cached) = refl

  changeEnvironment : ∀ {world beforeEnv afterEnv} → Phase world beforeEnv → Phase world afterEnv
  changeEnvironment noContext = noContext
  changeEnvironment (examining ctx cached) = examining ctx cached
  changeEnvironment (responded ctx (done answer)) = responded ctx (done answer)
  changeEnvironment (responded ctx (ready permission)) = examining ctx nothing
  changeEnvironment (responded ctx (needs blocked question)) = examining ctx nothing

  completedResultSurvivesEnvironmentChange : ∀ {world beforeEnv afterEnv} ctx answer →
    changeEnvironment {world} {beforeEnv} {afterEnv} (responded ctx (done answer)) ≡
      responded ctx (done answer)
  completedResultSurvivesEnvironmentChange ctx answer = refl

  -- External inputs are explicit. In particular choosing an alternative is
  -- possible only with a calling-agent choice from the offered, nonempty list.
  data Interaction : ∀ {world beforeEnv afterEnv} →
    Phase world beforeEnv → Phase world afterEnv → Set where
    providedContext : ∀ {world env} ctx → Interaction {world} {env} {env} noContext (examining ctx nothing)
    restored : ∀ {world env} ctx cached → Interaction {world} {env} {env} noContext (examining ctx cached)
    reconnected : ∀ {world env} phase available →
      Interaction {world} {env} {env} phase (reconnect phase available)
    corrected : ∀ {world env ctx blocked question} updates →
      All (λ update → Data.Product.proj₁ update ∈ Fields) updates →
      Interaction {world} {env} {env} (responded ctx (needs blocked question))
        (examining (repairMany updates ctx) nothing)
    clarified : ∀ {world env ctx blocked question} nextQuestion →
      Interaction {world} {env} {env} (responded ctx (needs blocked question))
        (responded ctx (needs blocked nextQuestion))
    contextStillNeeded : ∀ {world env} → Interaction {world} {env} {env} noContext noContext
    chosen : ∀ {world env ctx blocked first rest} selected → selected ∈ (first ∷ rest) →
      All (λ update → Data.Product.proj₁ update ∈ Fields) (Option.updates selected) →
      Interaction {world} {env} {env} (responded ctx (needs blocked (alternatives first rest)))
        (examining (repairMany (Option.updates selected) ctx) nothing)
    environmentChanged : ∀ {world beforeEnv afterEnv} phase →
      Interaction {world} {beforeEnv} {afterEnv} phase (changeEnvironment phase)
    contextLost : ∀ {world beforeEnv afterEnv} (phase : Phase world beforeEnv) →
      Interaction {world} {beforeEnv} {afterEnv} phase noContext

  -- World-index equality covers all owned persistent categories. Losing
  -- transient dialogue context cannot cancel accepted work or erase receipts.
  data Step : ∀ {beforeWorld afterWorld beforeEnv afterEnv} →
    Phase beforeWorld beforeEnv → Phase afterWorld afterEnv → Set where
    internal : ∀ {world env} {a b : Phase world env} → Internal a b → Step a b
    external : ∀ {world beforeEnv afterEnv} {a : Phase world beforeEnv} {b : Phase world afterEnv} →
      Interaction a b → Step a b

  preservesOwnedWorld : ∀ {beforeWorld afterWorld beforeEnv afterEnv}
    {a : Phase beforeWorld beforeEnv} {b : Phase afterWorld afterEnv} →
    Step a b → beforeWorld ≡ afterWorld
  preservesOwnedWorld (internal step) = refl
  preservesOwnedWorld (external step) = refl

  data Dispatchable : ∀ {world env} → Phase world env → Set where
    admitted : ∀ {world env ctx} (permission : Permission ctx world env) →
      Dispatchable (responded ctx (ready permission))

  dispatchRequiresPrerequisites : ∀ {world env} {phase : Phase world env} →
    Dispatchable phase → Σ Request (λ request → Prerequisites request world env)
  dispatchRequiresPrerequisites (admitted permission) =
    Permission.request permission , Permission.prerequisites permission

  data Reportable : ∀ {world env} → Phase world env → Set where
    certified : ∀ {world env ctx} (answer : Answer ctx world) →
      Reportable {world} {env} (responded ctx (done answer))

  reportRequiresOutcome : ∀ {world env} {phase : Phase world env} → Reportable phase →
    Σ Request (λ request → Σ (Result request) (λ result → Achieved request world result))
  reportRequiresOutcome (certified answer) =
    Answer.request answer , Answer.result answer , Answer.achieved answer
