{-# OPTIONS --safe #-}
-- The total closed dispatcher: every executable request carries the
-- independently specified proof instance for its operation. There is no
-- constructor that accepts a raw Script, and local editing cannot execute.
module Muninn.Dispatcher where

import Muninn.Catalog as Catalog
import Muninn.CatalogInputs as I
import Muninn.OwnedState as O
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module Execution = O.Execution
World = O.World

-- The required proof instance for one operation: the independently fixed
-- outcome goal and preservation frame (interface parameters, never
-- operation-supplied record fields), plus the complete interruption, retry
-- and constructive-termination contract.
record Operation (Input : Set) : Set₂ where
  field Result : Set
        Goal : Input → World → World → Set
        Frame : Input → World → World → Set
        recoverable : Execution.Recoverable Input Result Goal Frame

-- Which requests are operations. Local editing cannot carry an arbitrary
-- database script; its effectful Save, Check, Start and Refresh actions use
-- their shared public intents instead.
data OperationRequest : Catalog.Request → Set where
  isUser : ∀ adapter input → OperationRequest (Catalog.user adapter input)
  isBackground : ∀ job input → OperationRequest (Catalog.background job input)
  isControl : ∀ event input → OperationRequest (Catalog.control event input)

-- Local editing has no operation instance of any kind.
data NoOperation : Set₂ where

OperationOf : Catalog.Request → Set₂
OperationOf (Catalog.user adapter input) = Operation (I.IntentInput (Catalog.canonicalIntent adapter))
OperationOf (Catalog.background job input) = Operation (I.JobInput job)
OperationOf (Catalog.control event input) = Operation (I.ControlInput event)
OperationOf (Catalog.localUi input) = NoOperation

-- The only executable state: a registered operation carrying its full proof
-- instance. No constructor accepts a raw Script.
data Dispatched : Catalog.Request → Set₂ where
  run : ∀ {request} → OperationRequest request → OperationOf request → Dispatched request

-- Every executable state originates from a registered proof-carrying
-- operation; nothing else is constructible.
executesRegistered : ∀ request → Dispatched request → OperationRequest request × OperationOf request
executesRegistered request (run registered requirement) = registered , requirement

-- Local editing has no executable state at all.
localUiCannotExecute : ∀ input → Dispatched (Catalog.localUi input) → ⊥
localUiCannotExecute input (run registered requirement) with registered
... | ()

-- The complete contract one accepted operation carries.
module Contract (Input Result : Set) (Goal Frame : Input → World → World → Set)
  (requirement : Execution.Recoverable Input Result Goal Frame) where

  script : Input → O.DB.Rows → Execution.Script Result
  script = Execution.Recoverable.script requirement

  preserves : ∀ input before after →
    Execution.Interrupted (script input before) before after → Frame input before after
  preserves = Execution.Recoverable.preserves requirement

  converges : ∀ input before interrupted final result →
    Execution.Interrupted (script input before) before interrupted →
    Execution.Completed (script input interrupted) interrupted result final →
    Goal input before final
  converges = Execution.Recoverable.converges requirement

  terminates : ∀ input before →
    Σ Result (λ result → Σ O.DB.Rows (λ final → Execution.Completed (script input before) before result final))
  terminates = Execution.Recoverable.terminates requirement

  -- The operation keeps its registered proof instance throughout execution.
  keepsRegistration : ∀ input before →
    Σ (Execution.Script Result) (λ selected →
      selected ≡ script input before ×
      (∀ after → Execution.Interrupted selected before after → Frame input before after))
  keepsRegistration input before =
    script input before , refl , preserves input before
