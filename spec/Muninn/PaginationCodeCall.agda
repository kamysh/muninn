{-# OPTIONS --safe #-}
-- Concrete checkout eligibility for the atomic pagination operation.
module Muninn.PaginationCodeCall where
import Muninn.PaginationData as P
import Muninn.PaginationCommit as Commit
import Muninn.PaginationSource as Source
import Muninn.OwnedState as O
import Muninn.StoredPolicy as Policy
import Muninn.CatalogInputs as I
import Muninn.Types as T
import Muninn.SearchResumption as Resumption
import Muninn.RepositoryIdentity as Repository
import Muninn.Dialogue as D
open import Data.Nat using (ℕ)
open import Data.List using (List; map)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≢_)

module Family (family registrationSlot selected pointer : ℕ) (queryId : I.OperationId) (tokenId : T.UUID) where
  module Operation = Commit.Family family queryId tokenId
  record Eligible (world : O.World) (plan : P.Plan) (rows : List P.Item) : Set where
    field policy : Policy.Family.Saved family pointer world
          identity : Source.ScopeWitness family selected world (P.Plan.view plan)
    module Saved = Source.Checkout family selected pointer world policy (P.Plan.view plan) identity
    field view : Saved.Snapshot
    module Visible = Saved.In view
    field visible : All Visible.Row (map P.Item.ref rows)
  check : ∀ world plan rows → Maybe (Eligible world plan rows)
  check world plan rows with Policy.Family.observe family pointer world | Source.Identity.observe family registrationSlot selected world (P.Plan.view plan)
  ... | nothing | _ = nothing
  ... | _ | nothing = nothing
  ... | just policy | just identity = snapshot policy identity
    where
    module Saved = Source.Checkout family selected pointer world policy (P.Plan.view plan) identity
    snapshot : ∀ policy identity → Maybe (Eligible world plan rows)
    snapshot policy identity with Source.Checkout.observe family selected pointer world policy (P.Plan.view plan) identity
    ... | nothing = nothing
    ... | just view with Source.Checkout.In.restoreAll family selected pointer world policy (P.Plan.view plan) identity view (map P.Item.ref rows)
    ...   | nothing = nothing
    ...   | just visible = just record { policy = policy; identity = identity; view = view; visible = visible }
  module Checked = Operation.Checked Eligible check
  -- A restart reuses the actual saved query before asking for context and
  -- shares the existing authorized indexing scheduler, not a second queue.
  module Restart (jobId : I.OperationId) (separate : queryId ≢ jobId)
    (ctx : D.Context) (observed : Repository.Observation) where
    module Existing = Resumption.Family family registrationSlot selected pointer queryId jobId separate ctx observed
    resume = Existing.resume
