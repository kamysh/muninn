{-# OPTIONS --safe #-}
-- Actual private continuation rows; page operations never commit reader holds.
module Muninn.PaginationStore where
import Muninn.OwnedState as O
import Muninn.WorkQueue as Q
import Muninn.PaginationData as P
import Muninn.ExclusionOutcomes as E
import Muninn.ReceiptLedger as Ledger
import Muninn.RequestCodecs as Codecs
import Muninn.Canonical as C
import Muninn.CatalogInputs as I
import Muninn.Types as T
import Muninn.CleanupStorage as Storage
import Muninn.RecordAllocation as Allocation
import Muninn.CleanupAdmissionStorage as Insert
open import Data.Nat using (ℕ; _≟_)
open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
module DB = O.DB

tokenReserved : T.UUID → O.World → Data.Bool.Bool
tokenReserved id [] = false
tokenReserved id ((key , O.recordOf owner (O.continuation weak info)) ∷ rows) with Q.Continuation.payload info
... | Q.page (P.token token) with C.compare Codecs.uuid id (P.Token.id token)
...   | yes _ = true
...   | no _ = tokenReserved id rows
tokenReserved id ((key , O.recordOf owner (O.continuation weak info)) ∷ rows) | _ = tokenReserved id rows
tokenReserved id (row ∷ rows) = tokenReserved id rows

module Family (family : ℕ) where
  owner = O.family family
  module Find (A : Set) (select : Q.Continuation → Maybe A) where
    record At (world : O.World) : Set where
      field slot : ℕ
            weak : List ℕ
            info : Q.Continuation
            value : A
            located : DB.lookup slot world ≡ just (O.recordOf owner (O.continuation weak info))
            selected : select info ≡ just value
    inspect : ∀ world slot → (row : Maybe O.Record) → DB.lookup slot world ≡ row → Maybe (At world)
    inspect world slot (just (O.recordOf actualOwner (O.continuation weak info))) located with E.ownerEqual actualOwner owner
    ... | no other = nothing
    ... | yes refl with select info in selected
    ...   | nothing = nothing
    ...   | just value = just record { slot = slot; weak = weak; info = info; value = value; located = located; selected = selected }
    inspect world slot row located = nothing
    scan : (world : O.World) → O.World → Maybe (At world)
    scan world [] = nothing
    scan world ((slot , value) ∷ rest) with inspect world slot (DB.lookup slot world) refl
    ... | just found = just found
    ... | nothing = scan world rest
    find : (world : O.World) → Maybe (At world)
    find world = scan world world

  module Query (queryId : I.OperationId) where
    plan : Q.Continuation → Maybe P.Plan
    plan info with Ledger.sameId (Q.Continuation.parent info) queryId | Q.Continuation.payload info
    ... | yes same | Q.page (P.plan saved) with Ledger.sameId (P.Plan.id saved) queryId
    ...   | yes _ = just saved
    ...   | no _ = nothing
    plan info | _ | _ = nothing
    module Plans = Find P.Plan plan

    module Token (tokenId : T.UUID) where
      select : Q.Continuation → Maybe P.Token
      select info with Ledger.sameId (Q.Continuation.parent info) queryId | Q.Continuation.payload info
      ... | yes parent | Q.page (P.token saved) with C.compare Codecs.uuid (P.Token.id saved) tokenId | Ledger.sameId (P.Token.query saved) queryId
      ...   | yes _ | yes _ = just saved
      ...   | _ | _ = nothing
      select info | _ | _ = nothing
      module Tokens = Find P.Token select

  -- Replacement of private bookkeeping cannot invalidate any incoming strong
  -- reference: such references are forbidden by the existing store invariant.
  module Replace (world : O.World) (valid : O.Admissible world) (slot : ℕ)
    (oldWeak : List ℕ) (oldInfo : Q.Continuation)
    (found : DB.lookup slot world ≡ just (O.recordOf owner (O.continuation oldWeak oldInfo)))
    (newWeak : List ℕ) (newInfo : Q.Continuation) where
    added = O.recordOf owner (O.continuation newWeak newInfo)
    after = DB.write slot added world
    noIncoming : All.All (O.NoIncomingTo slot) world
    noIncoming = O.privateUnreferenced slot world _ valid found refl
    shifted : All.All (O.SoundReferences after) world
    shifted = All.zipWith (λ {row} (refs , publics) → All.zipWith (λ {ref} (resolved , visible) → keep (proj₂ row) ref resolved visible) (refs , publics)) (O.Admissible.sound valid , O.Admissible.privateBookkeeping valid)
      where
      keep : ∀ value ref → O.Resolves world (O.owner value) ref → O.PublicReference ref → O.Resolves after (O.owner value) ref
      keep value ref resolved publicRef = record
        { value = O.Resolves.value resolved
        ; found = trans (DB.writePreservesOther slot (O.target ref) added world different) (O.Resolves.found resolved)
        ; rightKind = O.Resolves.rightKind resolved; rightOwner = O.Resolves.rightOwner resolved }
        where
        different : slot ≢ O.target ref
        different same = impossible (trans (sym (O.Resolves.found resolved))
          (trans (cong (λ key → DB.lookup key world) (sym same)) found))
          where
          impossible : just (O.Resolves.value resolved) ≡ just (O.recordOf owner (O.continuation oldWeak oldInfo)) → Data.Empty.⊥
          impossible sameValue = O.privateReferenceImpossible O.continuationK refl ref publicRef
            (trans (sym (O.Resolves.rightKind resolved)) (cong (λ row → O.kind (O.body row)) (just-injective sameValue)))
    admissible : O.Admissible after
    admissible = record
      { unique = Storage.writeUnique slot added world (O.Admissible.unique valid)
      ; placed = O.local All.∷ O.deleteAll slot world (O.Admissible.placed valid)
      ; sound = All.[] All.∷ O.deleteAll slot world shifted
      ; privateBookkeeping = All.[] All.∷ O.deleteAll slot world (O.Admissible.privateBookkeeping valid) }
    other : ∀ key → slot ≢ key → DB.lookup key after ≡ DB.lookup key world
    other key different = DB.writePreservesOther slot key added world different
    publicFrame : ∀ key value → DB.lookup key world ≡ just value → O.kind (O.body value) ≢ O.continuationK →
      DB.lookup key after ≡ just value
    publicFrame key value present external with slot ≟ key
    ... | no different = trans (other key different) present
    ... | yes refl = ⊥-elim (external (cong (λ row → O.kind (O.body row)) (just-injective (trans (sym present) found))))

  newRow : Q.Continuation → List ℕ → O.Record
  newRow info weak = O.recordOf owner (O.continuation weak info)
  createsNoReferences : ∀ info weak → O.references (O.body (newRow info weak)) ≡ []
  createsNoReferences info weak = refl
  remainsPrivate : ∀ info weak → O.privateTarget (O.kind (O.body (newRow info weak))) ≡ true
  remainsPrivate info weak = refl
  insertAdmissible : ∀ world → O.Admissible world → ∀ info weak →
    O.Admissible (DB.write (Allocation.freshId world) (newRow info weak) world)
  insertAdmissible world valid info weak = Insert.insertAdmissible world (Allocation.freshId world) (newRow info weak)
    valid (Allocation.fresh world) O.local All.[] All.[]
