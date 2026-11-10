{-# OPTIONS --safe #-}
-- Restore page identities only from actual eligible rows in one saved view.
module Muninn.PaginationSource where
import Muninn.OwnedState as O
import Muninn.PaginationData as P
import Muninn.StoredPolicy as Policy
import Muninn.ContentViews as Content
import Muninn.ExclusionOutcomes as E
import Muninn.VectorData as V
import Muninn.ArtifactIdentity as Equal
import Muninn.Types as T
import Muninn.Canonical as C
import Muninn.RequestCodecs as Codecs
open import Data.Nat using (ℕ; _≟_)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Membership.DecPropositional
module Member = Data.List.Membership.DecPropositional _≟_
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Data.String using (String)
open import Data.Empty using (⊥)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
module DB = O.DB

snapshot : List P.Root → Maybe ℕ
snapshot [] = nothing
snapshot (P.snapshot key ∷ roots) = just key
snapshot (root ∷ roots) = snapshot roots

record ScopeWitness (family selected : ℕ) (world : O.World) (saved : P.View) : Set where
  field registrationSlot : ℕ
        registration : O.RegistrationInfo
        checkout : O.CheckoutInfo
        registered : DB.lookup registrationSlot world ≡ just (O.recordOf (O.family family) (O.registration registration))
        checkoutAt : DB.lookup selected world ≡ just (O.recordOf (O.family family) (O.checkout checkout))
        activeFamily : O.RegistrationInfo.retired registration ≡ false
        activeCheckout : O.CheckoutInfo.retired checkout ≡ false
        sameScope : P.View.scope saved ≡ P.checkout (O.RegistrationInfo.id registration) (O.CheckoutInfo.id checkout) (O.CheckoutInfo.incarnation checkout)

module Identity (family registrationSlot selected : ℕ) (world : O.World) (saved : P.View) where
  owner = O.family family
  check : ∀ registration checkout →
    DB.lookup registrationSlot world ≡ just (O.recordOf owner (O.registration registration)) →
    DB.lookup selected world ≡ just (O.recordOf owner (O.checkout checkout)) → Maybe (ScopeWitness family selected world saved)
  check registration checkout registered checkoutAt with P.View.scope saved in scope | O.RegistrationInfo.retired registration in retiredFamily | O.CheckoutInfo.retired checkout in retiredCheckout
  ... | P.checkout familyId checkoutId incarnation | false | false with
    C.compare Codecs.familyId familyId (O.RegistrationInfo.id registration) |
    C.compare Codecs.checkoutId checkoutId (O.CheckoutInfo.id checkout) |
    C.compare Codecs.uuid incarnation (O.CheckoutInfo.incarnation checkout)
  ...   | yes refl | yes refl | yes refl = just record
    { registrationSlot = registrationSlot; registration = registration; checkout = checkout
    ; registered = registered; checkoutAt = checkoutAt; activeFamily = retiredFamily; activeCheckout = retiredCheckout; sameScope = scope }
  ...   | _ | _ | _ = nothing
  check registration checkout registered checkoutAt | _ | _ | _ = nothing
  checkoutValue : ∀ registration → DB.lookup registrationSlot world ≡ just (O.recordOf owner (O.registration registration)) →
    (row : Maybe O.Record) → DB.lookup selected world ≡ row → Maybe (ScopeWitness family selected world saved)
  checkoutValue registration registered (just (O.recordOf actualOwner (O.checkout checkout))) located with E.ownerEqual actualOwner owner
  ... | yes refl = check registration checkout registered located
  ... | no _ = nothing
  checkoutValue registration registered row located = nothing
  familyValue : (row : Maybe O.Record) → DB.lookup registrationSlot world ≡ row → Maybe (ScopeWitness family selected world saved)
  familyValue (just (O.recordOf actualOwner (O.registration registration))) located with E.ownerEqual actualOwner owner
  ... | yes refl = checkoutValue registration located (DB.lookup selected world) refl
  ... | no _ = nothing
  familyValue row located = nothing
  observe : Maybe (ScopeWitness family selected world saved)
  observe = familyValue (DB.lookup registrationSlot world) refl

module Checkout (family selected pointer : ℕ) (world : O.World)
  (current : Policy.Family.Saved family pointer world) (saved : P.View)
  (identity : ScopeWitness family selected world saved) where
  owner = O.family family
  module Files = Content.Family (Policy.Family.rule family pointer current)
  record Snapshot : Set where
    field key : ℕ
          nodes edges : List ℕ
          payload : String
          sameRoot : snapshot (P.View.roots saved) ≡ just key
          located : DB.lookup key world ≡ just (O.recordOf owner (O.structuralSnapshot selected nodes edges payload))
          samePolicy : Policy.Family.Saved.version current ≡ P.View.policyVersion saved
          notRemoving : E.pendingRemovalFor owner world ≡ false
  inspect : ∀ key → snapshot (P.View.roots saved) ≡ just key → (row : Maybe O.Record) → DB.lookup key world ≡ row → Maybe Snapshot
  inspect key sameRoot (just (O.recordOf actualOwner (O.structuralSnapshot checkout nodes edges payload))) located with
    E.ownerEqual actualOwner owner | checkout ≟ selected | Policy.Family.Saved.version current ≟ P.View.policyVersion saved | E.pendingRemovalFor owner world in removing
  ... | yes refl | yes refl | yes samePolicy | false = just record
    { key = key; nodes = nodes; edges = edges; payload = payload; sameRoot = sameRoot
    ; located = located; samePolicy = samePolicy; notRemoving = removing }
  ... | _ | _ | _ | _ = nothing
  inspect key sameRoot row located = nothing
  observe : Maybe Snapshot
  observe with snapshot (P.View.roots saved) in sameRoot
  ... | nothing = nothing
  ... | just key = inspect key sameRoot (DB.lookup key world) refl

  module In (view : Snapshot) where
    record Code (path : T.FilePath) (key version : ℕ) : Set where
      field text : String
            gitDefault : Bool
            located : DB.lookup key world ≡ just (O.recordOf owner (O.chunk version text))
            visible : Files.visible world selected path ≡ just (Content.entry version gitDefault)
    record Symbol (key : ℕ) : Set where
      field path : T.FilePath
            version : ℕ
            text : String
            gitDefault : Bool
            located : DB.lookup key world ≡ just (O.recordOf owner (O.symbol version (T.FilePath.value path) text))
            visible : Files.visible world selected path ≡ just (Content.entry version gitDefault)
            inSnapshot : key ∈ Snapshot.nodes view
    record Vector (chunk slot : ℕ) : Set where
      field value : V.Value
            located : DB.lookup slot world ≡ just (O.recordOf owner (O.vector chunk (V.usable value)))
            profile : P.View.profile saved ≡ just (V.Value.profile value)
    data Row : P.Ref → Set where
      codeText : ∀ path key version → Code path key version → Row (P.codeRef path key version nothing)
      embedded : ∀ path key version slot → Code path key version → Vector key slot → Row (P.codeRef path key version (just slot))
      symbol : ∀ path key version → (found : Symbol key) → Symbol.path found ≡ path → Symbol.version found ≡ version → Row (P.symbolRef path key version)
      edge : ∀ key ordinal source target payload → DB.lookup key world ≡ just (O.recordOf owner (O.edge source target payload)) →
        key ∈ Snapshot.edges view → Symbol source → Symbol target → Row (P.edgeRef key ordinal)

    codeValue : ∀ path key version → (row : Maybe O.Record) → DB.lookup key world ≡ row → Maybe (Code path key version)
    codeValue path key version (just (O.recordOf actualOwner (O.chunk actual text))) located with E.ownerEqual actualOwner owner | actual ≟ version
    ... | yes refl | yes refl with Files.visible world selected path in visible
    ...   | nothing = nothing
    ...   | just cell with Content.Entry.version cell ≟ version
    ...     | no other = nothing
    ...     | yes refl = just record { text = text; gitDefault = Content.Entry.gitDefault cell; located = located; visible = visible }
    codeValue path key version (just (O.recordOf actualOwner (O.chunk actual text))) located | _ | _ = nothing
    codeValue path key version row located = nothing
    codeAt : ∀ path key version → Maybe (Code path key version)
    codeAt path key version = codeValue path key version (DB.lookup key world) refl

    symbolValue : ∀ key → (row : Maybe O.Record) → DB.lookup key world ≡ row → Maybe (Symbol key)
    symbolValue key (just (O.recordOf actualOwner (O.symbol version source text))) located with E.ownerEqual actualOwner owner | key Member.∈? Snapshot.nodes view
    ... | yes refl | yes member with Files.visible world selected path in visible
      where path = record { value = source }
    ...   | nothing = nothing
    ...   | just cell with Content.Entry.version cell ≟ version
    ...     | no other = nothing
    ...     | yes refl = just record { path = record { value = source }; version = version; text = text
        ; gitDefault = Content.Entry.gitDefault cell; located = located; visible = visible; inSnapshot = member }
    symbolValue key (just (O.recordOf actualOwner (O.symbol version source text))) located | _ | _ = nothing
    symbolValue key row located = nothing

    symbolAt : ∀ key → Maybe (Symbol key)
    symbolAt key = symbolValue key (DB.lookup key world) refl

    vectorValue : ∀ chunk slot → (row : Maybe O.Record) → DB.lookup slot world ≡ row → Maybe (Vector chunk slot)
    vectorValue chunk slot (just (O.recordOf actualOwner (O.vector actual (V.usable stored)))) located with
      E.ownerEqual actualOwner owner | actual ≟ chunk | P.View.profile saved in captured
    ... | yes refl | yes refl | just profile with Equal.EmbeddingKey? profile (V.Value.profile stored)
    ...   | yes refl = just record { value = stored; located = located; profile = captured }
    ...   | no _ = nothing
    vectorValue chunk slot (just (O.recordOf actualOwner (O.vector actual (V.usable stored)))) located | _ | _ | _ = nothing
    vectorValue chunk slot row located = nothing

    edgeValue : ∀ key ordinal → (row : Maybe O.Record) → DB.lookup key world ≡ row → Maybe (Row (P.edgeRef key ordinal))
    edgeValue key ordinal (just (O.recordOf actualOwner (O.edge source target payload))) located with
      E.ownerEqual actualOwner owner | key Member.∈? Snapshot.edges view | symbolAt source | symbolAt target
    ... | yes refl | yes member | just from | just to = just (edge key ordinal source target payload located member from to)
    ... | _ | _ | _ | _ = nothing
    edgeValue key ordinal row located = nothing

    restore : (ref : P.Ref) → Maybe (Row ref)
    restore (P.codeRef path key version nothing) with codeAt path key version
    ... | just found = just (codeText path key version found)
    ... | nothing = nothing
    restore (P.codeRef path key version (just slot)) with codeAt path key version | vectorValue key slot (DB.lookup slot world) refl
    ... | just found | just vector = just (embedded path key version slot found vector)
    ... | _ | _ = nothing
    restore (P.symbolRef path key version) with symbolAt key
    ... | nothing = nothing
    ... | just found with C.compare Codecs.path (Symbol.path found) path | Symbol.version found ≟ version
    ...   | yes refl | yes refl = just (symbol path key version found refl refl)
    ...   | _ | _ = nothing
    restore (P.edgeRef key ordinal) = edgeValue key ordinal (DB.lookup key world) refl
    restore (P.noteRef key vector) = nothing

    restoreAll : (refs : List P.Ref) → Maybe (All Row refs)
    restoreAll [] = just []
    restoreAll (ref ∷ refs) with restore ref | restoreAll refs
    ... | just found | just rest = just (found ∷ rest)
    ... | _ | _ = nothing

    -- Source-specific query matching and occurrence evidence are certified at
    -- capture by #39/#40/#42. These checks revalidate actual row visibility;
    -- note-version and family-only source bindings belong to #43.
    rowsHaveNoForeignOwner : ∀ path key version (row : Code path key version) →
      DB.lookup key world ≡ just (O.recordOf owner (O.chunk version (Code.text row)))
    rowsHaveNoForeignOwner path key version row = Code.located row
    codeCannotReappearWhenHidden : ∀ path key version → Files.visible world selected path ≡ nothing → Code path key version → ⊥
    codeCannotReappearWhenHidden path key version hidden row with Relation.Binary.PropositionalEquality.trans (Relation.Binary.PropositionalEquality.sym hidden) (Code.visible row)
    ... | ()
