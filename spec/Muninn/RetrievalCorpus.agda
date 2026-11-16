{-# OPTIONS --safe #-}
-- Complete eligible candidates and semantic coverage from the actual world.
module Muninn.RetrievalCorpus where
import Muninn.OwnedState as O
import Muninn.StoredPolicy as Policy
import Muninn.ContentViews as Content
import Muninn.PublishedViews as Published
import Muninn.VectorData as V
import Muninn.Worktree as W
import Muninn.RetrievalNumerics as Numeric
import Muninn.Types as T
import Muninn.ExclusionOutcomes as E
import Muninn.ArtifactIdentity as Equal
open import Data.Nat using (ℕ; suc; _≤_; _≟_)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
import Data.String as String
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Empty using (⊥)
open import Relation.Nullary using (does; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
module DB = O.DB

-- The adapter decodes uninterpreted stored vector payloads into the typed
-- state they represent; payload-byte correspondence remains #52 evidence.
record Matches (profile : W.EmbeddingKey) (key : ℕ) (text : String) : Set where
  constructor matches
  field saved : V.State
        profileMatches : V.profile saved ≡ profile
        sourceMatches : V.source saved ≡ text

decodeMatch : (profile : W.EmbeddingKey) (key : ℕ) (text : String) →
  (decode : String → Maybe V.State) → String → Maybe (Matches profile key text)
decodeMatch profile key text decode payload = inspect (decode payload)
  where
  matchSaved : V.State → Maybe (Matches profile key text)
  matchSaved saved with Equal.EmbeddingKey? (V.profile saved) profile | V.source saved String.≟ text
  ... | yes sameProfile | yes sameSource = just (matches saved sameProfile sameSource)
  ... | _ | _ = nothing
  inspect : Maybe V.State → Maybe (Matches profile key text)
  inspect nothing = nothing
  inspect (just saved) = matchSaved saved

candidate : (owner : O.Owner) (profile : W.EmbeddingKey) (decode : String → Maybe V.State) →
  (key : ℕ) (text : String) → O.Record → Maybe (Matches profile key text)
candidate owner profile decode key text (O.recordOf actualOwner (O.vector storedKey payload)) = selectRow
  where
  selectRow : Maybe (Matches profile key text)
  selectRow with E.ownerEqual actualOwner owner | storedKey ≟ key
  ... | yes refl | yes refl = decodeMatch profile key text decode payload
  ... | _ | _ = nothing
candidate owner profile decode key text value = nothing

module Family (family checkout pointer : ℕ) (world : O.World)
  (policy : Policy.Family.Saved family pointer world)
  (viewsValid : Published.Valid world)
  (filesValid : Content.Family.WellFormed (Policy.Family.rule family pointer policy) world)
  (profile : W.EmbeddingKey)
  (decode : String → Maybe V.State)
  (decodeConsistent : ∀ key text → Content.Consistent (candidate (O.family family) profile decode key text) world) where
  owner = O.family family
  selection = Policy.Family.rule family pointer policy

  module Eligibility where
    module Files = Content.Family selection

    -- A result must identify a stored chunk with the same version as the
    -- selected visible file. Rows from another checkout or older view are
    -- not eligible merely because they remain in the database.
    record CodeHit : Set where
      constructor codeHit
      field path : T.FilePath
            key version : ℕ
            text : String
            gitDefault : Bool
            chunkAt : DB.lookup key world ≡ just (O.recordOf owner (O.chunk version text))
            fileAt : Files.visible world checkout path ≡ just (Content.entry version gitDefault)

    codeRow : ∀ path key → (value : Maybe O.Record) → DB.lookup key world ≡ value → Maybe CodeHit
    codeRow path key (just (O.recordOf actualOwner (O.chunk version text))) chunkAt with E.ownerEqual actualOwner owner
    ... | no other = nothing
    ... | yes refl with Files.visible world checkout path in fileAt
    ...   | nothing = nothing
    ...   | just cell with Content.Entry.version cell ≟ version
    ...     | no other = nothing
    ...     | yes refl = just (codeHit path key version text (Content.Entry.gitDefault cell) chunkAt fileAt)
    codeRow path key value found = nothing

    code : T.FilePath → ℕ → Maybe CodeHit
    code path key = codeRow path key (DB.lookup key world) refl

    codes : List (T.FilePath × ℕ) → List CodeHit
    codes [] = []
    codes ((path , key) ∷ candidates) with code path key
    ... | nothing = codes candidates
    ... | just hit = hit ∷ codes candidates

    codeIsEligible : ∀ (hit : CodeHit) → DB.lookup (CodeHit.key hit) world ≡ just (O.recordOf owner (O.chunk (CodeHit.version hit) (CodeHit.text hit))) ×
      Files.visible world checkout (CodeHit.path hit) ≡ just (Content.entry (CodeHit.version hit) (CodeHit.gitDefault hit))
    codeIsEligible hit = CodeHit.chunkAt hit , CodeHit.fileAt hit

    otherVersionExcluded : ∀ path cell (hit : CodeHit) → Files.visible world checkout path ≡ just cell →
      CodeHit.path hit ≡ path → CodeHit.version hit ≢ Content.Entry.version cell → Data.Empty.⊥
    otherVersionExcluded path cell hit actual samePath different =
      different (sym (cong Content.Entry.version (just-injective (trans (sym actual) atPath))))
      where
      atPath : Files.visible world checkout path ≡ just (Content.entry (CodeHit.version hit) (CodeHit.gitDefault hit))
      atPath = trans (sym (cong (λ selectedPath → Files.visible world checkout selectedPath) samePath)) (CodeHit.fileAt hit)

  module Hit = Eligibility.CodeHit
  Hit = Eligibility.CodeHit
  Identity = T.FilePath × ℕ
  identity : Hit → Identity
  identity hit = Eligibility.CodeHit.path hit , Eligibility.CodeHit.key hit
  same : Hit → Hit → Bool
  same first second = does (Eligibility.CodeHit.key first ≟ Eligibility.CodeHit.key second) ∧
    does (T.FilePath.value (Eligibility.CodeHit.path first) String.≟ T.FilePath.value (Eligibility.CodeHit.path second))
  count : Hit → List Hit → ℕ
  count hit [] = 0
  count hit (first ∷ rest) with same hit first
  ... | true = suc (count hit rest)
  ... | false = count hit rest

  -- Source enumeration cannot be a top-N SQL result or handler-selected subset.
  -- Every actual eligible chunk/path pair must have a representative.
  record Inventory : Set where
    field items : List Hit
          complete : ∀ hit → Σ Hit (λ saved → saved ∈ items × identity saved ≡ identity hit)
          unique : ∀ hit → count hit items ≤ 1

  -- Availability classifies the actual stored association for one chunk/text.
  -- Decoder consistency makes the classification order-independent.
  data Availability : Set where
    pending waiting usable : Availability

  classify : ∀ {key text} → Maybe (Matches profile key text) → Availability
  classify nothing = pending
  classify (just (matches (V.pending _ _) _ _)) = pending
  classify (just (matches (V.waiting _ _ _) _ _)) = waiting
  classify (just (matches (V.usable _) _ _)) = usable

  availabilityEqual : Availability → Availability → Bool
  availabilityEqual pending pending = true
  availabilityEqual waiting waiting = true
  availabilityEqual usable usable = true
  availabilityEqual _ _ = false

  state : Hit → Availability
  state hit = classify (Content.find (candidate owner profile decode (Eligibility.CodeHit.key hit) (Eligibility.CodeHit.text hit)) world)

  stateSound : ∀ hit → state hit ≡ usable →
    Σ (ℕ × O.Record) (λ row → row ∈ world ×
      Σ V.Value (λ saved → Σ (V.Value.profile saved ≡ profile) (λ sameProfile →
        Σ (V.Value.source saved ≡ Eligibility.CodeHit.text hit) (λ sameSource →
          candidate owner profile decode (Eligibility.CodeHit.key hit) (Eligibility.CodeHit.text hit) (proj₂ row) ≡
            just (matches (V.usable saved) sameProfile sameSource)))))
  stateSound hit found with Content.find (candidate owner profile decode (Eligibility.CodeHit.key hit) (Eligibility.CodeHit.text hit)) world in observed
  ... | just (matches (V.usable saved) profileMatches sourceMatches) with
    Content.findSound (candidate owner profile decode (Eligibility.CodeHit.key hit) (Eligibility.CodeHit.text hit)) world
      (matches (V.usable saved) profileMatches sourceMatches) observed
  ...   | row , present , selected = row , present , saved , profileMatches , sourceMatches , selected
  stateSound hit () | just (matches (V.pending _ _) _ _)
  stateSound hit () | just (matches (V.waiting _ _ _) _ _)
  stateSound hit () | nothing

  -- A stored usable vector cannot be hidden by scan order or another row.
  usablePresent : ∀ hit saved row profileMatches sourceMatches → row ∈ world →
    candidate owner profile decode (Eligibility.CodeHit.key hit) (Eligibility.CodeHit.text hit) (proj₂ row) ≡
      just (matches (V.usable saved) profileMatches sourceMatches) → state hit ≡ usable
  usablePresent hit saved row profileMatches sourceMatches present selected =
    cong classify (Content.findComplete (candidate owner profile decode (Eligibility.CodeHit.key hit) (Eligibility.CodeHit.text hit)) world
      (decodeConsistent (Eligibility.CodeHit.key hit) (Eligibility.CodeHit.text hit))
      row (matches (V.usable saved) profileMatches sourceMatches) present selected)

  -- Full-text availability has no vector premise; the posting row carries the
  -- actual indexed text for one chunk key.
  postingPayload : (key : ℕ) → O.Record → Maybe String
  postingPayload key (O.recordOf actualOwner (O.posting storedKey payload)) with E.ownerEqual actualOwner owner | storedKey ≟ key
  ... | yes refl | yes refl = just payload
  ... | _ | _ = nothing
  postingPayload key value = nothing

  postedAt : (key : ℕ) → Maybe String
  postedAt key = Content.find (postingPayload key) world

  postedSound : ∀ key payload → postedAt key ≡ just payload →
    Σ (ℕ × O.Record) (λ row → row ∈ world × postingPayload key (proj₂ row) ≡ just payload)
  postedSound key payload = Content.findSound (postingPayload key) world payload

  postedAbsent : ∀ key → postedAt key ≡ nothing →
    ∀ row → row ∈ world → postingPayload key (proj₂ row) ≡ nothing
  postedAbsent key = Content.findAbsent (postingPayload key) world

  -- The typed value behind a usable state, from the actual row that carries it.
  readyAt : (key : ℕ) (text : String) → Maybe V.Value
  readyAt key text = extractReady (Content.find (candidate owner profile decode key text) world)
    where
    extractReady : Maybe (Matches profile key text) → Maybe V.Value
    extractReady nothing = nothing
    extractReady (just (matches (V.usable saved) _ _)) = just saved
    extractReady (just (matches (V.pending _ _) _ _)) = nothing
    extractReady (just (matches (V.waiting _ _ _) _ _)) = nothing

  readySound : ∀ key text saved → readyAt key text ≡ just saved →
    Σ (ℕ × O.Record) (λ row → row ∈ world ×
      Σ V.Value (λ stored → stored ≡ saved ×
        Σ (V.Value.profile stored ≡ profile) (λ sameProfile →
          Σ (V.Value.source stored ≡ text) (λ sameSource →
            candidate owner profile decode key text (proj₂ row) ≡ just (matches (V.usable stored) sameProfile sameSource)))))
  readySound key text saved found with Content.find (candidate owner profile decode key text) world in observed
  ... | just (matches (V.usable actual) profileMatches sourceMatches) with just-injective found
  ...   | refl with Content.findSound (candidate owner profile decode key text) world (matches (V.usable actual) profileMatches sourceMatches) observed
  ...     | row , present , selected = row , present , actual , refl , profileMatches , sourceMatches , selected
  readySound key text saved () | just (matches (V.pending _ _) _ _)
  readySound key text saved () | just (matches (V.waiting _ _ _) _ _)
  readySound key text saved () | nothing

  usableImpliesReady : ∀ hit → state hit ≡ usable → Σ V.Value (λ saved → readyAt (Eligibility.CodeHit.key hit) (Eligibility.CodeHit.text hit) ≡ just saved)
  usableImpliesReady hit found with Content.find (candidate owner profile decode (Eligibility.CodeHit.key hit) (Eligibility.CodeHit.text hit)) world in observed
  ... | just (matches (V.usable saved) _ _) = saved , refl
  usableImpliesReady hit () | just (matches (V.pending _ _) _ _)
  usableImpliesReady hit () | just (matches (V.waiting _ _ _) _ _)
  usableImpliesReady hit () | nothing

  readyImpliesUsable : ∀ hit saved → readyAt (Eligibility.CodeHit.key hit) (Eligibility.CodeHit.text hit) ≡ just saved → state hit ≡ usable
  readyImpliesUsable hit saved found with Content.find (candidate owner profile decode (Eligibility.CodeHit.key hit) (Eligibility.CodeHit.text hit)) world in observed
  ... | just (matches (V.usable actual) _ _) = refl
  readyImpliesUsable hit saved () | just (matches (V.pending _ _) _ _)
  readyImpliesUsable hit saved () | just (matches (V.waiting _ _ _) _ _)
  readyImpliesUsable hit saved () | nothing

  readyAbsentNotUsable : ∀ hit → readyAt (Eligibility.CodeHit.key hit) (Eligibility.CodeHit.text hit) ≡ nothing → state hit ≡ usable → ⊥
  readyAbsentNotUsable hit absent usableState with usableImpliesReady hit usableState
  ... | saved , ready with trans (sym ready) absent
  ...   | ()

  report : Inventory → List (Identity × Availability)
  report inventory = map (λ hit → identity hit , state hit) (Inventory.items inventory)

  countState : Availability → List Hit → ℕ
  countState wanted [] = 0
  countState wanted (hit ∷ rest) with state hit
  ... | actual = if availabilityEqual wanted actual then suc (countState wanted rest) else countState wanted rest

  allReady : List Hit → Bool
  allReady [] = true
  allReady (hit ∷ rest) with state hit
  ... | usable = allReady rest
  ... | _ = false

  -- The wire response carries bounded-size counts, not the internal full list.
  record Summary (inventory : Inventory) : Set where
    field total usableCount pendingCount waitingCount : ℕ
          complete : Bool
          totalCorrect : total ≡ length (Inventory.items inventory)
          usableCorrect : usableCount ≡ countState usable (Inventory.items inventory)
          pendingCorrect : pendingCount ≡ countState pending (Inventory.items inventory)
          waitingCorrect : waitingCount ≡ countState waiting (Inventory.items inventory)
          completenessCorrect : complete ≡ allReady (Inventory.items inventory)

  summary : (inventory : Inventory) → Summary inventory
  summary inventory = record
    { total = length (Inventory.items inventory)
    ; usableCount = countState usable (Inventory.items inventory)
    ; pendingCount = countState pending (Inventory.items inventory)
    ; waitingCount = countState waiting (Inventory.items inventory)
    ; complete = allReady (Inventory.items inventory)
    ; totalCorrect = refl; usableCorrect = refl; pendingCorrect = refl; waitingCorrect = refl
    ; completenessCorrect = refl }

  allReadySound : ∀ rows hit → allReady rows ≡ true → hit ∈ rows → state hit ≡ usable
  allReadySound (first ∷ rest) hit complete member with state first in observed
  ... | usable with member
  ...   | here refl = observed
  ...   | there later = allReadySound rest hit complete later
  allReadySound (first ∷ rest) hit () member | pending
  allReadySound (first ∷ rest) hit () member | waiting

  completeMeansActualCoverage : ∀ inventory (saved : Summary inventory) → Summary.complete saved ≡ true →
    ∀ hit → hit ∈ Inventory.items inventory → state hit ≡ usable
  completeMeansActualCoverage inventory saved claimed hit member = allReadySound (Inventory.items inventory) hit
    (trans (sym (Summary.completenessCorrect saved)) claimed) member

  mapMember : ∀ {A B : Set} (f : A → B) xs x → x ∈ xs → f x ∈ map f xs
  mapMember f (x ∷ xs) .x (here refl) = here refl
  mapMember f (first ∷ xs) x (there later) = there (mapMember f xs x later)

  everyEligibleIdentityReported : ∀ inventory hit →
    Σ Hit (λ saved → identity saved ≡ identity hit × (identity saved , state saved) ∈ report inventory)
  everyEligibleIdentityReported inventory hit with Inventory.complete inventory hit
  ... | saved , included , sameIdentity = saved , sameIdentity ,
    mapMember (λ hit → identity hit , state hit) (Inventory.items inventory) saved included

  -- A usable vector association for this chunk, text and current profile.
  record Semantic (hit : Hit) : Set where
    field value : V.Value
          associated : readyAt (Eligibility.CodeHit.key hit) (Eligibility.CodeHit.text hit) ≡ just value
          stored32 : Numeric.Stored32 (V.Value.values value)

  validVector : ∀ hit → (ready : Semantic hit) → V.Valid (W.EmbeddingKey.dimension profile) (V.Value.values (Semantic.value ready))
  validVector hit ready =
    subst (λ p → V.Valid (W.EmbeddingKey.dimension p) (V.Value.values (Semantic.value ready)))
      profileAgrees (V.Value.valid (Semantic.value ready))
    where
    witness = readySound (Eligibility.CodeHit.key hit) (Eligibility.CodeHit.text hit) (Semantic.value ready) (Semantic.associated ready)
    stored = proj₁ (proj₂ (proj₂ witness))
    storedIs = proj₁ (proj₂ (proj₂ (proj₂ witness)))
    sameProfile = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ witness))))
    profileAgrees : V.Value.profile (Semantic.value ready) ≡ profile
    profileAgrees = trans (cong V.Value.profile (sym storedIs)) sameProfile

  -- Missing vectors stay in the complete text inventory and coverage report.
  -- A successful semantic response must enumerate/classify the entire inventory.
  data Coverage (hit : Hit) : Set where
    ready : Semantic hit → Coverage hit
    unfinished : readyAt (Eligibility.CodeHit.key hit) (Eligibility.CodeHit.text hit) ≡ nothing → Coverage hit

  record SemanticInventory (inventory : Inventory) : Set where
    field coverageOf : ∀ hit → hit ∈ Inventory.items inventory → Coverage hit

  unfinishedCannotHideUsable : ∀ hit → readyAt (Eligibility.CodeHit.key hit) (Eligibility.CodeHit.text hit) ≡ nothing → Semantic hit → ⊥
  unfinishedCannotHideUsable hit absent semantic with trans (sym (Semantic.associated semantic)) absent
  ... | ()
