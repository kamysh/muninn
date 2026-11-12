{-# OPTIONS --safe #-}
-- Select each displayed path independently and retain physical identity.
module Muninn.SymlinkSelection where

import Muninn.SymlinkTraversal as Link
import Muninn.Config as Config
open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; foldl)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

-- Rendering must distinguish visible paths. The filesystem adapter establishes
-- that rendered components, link targets and object identities are accurate.
record Encoding : Set where
  field
    render : Link.Path → String
    injective : ∀ {first second} → render first ≡ render second → first ≡ second

applyObserved : ∀ {A B : Set} (observed : A) (use : (value : A) → observed ≡ value → B)
  {value : A} (seen : observed ≡ value) → use observed refl ≡ use value seen
applyObserved observed use refl = refl

-- The Git and ordered rule-match observations belong to one visible path.
-- Their correspondence to Git and the actual compiled rules is an adapter
-- obligation. Explicit rules override the Git default, last match wins.
record RuleObservation : Set where
  field
    gitIgnored : Bool
    exclusions : List (Bool × Bool)
    vendors : List (Bool × Bool)

classify : RuleObservation → Config.Decision
classify observation = Config.classify
  (foldl Config.resolveStep (RuleObservation.gitIgnored observation) (RuleObservation.exclusions observation))
  (foldl Config.resolveStep false (RuleObservation.vendors observation))

module Checkout (root : Link.Path) (snapshot : Link.Snapshot root)
  (encoding : Encoding) (objectAt : Link.Path → Maybe ℕ)
  (rulesAt : String → RuleObservation) where

  links = Link.Snapshot.links snapshot
  render = Encoding.render encoding

  record Entry (path : Link.Path) : Set where
    constructor entry
    field
      target : Link.Path
      resolution : Link.Resolution root links (root ++ path) target
      identity : ℕ
      observed : objectAt target ≡ just identity
      decision : Config.Decision
      chosen : classify (rulesAt (render path)) ≡ decision
      included : ¬ (decision ≡ Config.Drop)
  open Entry public

  selectRule : ∀ path target (trace : Link.Resolution root links (root ++ path) target)
    object → objectAt target ≡ just object → (decision : Config.Decision) →
    classify (rulesAt (render path)) ≡ decision → Maybe (Entry path)
  selectRule path target trace object found Config.Drop selectedRule = nothing
  selectRule path target trace object found Config.T1 selectedRule =
    just (entry target trace object found Config.T1 selectedRule (λ ()))
  selectRule path target trace object found Config.T2 selectedRule =
    just (entry target trace object found Config.T2 selectedRule (λ ()))

  selectFile : ∀ path target (trace : Link.Resolution root links (root ++ path) target) →
    (observed : Maybe ℕ) → objectAt target ≡ observed → Maybe (Entry path)
  selectFile path target trace nothing found = nothing
  selectFile path target trace (just object) found =
    selectRule path target trace object found (classify (rulesAt (render path))) refl

  selectResolution : (path : Link.Path) → Link.Result root links (root ++ path) → Maybe (Entry path)
  selectResolution path (Link.excluded noTarget) = nothing
  selectResolution path (Link.selected target trace) = selectFile path target trace (objectAt target) refl

  select : (path : Link.Path) → Maybe (Entry path)
  select path = selectResolution path
    (Link.resolve root links (root ++ path) (Link.rooted root path) (Link.finite snapshot (root ++ path)))

  -- Every resolvable file included by its own rules produces an entry.
  selectIncluded : ∀ path target (trace : Link.Resolution root links (root ++ path) target)
    object → objectAt target ≡ just object →
    (decision : Config.Decision) → classify (rulesAt (render path)) ≡ decision →
    ¬ (decision ≡ Config.Drop) → Σ (Entry path) (λ selected →
      (select path ≡ just selected) × (Entry.target selected ≡ target))
  selectIncluded path target trace object exists Config.Drop chosen included = ⊥-elim (included refl)
  selectIncluded path target trace object exists Config.T1 chosen included
    with Link.complete root links (root ++ path) target (Link.rooted root path)
      (Link.finite snapshot (root ++ path)) trace
  ... | actual , resolved = entry target actual object exists Config.T1 chosen (λ ()) ,
    (trans (cong (selectResolution path) resolved)
      (trans (applyObserved (objectAt target) (selectFile path target actual) exists)
        (applyObserved (classify (rulesAt (render path))) (selectRule path target actual object exists) chosen)) , refl)
  selectIncluded path target trace object exists Config.T2 chosen included
    with Link.complete root links (root ++ path) target (Link.rooted root path)
      (Link.finite snapshot (root ++ path)) trace
  ... | actual , resolved = entry target actual object exists Config.T2 chosen (λ ()) ,
    (trans (cong (selectResolution path) resolved)
      (trans (applyObserved (objectAt target) (selectFile path target actual) exists)
        (applyObserved (classify (rulesAt (render path))) (selectRule path target actual object exists) chosen)) , refl)

  targetInside : ∀ {path} (selected : Entry path) → Link.Prefix root (target selected)
  targetInside selected = Link.insideRoot (resolution selected)

  distinctDisplayed : ∀ first second → ¬ (first ≡ second) →
    ¬ (render first ≡ render second)
  distinctDisplayed first second different same = different (Encoding.injective encoding same)

  sameTargetSameIdentity : ∀ {first second} (left : Entry first) (right : Entry second) →
    target left ≡ target right → identity left ≡ identity right
  sameTargetSameIdentity left right refl = just-injective (trans (sym (observed left)) (observed right))

  collect : List Link.Path → List (Σ Link.Path Entry)
  collect [] = []
  collect (path ∷ rest) with select path
  ... | nothing = collect rest
  ... | just selected = (path , selected) ∷ collect rest

  everySelected : ∀ paths path (selected : Entry path) →
    path ∈ paths → select path ≡ just selected → (path , selected) ∈ collect paths
  everySelected (path ∷ rest) .path selected (here refl) chosen with select path
  ... | nothing with chosen
  ...   | ()
  everySelected (path ∷ rest) .path selected (here refl) chosen | just actual with chosen
  ...   | refl = here refl
  everySelected (first ∷ rest) path selected (there later) chosen with select first
  ... | nothing = everySelected rest path selected later chosen
  ... | just actual = there (everySelected rest path selected later chosen)

  -- Completeness is an outcome over filesystem paths, rather than an
  -- implementation-specific directory traversal order.
  record CompleteScan : Set where
    field
      paths : List Link.Path
      coversFile : ∀ visible target →
        Link.Resolution root links (root ++ visible) target →
        ∀ object → objectAt target ≡ just object → visible ∈ paths

  published : CompleteScan → List (Σ Link.Path Entry)
  published scan = collect (CompleteScan.paths scan)

  -- The intended result is stated against the filesystem, independently of
  -- the chosen scan list: every included reachable file is published.
  includedFilePublished : ∀ (scan : CompleteScan) visible target
    (trace : Link.Resolution root links (root ++ visible) target) object →
    objectAt target ≡ just object → (decision : Config.Decision) →
    classify (rulesAt (render visible)) ≡ decision → ¬ (decision ≡ Config.Drop) →
    Σ (Entry visible) (λ selected →
      ((visible , selected) ∈ published scan) × (Entry.target selected ≡ target))
  includedFilePublished scan visible target trace object exists decision chosen included
    with selectIncluded visible target trace object exists decision chosen included
  ... | selected , (selectedPath , targetSame) = selected ,
    (everySelected (CompleteScan.paths scan) visible selected
      (CompleteScan.coversFile scan visible target trace object exists) selectedPath , targetSame)

  bothVisible : ∀ (scan : CompleteScan) first second
    (firstEntry : Entry first) (secondEntry : Entry second) →
    first ∈ CompleteScan.paths scan → second ∈ CompleteScan.paths scan →
    select first ≡ just firstEntry → select second ≡ just secondEntry →
    ¬ (first ≡ second) →
    ((first , firstEntry) ∈ published scan) ×
      (((second , secondEntry) ∈ published scan) × (¬ (render first ≡ render second)))
  bothVisible scan first second firstEntry secondEntry firstMember secondMember firstSelected secondSelected different =
    everySelected (CompleteScan.paths scan) first firstEntry firstMember firstSelected ,
    everySelected (CompleteScan.paths scan) second secondEntry secondMember secondSelected ,
    distinctDisplayed first second different

  -- Two distinct included paths to one file are both present, retain
  -- distinct display names and share the same physical object identity.
  bothIncludedSameObject : ∀ (scan : CompleteScan) first second target →
    (firstTrace : Link.Resolution root links (root ++ first) target) →
    (secondTrace : Link.Resolution root links (root ++ second) target) →
    ∀ object → objectAt target ≡ just object →
    (firstDecision secondDecision : Config.Decision) →
    classify (rulesAt (render first)) ≡ firstDecision →
    classify (rulesAt (render second)) ≡ secondDecision →
    ¬ (firstDecision ≡ Config.Drop) → ¬ (secondDecision ≡ Config.Drop) → ¬ (first ≡ second) →
    Σ (Entry first) (λ left → Σ (Entry second) (λ right →
      ((first , left) ∈ published scan) × (((second , right) ∈ published scan) ×
        ((identity left ≡ identity right) × ¬ (render first ≡ render second)))))
  bothIncludedSameObject scan first second target firstTrace secondTrace object exists
    firstDecision secondDecision firstRule secondRule firstIncluded secondIncluded different
    with includedFilePublished scan first target firstTrace object exists firstDecision firstRule firstIncluded
       | includedFilePublished scan second target secondTrace object exists secondDecision secondRule secondIncluded
  ... | left , (firstMember , firstTarget) | right , (secondMember , secondTarget) =
    left , right , firstMember , secondMember ,
    sameTargetSameIdentity left right (trans firstTarget (sym secondTarget)) ,
    distinctDisplayed first second different
