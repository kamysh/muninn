{-# OPTIONS --safe #-}
-- One application/AGE schema pair per family. Baselines and analysis are shared;
-- each checkout publishes its own baseline reference, overlay, and graph.
module Muninn.Storage where

open import Muninn.Types
open import Muninn.Worktree
open import Muninn.Schema
open import Muninn.GraphMembership using (GraphView)
open import Muninn.IndexFsm using (GitState; Settled; Operating; Conflicted; GitBlocked;
  chooseSnapshot; blockedRetainsSnapshot)
open import Data.List using (List)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans)
open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Data.Empty using (⊥-elim)

record FamilyRegistration : Set where
  field key : FilePath -- canonical Git common-dir or independent non-Git root
        family : FamilyId
        schemas : SchemaPair

SchemaAssignment : Set
SchemaAssignment = FamilyId → SchemaPair

-- Neither member of a pair can alias either member of a different family.
IsolatedFamilies : SchemaAssignment → Set
IsolatedFamilies schemas = ∀ a b ra rb →
  schemaAt (schemas a) ra ≡ schemaAt (schemas b) rb → a ≡ b

checkoutSchemas : SchemaAssignment → Checkout → SchemaPair
checkoutSchemas schemas checkout = schemas (Checkout.family checkout)

sameFamilySameSchemaPair : ∀ schemas a b → Checkout.family a ≡ Checkout.family b →
  checkoutSchemas schemas a ≡ checkoutSchemas schemas b
sameFamilySameSchemaPair schemas a b same = cong schemas same

assignedSchemaIdentity : ∀ schemas → IsolatedFamilies schemas → ∀ a b ra rb →
  schemaAt (schemas a) ra ≡ schemaAt (schemas b) rb → a ≡ b × ra ≡ rb
assignedSchemaIdentity schemas isolated a b ra rb same =
  isolated a b ra rb same , schemaRoleInjective (schemas a) ra rb
    (trans same (cong (λ family → schemaAt (schemas family) rb)
      (sym (isolated a b ra rb same))))

distinctFamiliesNoSchemaOverlap : ∀ schemas → IsolatedFamilies schemas → ∀ a b ra rb →
  ¬ (a ≡ b) → ¬ (schemaAt (schemas a) ra ≡ schemaAt (schemas b) rb)
distinctFamiliesNoSchemaOverlap schemas isolated a b ra rb different same =
  different (isolated a b ra rb same)

UniqueFamilyKeys : List FamilyRegistration → Set
UniqueFamilyKeys registrations =
  ∀ a b → a ∈ registrations → b ∈ registrations →
    FamilyRegistration.key a ≡ FamilyRegistration.key b →
    FamilyRegistration.family a ≡ FamilyRegistration.family b

-- The graph carries explicit membership as well as endpoint visibility.
-- Correct name resolution remains a runtime obligation.
record PublishedSnapshot (baselines : Baselines) : Set where
  field view : WorktreeView
        differencesOnly : MinimalOverlay (baselines (WorktreeView.baseline view))
                                         (WorktreeView.overlay view)
        graph : GraphView (resolveView baselines view)

World : Baselines → Set
World baselines = CheckoutId → Maybe (PublishedSnapshot baselines)

viewsOf : ∀ {baselines} → World baselines → Views
viewsOf {baselines} world checkout with world checkout
... | nothing = λ _ → nothing
... | just snapshot = resolveView baselines (PublishedSnapshot.view snapshot)

replaceCheckout : ∀ {baselines} → ((a b : CheckoutId) → Dec (a ≡ b)) →
  CheckoutId → Maybe (PublishedSnapshot baselines) → World baselines → World baselines
replaceCheckout eq target next world selected with eq target selected
... | yes _ = next
... | no _ = world selected

otherCheckoutUnchanged : ∀ {baselines} eq target other next (world : World baselines) →
  ¬ (target ≡ other) → replaceCheckout eq target next world other ≡ world other
otherCheckoutUnchanged eq target other next world distinct with eq target other
... | yes same = ⊥-elim (distinct same)
... | no _ = refl

-- Snapshot contents are shared by reference. Both visible files and hidden
-- baseline files are roots: removing an overlay may expose a baseline again.
data ManifestOrigin : Set where
  SharedBaseline EffectiveView : ManifestOrigin

manifestAt : Baselines → WorktreeView → ManifestOrigin → Manifest
manifestAt baselines view SharedBaseline = baselines (WorktreeView.baseline view)
manifestAt baselines view EffectiveView = resolveView baselines view

Artifacts : Set
Artifacts = VersionRef → Maybe FileVersion

Resolved : Artifacts → FamilyId → VersionRef → Set
Resolved artifacts family ref = Σ FileVersion (λ version →
  artifacts ref ≡ just version ×
  (FileVersion.id version ≡ VersionRef.version ref ×
  (FileVersion.family version ≡ family × VersionRef.family ref ≡ family)))

ValidSnapshot : Artifacts → FamilyId → (baselines : Baselines) →
  PublishedSnapshot baselines → Set
ValidSnapshot artifacts family baselines snapshot =
  GraphView.family (PublishedSnapshot.graph snapshot) ≡ family ×
  (∀ origin path entry → manifestAt baselines (PublishedSnapshot.view snapshot) origin path ≡ just entry →
    Resolved artifacts family (FileEntry.version entry))

ValidSlot : Artifacts → FamilyId → (baselines : Baselines) →
  Maybe (PublishedSnapshot baselines) → Set
ValidSlot artifacts family baselines nothing = ⊤
ValidSlot artifacts family baselines (just snapshot) = ValidSnapshot artifacts family baselines snapshot

ValidWorld : Artifacts → (CheckoutId → FamilyId) → (baselines : Baselines) → World baselines → Set
ValidWorld artifacts families baselines world =
  ∀ checkout → ValidSlot artifacts (families checkout) baselines (world checkout)

-- Kryzhen's completed template and AGE receipt for the selected pair are required.
-- A candidate cannot be published while Git is blocked, even if built earlier.
publish : ∀ {baselines} (eq : (a b : CheckoutId) → Dec (a ≡ b)) →
  (required : FamilyTemplate) → (ledger : Ledger) → (schemas : SchemaAssignment) →
  (artifacts : Artifacts) → (families : CheckoutId → FamilyId) →
  (target : CheckoutId) → (git : GitState) →
  (candidate : Maybe (PublishedSnapshot baselines)) → (world : World baselines) →
  SchemaStep required ledger (schemas (families target)) Migrating Ready →
  ValidSlot artifacts (families target) baselines candidate → World baselines
publish eq required ledger schemas artifacts families target git candidate world ready valid =
  replaceCheckout eq target (chooseSnapshot git (world target) candidate) world

choicePreservesValidity : ∀ artifacts family baselines git previous candidate →
  ValidSlot artifacts family baselines previous → ValidSlot artifacts family baselines candidate →
  ValidSlot artifacts family baselines (chooseSnapshot git previous candidate)
choicePreservesValidity artifacts family baselines Settled previous nothing old new = old
choicePreservesValidity artifacts family baselines Settled previous (just candidate) old new = new
choicePreservesValidity artifacts family baselines Operating previous candidate old new = old
choicePreservesValidity artifacts family baselines Conflicted previous candidate old new = old

publicationPreservesReferences : ∀ {baselines} eq required ledger schemas artifacts families target git candidate world →
  (ready : SchemaStep required ledger (schemas (families target)) Migrating Ready) →
  (valid : ValidSlot artifacts (families target) baselines candidate) →
  ValidWorld artifacts families baselines world →
  ValidWorld artifacts families baselines
    (publish eq required ledger schemas artifacts families target git candidate world ready valid)
publicationPreservesReferences {baselines} eq required ledger schemas artifacts families target git candidate world ready valid old selected
  with eq target selected
... | yes refl = choicePreservesValidity artifacts (families target) baselines git (world target) candidate (old target) valid
... | no _ = old selected

-- This includes the entire graph, baseline reference, and all overrides.
publicationWhileBlockedRetains : ∀ {baselines} eq required ledger schemas artifacts families target git candidate world ready valid →
  GitBlocked git → ∀ selected →
  publish {baselines} eq required ledger schemas artifacts families target git candidate world ready valid selected ≡ world selected
publicationWhileBlockedRetains eq required ledger schemas artifacts families target git candidate world ready valid blocked selected
  with eq target selected
... | yes refl = blockedRetainsSnapshot git (world target) candidate blocked
... | no _ = refl

Extends : Artifacts → Artifacts → Set
Extends before after = ∀ ref version → before ref ≡ just version → after ref ≡ just version

extensionPreservesResolution : ∀ before after family ref → Extends before after →
  Resolved before family ref → Resolved after family ref
extensionPreservesResolution before after family ref extends (version , stored , identities) =
  version , extends ref version stored , identities

Referenced : ∀ {baselines} → World baselines → VersionRef → Set
Referenced {baselines} world ref = Σ CheckoutId (λ checkout →
  Σ (PublishedSnapshot baselines) (λ snapshot → world checkout ≡ just snapshot ×
    Σ ManifestOrigin (λ origin → Σ FilePath (λ path → Σ FileEntry (λ entry →
      manifestAt baselines (PublishedSnapshot.view snapshot) origin path ≡ just entry ×
      FileEntry.version entry ≡ ref)))))

removeArtifact : ((a b : VersionRef) → Dec (a ≡ b)) → VersionRef → Artifacts → Artifacts
removeArtifact eq target artifacts ref with eq target ref
... | yes _ = nothing
... | no _ = artifacts ref

-- Quantified over all roots, including retained baselines, not just current hits.
unreferencedRemovalPreservesReferences : ∀ {baselines} eq target artifacts families (world : World baselines) →
  ¬ Referenced world target → ValidWorld artifacts families baselines world →
  ValidWorld (removeArtifact eq target artifacts) families baselines world
unreferencedRemovalPreservesReferences {baselines} eq target artifacts families world unused valid selected =
  preserve (world selected) refl (valid selected)
  where
  preserve : (slot : Maybe (PublishedSnapshot baselines)) → world selected ≡ slot →
    ValidSlot artifacts (families selected) baselines slot →
    ValidSlot (removeArtifact eq target artifacts) (families selected) baselines slot
  preserve nothing observed old = tt
  preserve (just snapshot) observed old = proj₁ old , keep
    where
    keep : ∀ origin path entry →
      manifestAt baselines (PublishedSnapshot.view snapshot) origin path ≡ just entry →
      Resolved (removeArtifact eq target artifacts) (families selected) (FileEntry.version entry)
    keep origin path entry present with eq target (FileEntry.version entry)
    ... | yes same = ⊥-elim (unused (selected , snapshot , observed , origin , path , entry , present , sym same))
    ... | no _ = proj₂ old origin path entry present

-- Schema deletion is a family operation, never a consequence of removing one
-- linked worktree. Active readers/jobs and explicit removal intent are additional
-- runtime guards beyond this reference-safety predicate.
SafeFamilyDrop : ∀ {baselines} → World baselines → FamilyId → Set
SafeFamilyDrop world family = ∀ ref → VersionRef.family ref ≡ family → ¬ Referenced world ref

referencedFamilyCannotDrop : ∀ {baselines} (world : World baselines) ref → Referenced world ref →
  ¬ SafeFamilyDrop world (VersionRef.family ref)
referencedFamilyCannotDrop world ref used safe = safe ref refl used

NonEmptyFilePath : FilePath → Set
NonEmptyFilePath fp = ¬ (FilePath.value fp ≡ "")
