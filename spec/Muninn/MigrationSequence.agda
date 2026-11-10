{-# OPTIONS --safe #-}
-- Ordered migration blocks resume from their committed ledger entries.
module Muninn.MigrationSequence where
import Muninn.MigrationBlock as B
import Muninn.OwnedState as O
import Muninn.Dialogue as D
import Muninn.Schema as Schema
import Muninn.Worktree as W
import Data.String
open import Data.Nat using (ℕ)
open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym; cong; subst)
module Exec = O.Execution
module DB = Exec.DB

-- The required catalog is specified independently of the migration script.
record Requirement : Set where
  field scope : B.Scope
        schema : W.SchemaId
        slot : ℕ
        expected : Data.String.String

module Sequence (codec : B.LedgerCodec) where
  data Reply : Set where ready : Reply; ask : D.Prompt → Reply
  mutual
    script : List B.Block → Exec.Script Reply
    script [] = Exec.done ready
    script (block ∷ rest) = Exec.atomic (B.Apply.transaction codec block) (next block rest)
    next : (block : B.Block) → List B.Block → B.Reply → Exec.Script Reply
    next block rest B.prepared = script rest
    next block rest (B.ask guidance) = Exec.done (ask guidance)

  -- A migration block changes only its own catalog and ledger slots, whether it
  -- commits, is already applied, or leaves the transaction unchanged.
  blockFrame : ∀ block world key → B.Block.markerSlot block ≢ key → B.Block.catalogSlot block ≢ key →
    DB.lookup key (proj₂ (DB.execute (B.Apply.transaction codec block) world)) ≡ DB.lookup key world
  blockFrame block world key markerDifferent catalogDifferent with DB.lookup (B.Block.markerSlot block) world
  ... | just row with B.Apply.markerMatches codec block row
  ...   | true = refl
  ...   | false = refl
  blockFrame block world key markerDifferent catalogDifferent | nothing with B.Apply.catalogAccepts codec block (DB.lookup (B.Block.catalogSlot block) world)
  ... | true = B.Apply.otherPreserved codec block world key markerDifferent catalogDifferent
  ... | false = refl

  data Safe (key : ℕ) : List B.Block → Set where
    safeEnd : Safe key []
    safeNext : ∀ {block rest} → B.Block.markerSlot block ≢ key → B.Block.catalogSlot block ≢ key → Safe key rest → Safe key (block ∷ rest)

  -- A safe program preserves a key at each committed transaction, regardless
  -- of its replies. This uses the existing generic interruption semantics.
  data SafeProgram (key : ℕ) : Exec.Script Reply → Set₁ where
    safeDone : ∀ result → SafeProgram key (Exec.done result)
    safeAtomic : ∀ {A : Set} (transaction : DB.Transaction A) (continuation : A → Exec.Script Reply) →
      (∀ world → DB.lookup key (proj₂ (DB.execute transaction world)) ≡ DB.lookup key world) →
      (∀ reply → SafeProgram key (continuation reply)) → SafeProgram key (Exec.atomic transaction continuation)

  programFrame : ∀ {key program before residual after} → SafeProgram key program →
    Exec.Prefix program before residual after → DB.lookup key after ≡ DB.lookup key before
  programFrame safe Exec.stop = refl
  programFrame (safeAtomic transaction continuation frame nextSafe) (Exec.committed prefix) =
    trans (programFrame (nextSafe (proj₁ (DB.execute transaction _))) prefix) (frame _)

  safeProgram : ∀ blocks key → Safe key blocks → SafeProgram key (script blocks)
  safeProgram [] key safeEnd = safeDone ready
  safeProgram (block ∷ rest) key (safeNext markerDifferent catalogDifferent safe) =
    safeAtomic (B.Apply.transaction codec block) (next block rest)
      (λ world → blockFrame block world key markerDifferent catalogDifferent) continueSafe
    where
    continueSafe : ∀ reply → SafeProgram key (next block rest reply)
    continueSafe B.prepared = safeProgram rest key safe
    continueSafe (B.ask guidance) = safeDone (ask guidance)

  prefixFrame : ∀ blocks world key residual after → Safe key blocks →
    Exec.Prefix (script blocks) world residual after → DB.lookup key after ≡ DB.lookup key world
  prefixFrame blocks world key residual after safe prefix = programFrame (safeProgram blocks key safe) prefix

  continueStep : ∀ block rest before (result : B.Reply × O.World) reply final →
    DB.execute (B.Apply.transaction codec block) before ≡ result →
    Exec.Completed (next block rest (proj₁ result)) (proj₂ result) reply final →
    Exec.Completed (script (block ∷ rest)) before reply final
  continueStep block rest before .(DB.execute (B.Apply.transaction codec block) before) reply final refl tail = Exec.committed tail

  -- The finite manifest cannot create an unbounded migration loop. A needed
  -- clarification returns to the existing dialogue rather than spinning.
  terminates : ∀ blocks before → Σ Reply (λ reply → Σ O.World (λ final → Exec.Completed (script blocks) before reply final))
  terminates [] before = ready , before , Exec.stop
  terminates (block ∷ rest) before with DB.execute (B.Apply.transaction codec block) before in executed
  ... | (B.prepared , middle) with terminates rest middle
  ...   | reply , final , tail = reply , final , continueStep block rest before (B.prepared , middle) reply final executed tail
  terminates (block ∷ rest) before | (B.ask guidance , middle) =
    ask guidance , middle , continueStep block rest before (B.ask guidance , middle) (ask guidance) middle executed Exec.stop

  -- The plan is the intended migration history over actual shared records.
  -- Each step either observes its existing ledger entry or atomically commits
  -- the next schema state and ledger row.
  data Plan : List B.Block → O.World → O.World → Set where
    planDone : ∀ world → Plan [] world world
    already : ∀ {block rest world final} →
      DB.lookup (B.Block.markerSlot block) world ≡ just (B.Apply.ledger codec block) →
      (Safe (B.Block.catalogSlot block) rest → DB.lookup (B.Block.catalogSlot block) world ≡ just (B.Apply.updated codec block)) →
      Plan rest world final → Plan (block ∷ rest) world final
    apply : ∀ {block rest world final} →
      DB.lookup (B.Block.markerSlot block) world ≡ nothing →
      DB.lookup (B.Block.catalogSlot block) world ≡ B.Apply.original codec block →
      Plan rest (B.Apply.changed codec block world) final → Plan (block ∷ rest) world final

  data Ordered : List B.Block → Set where
    orderedEnd : Ordered []
    orderedNext : ∀ {block rest} → Safe (B.Block.markerSlot block) rest → Ordered rest → Ordered (block ∷ rest)

  completeStep : ∀ block rest before middle final →
    DB.execute (B.Apply.transaction codec block) before ≡ (B.prepared , middle) →
    Exec.Completed (script rest) middle ready final → Exec.Completed (script (block ∷ rest)) before ready final
  completeStep block rest before middle final executed tail = Exec.committed
    (subst (λ result → Exec.Prefix (next block rest (proj₁ result)) (proj₂ result) (Exec.done ready) final) (sym executed) tail)

  completes : ∀ {blocks before final} → Plan blocks before final → Exec.Completed (script blocks) before ready final
  completes (planDone world) = Exec.stop
  completes (already {block} {rest} {world} {final} saved lastValid tail) =
    completeStep block rest world world final (B.Apply.replay codec block world saved) (completes tail)
  completes (apply {block} {rest} {world} {final} missing found tail) =
    completeStep block rest world (B.Apply.changed codec block world) final (B.Apply.commits codec block world missing found) (completes tail)

  unstep : ∀ block rest before middle residual observed →
    DB.execute (B.Apply.transaction codec block) before ≡ (B.prepared , middle) →
    Exec.Prefix (script (block ∷ rest)) before residual observed →
    (observed ≡ before) ⊎ Exec.Prefix (script rest) middle residual observed
  unstep block rest before middle residual observed executed Exec.stop = inj₁ refl
  unstep block rest before middle residual observed executed (Exec.committed tail) = inj₂
    (subst (λ result → Exec.Prefix (next block rest (proj₁ result)) (proj₂ result) residual observed) executed tail)

  -- A retry starts at the beginning, but already committed blocks read their
  -- exact ledger rows and become no-ops. Later blocks cannot alter those rows.
  resumes : ∀ {blocks before final} → Ordered blocks → Plan blocks before final →
    ∀ observed → Exec.Interrupted (script blocks) before observed → Exec.Completed (script blocks) observed ready final
  resumes orderedEnd (planDone world) observed (residual , Exec.stop) = Exec.stop
  resumes (orderedNext safe ordered) plan@(already {block} {rest} {world} {final} saved lastValid tail) observed (residual , prefix)
    with unstep block rest world world residual observed (B.Apply.replay codec block world saved) prefix
  ... | inj₁ same = subst (λ start → Exec.Completed (script (block ∷ rest)) start ready final) (sym same) (completes plan)
  ... | inj₂ continued = completeStep block rest observed observed final
    (B.Apply.replay codec block observed markerAtObserved)
    (resumes ordered tail observed (residual , continued))
    where
    markerAtObserved : DB.lookup (B.Block.markerSlot block) observed ≡ just (B.Apply.ledger codec block)
    markerAtObserved = trans (prefixFrame rest world (B.Block.markerSlot block) residual observed safe continued) saved
  resumes (orderedNext safe ordered) plan@(apply {block} {rest} {world} {final} missing found tail) observed (residual , prefix)
    with unstep block rest world (B.Apply.changed codec block world) residual observed (B.Apply.commits codec block world missing found) prefix
  ... | inj₁ same = subst (λ start → Exec.Completed (script (block ∷ rest)) start ready final) (sym same) (completes plan)
  ... | inj₂ continued = completeStep block rest observed observed final
    (B.Apply.replay codec block observed markerAtObserved)
    (resumes ordered tail observed (residual , continued))
    where
    markerAtObserved : DB.lookup (B.Block.markerSlot block) observed ≡ just (B.Apply.ledger codec block)
    markerAtObserved = trans
      (prefixFrame rest (B.Apply.changed codec block world) (B.Block.markerSlot block) residual observed safe continued)
      (B.Apply.markerSaved codec block world)

  -- The goal is stated directly on the final database, independently of the
  -- execution script: every required block has its own exact ledger record.
  data Applied : List B.Block → O.World → Set where
    appliedEnd : ∀ {world} → Applied [] world
    appliedNext : ∀ {block rest world} →
      DB.lookup (B.Block.markerSlot block) world ≡ just (B.Apply.ledger codec block) →
      Applied rest world → Applied (block ∷ rest) world

  appliedAfter : ∀ {blocks before final} → Ordered blocks → Plan blocks before final → Applied blocks final
  appliedAfter orderedEnd (planDone world) = appliedEnd
  appliedAfter (orderedNext safe ordered) (already {block} {rest} {world} {final} saved lastValid tail) =
    appliedNext (trans (prefixFrame rest world (B.Block.markerSlot block) (Exec.done ready) final safe (completes tail)) saved)
      (appliedAfter ordered tail)
  appliedAfter (orderedNext safe ordered) (apply {block} {rest} {world} {final} missing found tail) =
    appliedNext (trans (prefixFrame rest (B.Apply.changed codec block world) (B.Block.markerSlot block) (Exec.done ready) final safe (completes tail))
      (B.Apply.markerSaved codec block world)) (appliedAfter ordered tail)

  -- The last block touching a catalog determines its required final schema.
  data Final (block : B.Block) : List B.Block → Set where
    finalHere : ∀ {rest} → Safe (B.Block.catalogSlot block) rest → Final block (block ∷ rest)
    finalLater : ∀ {other rest} → Final block rest → Final block (other ∷ rest)

  schemaAfter : ∀ {blocks before final} (plan : Plan blocks before final) block → Final block blocks →
    DB.lookup (B.Block.catalogSlot block) final ≡ just (B.Apply.updated codec block)
  schemaAfter (already {block} {rest} {world} {final} saved lastValid tail) .block (finalHere safe) =
    trans (prefixFrame rest world (B.Block.catalogSlot block) (Exec.done ready) final safe (completes tail)) (lastValid safe)
  schemaAfter (apply {block} {rest} {world} {final} missing found tail) .block (finalHere safe) =
    trans (prefixFrame rest (B.Apply.changed codec block world) (B.Block.catalogSlot block) (Exec.done ready) final safe (completes tail))
      (B.Apply.schemaSaved codec block world)
  schemaAfter (already saved lastValid tail) block (finalLater later) = schemaAfter tail block later
  schemaAfter (apply missing found tail) block (finalLater later) = schemaAfter tail block later

  -- Each independently required catalog must be the final outcome of some
  -- block, with its owner, schema identity, slot and content all fixed.
  record Realizes (requirements : List Requirement) (blocks : List B.Block) : Set where
    field find : ∀ requirement → requirement ∈ requirements → Σ B.Block (λ item →
            Final item blocks × (B.Block.scope item ≡ Requirement.scope requirement) ×
            (B.Block.schema item ≡ Requirement.schema requirement) × (B.Block.catalogSlot item ≡ Requirement.slot requirement) ×
            (B.Block.afterCatalog item ≡ Requirement.expected requirement))

  requirementsAfter : ∀ {blocks before final} (plan : Plan blocks before final) requirements → Realizes requirements blocks →
    ∀ requirement → requirement ∈ requirements →
    DB.lookup (Requirement.slot requirement) final ≡ just (B.catalog (Requirement.scope requirement) (Requirement.expected requirement))
  requirementsAfter plan requirements realizes requirement member with Realizes.find realizes requirement member
  ... | block , isFinal , refl , refl , refl , refl = schemaAfter plan block isFinal

  completedUnique : ∀ {program : Exec.Script Reply} {before firstWorld secondWorld : O.World} {first second : Reply} →
    Exec.Completed program before first firstWorld → Exec.Completed program before second secondWorld →
    (first ≡ second) × (firstWorld ≡ secondWorld)
  completedUnique Exec.stop Exec.stop = refl , refl
  completedUnique (Exec.committed first) (Exec.committed second) = completedUnique first second

  preservedAfter : ∀ {blocks before final} → Plan blocks before final →
    ∀ key value → DB.lookup key before ≡ just value →
    (∀ block → block ∈ blocks → B.Block.catalogSlot block ≢ key) → DB.lookup key final ≡ just value
  preservedAfter (planDone world) key value found safe = found
  preservedAfter (already saved lastValid tail) key value found safe =
    preservedAfter tail key value found (λ block member → safe block (there member))
  preservedAfter (apply {block} {rest} {world} missing found tail) key value valueAt safe =
    preservedAfter tail key value preserved (λ later member → safe later (there member))
    where
    markerDifferent : B.Block.markerSlot block ≢ key
    markerDifferent refl with trans (sym missing) valueAt
    ... | ()
    preserved : DB.lookup key (B.Apply.changed codec block world) ≡ just value
    preserved = trans (B.Apply.otherPreserved codec block world key markerDifferent (safe block (here refl))) valueAt

  record Goal (requirements : List Requirement) (blocks : List B.Block) (before after : O.World) : Set where
    field requiredSchemas : ∀ requirement → requirement ∈ requirements →
            DB.lookup (Requirement.slot requirement) after ≡ just (B.catalog (Requirement.scope requirement) (Requirement.expected requirement))
          allApplied : Applied blocks after
          preserved : ∀ key value → DB.lookup key before ≡ just value →
            (∀ block → block ∈ blocks → B.Block.catalogSlot block ≢ key) → DB.lookup key after ≡ just value
          finalSchemas : ∀ block → Final block blocks → DB.lookup (B.Block.catalogSlot block) after ≡ just (B.Apply.updated codec block)
          untouched : ∀ key → Safe key blocks → DB.lookup key after ≡ DB.lookup key before

  goalAfter : ∀ {blocks before final} requirements → Realizes requirements blocks → Ordered blocks → Plan blocks before final → Goal requirements blocks before final
  goalAfter {blocks} {before} {final} requirements realizes ordered plan = record
    { requiredSchemas = requirementsAfter plan requirements realizes
    ; allApplied = appliedAfter ordered plan
    ; preserved = preservedAfter plan
    ; finalSchemas = schemaAfter plan
    ; untouched = λ key safe → prefixFrame blocks before key (Exec.done ready) final safe (completes plan) }

  converges : ∀ {blocks before final} requirements → Realizes requirements blocks → (ordered : Ordered blocks) → (plan : Plan blocks before final) →
    ∀ observed reply after → Exec.Interrupted (script blocks) before observed →
    Exec.Completed (script blocks) observed reply after → Goal requirements blocks before after
  converges {blocks} {before} requirements realizes ordered plan observed reply after interrupted completed =
    subst (Goal requirements blocks before) (sym (proj₂ (completedUnique completed (resumes ordered plan observed interrupted)))) (goalAfter requirements realizes ordered plan)

  appliedLookup : ∀ {blocks world} (block : B.Block) → block ∈ blocks → Applied blocks world →
    DB.lookup (B.Block.markerSlot block) world ≡ just (B.Apply.ledger codec block)
  appliedLookup .block (here refl) (appliedNext {block} saved rest) = saved
  appliedLookup block (there member) (appliedNext saved rest) = appliedLookup block member rest

  -- Public and family application templates are distinct; neither may be
  -- satisfied by migration records owned by another scope.
  record Coverage (required : Schema.Template) (schema : W.SchemaId) (scope : B.Scope) (blocks : List B.Block) : Set where
    field covers : ∀ migration → migration ∈ required → Σ B.Block (λ item →
            (item ∈ blocks) × (B.Block.scope item ≡ scope) × (B.Block.schema item ≡ schema) × (B.Block.migration item ≡ migration))

  Installed : Schema.Template → W.SchemaId → B.Scope → List B.Block → O.World → Set
  Installed required schema scope blocks world = ∀ migration → migration ∈ required → Σ B.Block (λ block →
    (B.Block.scope block ≡ scope) × (B.Block.schema block ≡ schema) × (B.Block.migration block ≡ migration) ×
    (DB.lookup (B.Block.markerSlot block) world ≡ just (B.Apply.ledger codec block)))

  installedAfter : ∀ required schema scope blocks world → Coverage required schema scope blocks → Applied blocks world →
    Installed required schema scope blocks world
  installedAfter required schema scope blocks world coverage applied migration member with Coverage.covers coverage migration member
  ... | block , included , sameScope , sameSchema , sameMigration =
    block , sameScope , sameSchema , sameMigration , appliedLookup block included applied

  -- Startup needs an independently specified public catalog and family catalog.
  -- An empty requirements list therefore cannot establish readiness.
  record RequiredCatalogs (family : ℕ) (publicSchema : W.SchemaId) (pair : Schema.SchemaPair) (requirements : List Requirement) : Set where
    field publicCatalog familyCatalog : Requirement
          publicListed : publicCatalog ∈ requirements
          familyListed : familyCatalog ∈ requirements
          publicScope : Requirement.scope publicCatalog ≡ B.shared
          familyScope : Requirement.scope familyCatalog ≡ B.family family
          publicIdentity : Requirement.schema publicCatalog ≡ publicSchema
          familyIdentity : Requirement.schema familyCatalog ≡ Schema.SchemaPair.application pair

  record Ready (family : ℕ) (publicRequired familyRequired : Schema.Template) (publicSchema : W.SchemaId)
    (pair : Schema.SchemaPair) (requirements : List Requirement) (blocks : List B.Block) (world : O.World) : Set where
    field catalogs : RequiredCatalogs family publicSchema pair requirements
          requiredSchemas : ∀ requirement → requirement ∈ requirements →
            DB.lookup (Requirement.slot requirement) world ≡ just (B.catalog (Requirement.scope requirement) (Requirement.expected requirement))
          publicInstalled : Installed publicRequired publicSchema B.shared blocks world
          familyInstalled : Installed familyRequired (Schema.SchemaPair.application pair) (B.family family) blocks world
          graph : Schema.GraphReady pair

  readyAfter : ∀ family publicRequired familyRequired publicSchema pair requirements blocks before after →
    RequiredCatalogs family publicSchema pair requirements → Coverage publicRequired publicSchema B.shared blocks →
    Coverage familyRequired (Schema.SchemaPair.application pair) (B.family family) blocks →
    Schema.GraphReady pair → Goal requirements blocks before after →
    Ready family publicRequired familyRequired publicSchema pair requirements blocks after
  readyAfter family publicRequired familyRequired publicSchema pair requirements blocks before after catalogs publicCoverage familyCoverage graph goal = record
    { catalogs = catalogs; requiredSchemas = Goal.requiredSchemas goal
    ; publicInstalled = installedAfter publicRequired publicSchema B.shared blocks after publicCoverage (Goal.allApplied goal)
    ; familyInstalled = installedAfter familyRequired (Schema.SchemaPair.application pair) (B.family family) blocks after familyCoverage (Goal.allApplied goal)
    ; graph = graph }

  -- Public readiness is sufficient for installation-wide operations; a
  -- family graph is required only when operating on that family.
  record PublicReady (required : Schema.Template) (schema : W.SchemaId)
    (requirements : List Requirement) (blocks : List B.Block) (world : O.World) : Set where
    field catalog : Requirement
          listed : catalog ∈ requirements
          scope : Requirement.scope catalog ≡ B.shared
          identity : Requirement.schema catalog ≡ schema
          catalogReady : DB.lookup (Requirement.slot catalog) world ≡ just (B.catalog (Requirement.scope catalog) (Requirement.expected catalog))
          installed : Installed required schema B.shared blocks world

  publicReadyAfter : ∀ required schema requirements blocks before after (catalog : Requirement) →
    catalog ∈ requirements → Requirement.scope catalog ≡ B.shared → Requirement.schema catalog ≡ schema →
    Coverage required schema B.shared blocks → Goal requirements blocks before after →
    PublicReady required schema requirements blocks after
  publicReadyAfter required schema requirements blocks before after catalog listed scope identity coverage goal = record
    { catalog = catalog; listed = listed; scope = scope; identity = identity
    ; catalogReady = Goal.requiredSchemas goal catalog listed
    ; installed = installedAfter required schema B.shared blocks after coverage (Goal.allApplied goal) }
