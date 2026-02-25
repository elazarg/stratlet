import distilled.Vegas

/-!
# DAG State Machine for Vegas

A canonical, order-independent representation of Vegas programs as event DAGs.
Two programs that differ only in the ordering of independent events (e.g., two
commits for different players) have the same event graph, making commutativity
structural rather than requiring per-pair theorems.

## Structure

- **Layer 1** (§1–5): Event graph + state machine (no dependent typing)
- **Layer 2** (§6–8): Bridge connecting DAG execution to `outcomeDist` on `Prog`
- **Layer 3** (§9): Key theorems (outcome uniqueness, adequacy)

## Design

Inspired by compiler IRs (Kotlin coroutine state machine). The DAG is extracted
from a `Prog` by walking its structure and recording dependencies via
`exprVars`/`distExprVars`/`viewCtx`.
-/

-- ============================================================================
-- § 1. Nodes
-- ============================================================================

/-- The kind of event in the program DAG. -/
inductive EventKind where
  | letExpr  -- deterministic expression binding
  | sample   -- nature's random choice
  | commit   -- player's strategic choice
  | reveal   -- making a hidden value public
  deriving DecidableEq, Repr

/-- A node in the program DAG. -/
structure EventNode where
  id : VarId          -- the variable this node binds
  kind : EventKind    -- what kind of event
  deps : List VarId   -- variables this node reads
  deriving DecidableEq, Repr

-- ============================================================================
-- § 2. Partial environment
-- ============================================================================

/-- A value tagged with its base type. -/
structure TaggedVal where
  base : BaseTy
  val : Val base

instance : DecidableEq TaggedVal := by
  intro ⟨b₁, v₁⟩ ⟨b₂, v₂⟩
  cases b₁ <;> cases b₂
  · -- int, int
    exact if h : v₁ = v₂
      then .isTrue (by subst h; rfl)
      else .isFalse (by intro heq; cases heq; exact h rfl)
  · exact .isFalse (by intro h; cases h)
  · exact .isFalse (by intro h; cases h)
  · -- bool, bool
    exact if h : v₁ = v₂
      then .isTrue (by subst h; rfl)
      else .isFalse (by intro heq; cases heq; exact h rfl)

/-- A partial assignment of variable values. -/
def PartialEnv := VarId → Option TaggedVal

instance : Inhabited PartialEnv := ⟨fun _ => none⟩

/-- The empty partial environment. -/
def PartialEnv.empty : PartialEnv := fun _ => none

/-- Extend a partial environment with a single binding. -/
def PartialEnv.set (pe : PartialEnv) (x : VarId) (v : TaggedVal) : PartialEnv :=
  fun y => if y = x then some v else pe y

-- ============================================================================
-- § 3. Configuration
-- ============================================================================

/-- State of the DAG execution. -/
structure Config where
  pending : List EventNode   -- events not yet fired
  env     : PartialEnv       -- resolved variable values

/-- A node is ready when all its dependencies are resolved. -/
def EventNode.ready (e : EventNode) (c : Config) : Bool :=
  e.deps.all (fun x => (c.env x).isSome)

/-- The events that can fire right now. -/
def Config.readyEvents (c : Config) : List EventNode :=
  c.pending.filter (·.ready c)

/-- No pending events remain. -/
def Config.terminal (c : Config) : Prop := c.pending = []

instance : Decidable (Config.terminal c) :=
  inferInstanceAs (Decidable (c.pending = []))

-- ============================================================================
-- § 4. Step relation
-- ============================================================================

/-- One step: fire a ready node, recording its value. -/
structure Step (c₁ c₂ : Config) where
  node : EventNode
  value : TaggedVal
  hmem : node ∈ c₁.pending
  hready : node.ready c₁ = true
  henv : c₂.env = c₁.env.set node.id value
  hpending : c₂.pending = c₁.pending.erase node

-- ============================================================================
-- § 5. Execution
-- ============================================================================

/-- A complete execution: a sequence of steps from one config to another. -/
inductive Execution : Config → Config → Type where
  | done {c : Config} : Execution c c
  | step {c₁ c₂ c₃ : Config} : Step c₁ c₂ → Execution c₂ c₃ → Execution c₁ c₃

/-- Length of an execution (number of steps). -/
def Execution.length : Execution c₁ c₂ → Nat
  | .done => 0
  | .step _ rest => 1 + rest.length

-- ============================================================================
-- § 6. Extraction from Prog
-- ============================================================================

/-- Extract the event graph from a Prog. Walks the program structure and
    builds one EventNode per binding site.

    Dependency computation follows `toMAIDBuild` in GameSemantics.lean:
    - `letExpr x e k`: deps = `exprVars e`
    - `sample x τ m D k`: deps = `distExprVars D`
    - `commit x who acts R k`: deps = all vars visible to `who` in Γ
    - `reveal y who x hx k`: deps = `[x]` -/
def Prog.extractEvents : Prog Γ → List EventNode
  | .ret _ => []
  | .letExpr x e k =>
    { id := x, kind := .letExpr, deps := exprVars e } ::
    k.extractEvents
  | .sample x _τ _m D k =>
    { id := x, kind := .sample, deps := distExprVars D } ::
    k.extractEvents
  | .commit x who _acts _R k =>
    { id := x, kind := .commit,
      deps := (viewCtx who Γ).map Prod.fst } ::
    k.extractEvents
  | .reveal y _who x _hx k =>
    { id := y, kind := .reveal, deps := [x] } ::
    k.extractEvents

/-- Build a PartialEnv from a typed Env by looking up each variable in Γ. -/
noncomputable def initPartialEnv : (Γ : Ctx) → Env Γ → PartialEnv
  | [], _ => PartialEnv.empty
  | (x, τ) :: Γ', env =>
    let rest := initPartialEnv Γ' (fun a b h => env a b (.there h))
    rest.set x ⟨τ.base, env.get .here⟩

/-- Build initial Config from a Prog and an initial Env.
    The initial partial env is populated from the given Env Γ
    (the "already bound" variables). -/
noncomputable def Prog.initConfig (p : Prog Γ) (env : Env Γ) : Config where
  pending := p.extractEvents
  env := initPartialEnv Γ env

-- ============================================================================
-- § 7. PartialEnv ↔ Env bridge
-- ============================================================================

/-- A PartialEnv is consistent with an Env Γ when every variable
    in Γ maps to its correct value. -/
def PartialEnv.consistent (pe : PartialEnv) {Γ : Ctx} (env : Env Γ) : Prop :=
  ∀ x τ (h : HasVar Γ x τ), pe x = some ⟨τ.base, env.get h⟩

/-- Reconstruct a typed Env from a PartialEnv, if all variables
    in Γ are resolved with the correct base types. -/
noncomputable def PartialEnv.toEnv? (pe : PartialEnv) :
    (Γ : Ctx) → Option (Env Γ)
  | [] => some Env.empty
  | (x, τ) :: Γ' =>
    match pe x with
    | none => none
    | some ⟨b, v⟩ =>
      match decEq b τ.base with
      | .isTrue h =>
        match pe.toEnv? Γ' with
        | none => none
        | some env' => some (Env.cons (h ▸ v) env')
      | .isFalse _ => none

-- ============================================================================
-- § 8. Step weight
-- ============================================================================

/-- Weight of a step under a profile σ. Conceptual definition:
    - letExpr, reveal: weight 1 (deterministic)
    - sample: (evalDistExpr D env_deps) v
    - commit: (σ.commit who x acts R (env.toView who)) v
    Requires reconstructing a typed Env from the PartialEnv
    for the node's dependency context.

    This is sorry'd pending the bridge infrastructure (Milestone 2). -/
noncomputable def Step.weight (_σ : Profile) (_p : Prog Γ)
    (_s : Step c₁ c₂) : ℚ≥0 := sorry

/-- Weight of a complete execution (product of step weights). -/
noncomputable def Execution.weight (σ : Profile) (p : Prog Γ) :
    Execution c₁ c₂ → ℚ≥0
  | .done => 1
  | .step s rest => s.weight σ p * rest.weight σ p

-- ============================================================================
-- § 9. Key theorems (sorry'd — Milestone 3)
-- ============================================================================

/-- All complete executions from the same initial config produce
    the same final environment (regardless of firing order).
    This is the determinism theorem: the DAG has a unique fixpoint. -/
theorem execution_env_unique {c₁ c_term₁ c_term₂ : Config}
    (_exec₁ : Execution c₁ c_term₁)
    (_exec₂ : Execution c₁ c_term₂)
    (_hterm₁ : c_term₁.terminal) (_hterm₂ : c_term₂.terminal) :
    c_term₁.env = c_term₂.env := sorry

/-- The weighted-outcome distribution from the DAG state machine
    equals outcomeDist on the underlying Prog.

    dagOutcomeDist σ p env := sum over all complete executions of
    (execution.weight σ p) * (outcome from final env)

    This is the adequacy theorem connecting the two representations. -/
theorem dagOutcomeDist_eq_outcomeDist {Γ : Ctx} (_σ : Profile)
    (_p : Prog Γ) (_env : Env Γ) :
    True := sorry  -- placeholder: full statement needs dagOutcomeDist def

-- ============================================================================
-- § 10. Examples
-- ============================================================================

namespace DAGExamples

open Examples in
/-- Extract event graph from matching pennies. -/
def mpEvents : List EventNode := matchingPennies.extractEvents

-- Expected:
--   commit 0, deps=[] (player 0, no visible vars)
--   commit 1, deps=[] (player 1, no visible vars)
--   reveal 2, deps=[0]
--   reveal 3, deps=[1]
#eval mpEvents.map (fun n => (n.id, n.kind, n.deps))

open Examples in
/-- Extract event graph from conditioned game. -/
def cgEvents : List EventNode := conditionedGame.extractEvents

-- Expected:
--   commit 0, deps=[] (player 0, no visible vars)
--   reveal 2, deps=[0]
--   commit 1, deps=[2] (player 1, sees va' which is public)
--   reveal 3, deps=[1]
#eval cgEvents.map (fun n => (n.id, n.kind, n.deps))

end DAGExamples
