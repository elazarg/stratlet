import distilled.Vegas
import GameTheory.EFG
import GameTheory.MAID
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Game Semantics for Vegas Programs

Compiles Vegas programs to standard game-theoretic representations:
- `RGameTree` / `EFG.GameTree` (extensive-form game trees)
- `MAID.Node` list (multi-agent influence diagram)
-/

-- ============================================================================
-- § 1. Rat-weighted game tree (computable)
-- ============================================================================

/-- Computable game tree using `Rat` weights and `Int` payoffs. -/
inductive RGameTree where
  | terminal (payoff : Player → Int)
  | chance (branches : List (RGameTree × Rat))
  | decision (pid : Nat) (player : Player)
      (actions : List RGameTree)

-- ============================================================================
-- § 2. Compilation from Vegas to RGameTree
-- ============================================================================

/-- Compile a Vegas program to a computable game tree.
    Commit sites become decision nodes with actions filtered by `R`.
    Sample sites evaluate the syntactic `DistExpr` and enumerate support.
    Requires `Legal p` and `WF p`. -/
def toRGameTree : (p : Prog Γ) → Legal p → WF p → Env Γ → RGameTree
  | .ret u, _, _, env => .terminal (fun who => sorry) -- evalPayoffMap returns Outcome now
  | .letExpr x e k, hl, hw, env =>
    toRGameTree k hl hw.2 (Env.cons (x := x) (evalExpr e env) env)
  | .sample x τ m D k, hl, hw, env =>
    -- Evaluate the DistExpr to get support + weights
    -- For compilation we need to enumerate the support, which requires
    -- evaluating the noncomputable FDist. Use sorry for now.
    sorry
  | .commit x who acts R k, hl, hw, env =>
    let view := env.toView who
    let allowed := acts.filter (evalR R · view)
    .decision x who (allowed.map
      (fun a => toRGameTree k hl.2 hw.2 (Env.cons (x := x) a env)))
  | .reveal y _who _x (b := b) hx k, hl, hw, env =>
    let v : Val b := env.get hx
    toRGameTree k hl hw.2 (Env.cons (x := y) (τ := .pub b) v env)

-- ============================================================================
-- § 3. Bridge to classic EFG (noncomputable)
-- ============================================================================

/-- Construct a `PMF (Fin n)` from `NNReal` weights by normalizing.
    Falls back to uniform distribution if all weights are zero. -/
noncomputable def normalizedFinPMF {n : Nat} (weights : Fin n → NNReal)
    (hn : 0 < n) : PMF (Fin n) :=
  let f : Fin n → ENNReal := fun i => ↑(weights i)
  have htop : ∑' i, f i ≠ ⊤ := by
    rw [tsum_fintype, ← ENNReal.coe_finset_sum]
    exact ENNReal.coe_ne_top
  if h0 : ∑' i, f i = 0 then
    PMF.ofFintype (fun _ => (n : ENNReal)⁻¹) (by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact ENNReal.mul_inv_cancel (by exact_mod_cast hn.ne') (ENNReal.natCast_ne_top n))
  else
    PMF.normalize f h0 htop

/-- Convert `RGameTree` to `EFG.GameTree Player`.
    Casts `Rat → NNReal` for weights and `Int → ℝ` for payoffs.
    List-based branches are converted to `Fin n`-indexed branches.
    Noncomputable due to `NNReal`, `ℝ`, and `PMF`. -/
noncomputable def RGameTree.toEFG : RGameTree → EFG.GameTree Player
  | .terminal payoff =>
    .terminal (fun p => (payoff p : ℝ))
  | .chance branches =>
    let pairs := toChance branches
    let n := pairs.length
    if hn : 0 < n then
      .chance n (normalizedFinPMF (fun i => (pairs.get i).2) hn)
        (fun i => (pairs.get i).1)
    else .terminal (fun _ => 0)
  | .decision pid player actions =>
    let trees := toDecision actions
    let n := trees.length
    .decision pid player n (fun i => trees.get i)
where
  toChance : List (RGameTree × Rat) → List (EFG.GameTree Player × NNReal)
    | [] => []
    | (t, w) :: rest =>
      (t.toEFG, ⟨max (↑w) 0, le_max_right _ _⟩) :: toChance rest
  toDecision : List RGameTree → List (EFG.GameTree Player)
    | [] => []
    | t :: rest => t.toEFG :: toDecision rest

-- ============================================================================
-- § 4. Compilation from Vegas to MAID
-- ============================================================================

def payoffVars (u : PayoffMap Γ) : List VarId :=
  (u.entries.map (fun (_, e) => exprVars e)).flatten

/-- Internal state for MAID compilation. -/
structure MAIDBuilder where
  nextId : Nat
  nodes  : List MAID.Node
  /-- (varId, bindingType, transitive MAID node dependencies) -/
  vars   : List (VarId × BindTy × List Nat)

namespace MAIDBuilder

def empty : MAIDBuilder := ⟨0, [], []⟩

def lookupDeps (st : MAIDBuilder) (x : VarId) : List Nat :=
  match st.vars.find? (fun (v, _, _) => v == x) with
  | some (_, _, deps) => deps
  | none => []

def depsOfVars (st : MAIDBuilder) (xs : List VarId) : List Nat :=
  ((xs.map st.lookupDeps).flatten).dedup

def playerDeps (st : MAIDBuilder) (who : Player) : List Nat :=
  ((st.vars.filter (fun (_, τ, _) => canSee who τ)).map
    (fun (_, _, ds) => ds)).flatten.dedup

def pubDeps (st : MAIDBuilder) : List Nat :=
  ((st.vars.filter (fun (_, τ, _) => match τ with | .pub _ => true | .hidden _ _ => false)).map
    (fun (_, _, ds) => ds)).flatten.dedup

def addNode (st : MAIDBuilder) (kind : MAID.NodeKind) (parents : List Nat)
    (domainSize : Nat) : Nat × MAIDBuilder :=
  (st.nextId,
   { nextId := st.nextId + 1
     nodes := st.nodes ++ [{ id := st.nextId, kind := kind,
                              parents := parents, domainSize := domainSize }]
     vars := st.vars })

def addVar (st : MAIDBuilder) (x : VarId) (τ : BindTy) (deps : List Nat) :
    MAIDBuilder :=
  { st with vars := st.vars ++ [(x, τ, deps)] }

end MAIDBuilder

def BaseTy.domainSize : BaseTy → Nat
  | .bool => 2
  | .int => 0

/-- Compile a Vegas program to MAID nodes.
    Sample arm uses `distExprVars D` for dependencies.
    Commit arm uses `exprVars R` for restriction dependencies. -/
def toMAIDBuild : Prog Γ → MAIDBuilder → MAIDBuilder
  | .ret u, st =>
    let deps := st.depsOfVars (payoffVars u)
    let players := (u.entries.map Prod.fst).dedup
    players.foldl (fun s who =>
      (s.addNode (.utility who) deps 1).2) st
  | @Prog.letExpr _ x b e k, st =>
    let deps := st.depsOfVars (exprVars e)
    toMAIDBuild k (st.addVar x (.pub b) deps)
  | @Prog.sample _ x τ m D k, st =>
    let parents := match τ, m with
      | .pub _, .NaturePub => st.pubDeps
      | .hidden _ _, .NaturePriv => st.pubDeps
      | .hidden p _, .PlayerPriv => st.playerDeps p
    let distDeps := st.depsOfVars (distExprVars D)
    let allParents := (parents ++ distDeps).dedup
    let (id, st') := st.addNode .chance allParents τ.base.domainSize
    toMAIDBuild k (st'.addVar x τ [id])
  | @Prog.commit _ x who b acts R k, st =>
    let parents := st.playerDeps who
    let rDeps := st.depsOfVars (exprVars R)
    let allParents := (parents ++ rDeps).dedup
    let (id, st') := st.addNode (.decision who) allParents b.domainSize
    toMAIDBuild k (st'.addVar x (.hidden who b) [id])
  | @Prog.reveal _ y _who x b _hx k, st =>
    let deps := st.lookupDeps x
    toMAIDBuild k (st.addVar y (.pub b) deps)

def toMAIDNodes (p : Prog Γ) : List MAID.Node :=
  (toMAIDBuild p .empty).nodes

/-! ### Example: matching pennies MAID -/

-- Expected output:
--   Node 0: decision(P0), parents=[]
--   Node 1: decision(P1), parents=[]
--   Node 2: utility(P0), parents=[0, 1]
--   Node 3: utility(P1), parents=[0, 1]
#eval! (toMAIDNodes Examples.matchingPennies).map
  (fun n => (n.id, n.kind, n.parents))

/-! ### Example: conditioned game MAID -/

-- Expected (restriction now uses syntactic exprVars for dependency tracking):
--   Node 0: decision(P0), parents=[]
--   Node 1: decision(P1), parents=[0]   ← P1's R references va'
--   Node 2: utility(P0), parents=[]
--   Node 3: utility(P1), parents=[]
#eval! (toMAIDNodes Examples.conditionedGame).map
  (fun n => (n.id, n.kind, n.parents))
