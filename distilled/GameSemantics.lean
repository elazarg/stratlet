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
    Commit sites become decision nodes; reveal/letExpr/assert/observe
    are transparent. -/
def toRGameTree : Prog Γ → Env Γ → RGameTree
  | .ret u, env => .terminal (fun who => evalPayoffMap u env who)
  | .letExpr x e k, env =>
    toRGameTree k (Env.cons (x := x) (evalExpr e env) env)
  | .commit x who A k, env =>
    .decision x who ((A (env.toView who)).map
      (fun a => toRGameTree k (Env.cons (x := x) a env)))
  | .reveal y _who _x (b := b) hx k, env =>
    let v : Val b := env.get hx
    toRGameTree k (Env.cons (x := y) v env)
  | .assert _who c k, env =>
    if evalExpr c env then toRGameTree k env
    else .terminal (fun _ => 0)
  | .observe c k, env =>
    if evalExpr c env then toRGameTree k env
    else .terminal (fun _ => 0)

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

/-! Extract variable IDs referenced by an expression. -/
def exprVars : Expr Γ b → List VarId
  | .var x _     => [x]
  | .constInt _  => []
  | .constBool _ => []
  | .addInt l r  => exprVars l ++ exprVars r
  | .eqInt l r   => exprVars l ++ exprVars r
  | .eqBool l r  => exprVars l ++ exprVars r
  | .andBool l r => exprVars l ++ exprVars r
  | .notBool e   => exprVars e
  | .ite c t f   => exprVars c ++ exprVars t ++ exprVars f

def payoffVars (u : PayoffMap Γ) : List VarId :=
  (u.entries.map (fun (_, e) => exprVars e)).flatten

/-- Internal state for MAID compilation.

    **Variables**: For each Vegas variable, tracks its binding type and
    the set of MAID node IDs it transitively depends on. Transparent
    operations (`letExpr`, `reveal`, `assert`, `observe`) propagate
    dependencies without creating MAID nodes. -/
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

/-- MAID parents: all nodes reachable through variables visible to `who`. -/
def playerDeps (st : MAIDBuilder) (who : Player) : List Nat :=
  ((st.vars.filter (fun (_, τ, _) => canSee who τ)).map
    (fun (_, _, ds) => ds)).flatten.dedup

/-- Emit a MAID node. -/
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

/-- Domain cardinality for a base type.
    `bool` has 2 values; `int` is unbounded (0 = unbounded). -/
def BaseTy.domainSize : BaseTy → Nat
  | .bool => 2
  | .int => 0  -- unbounded; honest about int's infinite domain

/-- Compile a Vegas program to MAID nodes.

    **Node mapping:**
    - `commit` → decision node (domainSize from `BaseTy`)
    - `ret` → one utility node per player (domainSize = 1)
    - `letExpr`/`reveal`/`assert`/`observe` → transparent (propagate
      dependencies only, no MAID nodes emitted)

    **Domain sizes**: Decision nodes get `BaseTy.domainSize` (bool=2,
    int=0 for unbounded). Utility nodes get domainSize=1.

    **EU equivalence only.** Combined with `MAIDModel.evalDist`, this gives
    expected-utility equivalence with Vegas (under a value encoding), NOT
    distributional equivalence. See `MAIDModel.evalDist` doc.

    **Proof obligations** (not yet discharged):
    1. *Dependency over-approximation*: Parent sets are a superset of true
       semantic dependencies. Formally: for any two assignments that agree
       on `node.parents`, the node's distribution (under a well-formed
       `MAIDModel`, see `MAID.LocalTo`) is identical.
    2. *Value encoding*: A pair `encodeVal : Val b → Nat` /
       `decodeVal : Nat → Option (Val b)` with round-trip, plus a proof
       that `CondPolicy` under this encoding corresponds to Vegas `Profile`. -/
def toMAIDBuild : Prog Γ → MAIDBuilder → MAIDBuilder
  | .ret u, st =>
    let deps := st.depsOfVars (payoffVars u)
    let players := (u.entries.map Prod.fst).dedup
    players.foldl (fun s who =>
      (s.addNode (.utility who) deps 1).2) st
  | @Prog.letExpr _ x b e k, st =>
    let deps := st.depsOfVars (exprVars e)
    toMAIDBuild k (st.addVar x (.pub b) deps)
  | @Prog.commit _ x who b _A k, st =>
    let parents := st.playerDeps who
    let (id, st') := st.addNode (.decision who) parents b.domainSize
    toMAIDBuild k (st'.addVar x (.hidden who b) [id])
  | @Prog.reveal _ y _who x b _hx k, st =>
    let deps := st.lookupDeps x
    toMAIDBuild k (st.addVar y (.pub b) deps)
  | .assert _who _c k, st => toMAIDBuild k st
  | .observe _c k, st => toMAIDBuild k st

/-- Extract MAID nodes from a Vegas program. -/
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

/-! ### Example: conditioned game (observe is transparent in MAID) -/

/-- P0 commits, reveal P0's choice, observe guards on it being true,
    then P1 commits. The observe is transparent in the MAID — conditioning
    is handled by the Vegas denotational semantics, not the MAID structure. -/
def Examples.conditionedGame : Prog Examples.Γ0 :=
  .commit Examples.va 0 (Examples.boolActs 0)  -- ctx: [(va, hidden 0 bool)]
    (.reveal Examples.va' 0 Examples.va .here   -- ctx: [(va', pub bool), (va, hidden 0 bool)]
      (.observe (.var Examples.va' .here)        -- transparent in MAID
        (.commit Examples.vb 1 (Examples.boolActs 1) -- ctx grows
          (.ret ⟨[(0, .constInt 1), (1, .constInt 0)]⟩))))

-- Expected (observe is transparent, no guard node):
--   Node 0: decision(P0), parents=[]
--   Node 1: decision(P1), parents=[0]   ← P1 sees va' (pub) which depends on P0
--   Node 2: utility(P0), parents=[]     ← constant payoff, no dependencies
--   Node 3: utility(P1), parents=[]
#eval! (toMAIDNodes Examples.conditionedGame).map
  (fun n => (n.id, n.kind, n.parents))
