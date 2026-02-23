import distilled.Vegas
import GameTheory.EFG

/-!
# EFG Compilation for Vegas Programs

Compiles Vegas programs to game trees. Uses a computable Rat-weighted
game tree (`RGameTree`) for actual computation, with a noncomputable
bridge to `EFG.GameTree` for correctness statements.
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

namespace RGameTree

/-- Computable expected utility on `RGameTree`. -/
def eu (who : Player) : RGameTree → Rat
  | .terminal payoff => ↑(payoff who)
  | .chance branches => go_chance branches
  | .decision _pid _player actions => go_decision actions
where
  go_chance : List (RGameTree × Rat) → Rat
    | [] => 0
    | (t, w) :: rest => w * t.eu who + go_chance rest
  go_decision : List RGameTree → Rat
    | [] => 0
    | t :: _rest => t.eu who  -- picks first action (default)

end RGameTree

-- ============================================================================
-- § 2. Compilation from Vegas to RGameTree
-- ============================================================================

/-- Compile a Vegas program to a computable game tree.
    Commit sites become decision nodes; sample sites become
    chance nodes; reveal/letExpr/assert/observe are transparent. -/
def toRGameTree : Prog Γ → Env Γ → RGameTree
  | .ret u, env => .terminal (fun who => evalPayoffMap u env who)
  | .letExpr x e k, env =>
    toRGameTree k (Env.cons (x := x) (evalExpr e env) env)
  | .sample x τ m K k, env =>
    .chance ((K (env.projectSample τ m)).weights.map
      (fun (v, w) =>
        (toRGameTree k (Env.cons (x := x) v env), w)))
  | .commit x who A k, env =>
    .decision x who ((A (env.toView who)).map
      (fun a => toRGameTree k (Env.cons (x := x) a env)))
  | .reveal y _who _x (b := b) hx k, env =>
    let v : Val b := env.get hx
    toRGameTree k (Env.cons (x := y) v env)
  | .assert p P k, env =>
    if P (env.toView p) then toRGameTree k env
    else .terminal (fun _ => 0)
  | .observe c k, env =>
    if evalExpr c env then toRGameTree k env
    else .terminal (fun _ => 0)

-- ============================================================================
-- § 3. Bridge to classic EFG (noncomputable)
-- ============================================================================

/-- Convert `RGameTree` to `EFG.GameTree Player`.
    Casts `Rat → NNReal` for weights and `Int → ℝ` for payoffs.
    Noncomputable due to `NNReal` and `ℝ`. -/
noncomputable def RGameTree.toEFG : RGameTree → EFG.GameTree Player
  | .terminal payoff =>
    .terminal (fun p => (payoff p : ℝ))
  | .chance branches =>
    .chance (go_chance branches)
  | .decision pid player actions =>
    .decision pid player (go_decision actions)
where
  go_chance : List (RGameTree × Rat) → List (EFG.GameTree Player × NNReal)
    | [] => []
    | (t, w) :: rest =>
      (t.toEFG, ⟨max (↑w) 0, le_max_right _ _⟩) :: go_chance rest
  go_decision : List RGameTree → List (EFG.GameTree Player)
    | [] => []
    | t :: rest => t.toEFG :: go_decision rest

-- ============================================================================
-- § 4. Deviation and Nash equilibrium
-- ============================================================================

structure Deviator (who : Player) where
  commit : {Γ : Ctx} → {b : BaseTy} → VarId →
    ActSet who Γ b → CommitKernel who Γ b

def Profile.deviate (σ : Profile) {who : Player} (δ : Deviator who) : Profile where
  commit := fun {_Γ} {_b} p x A =>
    if h : p = who then
      h ▸ δ.commit x (h ▸ A)
    else
      σ.commit p x A

-- ============================================================================
-- § 10. Expected utility
-- ============================================================================

def EU (p : Prog Γ) (σ : Profile) (env : Env Γ) (who : Player) : Rat :=
  let d := outcomeDist σ p env
  d.weights.foldl (fun acc (f, w) => acc + w * ↑(f who)) 0

-- Expected utility computations
def mpEU_p0 : Rat :=
  EU Examples.matchingPennies Examples.mpProfile Env.empty 0
def mpEU_p1 : Rat :=
  EU Examples.matchingPennies Examples.mpProfile Env.empty 1

def IsNash (p : Prog Γ) (σ : Profile) (env : Env Γ) : Prop :=
  ∀ (who : Player) (δ : Deviator who),
    EU p σ env who ≥ EU p (σ.deviate δ) env who
