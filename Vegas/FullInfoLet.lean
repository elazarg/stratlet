/-
FullInfoLet: a first strategic-let calculus whose probabilistic specialization is “fix a strategy profile”.

Core idea:
- A strategic program has `letChoose p A k`, where `p : Player` controls the choice and `A` describes
  the available actions (possibly depending on the current environment).
- A strategy profile `σ` turns each strategic choice into a *kernel* (finite-support weighted choice)
  `Env Γ → WDist (Val τ)`.
- Replacing every `letChoose` by `letSample` using that kernel yields a probabilistic program.
- The semantics commutes with this translation (proved by structural recursion).

This is intentionally minimal: no `if-then-else`, no lambdas, and distributions are *only* those induced by strategies.
-/

import Mathlib.Data.Rat.Init
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic

import Vegas.Deterministic

namespace FullInfoLet

/-! ## 3) Weighted finite-support semantics -/

abbrev W := Rat
abbrev WDist (α : Type) := List (α × W)

namespace WDist

def pure {α} (a : α) : WDist α := [(a, (1 : W))]

def map {α β} (f : α → β) (xs : WDist α) : WDist β :=
  List.map (fun aw => (f aw.1, aw.2)) xs

def scale {α} (c : W) (xs : WDist α) : WDist α :=
  List.map (fun aw => (aw.1, c * aw.2)) xs

def bind {α β} (xs : WDist α) (f : α → WDist β) : WDist β :=
  match xs with
  | [] => []
  | (a, w) :: xs' =>
      scale w (f a) ++ bind xs' f

def mass {α} (xs : WDist α) : W :=
  xs.foldl (fun acc aw => acc + aw.2) 0

def normalize {α} (xs : WDist α) : Option (WDist α) :=
  let m := mass xs
  if m = 0 then none else some (scale (1 / m) xs)

end WDist

/-- A (finite-support) stochastic kernel from environments. -/
abbrev Kernel (Γ : Ctx) (τ : Ty) := Env Γ → WDist (Val τ)

/-! ## 4) Probabilistic let-calculus driven by kernels -/

/--
Probabilistic programs:
- `letSample K k` samples from kernel `K : Env Γ → WDist (Val τ')`.
This is intentionally the minimal general form needed to express strategy-induced randomness.
-/
inductive PProg : Ctx → Ty → Type where
  | ret {Γ τ} (e : Expr Γ τ) : PProg Γ τ
  | letDet {Γ τ τ'} (e : Expr Γ τ') (k : PProg (τ' :: Γ) τ) : PProg Γ τ
  | letSample {Γ τ τ'} (K : Kernel Γ τ') (k : PProg (τ' :: Γ) τ) : PProg Γ τ
  | observe {Γ τ} (cond : Expr Γ .bool) (k : PProg Γ τ) : PProg Γ τ

def evalP {Γ τ} : PProg Γ τ → Env Γ → WDist (Val τ)
  | .ret e, env =>
      WDist.pure (evalExpr e env)
  | .letDet e k, env =>
      let v := evalExpr e env
      evalP k (v, env)
  | .letSample K k, env =>
      WDist.bind (K env) (fun v => evalP k (v, env))
  | .observe cond k, env =>
      if evalExpr cond env then evalP k env else []

/-! ## 5) Strategic let-calculus (choices owned by players) -/

abbrev Player := Nat

/--
An action set for type `τ` in context `Γ`:
a (possibly environment-dependent) finite list of legal actions (values).
-/
abbrev Act (Γ : Ctx) (τ : Ty) := Env Γ → List (Val τ)

/--
Strategic programs:
- `letChoose p A k` binds a value chosen by player `p` from action set `A`.
-/
inductive SProg : Ctx → Ty → Type where
  | ret {Γ τ} (e : Expr Γ τ) : SProg Γ τ
  | letDet {Γ τ τ'} (e : Expr Γ τ') (k : SProg (τ' :: Γ) τ) : SProg Γ τ
  | letChoose {Γ τ τ'} (p : Player) (A : Act Γ τ') (k : SProg (τ' :: Γ) τ) : SProg Γ τ
  | observe {Γ τ} (cond : Expr Γ .bool) (k : SProg Γ τ) : SProg Γ τ

/--
A strategy profile gives, for each player and action set, a kernel (distribution) over actions.
We do not enforce “supported on A env” here; that can be an external well-formedness predicate.
-/
structure Profile where
  choose : {Γ : Ctx} → {τ : Ty} → Player → Act Γ τ → Kernel Γ τ

/--
Translate a strategic program to a probabilistic program by fixing a profile:
each `letChoose` becomes `letSample` with the kernel provided by `σ`.
-/
def toProb {Γ τ} (σ : Profile) : SProg Γ τ → PProg Γ τ
  | .ret e        => .ret e
  | .letDet e k   => .letDet e (toProb σ k)
  | .letChoose p A k =>
      .letSample (σ.choose p A) (toProb σ k)
  | .observe c k  => .observe c (toProb σ k)

/--
Direct strategic semantics parameterized by a profile.
(Defined directly; theorem below shows it coincides with evalP ∘ toProb.)
-/
def evalS {Γ τ} (σ : Profile) : SProg Γ τ → Env Γ → WDist (Val τ)
  | .ret e, env =>
      WDist.pure (evalExpr e env)
  | .letDet e k, env =>
      let v := evalExpr e env
      evalS σ k (v, env)
  | .letChoose p A k, env =>
      WDist.bind ((σ.choose p A) env) (fun v => evalS σ k (v, env))
  | .observe cond k, env =>
      if evalExpr cond env then evalS σ k env else []

/--
Key commuting theorem: evaluating a strategic program under a fixed profile equals
evaluating its probabilistic specialization (by `toProb`) under the probabilistic interpreter.
-/
theorem evalS_eq_evalP_toProb {Γ τ} (σ : Profile) (p : SProg Γ τ) (env : Env Γ) :
    evalS σ p env = evalP (toProb σ p) env := by
  induction p with
  | ret e =>
      simp [evalS, evalP, toProb]
  | letDet e k ih =>
      simp [evalS, evalP, toProb, ih]
  | letChoose p A k ih =>
      simp [evalS, evalP, toProb, ih]
  | observe c k ih =>
      simp [evalS, evalP, toProb, ih]

/-! ## 6) Tiny example -/

namespace Examples1

def Γ0 : Ctx := []

/-- A simple profile: player picks uniformly among available actions. -/
def uniformProfile : Profile where
  choose := by
    intro Γ τ p A env
    let xs := A env
    match xs.length with
    | 0 =>
        exact []
    | n =>
        let w : W := (1 : W) / (n : W)
        exact xs.map (fun a => (a, w))

/-- Action set: choose an Int in [2,4]. -/
def A24 : Act Γ0 .int := fun _ => [2, 3, 4]

/-- choose n ∈ {2,3,4}; return (n == 3). -/
def sEx : SProg Γ0 .bool :=
  SProg.letChoose 0 A24
    (SProg.ret (Expr.eqInt (Expr.var Var.vz) (Expr.constInt 3)))

#eval evalS uniformProfile sEx ()
#eval evalP (toProb uniformProfile sEx) ()

-- Both print: [(false, 1/3), (true, 1/3), (false, 1/3)]
-- (multiset semantics; use a separate combine if you want aggregation)

end Examples1

end FullInfoLet


namespace FullInfoLet

/-!
Behavioral interpreter:

`Beh τ` is a residual tree that can be:
- `ret v`          : finished with value
- `fail`           : rejected by `observe`
- `choose ...`     : a strategic decision point, exposing player + legal actions,
                     plus a thunk `dist : Profile → WDist (Val τ')` that produces
                     the node’s mixed action choice once a profile is supplied.
-/

/-- A profile-free behavior tree for closed evaluation from a concrete env. -/
inductive Beh : Ty → Type where
  | ret  {τ} (v : Val τ) : Beh τ
  | fail {τ} : Beh τ
  | choose {τ τ'} (p : Player)
      (actions : List (Val τ'))                  -- exposed to the user
      (dist    : Profile → WDist (Val τ'))       -- produced later by supplying σ
      (k       : Val τ' → Beh τ)                 -- continuation
      : Beh τ

/--
Behavioral interpreter: reduces deterministic computation immediately (using `env`),
and produces a `Beh τ` without requiring a profile.
-/
def behEval {Γ τ} : SProg Γ τ → Env Γ → Beh τ
  | .ret e, env =>
      Beh.ret (evalExpr e env)
  | .letDet e k, env =>
      let v := evalExpr e env
      behEval k (v, env)
  | .observe cond k, env =>
      if evalExpr cond env then
        behEval k env
      else
        Beh.fail
  | .letChoose (Γ := Γ) (τ := τ) (τ' := τ') p A k, env =>
      let acts : List (Val τ') := A env
      let distThunk : Profile → WDist (Val τ') :=
        fun σ => (σ.choose p A) env
      Beh.choose p acts distThunk (fun v => behEval k (v, env))

/--
Run a behavior tree under a supplied profile, yielding the same `WDist` semantics as before.
-/
def runBeh {τ} (σ : Profile) : Beh τ → WDist (Val τ)
  | Beh.ret v          => WDist.pure v
  | Beh.fail           => []
  | Beh.choose _ _ d k => WDist.bind (d σ) (fun v => runBeh σ (k v))

/--
Key theorem: behavioral evaluation + running under σ coincides with the direct strategic semantics.
-/
theorem runBeh_behEval_eq_evalS {Γ τ} (σ : Profile) (p : SProg Γ τ) (env : Env Γ) :
    runBeh σ (behEval p env) = evalS σ p env := by
  induction p with
  | ret e =>
      simp [behEval, runBeh, evalS]
  | letDet e k ih =>
      simp [behEval, evalS, ih]
  | observe c k ih =>
      by_cases h : evalExpr c env
      · simp [behEval, evalS, h, ih]
      · simp [behEval, runBeh, evalS, h]
  | letChoose p A k ih =>
      simp [behEval, runBeh, evalS, ih]

/--
Corollary: behavioral evaluation + running also coincides with probabilistic specialization.
-/
theorem runBeh_behEval_eq_evalP_toProb (σ : Profile) (p : SProg Γ τ) (env : Env Γ) :
    runBeh σ (behEval p env) = evalP (toProb σ p) env := by
  -- reuse your previous commutation theorem
  simpa [runBeh_behEval_eq_evalS] using (evalS_eq_evalP_toProb σ p env)

end FullInfoLet

namespace FullInfoLet

/-!
## 7) Toy runtime (operational semantics)

We interpret `letChoose` by querying an `Arena` that provides an action for the current player
from the offered finite action list. We *enforce legality*
(chosen action must be in the offered list).

Operational semantics is a big-step evaluator:
  evalOp : Arena → SProg Γ τ → Env Γ → Option (Val τ)

We then build a deterministic profile induced by an arena:
  Profile.ofArena : Arena → Profile

and prove:
  evalS (Profile.ofArena arena) p env =
    match evalOp arena p env with
    | some v => [(v, 1)]
    | none   => []
-/

/-- Decidable equality for runtime values (Int/Bool). -/
instance instDecEqVal (τ : Ty) : DecidableEq (Val τ) := by
  cases τ <;> infer_instance

/-- A tiny “arena”: given a player and a list of legal actions, optionally pick an action. -/
structure Arena where
  move : {τ : Ty} → Player → List (Val τ) → Option (Val τ)

/--
Operational semantics (big-step): run a strategic program in an arena.

- `ret` returns the evaluated value.
- `letDet` computes and extends the environment.
- `observe` rejects if condition is false.
- `letChoose` asks the arena for a move; rejects if `none` or illegal.
-/
def evalOp {Γ τ} (arena : Arena) : SProg Γ τ → Env Γ → Option (Val τ)
  | .ret e, env =>
      some (evalExpr e env)
  | .letDet e k, env =>
      let v := evalExpr e env
      evalOp arena k (v, env)
  | .observe cond k, env =>
      if evalExpr cond env then
        evalOp arena k env
      else
        none
  | .letChoose (Γ := Γ) (τ := τ) (τ' := τ') p A k, env =>
      let acts : List (Val τ') := A env
      match arena.move (τ := τ') p acts with
      | none => none
      | some a =>
          if a ∈ acts then
            evalOp arena k (a, env)
          else
            none

namespace WDist

/-- Dirac / point-mass distribution (as a weighted list). -/
def dirac {α} (a : α) : WDist α := [(a, (1 : W))]

end WDist

/--
A deterministic profile induced by an arena:
- at each choice node, the kernel is a Dirac at the arena’s chosen action
- if the arena refuses or chooses illegally, the kernel is empty
-/
def Profile.ofArena (arena : Arena) : Profile where
  choose := by
    intro Γ τ p A env
    let acts := A env
    match arena.move (τ := τ) p acts with
    | none => exact []
    | some a =>
        if h : a ∈ acts then
          exact WDist.dirac a
        else
          exact []

/--
Main bridge theorem:
Operational evaluation in an arena matches denotational evaluation
under the induced deterministic profile.
-/
theorem evalS_ofArena_eq_evalOp {Γ τ}
    (arena : Arena) (p : SProg Γ τ) (env : Env Γ) :
    evalS (Profile.ofArena arena) p env
      =
    match evalOp arena p env with
    | some v => WDist.dirac v
    | none   => [] := by
  induction p with
  | ret e =>
      simp [evalS, evalOp, WDist.dirac, WDist.pure]
  | letDet e k ih =>
      simp [evalS, evalOp, ih]
  | observe c k ih =>
      by_cases h : evalExpr c env
      · simp [evalS, evalOp, h, ih]
      · simp [evalS, evalOp, h]
  | letChoose p A k ih =>
      -- freeze the offered action list in the current environment
      set acts : List (Val _) := A env with hacts
      -- split on what the arena does
      cases hm : arena.move p acts with
      | none =>
          -- profile kernel = []; operational returns none; both sides []
          simp [evalS, evalOp, Profile.ofArena, WDist.dirac, WDist.bind, hm, acts]
      | some a =>
          by_cases hmem : a ∈ acts
          · -- legal move: denotation is bind (dirac a) (…); operational continues with (a,env)
            -- after simp, goal becomes exactly the IH at (a, env)
            simpa [evalS, evalOp, Profile.ofArena, WDist.dirac, WDist.bind, WDist.scale,
                   hm, hmem, acts] using ih (env := (a, env))
          · -- illegal move: profile kernel = []; operational rejects; both sides []
            simp [evalS, evalOp, Profile.ofArena, WDist.dirac, WDist.bind,
                  hm, hmem, acts]


/-!
## 8) Tiny runnable example
-/

namespace Examples2

def Γ0 : Ctx := []

/-- Action set: choose an Int in [2,4]. -/
def A24 : Act Γ0 .int := fun _ => [2, 3, 4]

/-- choose n ∈ {2,3,4}; return (n == 3). -/
def sEx : SProg Γ0 .bool :=
  SProg.letChoose 0 A24
    (SProg.ret (Expr.eqInt (Expr.var Var.vz) (Expr.constInt 3)))

/-- Arena that always picks the first offered action (if any). -/
def firstArena : Arena where
  move := by
    intro τ p acts
    match acts with
    | [] => exact none
    | a :: _ => exact some a

#eval evalOp firstArena sEx ()     -- should be: some false
#eval evalS (Profile.ofArena firstArena) sEx ()  -- should be: [(false, 1)]

end Examples2

end FullInfoLet
