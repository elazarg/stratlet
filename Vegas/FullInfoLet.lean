/-
FullInfoLet: a first strategic-let calculus whose probabilistic specialization is "fix a strategy profile".

Core idea:
- A strategic program has `letChoose p A k`, where `p : Player` controls the choice and `A` describes
  the available actions (possibly depending on the current environment).
- A strategy profile `σ` turns each strategic choice into a *kernel* (finite-support weighted choice)
  `L.Env Γ → WDist (L.Val τ)`.
- Replacing every `letChoose` by `letSample` using that kernel yields a probabilistic program.
- The semantics commutes with this translation (proved by structural recursion).

This is intentionally minimal: no `if-then-else`, no lambdas, and distributions are *only* those induced by strategies.
-/
import Mathlib.Data.List.Basic

import Vegas.WDist
import Vegas.ProgCore
import Vegas.Env
import Vegas.ProbLet
import Vegas.GameDefs

namespace FullInfoLet

open GameDefs

/-! ## Strategic let-calculus (choices owned by players) -/

variable {L : Language}

/--
An action set for type `τ` in context `Γ`:
a (possibly environment-dependent) finite list of legal actions (values).
-/
abbrev Act (Γ : L.Ctx) (τ : L.Ty) := L.Env Γ → List (L.Val τ)

inductive CmdBindS : ProgCore.CmdB (L := L) where
  | choose {Γ τ} (p : Player) (A : Act Γ τ) : CmdBindS Γ τ

abbrev CmdStmtS := ProgCore.CmdStmtObs (L := L)

/--
Strategic programs:
- `letChoose p A k` binds a value chosen by player `p` from action set `A`.
-/
abbrev SProg := ProgCore.Prog (L := L) CmdBindS CmdStmtS

namespace SProg

def ret {Γ τ} (e : L.Expr Γ τ) : SProg Γ τ := ProgCore.Prog.ret e

def letDet {Γ τ τ'} (e : L.Expr Γ τ') (k : SProg (τ' :: Γ) τ) : SProg Γ τ :=
  ProgCore.Prog.letDet e k

def letChoose {Γ τ τ'} (p : Player) (A : Act Γ τ') (k : SProg (L := L) (τ' :: Γ) τ) : SProg Γ τ :=
  .doBind (.choose p A) k

def observe {Γ τ} (cond : L.Expr Γ L.bool) (k : SProg Γ τ) : SProg Γ τ :=
  .doStmt (.observe cond) k

end SProg

def EffWDist : ProgCore.Eff WDist := ProbLet.EffWDist

/--
A strategy profile gives, for each player and action set, a kernel (distribution) over actions.
We do not enforce "supported on A L.Env" here; that can be an external well-formedness predicate.
-/
structure Profile where
  choose : {τ : L.Ty} → Player → Act Γ τ → ProbLet.Kernel Γ τ

def StratSem (σ : Profile (L := L)) : ProgCore.LangSem (L := L) CmdBindS CmdStmtS WDist where
  E := EffWDist
  handleBind
    | .choose p A => σ.choose p A
  handleStmt
    | .observe cond, env =>
        if L.toBool (L.eval cond env) then .pure () else .zero

@[simp] theorem StratSem_handleBind_choose (σ : Profile) (p : Player)
      (A : Act Γ τ) (env : L.Env Γ) :
    (StratSem σ).handleBind (CmdBindS.choose p A) env = σ.choose p A env := rfl

@[simp] theorem StratSem_handleStmt_observe (σ : Profile) (cond : L.Expr Γ L.bool) (env : L.Env Γ) :
    (StratSem σ).handleStmt (ProgCore.CmdStmtObs.observe (Γ := Γ) cond) env =
      (if L.toBool (L.eval cond env) then WDist.pure () else WDist.zero) := rfl

/--
Translate a strategic program to a probabilistic program by fixing a profile:
each `letChoose` becomes `letSample` with the kernel provided by `σ`.
-/
def toProb (σ : Profile (L := L)) : SProg (L := L) Γ τ → ProbLet.PProg (L := L) Γ τ
  | .ret e      => .ret e
  | .letDet e k => .letDet e (toProb σ k)
  | .doStmt s k => .doStmt s (toProb σ k)
  | .doBind c k =>
      match c with
      | CmdBindS.choose p A =>
          .doBind (.sample (σ.choose p A)) (toProb σ k)

/--
Direct strategic semantics parameterized by a profile.
(Defined directly; theorem below shows it coincides with evalP ∘ toProb.)
-/
def evalS {Γ τ} (σ : Profile (L := L)) : SProg Γ τ → L.Env Γ → WDist (L.Val τ) :=
   ProgCore.evalWith (StratSem σ)

/--
Key commuting theorem: evaluating a strategic program under a fixed profile equals
evaluating its probabilistic specialization (by `toProb`) under the probabilistic interpreter.
-/
theorem evalS_eq_evalP_toProb {Γ τ} (σ : Profile) (p : SProg Γ τ) (env : L.Env Γ) :
    evalS σ p env = ProbLet.evalP (toProb σ p) env := by
  simp only [evalS, StratSem, EffWDist, ProbLet.evalP, ProbLet.ProbSem]
  induction p with
  | ret e => simp [toProb]
  | letDet e k ih => simp [toProb, ih]
  | doStmt s k ih =>
      simp_all only [ProgCore.evalWith_doStmt]
      rfl
  | doBind c k ih =>
      cases c with
      | choose p A => simp [toProb, ih]

/-!
Behavioral interpreter:

`Beh τ` is a residual tree that can be:
- `ret v`          : finished with value
- `fail`           : rejected by `observe`
- `choose ...`     : a strategic decision point, exposing player + legal actions,
                     plus a thunk `dist : Profile → WDist (L.Val τ')` that produces
                     the node’s mixed action choice once a profile is supplied.
-/

/-- A profile-free behavior tree for closed evaluation from a concrete L.Env. -/
inductive Beh : L.Ty → Type where
  | ret  {τ} (v : L.Val τ) : Beh τ
  | fail {τ} : Beh τ
  | choose {τ τ'} (p : Player)
      (actions : List (L.Val τ'))                  -- exposed to the user
      (dist    : Profile (L := L) → WDist (L.Val τ'))       -- produced later by supplying σ
      (k       : L.Val τ' → Beh τ)                 -- continuation
      : Beh τ

/--
Behavioral interpreter: reduces deterministic computation immediately (using `L.Env`),
and produces a `Beh τ` without requiring a profile.
-/
def behEval {Γ τ} : SProg Γ τ → L.Env Γ → Beh τ
  | .ret e, env =>
      Beh.ret (L.eval e env)
  | .letDet e k, env =>
      let v := L.eval e env
      behEval k (v, env)
  | .observe cond k, env =>
      if L.toBool (L.eval cond env) then
        behEval k env
      else
        Beh.fail
  | .letChoose (τ' := τ') p A k, env =>
      let acts : List (L.Val τ') := A env
      let distThunk : Profile → WDist (L.Val τ') :=
        fun σ => (σ.choose p A) env
      Beh.choose p acts distThunk (fun v => behEval k (v, env))

/--
Run a behavior tree under a supplied profile, yielding the same `WDist` semantics as before.
-/
def runBeh {τ} (σ : Profile (L := L)) : Beh τ → WDist (L.Val τ)
  | Beh.ret v          => WDist.pure v
  | Beh.fail           => .zero
  | Beh.choose _ _ d k => WDist.bind (d σ) (fun v => runBeh σ (k v))

/--
Key theorem: behavioral evaluation + running under σ coincides with the direct strategic semantics.
-/
theorem runBeh_behEval_eq_evalS {Γ τ} (σ : Profile) (p : SProg Γ τ) (env : L.Env Γ) :
    runBeh σ (behEval p env) = evalS σ p env := by
  induction p with
  | ret e => rfl
  | letDet e k ih => apply ih
  | doStmt s k ih =>
      cases s with
      | observe cond =>
          simp only [evalS, behEval]
          by_cases h : L.toBool (L.eval cond env)
          · simp [h, ih, StratSem, EffWDist, ProbLet.EffWDist]
            rfl
          · simp [runBeh, h]
            simp [Bool.not_eq_true] at h
            rfl
  | doBind c k ih =>
      cases c with
      | choose p A =>
          simp only [behEval, runBeh, evalS, ProgCore.evalWith_doBind, StratSem_handleBind_choose]
          simp_all only
          rfl


/--
Corollary: behavioral evaluation + running also coincides with probabilistic specialization.
-/
theorem runBeh_behEval_eq_evalP_toProb (σ : Profile) (p : SProg Γ τ) (env : L.Env Γ) :
    runBeh σ (behEval p env) = ProbLet.evalP (toProb σ p) env := by
  simpa [runBeh_behEval_eq_evalS] using (evalS_eq_evalP_toProb σ p env)

/-!
## 7) Toy runtime (operational semantics)

We interpret `letChoose` by querying an `Arena` that provides an action for the current player
from the offered finite action list. We *enforce legality*
(chosen action must be in the offered list).

Operational semantics is a big-step evaluator:
  evalOp : Arena → SProg Γ τ → L.Env Γ → Option (L.Val τ)

We then build a deterministic profile induced by an arena:
  Profile.ofArena : Arena → Profile

and prove:
  evalS (Profile.ofArena arena) p L.Env =
    match evalOp arena p L.Env with
    | some v => WDist.pure v
    | none   => .zero
-/

/-- A tiny "arena": given a player and a list of legal actions, optionally pick an action. -/
structure Arena where
  move : {τ : L.Ty} → Player → List (L.Val τ) → Option (L.Val τ)

/--
Operational semantics (big-step): run a strategic program in an arena.

- `ret` returns the evaluated value.
- `letDet` computes and extends the environment.
- `observe` rejects if condition is false.
- `letChoose` asks the arena for a move; rejects if `none` or illegal.
-/
def evalOp {Γ τ} (arena : Arena (L := L)) : SProg Γ τ → L.Env Γ → Option (L.Val τ)
  | .ret e, env =>
      some (L.eval e env)
  | .letDet e k, env =>
      let v := L.eval e env
      evalOp arena k (v, env)
  | .observe cond k, env =>
      if L.toBool (L.eval cond env) then
        evalOp arena k env
      else
        none
  | .letChoose (τ' := τ') p A k, env =>
      let acts : List (L.Val τ') := A env
      match arena.move (τ := τ') p acts with
      | none => none
      | some a =>
          if a ∈ acts then
            evalOp arena k (a, env)
          else
            none

/--
A deterministic profile induced by an arena:
- at each choice node, the kernel is a Dirac at the arena's chosen action
- if the arena refuses or chooses illegally, the kernel is empty
-/
def Profile.ofArena (arena : Arena (L := L)) : Profile (L := L) where
  choose := by
    intro Γ τ p A L.Env
    let acts := A L.Env
    match arena.move (τ := τ) p acts with
    | none => exact .zero
    | some a =>
        if _ : a ∈ acts then
          exact WDist.pure a
        else
          exact .zero

/--
Main bridge theorem:
Operational evaluation in an arena matches denotational evaluation
under the induced deterministic profile.
-/
theorem evalS_ofArena_eq_evalOp {Γ τ}
    (arena : Arena) (p : SProg Γ τ) (env : L.Env Γ) :
    evalS (Profile.ofArena arena) p env
      =
    match evalOp arena p env with
    | some v => WDist.pure v
    | none   => .zero := by
  -- unfold evalS once so simp can see the generic evaluator
  simp only [evalS, StratSem, EffWDist, ProbLet.EffWDist]
  -- we need IH for all L.Env because the evaluator extends L.Env
  induction p with
  | ret e =>
      simp [evalOp, WDist.pure]
  | letDet e k ih =>
      simp [evalOp, ih]
  | doStmt s k ih =>
      cases s with
      | observe cond =>
          by_cases h : L.toBool (L.eval cond env)
          · simp [evalOp, h, ih]
          · simp [evalOp, h]
  | doBind c k ih =>
      cases c with
      | choose p A =>
          -- freeze offered actions
          set acts : List (L.Val _) := A env with hacts
          -- split on arena.move
          cases hm : arena.move (τ := _) p acts with
          | none =>
              -- kernel is zero; op is none
              simp [evalOp, Profile.ofArena, hm, acts]
          | some a =>
              by_cases hmem : a ∈ acts
              · -- legal: kernel is pure a; op continues with (a, L.Env)
                simpa [evalOp, Profile.ofArena, hm, hmem, acts,
                       WDist.pure, WDist.bind] using ih (a, env)
              · -- illegal: kernel is zero; op is none
                simp [evalOp, Profile.ofArena, hm, hmem, acts]

end FullInfoLet
