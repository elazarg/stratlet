import Mathlib.Data.List.Basic

import Vegas.LetProb.WDist
import Vegas.LetCore.Prog
import Vegas.LetCore.Env
import Vegas.LetProb.Prob
import Vegas.Defs

namespace Dag

open Prog Defs

variable {L : Language}
variable {W : Type} [WeightModel W]

/-!
# DagLet: A DAG-style let-calculus with explicit information projections

Goal: model partial information by making every strategic choice depend only on an
explicitly declared *view* (a projection of the environment).
This avoids baking in any particular operational mechanism (e.g. commit/reveal);
those can be compiled later.

Key idea:
- A `View Γ` is a sub-context `Δ` together with a projection `Env Γ → Env Δ`.
- A player's choice at type `τ` is specified relative to a view `v : View Γ`:
  the strategy kernel is a function of `Env v.Δ`.
-/

/-! ## Views and action sets -/

/-- A view of an environment `Γ` is a smaller context `Δ` plus a projection `Γ → Δ`. -/
structure View (Γ : L.Ctx) where
  Δ : L.Ctx
  proj : L.Env Γ → L.Env Δ

/-- An action set for type `τ` under a view `v`:
a finite list of legal actions (values), possibly dependent on the viewed environment. -/
abbrev Act {Γ : L.Ctx} (v : View (L := L) Γ) (τ : L.Ty) : Type :=
  L.Env v.Δ → List (L.Val τ)

/-! ## Strategic commands / programs -/

/-- Bind commands for DagLet: the only strategic bind is `choose`. -/
inductive CmdBindD (W : Type) [WeightModel W] : Prog.CmdB (L := L) where
  | choose {Γ : L.Ctx} {τ : L.Ty} (who : Player) (v : View (L := L) Γ) (A : Act (L := L) v τ) :
      CmdBindD W Γ τ

/-- Statements: we reuse probabilistic observe (boolean guard). -/
abbrev CmdStmtD := Prog.CmdStmtObs (L := L)

/-- DagLet programs. -/
abbrev DagProg : L.Ctx → L.Ty → Type :=
  Prog.Prog (L := L) (CmdBindD W) CmdStmtD

namespace DagProg

def ret {Γ τ} (e : L.Expr Γ τ) : DagProg (L := L) (W := W) Γ τ :=
  Prog.Prog.ret e

def letDet {Γ τ τ'} (e : L.Expr Γ τ') (k : DagProg (L := L) (W := W) (τ' :: Γ) τ) :
    DagProg (L := L) (W := W) Γ τ :=
  Prog.Prog.letDet e k

/-- Strategic let: bind a value chosen by player `who`, conditioned only on `v`. -/
def letChoose {Γ τ τ'} (who : Player) (v : View (L := L) Γ) (A : Act (L := L) v τ')
    (k : DagProg (L := L) (W := W) (τ' :: Γ) τ) : DagProg (L := L) (W := W) Γ τ :=
  .doBind (.choose who v A) k

def observe {Γ τ} (cond : L.Expr Γ L.bool) (k : DagProg (L := L) (W := W) Γ τ) :
    DagProg (L := L) (W := W) Γ τ :=
  .doStmt (.observe cond) k

end DagProg

/-! ## Semantics via profiles (strategy kernels) -/

/-- We evaluate DagLet programs into `WDist W` using the same effect as Prob. -/
abbrev EffWDist : Prog.Eff (WDist W) := Prob.EffWDist

/-- A strategy profile: for each player and view/action-set, provides a kernel on the viewed env. -/
structure Profile where
  choose :
    {Γ : L.Ctx} → {τ : L.Ty} →
      Player → (v : View (L := L) Γ) → Act (L := L) v τ → (L.Env v.Δ → WDist W (L.Val τ))

/-- Helper: lift a view-kernel to a kernel on the full environment by precomposing with `v.proj`. -/
def liftKernel {Γ : L.Ctx} {τ : L.Ty}
    (σ : Profile (L := L) (W := W)) (who : Player) (v : View (L := L) Γ) (A : Act (L := L) v τ) :
    (L.Env Γ → WDist W (L.Val τ)) :=
  fun env => σ.choose who v A (v.proj env)

/-- The language semantics for DagLet given a profile. -/
def StratSem (σ : Profile (L := L) (W := W)) :
    Prog.LangSem (L := L) (CmdBindD W) CmdStmtD (WDist W) where
  E := EffWDist
  handleBind
    | .choose who v A => liftKernel (L := L) σ who v A
  handleStmt
    | .observe cond, env =>
        if L.toBool (L.eval cond env) then .pure () else .zero

@[simp] theorem StratSem_handleBind_choose
    {Γ : L.Ctx} {τ : L.Ty} (σ : Profile (L := L) (W := W))
    (who : Player) (v : View (L := L) Γ) (A : Act (L := L) v τ) (env : L.Env Γ) :
    (StratSem σ).handleBind (CmdBindD.choose who v A) env
      =
    σ.choose who v A (v.proj env) := rfl

@[simp] theorem StratSem_handleStmt_observe
    {Γ : L.Ctx} (σ : Profile (L := L) (W := W)) (cond : L.Expr Γ L.bool) (env : L.Env Γ) :
    (StratSem σ).handleStmt (Prog.CmdStmtObs.observe (Γ := Γ) cond) env
      =
    (if L.toBool (L.eval cond env) then WDist.pure () else WDist.zero) := rfl

/-- Evaluate a DagLet program under a profile, producing a weighted distribution. -/
abbrev evalD (σ : Profile (L := L) (W := W)) {Γ : L.Ctx} {τ : L.Ty} :
    DagProg (L := L) (W := W) Γ τ → L.Env Γ → WDist W (L.Val τ) :=
  Prog.evalWith (L := L) (StratSem σ)

/-! ## Translation to ProbLet by fixing a profile -/

/--
Translate a DagLet program to a ProbLet program by fixing a profile:
each `letChoose` becomes `letSample` from the lifted kernel `env ↦ σ.choose ... (v.proj env)`.
-/
def toProb (σ : Profile (L := L) (W := W)) {Γ : L.Ctx} {τ : L.Ty} :
      DagProg (L := L) (W := W) Γ τ → Prob.PProg (W := W) Γ τ
  | .ret e        => .ret e
  | .letDet e k   => .letDet e (toProb σ k)
  | .doStmt s k   => .doStmt s (toProb σ k)
  | .doBind c k   =>
      match c with
      | .choose who v A =>
          .doBind (.sample (liftKernel σ who v A)) (toProb σ k)

@[simp] theorem toProb_ret {Γ τ} (σ : Profile (L := L) (W := W)) (e : L.Expr Γ τ) :
    toProb σ (DagProg.ret e) = (.ret e : Prob.PProg (W := W) Γ τ) := rfl

@[simp] theorem toProb_letDet {Γ τ τ'} (σ : Profile (L := L) (W := W)) (e : L.Expr Γ τ')
    (k : DagProg (L := L) (W := W) (τ' :: Γ) τ) :
    toProb σ (DagProg.letDet e k) = (.letDet e (toProb σ k)) := rfl

@[simp] theorem toProb_observe {Γ τ} (σ : Profile (L := L) (W := W))
    (c : L.Expr Γ L.bool) (k : DagProg (L := L) (W := W) Γ τ) :
    toProb σ (DagProg.observe c k)
      =
    (.doStmt (.observe c) (toProb σ k) : Prob.PProg (W := W) Γ τ) := rfl

@[simp] lemma evalP_eq_evalWith {Γ τ} (p : Prob.PProg (W := W) Γ τ) (env : L.Env Γ) :
    Prob.evalP p env =
      Prog.evalWith (Prob.ProbSem (W := W)) p env := rfl

@[simp] lemma EffWDist_bind {α β} (xs : WDist W α) (f : α → WDist W β) :
    ((Prob.EffWDist (W := W)).bind xs f) = WDist.bind xs f := rfl

/-! ## Fundamental link: evalD = Prob.evalP ∘ toProb -/

/-- Evaluation under a profile agrees with evaluation of the translated ProbLet program. -/
theorem evalD_eq_evalP_toProb
    (σ : Profile (L := L) (W := W)) {Γ : L.Ctx} {τ : L.Ty}
    (p : DagProg (L := L) (W := W) Γ τ) (env : L.Env Γ) :
    evalD σ p env = Prob.evalP (toProb σ p) env := by
  induction p with
  | ret e =>
      -- key: unfold RHS `evalP` (and `toProb`) so both sides are the same core eval
      simp [evalD, toProb, Prob.evalP, Prob.ProbSem, Prog.evalWith, Prog.evalProg_gen,
            StratSem, EffWDist]
  | letDet e k ih =>
      simp only [evalD, evalWith, evalProg_gen, StratSem, EffWDist,
                 Prob.evalP, Prob.ProbSem, toProb]
      simp_all only [evalP_eq_evalWith]
      apply ih
  | doStmt s k ih =>
      cases s with
      | observe cond =>
          by_cases h : L.toBool (L.eval cond env)
          · -- succeed: both sides reduce to the continuation
            simp only [evalD, evalWith, evalProg_gen, StratSem, EffWDist, h, ↓reduceIte,
              EffWDist_bind, WDist.bind_pure, Prob.evalP, Prob.ProbSem, toProb]
            simp_all only [evalP_eq_evalWith]
            apply ih
          · -- fail: both sides are zero, done
            simp [evalD, toProb, Prob.evalP, Prob.ProbSem,
                  Prog.evalWith, Prog.evalProg_gen,
                  StratSem, EffWDist, h]
  | doBind c k ih =>
      cases c with
      | choose who v A =>
          simp only [evalD, evalWith, evalProg_gen, StratSem, EffWDist, liftKernel, EffWDist_bind,
            Prob.evalP, Prob.ProbSem, toProb]
          refine congrArg (fun f => WDist.bind (σ.choose who v A (v.proj env)) f) ?_
          funext a
          simpa using ih (env := (a, env))

end Dag
