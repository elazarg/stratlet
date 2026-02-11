import Mathlib.Data.List.Basic

import Vegas.LetProb.WDist
import Vegas.LetCore.Prog
import Vegas.LetCore.Env
import Vegas.LetProb.Prob
import Vegas.LetProb.ProbLemmas
import Vegas.Defs
import Vegas.LetProtocol.Dag

namespace Dag

open Prog Defs

variable {L : Language}
variable {W : Type} [WeightModel W]

/-! ## Extensional "sanity" properties -/

/-- A program with no choices (no `.doBind`) is profile-independent. -/
def noChoices {Γ : L.Ctx} {τ : L.Ty} : DagProg (W := W) Γ τ → Prop
  | .ret _        => True
  | .letDet _ k   => noChoices k
  | .doStmt _ k   => noChoices k
  | .doBind _ _   => False

@[simp] lemma StratSem_E_bind (σ : Profile (L := L) (W := W)) {α β}
    (xs : WDist W α) (f : α → WDist W β) :
    (StratSem σ).E.bind xs f = WDist.bind xs f := rfl

/-- Profile-independence: programs without choices evaluate the same under any profile. -/
theorem evalD_profile_indep {Γ : L.Ctx} {τ : L.Ty}
    (p : DagProg (W := W) Γ τ) (hp : noChoices p)
    (σ₁ σ₂ : Profile (L := L) (W := W)) (env : L.Env Γ) :
    evalD σ₁ p env = evalD σ₂ p env := by
  induction p with
  | ret e =>
      simp [evalD, Prog.evalWith, Prog.evalProg_gen, StratSem, EffWDist]
  | letDet e k ih =>
      have hk : noChoices k := hp
      simp [evalD, Prog.evalWith, Prog.evalProg_gen, StratSem, EffWDist]
      simpa using ih hk (env := (L.eval e env, env))
  | doStmt s k ih =>
      have hk : noChoices k := hp
      cases s with
      | observe cond =>
          by_cases h : L.toBool (L.eval cond env)
          · simp [evalD, Prog.evalWith, Prog.evalProg_gen, StratSem, EffWDist, h]
            simpa using ih hk (env := env)
          · simp [evalD, Prog.evalWith, Prog.evalProg_gen, StratSem, EffWDist, h]
  | doBind c k =>
      cases hp

/-! ## Observe-fusion (delegated to ProbLet + ExprLaws) -/

/--
Observe-fusion: consecutive observations fuse into conjunction.
-/
theorem observe_fuse
    (σ : Profile (L := L) (W := W)) {EL : ExprLaws (L := L)}
    {Γ : L.Ctx} {τ : L.Ty} (c₁ c₂ : L.Expr Γ L.bool) (k : DagProg (W := W) Γ τ) :
    (fun env => evalD σ (DagProg.observe c₁ (DagProg.observe c₂ k)) env)
      =
    (fun env => evalD σ (DagProg.observe (EL.andBool c₁ c₂) k) env) := by
  funext env
  -- Push to ProbLet via translation, fuse there, and pull back.
  simp [evalD_eq_evalP_toProb σ, DagProg.observe, toProb]
  -- Now it's exactly the ProbLet lemma (function equality) specialized at `env`.
  simpa using congrArg (fun f => f env) (Prob.observe_fuse EL)

end Dag
