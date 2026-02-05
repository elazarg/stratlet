import Mathlib.Data.List.Basic

import Vegas.WDist
import Vegas.ProgCore
import Vegas.Env
import Vegas.ProbLet
import Vegas.ProbLetLemmas
import Vegas.GameDefs
import Vegas.DagLet

namespace DagLet

open ProgCore GameDefs

variable {L : Language}

/-! ## Extensional “sanity” properties -/

/-- A program with no choices (no `.doBind`) is profile-independent. -/
def noChoices {Γ : L.Ctx} {τ : L.Ty} : DagProg (L := L) Γ τ → Prop
  | .ret _        => True
  | .letDet _ k   => noChoices k
  | .doStmt _ k   => noChoices k
  | .doBind _ _   => False

@[simp] lemma StratSem_E_bind (σ : Profile (L := L)) {α β} (xs : WDist α) (f : α → WDist β) :
    (StratSem (L := L) σ).E.bind xs f = WDist.bind xs f := rfl

/-- Profile-independence: programs without choices evaluate the same under any profile. -/
theorem evalD_profile_indep {Γ : L.Ctx} {τ : L.Ty}
    (p : DagProg (L := L) Γ τ) (hp : noChoices (L := L) p)
    (σ₁ σ₂ : Profile (L := L)) (env : L.Env Γ) :
    evalD (L := L) σ₁ p env = evalD (L := L) σ₂ p env := by
  induction p with
  | ret e =>
      simp [evalD, ProgCore.evalWith, ProgCore.evalProg_gen, StratSem, EffWDist]
  | letDet e k ih =>
      have hk : noChoices (L := L) k := hp
      simp [evalD, ProgCore.evalWith, ProgCore.evalProg_gen, StratSem, EffWDist]
      simpa using ih hk (env := (L.eval e env, env))
  | doStmt s k ih =>
      have hk : noChoices (L := L) k := hp
      cases s with
      | observe cond =>
          by_cases h : L.toBool (L.eval cond env)
          · simp [evalD, ProgCore.evalWith, ProgCore.evalProg_gen, StratSem, EffWDist, h]
            simpa using ih hk (env := env)
          · simp [evalD, ProgCore.evalWith, ProgCore.evalProg_gen, StratSem, EffWDist, h]
  | doBind c k =>
      cases hp

/-! ## Observe-fusion (delegated to ProbLet + ExprLaws) -/

/--
Observe-fusion: consecutive observations fuse into conjunction.
-/
theorem observe_fuse
    (σ : Profile (L := L)) {EL : ExprLaws (L := L)}
    {Γ : L.Ctx} {τ : L.Ty} (c₁ c₂ : L.Expr Γ L.bool) (k : DagProg (L := L) Γ τ) :
    (fun env => evalD (L := L) σ (DagProg.observe (L := L) c₁ (DagProg.observe (L := L) c₂ k)) env)
      =
    (fun env => evalD (L := L) σ (DagProg.observe (L := L) (EL.andBool c₁ c₂) k) env) := by
  funext env
  -- Push to ProbLet via translation, fuse there, and pull back.
  simp [evalD_eq_evalP_toProb (L := L) σ, DagProg.observe, toProb]
  -- Now it's exactly the ProbLet lemma (function equality) specialized at `env`.
  simpa using congrArg (fun f => f env) (ProbLet.observe_fuse (L := L) EL)

end DagLet
