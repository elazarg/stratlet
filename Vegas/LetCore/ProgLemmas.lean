import Vegas.LetCore.Env
import Vegas.LetCore.Language
import Vegas.LetCore.Prog

namespace Prog

variable {L} (EL : ExprLaws L)

open Prog

@[simp] theorem evalProgOption_observe {Γ τ}
    (c : L.Expr Γ L.bool) (k : DProg Γ τ) (env : L.Env Γ) :
    evalProgOption (DProg.observe c k) env
      =
    if L.toBool (L.eval c env) then evalProgOption k env else none := by
  simp [Prog.DProg.observe, Prog.evalProgOption, Prog.evalWith,
        Prog.evalProg_gen, Prog.DetOptionSem, Eff.guard]
  split <;> rfl

theorem observe_fuse {Γ τ} (c₁ c₂ : L.Expr Γ L.bool) (k : DProg Γ τ) :
    (fun env => evalProgOption (DProg.observe c₁ (DProg.observe c₂ k)) env)
    =
    (fun env => evalProgOption (DProg.observe (EL.andBool c₁ c₂) k) env) := by
  funext env
  by_cases h1 : L.toBool (L.eval c₁ env) <;> by_cases h2 : L.toBool (L.eval c₂ env) <;> simp [h1, h2, EL.toBool_eval_andBool]

theorem observe_hoist_letDet {Γ τ τ'} (e : L.Expr Γ τ') (c : L.Expr Γ L.bool)
    (k : DProg (τ' :: Γ) τ) :
    (fun env =>
      evalProgOption
        (DProg.letDet e (DProg.observe (EL.weaken c) k)) env)
    =
    (fun env =>
      evalProgOption
        (DProg.observe c (DProg.letDet e k)) env) := by
  funext env
  -- unfold letDet and observe once; the key is rewriting the guard via eval_weaken
  simp [Prog.DProg.letDet, Prog.DProg.observe, Prog.evalProgOption,
        Prog.evalWith, Prog.evalProg_gen, Prog.DetOptionSem, Eff.guard,
        EL.eval_weaken]

@[simp] theorem evalProgOption_ret_weaken {Γ τ τ'} (e : L.Expr Γ τ) (env : L.Env Γ) (v : L.Val τ') :
    evalProgOption (DProg.ret (EL.weaken e)) (v, env)
      =
    evalProgOption (DProg.ret e) env := by
  simp [Prog.DProg.ret, Prog.evalProgOption, Prog.evalWith,
        Prog.evalProg_gen, EL.eval_weaken]
