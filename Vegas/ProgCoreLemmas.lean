import Vegas.Env
import Vegas.ExprLanguageInterface
import Vegas.ProgCore

namespace ProgCore

variable (EL : ExprLaws L)

open ProgCore

@[simp] theorem evalProgOption_observe {Γ τ}
    (c : L.Expr Γ L.bool) (k : DProg Γ τ) (env : EnvL Γ) :
    evalProgOption (DProg.observe c k) env
      =
    if L.toBool (L.eval c env) then evalProgOption k env else none := by
  simp [ProgCore.DProg.observe, ProgCore.evalProgOption, ProgCore.evalWith,
        ProgCore.evalProg_gen, ProgCore.DetOptionSem, Eff.guard]
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
  simp [ProgCore.DProg.letDet, ProgCore.DProg.observe, ProgCore.evalProgOption,
        ProgCore.evalWith, ProgCore.evalProg_gen, ProgCore.DetOptionSem, Eff.guard,
        EL.eval_weaken]

@[simp] theorem evalProgOption_ret_weaken {Γ τ τ'} (e : L.Expr Γ τ) (env : EnvL Γ) (v : L.Val τ') :
    evalProgOption (DProg.ret (EL.weaken e)) (v, env)
      =
    evalProgOption (DProg.ret e) env := by
  simp [ProgCore.DProg.ret, ProgCore.evalProgOption, ProgCore.evalWith,
        ProgCore.evalProg_gen, EL.eval_weaken]
