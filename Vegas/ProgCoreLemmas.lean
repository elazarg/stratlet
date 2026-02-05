import Vegas.ProgCore
import Vegas.Env

namespace ProgCore

/-!
# Extensional Properties for ProgCore / DProg
-/

open ProgCore

/-! ## Weakening helpers -/

@[simp] theorem evalProgOption_observe {Γ τ}
    (c : Expr Γ .bool) (k : DProg Γ τ) (env : Env Γ) :
    evalProgOption (DProg.observe c k) env
      =
    if evalExpr c env then evalProgOption k env else none := by
  simp [DProg.observe, evalProgOption, evalWith, evalProg_gen, DetOptionSem]
  split <;> rfl

@[simp] theorem evalProgOption_doStmt {Γ τ}
    (s : CmdStmtD  Γ) (k : DProg Γ τ) (env : Env Γ) :
    evalProgOption (.doStmt s k) env
      =
    (DetOptionSem.handleStmt s env).bind (fun _ => evalProgOption k env) := by
  simp [evalProgOption, ProgCore.evalWith, ProgCore.evalProg_gen]
  rfl

/-!
The following proofs use only:
- unfolding `DProg.observe` / `DProg.letDet` / `DProg.ret`
- unfolding `evalProgOption` via `evalWith DetOptionSem`
- case splits on the boolean guards
- plus the weakening lemma above
-/

/-- Observe-fusion: consecutive observations fuse into conjunction. -/
theorem observe_fuse {Γ τ} (c₁ c₂ : Expr Γ .bool) (k : DProg Γ τ) :
    (fun env => evalProgOption (DProg.observe c₁ (DProg.observe c₂ k)) env)
    =
    (fun env => evalProgOption (DProg.observe (Expr.andBool c₁ c₂) k) env) := by
  funext env
  by_cases h1 : evalExpr c₁ env
  · by_cases h2 : evalExpr c₂ env
    · simp [h1, h2, evalExpr]
    · simp [h1, h2, evalExpr]
  · simp [h1, evalExpr]


theorem observe_hoist_letDet {Γ τ τ'} (e : Expr Γ τ') (c : Expr Γ .bool) (k : DProg (τ' :: Γ) τ) :
    (fun env => evalProgOption (DProg.letDet e (DProg.observe (Expr.weaken c) k)) env)
    =
    (fun env => evalProgOption (DProg.observe c (DProg.letDet e k)) env) := by
  funext env
  simp [DProg.letDet, evalProgOption, ProgCore.evalWith, ProgCore.evalProg_gen, DProg.observe, DetOptionSem]


/-- Observe is idempotent. -/
theorem observe_idem {Γ τ} (c : Expr Γ .bool) (k : DProg Γ τ) :
    (fun env => evalProgOption (DProg.observe c (DProg.observe c k)) env)
    =
    (fun env => evalProgOption (DProg.observe c k) env) := by
  funext env
  by_cases hc : evalExpr c env <;> simp [hc]

/-- letDet followed by ret of the bound variable is identity on the expression. -/
theorem letDet_ret_var {Γ τ} (e : Expr Γ τ) :
    (fun env => evalProgOption (DProg.letDet e (DProg.ret (Expr.var Var.vz))) env)
    =
    (fun env => evalProgOption (DProg.ret e) env) := by
  funext env
  simp [DProg.letDet, DProg.ret, evalProgOption]
  rfl

/-- Observe true is identity. -/
theorem observe_true {Γ τ} (k : DProg Γ τ) :
    (fun env => evalProgOption (DProg.observe (Expr.constBool true) k) env)
    =
    (fun env => evalProgOption k env) := by
  funext env
  simp [DProg.observe, evalProgOption]
  rfl

/-- Observe false always fails. -/
theorem observe_false {Γ τ} (k : DProg Γ τ) :
    (fun env => evalProgOption (DProg.observe (Expr.constBool false) k) env)
    =
    (fun _ => none) := by
  funext env
  simp [DProg.observe, evalProgOption]
  rfl

theorem observe_push_letDet {Γ τ τ'} (e : Expr Γ τ') (c : Expr Γ .bool) (k : DProg (τ' :: Γ) τ) :
    (fun env => evalProgOption (DProg.observe c (DProg.letDet e k)) env)
    =
    (fun env => evalProgOption (DProg.letDet e (DProg.observe (Expr.weaken c) k)) env) := by
  simpa using (observe_hoist_letDet (Γ := Γ) (τ := τ) (τ' := τ') e c k).symm

@[simp] theorem evalProgOption_ret_weaken {Γ τ τ'} (e : Expr Γ τ) (env : Env Γ) (v : Val τ') :
    evalProgOption (DProg.ret (Expr.weaken (τ' := τ') e)) (v, env)
      =
    evalProgOption (DProg.ret e) env := by
  simp [DProg.ret, evalProgOption, evalExpr_weaken]

end ProgCore
