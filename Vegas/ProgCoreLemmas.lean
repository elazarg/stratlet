import Vegas.ProgCore
import Vegas.Expr
import Vegas.Env

namespace ProgCore

/-!
# Extensional Properties for ProgCore / DProg
-/

open ProgCore

/-! ## Weakening helpers -/

/-- Weaken a variable reference to work in an extended context. -/
def Var.weaken {Γ τ τ'} : Var Γ τ → Var (τ' :: Γ) τ
  | .vz    => .vs .vz
  | .vs v  => .vs (Var.weaken v)

/-- Lift an expression to work in an extended context (weakening). -/
def Expr.weaken {Γ τ τ'} : Expr Γ τ → Expr (τ' :: Γ) τ
  | .var v        => .var (Var.weaken v)
  | .constInt i   => .constInt i
  | .constBool b  => .constBool b
  | .addInt l r   => .addInt (Expr.weaken l) (Expr.weaken r)
  | .eqInt l r    => .eqInt (Expr.weaken l) (Expr.weaken r)
  | .andBool l r  => .andBool (Expr.weaken l) (Expr.weaken r)
  | .notBool e    => .notBool (Expr.weaken e)

/-- Evaluating a weakened variable in an extended environment recovers the old value. -/
@[simp] theorem Env.get_weaken {Γ τ} (x : Var Γ τ) :
    ∀ {τ' : Ty} {v : Val τ'} {env : Env Γ},
      Env.get (Γ := τ' :: Γ) (v, env) (Var.weaken x)
        =
      Env.get env x := by
  intro τ' v env
  induction x generalizing τ' v with
  | vz =>
      cases env with
      | mk head tail =>
          rfl
  | vs x ih =>
      cases env with
      | mk head tail =>
          simp [Var.weaken, Env.get]
          simpa using ih (v := head) (env := tail)

/-- Weakening preserves expression evaluation when you extend the env by one value. -/
@[simp] theorem evalExpr_weaken {Γ τ τ'} (e : Expr Γ τ) (env : Env Γ) (v : Val τ') :
    evalExpr (Expr.weaken e) (v, env) = evalExpr e env := by
  induction e with
  | var x => simp [Expr.weaken, evalExpr]
  | constInt i => rfl
  | constBool b => rfl
  | addInt l r ihl ihr => simp [Expr.weaken, evalExpr, ihl, ihr]
  | eqInt l r ihl ihr => simp [Expr.weaken, evalExpr, ihl, ihr]
  | andBool l r ihl ihr => simp [Expr.weaken, evalExpr, ihl, ihr]
  | notBool e ihe => simp [Expr.weaken, evalExpr, ihe]

@[simp] theorem Var_weaken_vz : Var.weaken (τ' := τ') (Var.vz : Var (τ :: Γ) τ) = Var.vs Var.vz := rfl
@[simp] theorem Var_weaken_vs (x : Var Γ τ) :
  Var.weaken (τ' := τ') (Var.vs x) = Var.vs (Var.weaken (τ' := τ') x) := rfl

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
  -- adjust names if yours differ
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

end ProgCore
