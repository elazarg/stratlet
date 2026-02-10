import Vegas.LetCore.Env
import Vegas.LetCore.Language

inductive Ty where
  | int  : Ty
  | bool : Ty
deriving Repr, DecidableEq

abbrev Val : Ty → Type
  | .int  => Int
  | .bool => Bool

/-- Decidable equality for runtime values (Int/Bool). -/
instance instDecEqVal {τ : Ty} : DecidableEq (Val τ) := by
  cases τ <;> infer_instance

abbrev Ctx := Env.Ctx (Ty := Ty)

inductive Expr : Ctx → Ty → Type where
  | var {Γ τ} (v : Env.Var Γ τ) : Expr Γ τ
  | constInt  {Γ} (i : Int)  : Expr Γ .int
  | constBool {Γ} (b : Bool) : Expr Γ .bool
  | addInt {Γ} (l r : Expr Γ .int) : Expr Γ .int
  | eqInt  {Γ} (l r : Expr Γ .int) : Expr Γ .bool
  | andBool {Γ} (l r : Expr Γ .bool) : Expr Γ .bool
  | notBool {Γ} (b : Expr Γ .bool) : Expr Γ .bool
deriving Repr

def evalExpr {Γ : Ctx} {τ : Ty} : Expr Γ τ → Env.Env Val Γ → Val τ
  | .var v,       env => env.get v
  | .constInt i,  _   => i
  | .constBool b, _   => b
  | .addInt l r,  env => evalExpr l env + evalExpr r env
  | .eqInt l r,   env => decide ((evalExpr l env) = (evalExpr r env))  -- or use BEq if you prefer
  | .andBool l r, env => (evalExpr l env) && (evalExpr r env)
  | .notBool b,   env => !(evalExpr b env)

def BasicLang : Language := {
  Ty := Ty
  decEqTy := inferInstance
  Val := Val
  decEqVal := instDecEqVal
  bool := Ty.bool
  toBool := fun b => b
  fromBool := fun b => b
  Expr := Expr
  eval := evalExpr
}

/-- Weaken an expression to work in an extended context. -/
def weakenExpr {Γ : Env.Ctx (Ty := Ty)} {τ τ' : Ty} :
    Expr Γ τ → Expr (τ' :: Γ) τ
  | .var v       => .var (Env.Var.weaken v)
  | .constInt i  => .constInt i
  | .constBool b => .constBool b
  | .addInt l r  => .addInt (weakenExpr l) (weakenExpr r)
  | .eqInt l r   => .eqInt (weakenExpr l) (weakenExpr r)
  | .andBool l r => .andBool (weakenExpr l) (weakenExpr r)
  | .notBool b   => .notBool (weakenExpr b)

theorem evalExpr_weaken {Γ : Env.Ctx (Ty := Ty)} {τ τ' : Ty}
    (e : Expr Γ τ) (env : Env.Env Val Γ) (v : Val τ') :
    evalExpr (weakenExpr e) (v, env) = evalExpr e env := by
  induction e with
  | var x =>
      simp only [weakenExpr, evalExpr]
      exact Env.Env.get_weaken x v env
  | constInt i => rfl
  | constBool b => rfl
  | addInt l r ihl ihr => simp [weakenExpr, evalExpr, ihl, ihr]
  | eqInt l r ihl ihr => simp [weakenExpr, evalExpr, ihl, ihr]
  | andBool l r ihl ihr => simp [weakenExpr, evalExpr, ihl, ihr]
  | notBool b ih => simp [weakenExpr, evalExpr, ih]

def basicExprLaws : ExprLaws BasicLang where
  weaken := weakenExpr
  eval_weaken := evalExpr_weaken
  constBool := Expr.constBool
  andBool := Expr.andBool
  toBool_eval_constBool := by intros; rfl
  toBool_eval_andBool := by intros; rfl
  var := Expr.var
  eval_var := by intros; rfl
