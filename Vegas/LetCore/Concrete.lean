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
