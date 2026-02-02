import Vegas.Env

inductive Expr : Ctx → Ty → Type where
  | var {Γ τ} (v : Var Γ τ) : Expr Γ τ
  | constInt  {Γ} (i : Int)  : Expr Γ .int
  | constBool {Γ} (b : Bool) : Expr Γ .bool
  | addInt {Γ} (l r : Expr Γ .int) : Expr Γ .int
  | eqInt  {Γ} (l r : Expr Γ .int) : Expr Γ .bool
  | andBool {Γ} (l r : Expr Γ .bool) : Expr Γ .bool
  | notBool {Γ} (b : Expr Γ .bool) : Expr Γ .bool
deriving Repr

def evalExpr {Γ τ} : Expr Γ τ → Env Γ → Val τ
  | .var v,         env => env.get v
  | .constInt i,    _   => i
  | .constBool b,   _   => b
  | .addInt l r,    env => evalExpr l env + evalExpr r env
  | .eqInt l r,     env => (evalExpr l env) == (evalExpr r env)
  | .andBool l r,   env => (evalExpr l env) && (evalExpr r env)
  | .notBool b,     env => !(evalExpr b env)
