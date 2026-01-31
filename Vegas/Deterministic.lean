
/-! ## 1) Types, contexts, values, variables, environments -/

inductive Ty where
  | int  : Ty
  | bool : Ty
deriving Repr, DecidableEq

abbrev Ctx := List Ty

abbrev Val : Ty → Type
  | .int  => Int
  | .bool => Bool

/-- Typed De Bruijn variables. -/
inductive Var : Ctx → Ty → Type where
  | vz {Γ τ} : Var (τ :: Γ) τ
  | vs {Γ τ τ'} (v : Var Γ τ) : Var (τ' :: Γ) τ
deriving Repr

/-- Runtime environments matching a context. -/
def Env : Ctx → Type
  | []      => Unit
  | τ :: Γ  => Val τ × Env Γ

/-- Total lookup. -/
def Env.get {τ} : {Γ : Ctx} → Env Γ → Var Γ τ → Val τ
  | _ :: _, (x, _),  Var.vz    => x
  | _ :: _, (_, xs), Var.vs v  => Env.get xs v

/-! ## 2) Deterministic expressions -/

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
