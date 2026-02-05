
inductive Ty where
  | int  : Ty
  | bool : Ty
deriving Repr, DecidableEq

abbrev Ctx := List Ty

abbrev Val : Ty → Type
  | .int  => Int
  | .bool => Bool

/-- Decidable equality for runtime values (Int/Bool). -/
instance instDecEqVal (τ : Ty) : DecidableEq (Val τ) := by
  cases τ <;> infer_instance

/-- Typed De Bruijn variables. -/
inductive Var : Ctx → Ty → Type where
  | vz {Γ τ} : Var (τ :: Γ) τ
  | vs {Γ τ τ'} (v : Var Γ τ) : Var (τ' :: Γ) τ
deriving Repr

/-- Weaken a variable reference to work in an extended context. -/
def Var.weaken {Γ τ τ'} : Var Γ τ → Var (τ' :: Γ) τ
  | .vz    => .vs .vz
  | .vs v  => .vs (Var.weaken v)

/-- Runtime environments matching a context. -/
def Env : Ctx → Type
  | []      => Unit
  | τ :: Γ  => Val τ × Env Γ

namespace Env
/-- Total lookup. -/
def get {τ} : {Γ : Ctx} → Env Γ → Var Γ τ → Val τ
  | _ :: _, (x, _),  Var.vz    => x
  | _ :: _, (_, xs), Var.vs v  => Env.get xs v

def cons {Γ : Ctx} {τ : Ty} (a : Val τ) (env : Env Γ) : Env (τ :: Γ) :=
  (a, env)

def head {Γ : Ctx} {τ : Ty} : Env (τ :: Γ) → Val τ
  | (a, _) => a

def tail {Γ : Ctx} {τ : Ty} : Env (τ :: Γ) → Env Γ
  | (_, env) => env

@[simp] theorem get_vz {Γ : Ctx} {τ : Ty} (env : Env (τ :: Γ)) :
    Env.get (Γ := τ :: Γ) env Var.vz = env.head := by
  cases env; rfl

@[simp] theorem get_cons_vz {Γ : Ctx} {τ : Ty} (a : Val τ) (env : Env Γ) :
    Env.get (Γ := τ :: Γ) (Env.cons a env) Var.vz = a := by
  rfl

@[simp] theorem get_cons_vs {Γ : Ctx} {τ τ' : Ty} (a : Val τ') (env : Env Γ) (x : Var Γ τ) :
    Env.get (Γ := τ' :: Γ) (Env.cons a env) (Var.vs x) = Env.get env x := by
  rfl

/-- Evaluating a weakened variable in an extended environment recovers the old value. -/
@[simp] theorem get_weaken {Γ τ} (x : Var Γ τ) :
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

@[ext] theorem ext :
    ∀ {Γ : Ctx} {env₁ env₂ : Env Γ},
      (∀ {τ} (x : Var Γ τ), Env.get env₁ x = Env.get env₂ x) →
      env₁ = env₂
  | [], env₁, env₂, _ => by
    cases env₁
    cases env₂
    rfl
  | _ :: _,  (a, e₁), (b, e₂), h => by
    have ha : a = b := by simpa using h Var.vz
    have ht : e₁ = e₂ := by
      apply ext
      intro τ x
      simpa using h (Var.vs x)
    cases ha
    cases ht
    rfl

end Env

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

/-- Lift an expression to work in an extended context (weakening). -/
def Expr.weaken {Γ τ τ'} : Expr Γ τ → Expr (τ' :: Γ) τ
  | .var v        => .var (Var.weaken v)
  | .constInt i   => .constInt i
  | .constBool b  => .constBool b
  | .addInt l r   => .addInt (Expr.weaken l) (Expr.weaken r)
  | .eqInt l r    => .eqInt (Expr.weaken l) (Expr.weaken r)
  | .andBool l r  => .andBool (Expr.weaken l) (Expr.weaken r)
  | .notBool e    => .notBool (Expr.weaken e)

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
