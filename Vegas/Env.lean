
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

end Env
