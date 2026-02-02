
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

/-- Total lookup. -/
def Env.get {τ} : {Γ : Ctx} → Env Γ → Var Γ τ → Val τ
  | _ :: _, (x, _),  Var.vz    => x
  | _ :: _, (_, xs), Var.vs v  => Env.get xs v
