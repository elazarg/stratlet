/-! # Generic Environment and Variables

This file defines De Bruijn indices and runtime environments in a
type-system-agnostic way. It depends only on a universe of types `Ty`
and a valuation `Val : Ty → Type`.
-/

namespace Env

section Ctx

variable {Ty : Type}

abbrev Ctx : Type := List Ty

end Ctx

section Var

variable {Ty : Type}

/-- De Bruijn indices depend only on the list of types. -/
inductive Var : Ctx → Ty → Type where
  | vz {Γ τ} : Var (τ :: Γ) τ
  | vs {Γ τ τ'} (v : Var Γ τ) : Var (τ' :: Γ) τ
deriving Repr

/-- Weaken a variable reference to work in an extended context. -/
def Var.weaken {Γ : Ctx} {τ τ' : Ty} : Var Γ τ → Var (τ' :: Γ) τ
  | .vz   => .vs .vz
  | .vs v => .vs (Var.weaken v)

@[simp] theorem Var.weaken_vz {Γ : Ctx} {τ τ' : Ty} :
    Var.weaken (τ' := τ') (Var.vz : Var (τ :: Γ) τ) = Var.vs Var.vz := rfl

@[simp] theorem Var.weaken_vs {Γ : Ctx} {τ τ' τ'' : Ty} (x : Var Γ τ) :
    Var.weaken (τ' := τ'') (Var.vs x : Var (τ' :: Γ) τ) = Var.vs (Var.weaken x) := rfl

end Var

section Env

variable {Ty : Type}

def Env : Ctx → Type
  | [] => Unit
  | τ :: Γ => Val τ × Env Γ

namespace Env

/-- Total lookup. -/
def get {Val : Ty → Type} {Γ : Ctx} {τ : Ty} (ρ : Env Val Γ) (x : Var Γ τ) : Val τ :=
  match x, ρ with
  | .vz,   (v, _) => v
  | .vs v, (_, ρ) => get ρ v

/-- Construct an environment by consing a value. -/
def cons {Val : Ty → Type} {Γ : Ctx} {τ : Ty} (v : Val τ) (ρ : Env Val Γ) : Env Val (τ :: Γ) :=
  (v, ρ)

/-- Head of the environment. -/
def head {Val : Ty → Type} {Γ : Ctx} {τ : Ty} : Env Val (τ :: Γ) → Val τ
  | (v, _) => v

/-- Tail of the environment. -/
def tail {Val : Ty → Type} {Γ : Ctx} {τ : Ty} : Env Val (τ :: Γ) → Env Val Γ
  | (_, ρ) => ρ

@[simp] theorem get_vz {Val : Ty → Type} {Γ : Ctx} {τ : Ty} (ρ : Env Val (τ :: Γ)) :
    get ρ Var.vz = head ρ := by
  cases ρ; rfl

@[simp] theorem get_cons_vz {Val : Ty → Type} {Γ : Ctx} {τ : Ty} (v : Val τ) (ρ : Env Val Γ) :
    get (cons v ρ) Var.vz = v :=
  rfl

@[simp] theorem get_cons_vs {Val : Ty → Type} {Γ : Ctx} {τ τ' : Ty} (v : Val τ') (ρ : Env Val Γ) (x : Var Γ τ) :
    get (cons v ρ) (Var.vs x) = get ρ x :=
  rfl

/-- Evaluating a weakened variable in an extended environment recovers the old value. -/
@[simp] theorem get_weaken
    {Val : Ty → Type} {Γ : Ctx} {τ τ' : Ty}
    (x : Var Γ τ) (v : Val τ') (ρ : Env Val Γ) :
    get (cons v ρ) (Var.weaken x) = get ρ x := by
  induction x generalizing τ' v with
  | vz =>
      simp [Var.weaken, Env.get, Env.cons]
  | vs x ih =>
      cases ρ with
      | mk v₀ ρ₀ =>
          simpa [Var.weaken, Env.get, Env.cons] using (ih (v := v₀) (ρ := ρ₀))

@[ext] theorem ext {Val : Ty → Type} {Γ : Ctx} {ρ₁ ρ₂ : Env Val Γ}
    (h : ∀ {τ} (x : Var Γ τ), get ρ₁ x = get ρ₂ x) : ρ₁ = ρ₂ := by
  induction Γ with
  | nil => cases ρ₁; cases ρ₂; rfl
  | cons τ Γ ih =>
    cases ρ₁ with | mk v₁ tail₁ =>
    cases ρ₂ with | mk v₂ tail₂ =>
      congr
      · exact h Var.vz
      · apply ih
        intro τ' x
        exact h (Var.vs x)

end Env

end Env

end Env
