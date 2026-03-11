import distilled.Language

/-!
# A small concrete backend language

This file provides a simple reusable instantiation of `Language`:

- truth values via `bool`
- finite scalar values via `range n`
- a small expression language with evaluation and dependency extraction
- a small finite-support distribution language

Finiteness is supplied separately via `FiniteValuation`.
-/

namespace Distilled.BasicLanguage

open Distilled

/-- Backend value types: booleans and finite ranges. -/
inductive Ty where
  | bool
  | range (n : Nat)
deriving DecidableEq, Repr

/-- Runtime values for `Ty`. -/
abbrev Val : Ty → Type
  | .bool => Bool
  | .range n => Fin n

instance instDecEqVal : ∀ {τ : Ty}, DecidableEq (Val τ) := by
  intro τ
  cases τ <;> infer_instance

instance instFintypeVal : (τ : Ty) → Fintype (Val τ)
  | .bool => inferInstance
  | .range _ => inferInstance

/-- The backend language instance. -/
def lang : Language where
  Ty := Ty
  decEqTy := inferInstance
  Val := Val
  decEqVal := instDecEqVal
  bool := .bool

/-- Finite valuation for the backend language. -/
def finite : FiniteValuation lang where
  fintypeVal := instFintypeVal

abbrev Ctx := lang.Ctx
abbrev Var (Γ : Ctx) (τ : Ty) := lang.Var Γ τ
abbrev Env (Γ : Ctx) := lang.Env Γ

@[simp] theorem domainSize_bool :
    finite.domainSize lang .bool = 2 := by
  simp [FiniteValuation.domainSize, finite, lang, Val]

@[simp] theorem domainSize_range (n : Nat) :
    finite.domainSize lang (.range n) = n := by
  simp [FiniteValuation.domainSize, finite, lang, Val]

/-- Expressions over the concrete backend language. -/
inductive Expr : Ctx → Ty → Type where
  | var : Var Γ τ → Expr Γ τ
  | constBool : Bool → Expr Γ .bool
  | constRange (n : Nat) : Fin n → Expr Γ (.range n)
  | eq : Expr Γ τ → Expr Γ τ → Expr Γ .bool
  | and : Expr Γ .bool → Expr Γ .bool → Expr Γ .bool
  | not : Expr Γ .bool → Expr Γ .bool
  | ite : Expr Γ .bool → Expr Γ τ → Expr Γ τ → Expr Γ τ

/-- Evaluate an expression under an environment. -/
def evalExpr : Expr Γ τ → Env Γ → Val τ
  | .var x, env => Env.get env x
  | .constBool b, _ => b
  | .constRange _ v, _ => v
  | .eq l r, env => decide (evalExpr l env = evalExpr r env)
  | .and l r, env => evalExpr l env && evalExpr r env
  | .not e, env => !(evalExpr e env)
  | .ite c t f, env => if evalExpr c env then evalExpr t env else evalExpr f env

/-- Free variables of an expression. Duplicates are allowed. -/
def exprDeps : Expr Γ τ → List (Sigma fun τ => Var Γ τ)
  | .var x => [⟨_, x⟩]
  | .constBool _ => []
  | .constRange _ _ => []
  | .eq l r => exprDeps l ++ exprDeps r
  | .and l r => exprDeps l ++ exprDeps r
  | .not e => exprDeps e
  | .ite c t f => exprDeps c ++ exprDeps t ++ exprDeps f

/-- Concrete expression kit for `lang`. -/
def exprKit : ExprKit lang where
  Expr := Expr
  eval := evalExpr
  deps := exprDeps

/-- Finite-support distributions over backend values. `atom` is already
semantic, while `ite` adds dependency-sensitive branching. -/
inductive DistExpr : Ctx → Ty → Type where
  | atom : PMF (Val τ) → DistExpr Γ τ
  | ite : Expr Γ .bool → DistExpr Γ τ → DistExpr Γ τ → DistExpr Γ τ

namespace DistExpr

noncomputable def pure (v : Val τ) : DistExpr Γ τ :=
  .atom (PMF.pure v)

end DistExpr

/-- Evaluate a distribution expression. -/
def evalDistExpr : DistExpr Γ τ → Env Γ → PMF (Val τ)
  | .atom μ, _ => μ
  | .ite c t f, env => if evalExpr c env then evalDistExpr t env else evalDistExpr f env

/-- Free variables of a distribution expression. -/
def distDeps : DistExpr Γ τ → List (Sigma fun τ => Var Γ τ)
  | .atom _ => []
  | .ite c t f => exprDeps c ++ distDeps t ++ distDeps f

/-- Concrete finite-support distribution kit for `lang`. -/
def distKit : DistKit lang where
  DistExpr := DistExpr
  eval := evalDistExpr
  deps := distDeps

end Distilled.BasicLanguage
