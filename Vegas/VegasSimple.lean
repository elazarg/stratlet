import Vegas.ExprSimple

/-!
# Vegas protocol syntax

This file defines the concrete Vegas protocol syntax on top of the concrete
value and expression layer from `Vegas.ExprSimple`.
-/

namespace Vegas

inductive DistExpr (Γ : CtxSimple) (b : BaseTy) : Type where
  | weighted (entries : List (Val b × ℚ≥0)) : DistExpr Γ b
  | ite (c : Expr Γ .bool) (t f : DistExpr Γ b) : DistExpr Γ b

noncomputable def evalDistExpr : DistExpr Γ b → EnvSimple Γ → FDist (Val b)
  | .weighted entries, _ => FDist.ofList entries
  | .ite c t f, env =>
      if evalExpr c env then evalDistExpr t env else evalDistExpr f env

@[simp] theorem evalDistExpr_weighted {Γ : CtxSimple} {b : BaseTy}
    (entries : List (Val b × ℚ≥0)) (env : EnvSimple Γ) :
    evalDistExpr (.weighted entries) env = FDist.ofList entries := rfl

theorem evalDistExpr_ite_true {Γ : CtxSimple} {b : BaseTy}
    {c : Expr Γ .bool} {t f : DistExpr Γ b} {env : EnvSimple Γ}
    (hc : evalExpr c env = true) :
    evalDistExpr (.ite c t f) env = evalDistExpr t env := by
  simp [evalDistExpr, hc]

theorem evalDistExpr_ite_false {Γ : CtxSimple} {b : BaseTy}
    {c : Expr Γ .bool} {t f : DistExpr Γ b} {env : EnvSimple Γ}
    (hc : evalExpr c env = false) :
    evalDistExpr (.ite c t f) env = evalDistExpr f env := by
  simp [evalDistExpr, hc]

def DistExpr.point (v : Val b) : DistExpr Γ b := .weighted [(v, 1)]

def DistExpr.uniform (vs : List (Val b)) : DistExpr Γ b :=
  let w : ℚ≥0 := 1 / (vs.length : ℚ≥0)
  .weighted (vs.map fun v => (v, w))

/-- Extract variable IDs referenced by a distribution expression. -/
def distExprVars : DistExpr Γ b → List VarId
  | .weighted _ => []
  | .ite c t f => exprVars c ++ distExprVars t ++ distExprVars f

/-- The current Vegas sampling layer, exposed through the generic
visibility-aware protocol interface. -/
noncomputable instance distKitSimple : Vegas.DistKit Player simpleExpr where
  DistExpr := DistExpr
  eval := @evalDistExpr
  deps := @distExprVars

def EnvSimple.projectDist {Γ : CtxSimple} (τ : BindTySimple) (m : SampleMode τ)
    (env : EnvSimple Γ) : EnvSimple (distCtx τ m Γ) :=
  Vegas.Env.projectDist (Player := Player) (L := simpleExpr) τ m env

/-- Per-player payoff expressions with no duplicate players.
    Convenience wrapper for constructing `ret` payloads. -/
structure PayoffMap (Γ : CtxSimple) where
  entries : List (Player × Expr Γ .int)
  nodup : (entries.map Prod.fst).Nodup

/-- Evaluate a PayoffMap into an outcome (Player →₀ Int). -/
noncomputable def evalPayoffMap (u : PayoffMap Γ) (env : EnvSimple Γ) :
    Outcome Player :=
  u.entries.foldl (fun acc (p, e) => acc + Finsupp.single p (evalExpr e env)) 0

abbrev evalR {Γ : CtxSimple} {b : BaseTy} {who : Player} {x : VarId}
    (R : Expr ((x, .pub b) :: flattenCtx (viewCtx who Γ)) .bool)
    (a : Val b) (view : EnvSimple (viewCtx who Γ)) : Bool :=
  Vegas.evalGuard (Player := Player) (L := simpleExpr) inferInstance R a view

abbrev VegasSimple : CtxSimple → Type := Vegas.VegasCore Player simpleExpr

abbrev CommitKernelSimple (who : Player) (Γ : CtxSimple) (b : BaseTy) : Type :=
  Vegas.CommitKernel Player simpleExpr who Γ b

abbrev ProfileSimple : Type := Vegas.Profile Player simpleExpr

abbrev PProfileSimple : Type := Vegas.PProfile Player simpleExpr

end Vegas
