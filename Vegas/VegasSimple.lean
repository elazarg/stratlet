import Vegas.ExprSimple
import Vegas.Operational

/-!
# Vegas protocol syntax

This file defines the concrete Vegas protocol syntax on top of the concrete
value and expression layer from `Vegas.ExprSimple`.
-/

namespace Vegas

def VEnvSimple.eraseSampleEnv {Γ : VCtxSimple}
    (env : VEnvSimple Γ) : Env simpleExpr.Val (erasePubVCtx Γ) :=
  Vegas.VEnv.eraseSampleEnv (Player := Player) (L := simpleExpr) env

/-- Per-player payoff expressions with no duplicate players.
    Convenience wrapper for constructing `ret` payloads. -/
structure PayoffMap (Γ : VCtxSimple) where
  entries : List (Player × simpleExpr.Expr (erasePubVCtx Γ) .int)
  nodup : (entries.map Prod.fst).Nodup

/-- Evaluate a PayoffMap into an outcome (Player →₀ Int). -/
noncomputable def evalPayoffMap (u : PayoffMap Γ) (env : VEnvSimple Γ) :
    Outcome Player :=
  Vegas.evalPayoffs u.entries env

noncomputable abbrev evalR {Γ : VCtxSimple} {b : BaseTy} {x : VarId}
    (R : simpleExpr.Expr ((x, b) :: eraseVCtx Γ) .bool)
    (a : Val b) (env : Env simpleExpr.Val (eraseVCtx Γ)) : Bool :=
  Vegas.evalGuard (Player := Player) (L := simpleExpr) R a env

abbrev VegasSimple : VCtxSimple → Type := Vegas.VegasCore Player simpleExpr

abbrev CommitKernelSimple (who : Player) (Γ : VCtxSimple) (b : BaseTy) :
    Type :=
  Vegas.CommitKernel Player simpleExpr who Γ b

abbrev OmniscientOperationalProfileSimple : Type :=
  Vegas.OmniscientOperationalProfile Player simpleExpr

abbrev PartialOmniscientOperationalProfileSimple : Type :=
  Vegas.PartialOmniscientOperationalProfile Player simpleExpr

end Vegas
