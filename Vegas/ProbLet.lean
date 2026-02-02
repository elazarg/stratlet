import Mathlib.Data.Rat.Init
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic

import Vegas.WDist
import Vegas.ProgCore
import Vegas.Env
import Vegas.Expr

namespace ProbLet

/-- A (finite-support) stochastic kernel from environments. -/
abbrev Kernel (Γ : Ctx) (τ : Ty) := Env Γ → WDist (Val τ)

/-- Effect interface instance for `WDist`. -/
def EffWDist : ProgCore.Eff WDist where
  pure := fun x => [(x, 1)]
  bind := fun xs f => WDist.bind xs f
  fail := []

/-- Bind-commands for the probabilistic language: sampling from a kernel. -/
inductive CmdBindP : ProgCore.CmdB where
  | sample {Γ τ} (K : Kernel Γ τ) : CmdBindP Γ τ

/-- Statement-commands: hard evidence / rejection. -/
abbrev CmdStmtP := ProgCore.CmdStmtObs

/-- Probabilistic programs are `Prog` instantiated with these commands. -/
abbrev PProg := ProgCore.Prog CmdBindP CmdStmtP

/-- Pack the semantics as a `LangSem`. -/
def ProbSem : ProgCore.LangSem CmdBindP CmdStmtP WDist where
  E := EffWDist
  handleBind
    | .sample K, env => K env
  handleStmt
    | .observe cond, env =>
        if evalExpr cond env then WDist.pure () else EffWDist.fail

@[simp] theorem ProbSem_handleBind_sample (K : Kernel Γ τ) (env : Env Γ) :
    ProbSem.handleBind (CmdBindP.sample (Γ := Γ) (τ := τ) K) env = K env := rfl

@[simp] theorem ProbSem_handleStmt_observe (cond : Expr Γ .bool) (env : Env Γ) :
    ProbSem.handleStmt (ProgCore.CmdStmtObs.observe (Γ := Γ) cond) env =
      (if evalExpr cond env then WDist.pure () else WDist.zero) := rfl

/-- Evaluator for probabilistic programs. -/
def evalP {Γ τ} : PProg Γ τ → Env Γ → WDist (Val τ) :=
  ProgCore.evalWith ProbSem

end ProbLet
