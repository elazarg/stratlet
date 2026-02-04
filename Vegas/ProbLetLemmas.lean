import Mathlib.Data.Rat.Init
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic

import Vegas.ProbLet
import Vegas.ProgCore
import Vegas.WDist
import Vegas.Env
import Vegas.Expr

import Vegas.ProgCoreLemmas

namespace ProbLet

open ProgCore

/-! A few simp bridges so simp sees `WDist.bind/pure/zero`. -/


@[simp] lemma ProbSem_E_pure {α} (x : α) :
    ProbSem.E.pure x = WDist.pure x := rfl

@[simp] lemma ProbSem_E_fail {α} :
    (ProbSem.E.fail : WDist α) = WDist.zero := rfl

@[simp] lemma ProbSem_E_bind {α β} (xs : WDist α) (f : α → WDist β) :
    ProbSem.E.bind xs f = WDist.bind xs f := rfl

lemma ProbSem_E_eq : ProbSem.E = EffWDist := rfl

/-! A very useful derived simp lemma: observe is an if-then-else at evalP level. -/
@[simp] lemma evalP_observe {Γ τ} (c : Expr Γ .bool) (k : PProg Γ τ) (env : Env Γ) :
    evalP (.doStmt (.observe c) k) env =
    if evalExpr c env then evalP k env else .zero := by
  simp [evalP]
  by_cases h : evalExpr c env = true <;> simp [h]

/-! ## Observe-Fusion Law -/

theorem observe_fuse {Γ τ} (c₁ c₂ : Expr Γ .bool) (k : PProg Γ τ) :
    (fun env => evalP (.doStmt (.observe c₁) (.doStmt (.observe c₂) k)) env)
    =
    (fun env => evalP (.doStmt (.observe (Expr.andBool c₁ c₂)) k) env) := by
  funext env
  by_cases h1 : evalExpr c₁ env
  · by_cases h2 : evalExpr c₂ env
    · -- both true
      simp [evalP_observe, h1, h2, evalExpr]
    · -- c₁ true, c₂ false
      simp [evalP_observe, h1, h2, evalExpr]
  · -- c₁ false
    simp [evalP_observe, h1, evalExpr]

/-! ## Conservation: deterministic embeds into probabilistic -/

def embedDProg : ProgCore.DProg Γ τ → PProg Γ τ
  | .ret e => .ret e
  | .letDet e k => .letDet e (embedDProg k)
  | .doBind c _ => nomatch c
  | .doStmt (.observe cond) k => .doStmt (.observe cond) (embedDProg k)

def liftOption : Option (Val τ) → WDist (Val τ)
  | none => .zero
  | some v => .pure v

-- helpful simp for Option→WDist + Option semantics of observe
@[simp] lemma liftOption_bind_guard {α β}
    (b : Bool) (x : α) (k : α → Option (Val β)) :
    liftOption (Option.bind (if b then some x else none) k)
      =
    if b then liftOption (k x) else .zero := by
  by_cases hb : b <;> simp [liftOption, hb]

theorem evalP_embed_eq_lift {Γ τ} (p : ProgCore.DProg Γ τ) (env : Env Γ) :
    evalP (embedDProg p) env = liftOption (ProgCore.evalProgOption p env) := by
  -- structural induction on the deterministic program
  induction p with
  | ret e =>
      -- evalP ret = pure; evalProgOption ret = some
      simp [embedDProg, evalP, liftOption, ProgCore.evalProgOption, ProgCore.evalWith_ret,
            ProgCore.DetOptionSem, ProgCore.EffOption]
  | letDet e k ih =>
      simp [embedDProg, evalP, ProgCore.evalProgOption,
            ProgCore.evalWith_letDet] at *
      -- both evaluators extend env the same way
      simpa using ih (env := (evalExpr e env, env))
  | doStmt s k ih =>
      cases s with
      | observe cond =>
          -- probabilistic side uses evalP_observe; option side uses the underlying handleStmt,
          -- but we can just unfold one step and case split, like you did elsewhere.
          by_cases h : evalExpr cond env
          · -- cond true
            -- LHS: evalP observe = evalP k ; RHS: Option also continues
            simp [embedDProg, evalP_observe, h, liftOption,
                  ProgCore.evalProgOption, ProgCore.evalWith_doStmt,
                  ProgCore.DetOptionSem, ProgCore.EffOption] at *
            -- reduce to IH
            simpa using ih (env := env)
          · -- cond false: both become empty/none
            simp [embedDProg, evalP_observe, h, liftOption,
                  ProgCore.evalProgOption, ProgCore.evalWith_doStmt,
                  ProgCore.DetOptionSem, ProgCore.EffOption]
  | doBind c k =>
      cases c  -- impossible (CmdBindD = Empty)

/-! ## Kleisli / bind homomorphism -/

theorem evalP_sample_bind {Γ τ τ'} (K : Kernel Γ τ') (k : PProg (τ' :: Γ) τ) (env : Env Γ) :
    evalP (.doBind (.sample K) k) env
    =
    WDist.bind (K env) (fun v => evalP k (v, env)) := by
  -- this is basically definitional
  simp [evalP, ProgCore.evalWith_doBind, ProbSem_handleBind_sample]

/-! ## Observe after sampling -/

theorem sample_observe_eq_cond {Γ τ} (K : Kernel Γ τ) (c : Expr (τ :: Γ) .bool)
    (k : PProg (τ :: Γ) τ) (env : Env Γ) :
    evalP (.doBind (.sample K) (.doStmt (.observe c) k)) env
    =
    WDist.bind (K env) (fun v =>
      if evalExpr c (v, env)
      then evalP k (v, env)
      else .zero) := by
  simp only [evalP, evalWith_doBind, evalWith_doStmt,
    ProbSem_handleStmt_observe, ProbSem_E_bind]
  refine congrArg (fun f => WDist.bind (K env) f) ?_
  funext v
  split
  next h => simp [WDist.bind]
  next h =>
    simp_all only [Bool.not_eq_true]
    rfl

/-! ## Mass properties -/
theorem mass_evalP_ret {Γ τ} (e : Expr Γ τ) (env : Env Γ) :
    WDist.mass (evalP (.ret e) env) = 1 := by
  simp only [WDist.mass, evalP, evalWith_ret, ProbSem_E_pure, WDist.pure,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]

theorem mass_evalP_observe_le {Γ τ} (c : Expr Γ .bool) (k : PProg Γ τ) (env : Env Γ) :
    WDist.mass (evalP (.doStmt (.observe c) k) env) ≤ WDist.mass (evalP k env) := by
  by_cases h : evalExpr c env <;> simp [evalP_observe, h, WDist.mass]

/-! ## Observe true/false -/

theorem observe_true {Γ τ} (k : PProg Γ τ) :
    (fun env => evalP (.doStmt (.observe (Expr.constBool true)) k) env)
    =
    (fun env => evalP k env) := by
  funext env
  simp [evalP_observe, evalExpr]

theorem observe_false {Γ τ} (k : PProg Γ τ) :
    (fun env => evalP (.doStmt (.observe (Expr.constBool false)) k) env)
    =
    (fun _ => .zero) := by
  funext env
  simp [evalP_observe, evalExpr]

/-! ## Sample from Dirac / Zero -/

theorem sample_dirac_eq_letDet {Γ τ τ'} (e : Expr Γ τ') (k : PProg (τ' :: Γ) τ) :
    (fun env => evalP (.doBind (.sample (fun env' => WDist.pure (evalExpr e env'))) k) env)
    =
    (fun env => evalP (.letDet e k) env) := by
  funext env
  -- outer doBind becomes bind (pure (evalExpr e env)) ...
  simp [evalP, ProgCore.evalWith_doBind, ProbSem_handleBind_sample,
        ProgCore.evalWith_letDet]

theorem sample_zero {Γ τ τ'} (k : PProg (τ' :: Γ) τ) :
    (fun env => evalP (.doBind (.sample (fun _ => WDist.zero)) k) env)
    =
    (fun _ => WDist.zero) := by
  funext env
  simp [evalP, ProgCore.evalWith_doBind, ProbSem_handleBind_sample]

end ProbLet
