import Mathlib.Data.List.Basic

import Vegas.LetProb.Prob
import Vegas.LetCore.Prog
import Vegas.LetProb.WDist
import Vegas.LetProb.WDistLemmas
import Vegas.LetCore.Env

import Vegas.LetCore.ProgLemmas

namespace Prob

open Prog

variable {L : Language}
variable (EL : ExprLaws L)
variable {W : Type} [WeightModel W]

/-! A few simp bridges so simp sees `WDist.bind/pure/zero`. -/

@[simp] lemma ProbSem_E_pure {α} (x : α) :
  (EffWDist (W := W)).pure x = WDist.pure x := rfl

@[simp] lemma ProbSem_E_fail {α} :
    (EffWDist (W := W)).fail = (WDist.zero : WDist W α) := rfl

@[simp] lemma ProbSem_E_bind {α β} (xs : WDist W α) (f : α → WDist W β) :
    (EffWDist (W := W)).bind xs f = WDist.bind xs f := rfl

-- lemma ProbSem_E_eq : ProbSem.E = EffWDist := rfl

/-! A very useful derived simp lemma: observe is an if-then-else at evalP level. -/
@[simp] lemma evalP_observe
    {Γ : Env.Ctx (Ty := L.Ty)} {τ : L.Ty}
    (c : L.Expr Γ L.bool) (k : PProg (W := W) Γ τ) (env : Env.Env (Val := L.Val) Γ) :
    evalP (.doStmt (.observe c) k) env
      =
    if L.toBool (L.eval c env) then evalP k env else WDist.zero := by
  by_cases h : L.toBool (L.eval c env)
  · -- h : ... = true
    simp [EffWDist, Prob.evalP, Prob.ProbSem, Prog.evalWith, Prog.evalProg_gen, h]
  · -- h : ... = false
    simp [EffWDist, Prob.evalP, Prob.ProbSem, Prog.evalWith, Prog.evalProg_gen, h]

/-! ## Observe-Fusion Law -/

theorem observe_fuse
    {Γ : Env.Ctx (Ty := L.Ty)} {τ : L.Ty}
    {c₁ c₂ : L.Expr Γ L.bool} {k : PProg (W := W) Γ τ} :
    (fun env => evalP (.doStmt (.observe c₁) (.doStmt (.observe c₂) k)) env)
    =
    (fun env => evalP (.doStmt (.observe (EL.andBool c₁ c₂)) k) env) := by
  funext env
  by_cases h1 : L.toBool (L.eval c₁ env)
  · by_cases h2 : L.toBool (L.eval c₂ env)
    · simp [evalP_observe (L := L), h1, h2, EL.toBool_eval_andBool]
    · simp [evalP_observe (L := L), h1, h2, EL.toBool_eval_andBool]
  · simp [evalP_observe (L := L), h1, EL.toBool_eval_andBool]

theorem observe_hoist_letDet
    {Γ : Env.Ctx (Ty := L.Ty)} {τ τ' : L.Ty}
    (e : L.Expr Γ τ') (c : L.Expr Γ L.bool)
    (k : PProg (W := W) (τ' :: Γ) τ) :
    (fun env =>
      evalP (.letDet e (.doStmt (.observe (EL.weaken c)) k)) env)
    =
    (fun env =>
      evalP (.doStmt (.observe c) (.letDet e k)) env) := by
  funext env
  -- unfold; the only nontrivial rewrite is the guard under the extended env
  simp [Prob.evalP, Prog.evalWith, Prog.evalProg_gen, Prob.ProbSem,
        EL.eval_weaken]

/-! ## Conservation: deterministic embeds into probabilistic -/

def embedDProg : Prog.DProg Γ τ → PProg (W := W) Γ τ
  | .ret e => .ret e
  | .letDet e k => .letDet e (embedDProg k)
  | .doBind c _ => nomatch c
  | .doStmt (.observe cond) k => .doStmt (.observe cond) (embedDProg k)

def liftOption : Option (L.Val τ) → WDist W (L.Val τ)
  | none => .zero
  | some v => .pure v

-- helpful simp for Option→WDist + Option semantics of observe
@[simp] lemma liftOption_bind_guard {α β}
    (b : Bool) (x : α) (k : α → Option (L.Val β)) :
    liftOption (Option.bind (if b then some x else none) k)
      =
    if b then liftOption (k x) else (WDist.zero : WDist W _) := by
  by_cases hb : b <;> simp [liftOption, hb]

theorem evalP_embed_eq_lift {Γ τ} (p : Prog.DProg Γ τ) (env : L.Env Γ) :
    evalP (W := W) (embedDProg p) env = liftOption (Prog.evalProgOption p env) := by
  -- structural induction on the deterministic program
  induction p with
  | ret e =>
      -- evalP ret = pure; evalProgOption ret = some
      simp [embedDProg, evalP, liftOption, Prog.evalProgOption, Prog.evalWith_ret,
            Prog.DetOptionSem, Prog.EffOption]
      rfl
  | letDet e k ih =>
      simp [embedDProg, evalP, Prog.evalProgOption,
            Prog.evalWith_letDet] at *
      -- both evaluators extend env the same way
      simpa using ih (env := (L.eval e env, env))
  | doStmt s k ih =>
      cases s with
      | observe cond =>
          by_cases h : L.toBool (L.eval cond env)
          · -- cond true
            -- LHS: evalP observe = evalP k ; RHS: Option also continues
            simp [embedDProg, evalP_observe, h, liftOption,
                  Prog.evalProgOption, Prog.evalWith_doStmt,
                  Prog.DetOptionSem, Prog.EffOption] at *
            -- reduce to IH
            simpa using ih (env := env)
          · -- cond false: both become empty/none
            simp [embedDProg, evalP_observe, h, liftOption,
                  Prog.evalProgOption, Prog.evalWith_doStmt,
                  Prog.DetOptionSem, Prog.EffOption]
            rfl
  | doBind c k =>
      cases c  -- impossible (CmdBindD = Empty)

/-! ## Kleisli / bind homomorphism -/

theorem evalP_sample_bind {Γ τ τ'}
    (K : Kernel (W := W) Γ τ') (k : PProg (W := W) (τ' :: Γ) τ) (env : L.Env Γ) :
    evalP (.doBind (.sample K) k) env
    =
    WDist.bind (K env) (fun v => evalP k (v, env)) := by
  -- this is basically definitional
  simp [evalP, Prog.evalWith_doBind, ProbSem_handleBind_sample]
  rfl

/-! ## Observe after sampling -/

theorem sample_observe_eq_cond
    {Γ : Env.Ctx (Ty := L.Ty)} {τ : L.Ty}
    (K : Kernel (W := W) Γ τ) (c : L.Expr (τ :: Γ) L.bool)
    (k : PProg (W := W) (τ :: Γ) τ) (env : Env.Env (Val := L.Val) Γ) :
    evalP (.doBind (.sample K) (.doStmt (.observe c) k)) env
    =
    WDist.bind (K env) (fun v =>
      if L.toBool (L.eval c (v, env))
      then evalP k (v, env)
      else WDist.zero) := by
  -- unfold the outer doBind semantics to WDist.bind (K env) ...
  simp only [evalP, evalWith, evalProg_gen, ProbSem, EffWDist]
  refine congrArg (fun f => WDist.bind (K env) f) ?_
  funext v
  by_cases h : L.toBool (L.eval c (v, env))
  · -- h = true: inner bind is bind (pure ()) (fun _ => X) = X
    simp [h]
  · -- h = false: inner bind is bind zero (fun _ => X) = zero
    simp [h]

/-! ## Mass properties -/
theorem mass_evalP_ret
    {Γ : Env.Ctx (Ty := L.Ty)} {τ : L.Ty}
    (e : L.Expr Γ τ) (env : Env.Env (Val := L.Val) Γ) :
    WDist.mass (evalP (W := W) (.ret e) env) = (1 : W) := by
  -- evalP ret = pure (L.eval e env)
  unfold evalP Prog.evalWith Prog.evalProg_gen
  simp [ProbSem, EffWDist, WDist.mass_pure]

theorem mass_evalP_observe_le_toReal {Γ τ}
    (c : L.Expr Γ L.bool) (k : PProg (W := W) Γ τ) (env : L.Env Γ) :
    WeightModel.toReal (WDist.mass (evalP (.doStmt (.observe c) k) env)) ≤
    WeightModel.toReal (WDist.mass (evalP k env)) := by
  by_cases h : L.toBool (L.eval c env)
  · simp [evalP_observe, h]
  · simp [evalP_observe, h, WDist.mass, WeightModel.toReal_zero]
    exact WeightModel.toReal_nonneg _

/-! ## Observe true/false -/

theorem observe_true
    {Γ : L.Ctx} {τ : L.Ty}
    (k : PProg (W := W) Γ τ) :
    (fun env => evalP (.doStmt (.observe (EL.constBool true)) k) env)
    =
    (fun env => evalP k env) := by
  funext env
  simp [evalP_observe, EL.toBool_eval_constBool]

theorem observe_false
    {Γ : L.Ctx} {τ : L.Ty}
    (k : PProg (W := W) Γ τ) :
    (fun env => evalP (.doStmt (.observe (EL.constBool false)) k) env)
    =
    (fun _ => WDist.zero) := by
  funext env
  simp [evalP_observe, EL.toBool_eval_constBool]

/-! ## Sample from Dirac / Zero -/
theorem sample_dirac_eq_letDet
    {Γ : Env.Ctx (Ty := L.Ty)} {τ τ' : L.Ty}
    (e : L.Expr Γ τ') (k : PProg (W := W) (τ' :: Γ) τ) :
    (fun env => evalP (.doBind (.sample (fun env' => WDist.pure (L.eval e env'))) k) env)
    =
    (fun env => evalP (.letDet e k) env) := by
  funext env
  -- unfold evalP and the handlers; you already got to this shape
  simp [Prob.evalP, Prob.ProbSem, Prog.evalWith, Prog.evalProg_gen, EffWDist]

theorem sample_zero
    {Γ : Env.Ctx (Ty := L.Ty)} {τ τ' : L.Ty} (k : PProg (W := W) (τ' :: Γ) τ) :
    (fun env => evalP (.doBind (.sample (fun _ => WDist.zero)) k) env)
    =
    (fun _ => WDist.zero) := by
  funext env
  simp [Prob.evalP, Prob.ProbSem, Prog.evalWith, Prog.evalProg_gen, EffWDist]

/-! ## Measure-theoretic interpretation of evalP

These theorems connect the compositional evaluator `evalP` to measure theory
via `WDist.toMeasure`, establishing the discrete analogue of the measure
transformer semantics of Borgström, Gordon, Greenberg, Margetson, and Van Gael,
"Measure Transformer Semantics for Bayesian Machine Learning"
(LMCS 9(3:11), 2013).

For a closed program `p : PProg [] τ`, the WDist `evalP p ()` encodes the
*unnormalized* posterior distribution.  Concretely:

- `(evalP p ()).mass` is the total probability of a valid run, analogous to
  Borgström et al.'s P_M[valid].
- For each value `v`, the weight of `v` in the distribution is the joint
  probability P_M[value = v ∧ valid].
- Normalizing via `WDist.toProbabilityMeasure` (when mass > 0) yields the
  posterior P_M[value = · | valid].

This correspondence is the discrete analogue of their Theorem 3.3.
Vegas's `evalP` plays the role of Fun's measure transformer semantics A⟦M⟧,
and `WDist.toProbabilityMeasure` plays the role of normalization
P[value = V | valid] = µ({V}) / |µ|.
-/

section MeasureSemantics

open MeasureTheory

variable {Γ : Env.Ctx (Ty := L.Ty)} {τ τ' : L.Ty}
variable [MeasurableSpace (L.Val τ)]

-- No MeasurableSingletonClass needed.
theorem WDist.toMeasure_pure' {α} [MeasurableSpace α] (x : α) :
    (WDist.pure x : WDist W α).toMeasure = Measure.dirac x := by
  -- pure x = [(x,1)]
  -- toMeasure folds: 0 + 1 • dirac x
  simp [WDist.pure, WDist.toMeasure, zero_add]


/-- `evalP` of a return produces a Dirac measure: certain outcome, no mass loss.

Corresponds to Borgström et al.'s rule:
  A⟦V⟧ = pure (λ s. (s, V⟦V⟧ s))
specialized to closed evaluation without state threading. -/
theorem toMeasure_evalP_ret
    {Γ : L.Ctx} {τ : L.Ty} [MeasurableSpace (L.Val τ)]
    (e : L.Expr Γ τ) (env : L.Env Γ) :
    (evalP (W := W) (.ret e) env).toMeasure = Measure.dirac (L.eval e env) := by
  -- force the `pure` to be the actual WDist.pure
  simp [Prob.evalP, Prog.evalWith, Prog.evalProg_gen, Prob.ProbSem, EffWDist,
        WDist.toMeasure_pure']

/-- `evalP` through sampling decomposes as discrete integration: the output
measure is the weighted sum of continuation measures, integrated over the
sampling kernel's support.

This is the compositional heart of the measure transformer semantics.
It corresponds to Borgström et al.'s rule:
  A⟦random D(V)⟧ = extend (λ s. µ_{D(V⟦V⟧ s)})
specialized to discrete kernels, where `extend` becomes `WDist.bind` and
integration becomes weighted summation over the kernel's finite support. -/
theorem toMeasure_evalP_sample [MeasurableSpace (L.Val τ')]
    (K : Kernel (W := W) Γ τ') (k : PProg (W := W) (τ' :: Γ) τ) (env : L.Env Γ) :
    (evalP (.doBind (.sample K) k) env).toMeasure =
      (K env).weights.foldr
        (fun (v, w) μ => μ + (WeightModel.toENNReal w) • (evalP k (v, env)).toMeasure) 0 := by
  simpa [evalP_sample_bind] using
    (WDist.toMeasure_bind (d := K env) (f := fun v => evalP k (v, env)))

/-- `evalP` through observe either preserves or kills the measure, depending on
the boolean condition.

Corresponds to Borgström et al.'s observe combinator:
  observe p µ A = µ(A ∩ {x | p(x) = 0_b})
specialized to boolean predicates, where observe is simply filtering. -/
theorem toMeasure_evalP_observe
    (c : L.Expr Γ L.bool) (k : PProg (W := W) Γ τ) (env : L.Env Γ) :
    (evalP (.doStmt (.observe c) k) env).toMeasure =
      if L.toBool (L.eval c env) then (evalP k env).toMeasure else 0 := by
  by_cases h : L.toBool (L.eval c env)
  · -- condition true
    simp [evalP_observe, h]
  · -- condition false
    simp [evalP_observe, h]
    simp_all only [Bool.not_eq_true]
    rfl

/-- The posterior distribution for a closed probabilistic program.

Given a closed program `p : PProg [] τ` whose evaluation has nonzero mass
(i.e., at least one valid execution path exists), the posterior is the
normalized output distribution.

This is the Vegas analogue of Borgström et al. (2013), Theorem 3.3:
for discrete Fun (Bernoulli Fun),

    P_M[value = V | valid] = A⟦M⟧(δ_())(V) / |A⟦M⟧(δ_())|

Here `evalP p ()` plays the role of A⟦M⟧(δ_()), and normalization via
`toProbabilityMeasure` yields the posterior. -/
noncomputable def posterior (p : PProg (W := W) [] τ)
    (h : (evalP p ()).mass ≠ 0) : ProbabilityMeasure (L.Val τ) :=
  (evalP p ()).toProbabilityMeasure h

/-- The posterior measure is the evalP output scaled by the inverse total mass.

Concretely, for any measurable set B:
    posterior(B) = evalP(...).toMeasure(B) / evalP(...).toMeasure(Univ)
which is exactly the conditional probability P[value ∈ B | valid]. -/
theorem posterior_apply (p : PProg (W := W) [] τ)
    (h : (evalP p ()).mass ≠ 0) (B : Set (L.Val τ)) :
    (posterior p h).val B =
      (evalP p ()).toMeasure B * (WeightModel.toENNReal (evalP p ()).mass)⁻¹ := by
  simp [posterior, WDist.toProbabilityMeasure, mul_comm]

/-- The posterior of the full space is 1 (it is a probability measure).
This is a direct consequence of the construction, included for clarity. -/
theorem posterior_univ (p : PProg (W := W) [] τ)
    (h : (evalP p ()).mass ≠ 0) :
    (posterior p h).val Set.univ = 1 := by
  simp [posterior]

end MeasureSemantics

end Prob
