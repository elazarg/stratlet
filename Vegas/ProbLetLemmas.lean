import Mathlib.Data.Rat.Init
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic

import Vegas.ProbLet
import Vegas.ProgCore
import Vegas.WDist
import Vegas.Env
import Vegas.Expr

import Vegas.ProgCoreLemmas
import Vegas.WDistLemmas

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

variable {Γ : Ctx} {τ τ' : Ty}
variable [MeasurableSpace (Val τ)]

/-- `evalP` of a return produces a Dirac measure: certain outcome, no mass loss.

Corresponds to Borgström et al.'s rule:
  A⟦V⟧ = pure (λ s. (s, V⟦V⟧ s))
specialized to closed evaluation without state threading. -/
theorem toMeasure_evalP_ret [MeasurableSingletonClass (Val τ)]
    (e : Expr Γ τ) (env : Env Γ) :
    (evalP (.ret e) env).toMeasure = Measure.dirac (evalExpr e env) := by
  simp [evalP, ProgCore.evalWith_ret, WDist.toMeasure, WDist.pure]

/-- `evalP` through sampling decomposes as discrete integration: the output
measure is the weighted sum of continuation measures, integrated over the
sampling kernel's support.

This is the compositional heart of the measure transformer semantics.
It corresponds to Borgström et al.'s rule:
  A⟦random D(V)⟧ = extend (λ s. µ_{D(V⟦V⟧ s)})
specialized to discrete kernels, where `extend` becomes `WDist.bind` and
integration becomes weighted summation over the kernel's finite support. -/
theorem toMeasure_evalP_sample [MeasurableSpace (Val τ')]
    (K : Kernel Γ τ') (k : PProg (τ' :: Γ) τ) (env : Env Γ) :
    (evalP (.doBind (.sample K) k) env).toMeasure =
      (K env).weights.foldr
        (fun (v, w) μ => μ + (w : ENNReal) • (evalP k (v, env)).toMeasure) 0 := by
  simpa [evalP_sample_bind] using
    (WDist.toMeasure_bind (d := K env) (f := fun v => evalP k (v, env)))

/-- `evalP` through observe either preserves or kills the measure, depending on
the boolean condition.

Corresponds to Borgström et al.'s observe combinator:
  observe p µ A = µ(A ∩ {x | p(x) = 0_b})
specialized to boolean predicates, where observe is simply filtering. -/
theorem toMeasure_evalP_observe
    (c : Expr Γ .bool) (k : PProg Γ τ) (env : Env Γ) :
    (evalP (.doStmt (.observe c) k) env).toMeasure =
      if evalExpr c env then (evalP k env).toMeasure else 0 := by
  by_cases h : evalExpr c env
  · -- condition true
    simp [evalP_observe, h]
  · -- condition false
    -- evalP_observe gives WDist.zero; toMeasure_zero turns that into 0
    simp [evalP_observe, h, WDist.toMeasure_zero]

/-- The posterior distribution for a closed probabilistic program.

Given a closed program `p : PProg [] τ` whose evaluation has nonzero mass
(i.e., at least one valid execution path exists), the posterior is the
normalized output distribution.

This is the Vegas analogue of Borgström et al. (2013), Theorem 3.3:
for discrete Fun (Bernoulli Fun),

    P_M[value = V | valid] = A⟦M⟧(δ_())(V) / |A⟦M⟧(δ_())|

Here `evalP p ()` plays the role of A⟦M⟧(δ_()), and normalization via
`toProbabilityMeasure` yields the posterior. -/
noncomputable def posterior (p : PProg [] τ)
    (h : (evalP p ()).mass ≠ 0) : ProbabilityMeasure (Val τ) :=
  (evalP p ()).toProbabilityMeasure h

/-- The posterior measure is the evalP output scaled by the inverse total mass.

Concretely, for any measurable set B:
    posterior(B) = evalP(...).toMeasure(B) / evalP(...).toMeasure(Univ)
which is exactly the conditional probability P[value ∈ B | valid]. -/
theorem posterior_apply (p : PProg [] τ)
    (h : (evalP p ()).mass ≠ 0) (B : Set (Val τ)) :
    (posterior p h).val B =
      (evalP p ()).toMeasure B * ((evalP p ()).mass : ENNReal)⁻¹ := by
  simp [posterior, WDist.toProbabilityMeasure, mul_comm]

/-- The posterior of the full space is 1 (it is a probability measure).
This is a direct consequence of the construction, included for clarity. -/
theorem posterior_univ (p : PProg [] τ)
    (h : (evalP p ()).mass ≠ 0) :
    (posterior p h).val Set.univ = 1 := by
  simp [posterior]

end MeasureSemantics

/-!
# Roadmap Notes: From “measure semantics” to a real *calculus* (Level 3/4)

These notes pin down what we mean by:

- **Level 3**: a probabilistic *calculus* (equational theory / contextual reasoning),
- **Level 4**: a connection to Borgström et al. (2013) measure-transformer semantics.

They are intentionally *checklist-style* (acceptance criteria + suggested lemma names)
so the goalposts don’t move during refactors.

## Current status (Level 1–2 already achieved)
We currently have a compositional evaluator
  evalP : PProg Γ τ → Env Γ → WDist (Val τ)
and a meaning function
  WDist.toMeasure : WDist α → Measure α

Together with bridge lemmas:
- return ↦ dirac (toMeasure_evalP_ret)
- sample ↦ discrete integration / weighted sum (toMeasure_evalP_sample via WDist.toMeasure_bind)
- observe ↦ keep-or-kill (toMeasure_evalP_observe)
  and also restriction at WDist level (observe_eq_restrict)
- posterior normalization when mass ≠ 0 (posterior_apply, posterior_univ)

Scope note: this is a **finite-support discrete** semantics.

------------------------------------------------------------------------------

## Level 3: Equational theory / contextual equivalence (“a real calculus”)

### Goal
Define a *program equivalence* that is stable under contexts (a congruence),
and build a library of derived laws stated at the measure level (not list-level).
This is the point where we can claim “calculus” rather than “interpreter.”

### 3.1. Define the notion of observational equivalence
We need an equality notion that forgets list representation details.

Recommended:
  def MeasEq (d₁ d₂ : WDist α) : Prop := d₁.toMeasure = d₂.toMeasure

Then define program equivalence:
  def ProgEq (p q : PProg Γ τ) : Prop :=
    ∀ env, (evalP p env).toMeasure = (evalP q env).toMeasure

(Optionally: use = of WDist if you canonicalize weights, but **do not**
tie “program equivalence” to list order/multiplicity unless you want that.)

Acceptance:
- `ProgEq` is an equivalence relation (refl/symm/trans).
  lemma names:
    progEq_refl, progEq_symm, progEq_trans

### 3.2. Congruence under syntax (context closure)
Prove `ProgEq` is preserved by each constructor (the “congruence lemmas”):

- ret congruence is trivial.
- letDet congruence:
    if k₁ ≈ k₂ pointwise, then letDet e k₁ ≈ letDet e k₂
- doStmt(.observe c) congruence:
    if k₁ ≈ k₂ then observe c k₁ ≈ observe c k₂
- doBind(.sample K) congruence:
    if k₁ ≈ k₂ then sample K k₁ ≈ sample K k₂

Suggested lemma names:
  progEq_letDet, progEq_observe, progEq_sample

(If you later add more constructs, you add the corresponding congruence lemma.)

Acceptance:
- A single theorem:
    theorem ProgEq.congr : (∀ subterms, ...) → ProgEq (C[subterms]) (C[subterms'])
  but in Lean it’s often best to keep this as per-constructor lemmas.

### 3.3. Beta/eta laws and derived equations (measure-level)
Once congruence exists, add the “algebra” laws as *theorems about ProgEq*:

Core laws:
- sample from Dirac equals letDet (already have evalP-level: sample_dirac_eq_letDet)
  restate as ProgEq:
    progEq_sample_dirac_letDet
- sample from zero kills (sample_zero)
- observe fusion (observe_fuse)
- observe true/false (observe_true, observe_false)

Crucially: state them as `ProgEq` theorems (or pointwise measure equalities),
so they remain stable if WDist list representation changes.

Acceptance:
- A small `namespace ProbLet.Laws` with ~10 lemmas that allow rewriting
  programs symbolically, and each lemma has a `by funext env; ...` proof.

### 3.4. A “substitution” lemma (usually the first nontrivial one)
You will eventually want a lemma that feels like:
- “replace a subprogram with an equivalent one inside a larger program.”

This is essentially a corollary of congruence, but it helps usage.

Suggested:
  theorem replace {p q : PProg Γ τ} (h : ProgEq p q) :
      ProgEq (Context.apply C p) (Context.apply C q)

This may require defining an explicit context datatype; optional,
but very useful for rewriting proofs.

### 3.5. Canonicalization (optional but can simplify life)
If you keep WDist as list-of-weighted outcomes, you may want
a `normalizeWeights`/`combine` function that merges equal outcomes
so that WDist equality becomes less brittle.

Important: do **not** bake this into semantics unless you want it.
Instead: provide lemma
  toMeasure (combine d) = toMeasure d
so program equivalence continues to use `toMeasure`.
-/

end ProbLet
