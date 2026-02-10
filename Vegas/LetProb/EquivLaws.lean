import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Data.List.Basic

import Vegas.LetProb.WDist
import Vegas.LetProb.WDistLemmas
import Vegas.LetProb.Prob
import Vegas.LetProb.ProbLemmas

namespace Prob

open MeasureTheory ENNReal
open Prog

variable {L : Language}

/-!
# Level 3: Equational Theory for Probabilistic Programs

We define observational equivalence (`ProgEq`) via the underlying measures,
abstracting away `WDist` implementation details (list order, duplicates).
-/

section Definitions

variable {α : Type*}

/-- Two distributions are measure-equivalent if they denote the same measure. -/
def MeasEq [MeasurableSpace α] (d₁ d₂ : WDist α) : Prop :=
  d₁.toMeasure = d₂.toMeasure

infix:50 " ≈ₘ " => MeasEq

/-- Two programs are observationally equivalent if they produce the same measure
in all environments. -/
def ProgEq {Γ τ} [MeasurableSpace (L.Val τ)] (p q : PProg Γ τ) : Prop :=
  ∀ env, MeasEq (evalP p env) (evalP q env)

infix:50 " ≈ " => ProgEq

end Definitions

/-!
## A canonical "zero program"

Sample from the zero kernel and return the sampled value. The continuation is irrelevant
since `bind zero f = zero`, but we pick the simplest well-typed one.
-/

/-- Canonical "zero program": sample from the zero kernel, then return `vz`. -/
def zeroProg {EL : ExprLaws L} {Γ : L.Ctx} {τ : L.Ty} : PProg Γ τ :=
  .doBind
    (.sample (fun _ : L.Env Γ => (WDist.zero : WDist (L.Val τ))))
    (.ret (EL.var .vz))

section

variable {Γ : L.Ctx} {τ : L.Ty}

@[simp] lemma evalP_zeroProg {EL : ExprLaws L} (env : L.Env Γ) :
    evalP (zeroProg (EL := EL)) env = (WDist.zero : WDist (L.Val τ)) := by
  -- unfold and reduce doBind to WDist.bind, then bind_zero_left
  simp [zeroProg, evalP_sample_bind]

@[simp] lemma toMeasure_evalP_zeroProg {EL : ExprLaws L} [MeasurableSpace (L.Val τ)]
    {env : L.Env Γ} :
    (evalP (zeroProg (EL := EL) (τ := τ)) env).toMeasure = 0 := by
  simp
  rfl

end

/-!
## Equivalence structure
-/

section Equivalence

variable {Γ τ} [MeasurableSpace (L.Val τ)]

@[refl] theorem ProgEq.refl (p : PProg Γ τ) : p ≈ p :=
  fun _ => rfl

@[symm] theorem ProgEq.symm {p q : PProg Γ τ} (h : p ≈ q) : q ≈ p :=
  fun env => (h env).symm

@[trans] theorem ProgEq.trans {p q r : PProg Γ τ} (h₁ : p ≈ q) (h₂ : q ≈ r) : p ≈ r :=
  fun env => (h₁ env).trans (h₂ env)

end Equivalence

/-!
## Congruence Lemmas

`ProgEq` is preserved by all program constructors.
-/

section Congruence

variable {Γ τ τ'}
variable [MeasurableSpace (L.Val τ)]

/-- `ret` is congruent (trivial, but useful for automation). -/
theorem ProgEq.ret {e : L.Expr Γ τ} : (.ret e : PProg Γ τ) ≈ (.ret e : PProg Γ τ) :=
  ProgEq.refl _

/-- `letDet` congruence. -/
theorem ProgEq.letDet (e : L.Expr Γ τ') (k₁ k₂ : PProg (τ' :: Γ) τ)
    (h : k₁ ≈ k₂) :
    (Prog.Prog.letDet e k₁) ≈ (.letDet e k₂) := by
  intro env
  -- unfold ProgEq/MeasEq and the evaluator for letDet
  simp [MeasEq, evalP, Prog.evalWith_letDet]
  -- reduce to the hypothesis in the extended environment
  simpa using h (env := (L.eval e env, env))

/-- `observe` congruence. -/
theorem ProgEq.observe (c : L.Expr Γ L.bool) (k₁ k₂ : PProg Γ τ)
    (h : k₁ ≈ k₂) :
    (Prog.Prog.doStmt (.observe c) k₁) ≈ (.doStmt (.observe c) k₂) := by
  intro env
  -- reduce both sides by the measure-level observe lemma
  simp only [MeasEq, toMeasure_evalP_observe]
  by_cases hc : L.toBool (L.eval c env)
  · simp only [hc, ↓reduceIte]
    exact h env
  · simp [hc]

/-!
`sample` congruence is the only one that genuinely needs a fold/measure argument.
We avoid relying on a nonstandard `List.foldr_ext` and prove equality by induction
on the kernel support list.
-/
private lemma foldr_congr
    {α β : Type*} (ws : List α) (f g : α → β → β) (z : β)
    (hfg : ∀ a b, f a b = g a b) :
    List.foldr f z ws = List.foldr g z ws := by
  induction ws with
  | nil => simp
  | cons a ws ih =>
      simp [List.foldr, hfg, ih]

/-- `sample` congruence. -/
theorem ProgEq.sample (K : Kernel Γ τ') (k₁ k₂ : PProg (τ' :: Γ) τ)
    (h : k₁ ≈ k₂) :
    (Prog.Prog.doBind (.sample K) k₁) ≈ (.doBind (.sample K) k₂) := by
  classical
  intro env
  -- reduce evalP to WDist.bind
  simp only [MeasEq]
  rw [evalP_sample_bind, evalP_sample_bind]
  -- convert bind to foldr measure integration
  rw [WDist.toMeasure_bind, WDist.toMeasure_bind]
  -- the foldr steps coincide pointwise because continuations coincide pointwise
  refine foldr_congr (ws := (K env).weights)
    (f := fun (vw : (L.Val τ' × NNReal)) μ =>
      μ + (vw.2 : ℝ≥0∞) • (evalP k₁ (vw.1, env)).toMeasure)
    (g := fun (vw : (L.Val τ' × NNReal)) μ =>
      μ + (vw.2 : ℝ≥0∞) • (evalP k₂ (vw.1, env)).toMeasure)
    (z := (0 : Measure (L.Val τ))) ?_
  intro vw μ
  -- use hypothesis at environment (v, env)
  have hk : (evalP k₁ (vw.1, env)).toMeasure = (evalP k₂ (vw.1, env)).toMeasure :=
    h (vw.1, env)
  simp [hk]

end Congruence

/-!
## Algebraic Laws at the `ProgEq` level
-/

section Laws

variable {Γ τ τ'} [MeasurableSpace (L.Val τ)]

/-- Sample from Dirac is equivalent to letDet. -/
theorem ProgEq.sample_dirac_letDet (e : L.Expr Γ τ') (k : PProg (τ' :: Γ) τ) :
    (Prog.Prog.doBind (.sample (fun env => WDist.pure (L.eval e env))) k)
    ≈
    (.letDet e k) := by
  intro env
  -- we already have a WDist-level equality lemma; push it through `toMeasure`
  have hev :
      evalP (.doBind (.sample (fun env' => WDist.pure (L.eval e env'))) k) env
        =
      evalP (.letDet e k) env :=
    congrFun (Prob.sample_dirac_eq_letDet e k) env
  -- convert to measure equality
  simp [MeasEq, hev]

variable (EL : ExprLaws L)

/-- Sampling from the zero kernel yields `zeroProg`, regardless of continuation. -/
theorem ProgEq.sample_zero (k : PProg (τ' :: Γ) τ) :
    ProgEq
      (Prog.Prog.doBind (.sample (fun _ : L.Env Γ => (WDist.zero : WDist (L.Val τ')))) k)
      (zeroProg (EL := EL) (Γ := Γ) (τ := τ)) := by
  intro env
  simp [MeasEq, evalP_sample_bind, zeroProg]

/-- Observe fusion: `observe c₁; observe c₂` ≈ `observe (c₁ && c₂)` -/
theorem ProgEq.observe_fuse
    {Γ : L.Ctx} {τ : L.Ty} [MeasurableSpace (L.Val τ)]
    (c₁ c₂ : L.Expr Γ L.bool) (k : PProg Γ τ) :
    (Prog.Prog.doStmt (.observe c₁) (.doStmt (.observe c₂) k))
    ≈
    (.doStmt (.observe (EL.andBool c₁ c₂)) k) := by
  intro env
  -- reduce to equality of evalP, then push through toMeasure
  have hev :
      evalP (.doStmt (.observe c₁) (.doStmt (.observe c₂) k)) env
        =
      evalP (.doStmt (.observe (EL.andBool c₁ c₂)) k) env :=
    congrFun (Prob.observe_fuse EL) env
  simp [MeasEq, hev]

/-- Observe true is identity. -/
theorem ProgEq.observe_true
    {Γ τ} [MeasurableSpace (L.Val τ)]
    (k : PProg Γ τ) :
    (.doStmt (.observe (EL.constBool true)) k) ≈ k := by
  intro env
  have hev :
      evalP (.doStmt (.observe (EL.constBool true)) k) env
        =
      evalP k env :=
    congrFun (Prob.observe_true EL k) env
  simp [MeasEq, hev]

/-- `observe false; k` is observationally equivalent to `zeroProg`. -/
theorem ProgEq.observe_false {Γ τ} [MeasurableSpace (L.Val τ)] (k : PProg Γ τ) :
    ProgEq
      (.doStmt (.observe (EL.constBool false)) k)
      (zeroProg (EL := EL)) := by
  intro env
  -- Left side becomes WDist.zero by evalP_observe + constBool law.
  have hfalse : L.toBool (L.eval (EL.constBool false) env) = false :=
    EL.toBool_eval_constBool (b := false) (env := env)
  -- Right side is WDist.zero by evalP_zeroProg.
  simp [MeasEq, evalP_observe, hfalse, zeroProg, evalP_sample_bind]


end Laws

end Prob
