import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

import Vegas.WDist
import Vegas.WDistLemmas
import Vegas.ProbLet
import Vegas.ProbLetLemmas

namespace ProbLet

open MeasureTheory ENNReal

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
def ProgEq {Γ τ} [MeasurableSpace (Val τ)] (p q : PProg Γ τ) : Prop :=
  ∀ env, MeasEq (evalP p env) (evalP q env)

infix:50 " ≈ " => ProgEq

end Definitions


/-- Canonical “zero program”: sample from the zero kernel, then return the sampled value.
This has type `PProg Γ τ` for any `Γ τ`. -/
def zeroProg {Γ : Ctx} {τ : Ty} : PProg Γ τ :=
  ProgCore.Prog.doBind
    (.sample (fun _ : Env Γ => (WDist.zero : WDist (Val τ))))
    (.ret (Expr.var Var.vz))

section

variable {Γ : Ctx} {τ : Ty}

@[simp] lemma evalP_zeroProg (env : Env Γ) :
    evalP (zeroProg (τ := τ)) env = (WDist.zero : WDist (Val τ)) := by
  -- unfold and reduce doBind to WDist.bind, then bind_zero_left
  simp [zeroProg, evalP_sample_bind]

@[simp] lemma toMeasure_evalP_zeroProg [MeasurableSpace (Val τ)] (env : Env Γ) :
    (evalP (zeroProg (τ := τ)) env).toMeasure = 0 := by
  simp [evalP_zeroProg]
  rfl

end

section Equivalence

variable {Γ τ} [MeasurableSpace (Val τ)]

@[refl] theorem ProgEq.refl (p : PProg Γ τ) : p ≈ p :=
  fun _ => rfl

@[symm] theorem ProgEq.symm {p q : PProg Γ τ} (h : p ≈ q) : q ≈ p :=
  fun env => (h env).symm

@[trans] theorem ProgEq.trans {p q r : PProg Γ τ} (h₁ : p ≈ q) (h₂ : q ≈ r) : p ≈ r :=
  fun env => (h₁ env).trans (h₂ env)

end Equivalence

/-!
## Congruence Lemmas

We prove that `ProgEq` is preserved by all program constructors.
This allows "rewriting deep inside" a program.
-/

section Congruence

variable {Γ τ τ'}
-- We need measurable spaces for return types to talk about toMeasure
variable [MeasurableSpace (Val τ)]

/-- `ret` is congruent (trivial, but useful for automation). -/
theorem ProgEq.ret {e : Expr Γ τ} : (.ret e : PProg Γ τ) ≈ (.ret e : PProg Γ τ) :=
  ProgEq.refl _

/-- `letDet` congruence. -/
theorem ProgEq.letDet (e : Expr Γ τ') (k₁ k₂ : PProg (τ' :: Γ) τ)
    (h : k₁ ≈ k₂) :
    (ProgCore.Prog.letDet e k₁) ≈ (.letDet e k₂) := by
  intro env
  simp [MeasEq, evalP, ProgCore.evalWith_letDet]
  simpa using h (env := (evalExpr e env, env))

/-- `observe` congruence. -/
theorem ProgEq.observe (c : Expr Γ .bool) (k₁ k₂ : PProg Γ τ)
    (h : k₁ ≈ k₂) :
    (ProgCore.Prog.doStmt (.observe c) k₁) ≈ (.doStmt (.observe c) k₂) := by
  intro env
  -- unfold ProgEq/MeasEq
  simp only [MeasEq, toMeasure_evalP_observe]
  -- reduce both sides by your measure lemma
  by_cases hc : evalExpr c env
  · simp only [hc, reduceIte]
    apply h
  · simp [hc]

/-- `sample` congruence.
    This is the most involved proof, requiring `toMeasure_bind`. -/
theorem ProgEq.sample (K : Kernel Γ τ') (k₁ k₂ : PProg (τ' :: Γ) τ)
    (h : k₁ ≈ k₂) :
    (ProgCore.Prog.doBind (.sample K) k₁) ≈ (.doBind (.sample K) k₂) := by
  intro env
  simp only [MeasEq]
  -- 1. Reduce evalP to WDist.bind
  rw [evalP_sample_bind, evalP_sample_bind]
  -- 2. Apply measure-theoretic bind formula (discrete integration)
  rw [WDist.toMeasure_bind, WDist.toMeasure_bind]
  -- 3. Show the integrals are equal because the continuations are equal (h)
  apply List.foldr_ext
  intro (v, w) acc h_acc
  -- The continuations match by hypothesis `h`:
  have hk : (evalP k₁ (v, env)).toMeasure = (evalP k₂ (v, env)).toMeasure := h (v, env)
  simp [hk]

end Congruence

/-!
## Algebraic Laws

Derived equations stated at the `ProgEq` level.
-/

section Laws

variable {Γ τ τ'} [MeasurableSpace (Val τ)]

/-- Sample from Dirac is equivalent to letDet. -/
theorem ProgEq.sample_dirac_letDet (e : Expr Γ τ') (k : PProg (τ' :: Γ) τ) :
    (ProgCore.Prog.doBind (.sample (fun env => WDist.pure (evalExpr e env))) k)
    ≈
    (.letDet e k) := by
  intro env
  -- We already have this at the WDist level (extensional equality of lists)
  -- so it certainly holds at measure level.
  have := sample_dirac_eq_letDet (Γ := Γ) (τ := τ) e k
  rw [congrFun this env]
  rfl

/-- Sampling from the zero kernel yields the zero program, regardless of continuation. -/
theorem ProgEq.sample_zero (k : PProg (τ' :: Γ) τ) :
    ProgEq
      (ProgCore.Prog.doBind (.sample (fun _ : Env Γ => (WDist.zero : WDist (Val τ')))) k)
      (zeroProg (τ := τ)) := by
  intro env
  simp [MeasEq, evalP_sample_bind, zeroProg]

/-- Observe fusion: `observe c₁; observe c₂` ≈ `observe (c₁ && c₂)` -/
theorem ProgEq.observe_fuse
    {Γ τ} [MeasurableSpace (Val τ)]
    (c₁ c₂ : Expr Γ .bool) (k : PProg Γ τ) :
    (ProgCore.Prog.doStmt (.observe c₁) (.doStmt (.observe c₂) k))
    ≈
    (.doStmt (.observe (Expr.andBool c₁ c₂)) k) := by
  intro env
  -- unfold the observational equivalence
  dsimp [ProgEq, MeasEq]
  -- use the already-proved function equality lemma
  have hev :
      evalP (.doStmt (.observe c₁) (.doStmt (.observe c₂) k)) env
        =
      evalP (.doStmt (.observe (Expr.andBool c₁ c₂)) k) env :=
    congrFun (ProbLet.observe_fuse (Γ := Γ) (τ := τ) c₁ c₂ k) env
  -- push equality through the measure interpretation
  simp [hev]

/-- Observe true is identity. -/
theorem ProgEq.observe_true
    {Γ τ} [MeasurableSpace (Val τ)]
    (k : PProg Γ τ) :
    (.doStmt (.observe (Expr.constBool true)) k) ≈ k := by
  intro env
  dsimp [ProgEq, MeasEq]
  have hev :
      evalP (.doStmt (.observe (Expr.constBool true)) k) env
        =
      evalP k env :=
    congrFun (ProbLet.observe_true (Γ := Γ) (τ := τ) k) env
  simp [hev]

/-- `observe false; k` is observationally equivalent to `zeroProg`. -/
theorem ProgEq.observe_false (k : PProg Γ τ) :
    ProgEq
      (.doStmt (.observe (Expr.constBool false)) k)
      (zeroProg (Γ := Γ) (τ := τ)) := by
  intro env
  simp [MeasEq, evalP_observe, evalExpr, zeroProg, evalP_sample_bind]

end Laws

end ProbLet
