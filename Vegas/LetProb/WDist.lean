import Mathlib.Data.List.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Vegas.LetProb.WeightModel

open MeasureTheory ENNReal NNReal

/-- The Computational Core:
  Pure data, parametric over a weight semiring `W`.
  No MeasureTheory dependencies in the structure itself.
-/
structure WDist (W : Type*) (α : Type*) where
  weights : List (α × W)
  deriving Inhabited

namespace WDist

variable {W : Type*} {α : Type*}

section Syntax

variable [Semiring W]

/-- Total mass calculated via simple list summation. Computable. -/
def mass (d : WDist W α) : W :=
  (d.weights.map Prod.snd).sum

/-- Hard Rejection (Observation) using a boolean predicate. -/
def observe (p : α → Bool) (d : WDist W α) : WDist W α :=
  { weights := d.weights.filter (fun (x, _) => p x) }

section Eff

def pure (x : α) : WDist W α := { weights := [(x, 1)] }

def zero : WDist W α := { weights := [] }

def bind {β : Type*} (d : WDist W α) (f : α → WDist W β) : WDist W β :=
  { weights :=
      d.weights.flatMap (fun (a,w) =>
        (f a).weights.map (fun (b,w') => (b, w * w'))) }

def fail : WDist W α := zero

def map {β : Type*} (f : α → β) (d : WDist W α) : WDist W β :=
  { weights := d.weights.map (fun (a,w) => (f a, w)) }

instance : Monad (WDist W) where
  pure := pure
  bind := bind

end Eff

/-- Safe Normalization:
  Returns `some` if mass > 0, `none` otherwise.
  Returns a `WDist` (still a list), not a Measure yet.
  Useful for the interpreter loop.
-/
noncomputable def normalize? (d : WDist W α) [Inv W] [DecidableEq W] :
    Option (WDist W α) :=
  let m := d.mass
  if m = 0 then none
  else
    some { weights := d.weights.map (fun (x, w) => (x, w * m⁻¹)) }

end Syntax

section Semantics

variable [WeightModel W] [MeasurableSpace α]

/-- Converts the list to a Measure.
  This is the "Meaning" of the WDist.
-/
noncomputable def toMeasure (d : WDist W α) : Measure α :=
  d.weights.foldr (fun (x, w) μ => μ + (WeightModel.toENNReal w) • Measure.dirac x) 0

/-! ## 3. Verification Lemmas (The "Useful" Part) -/

/-- `observe` corresponds to `Measure.restrict`.
  Note: Requires the set `{x | p x}` to be measurable.
-/
theorem observe_eq_restrict (d : WDist W α) (p : α → Bool)
    (h_meas : MeasurableSet {x | p x}) :
    (d.observe p).toMeasure = d.toMeasure.restrict {x | p x} := by
  classical
  -- name the predicate-set and its measurability
  let s : Set α := {x | p x}
  have hs : MeasurableSet s := by simpa [s] using h_meas
  -- two helper lemmas about restricting a Dirac measure
  have dirac_restrict_of_mem (x : α) (hx : x ∈ s) :
      (Measure.dirac x).restrict s = Measure.dirac x := by
    ext t ht
    -- both sides are evaluated on measurable sets t
    -- LHS = dirac x (t ∩ s), RHS = dirac x t
    simp [ht, hs]
    by_cases hxt : x ∈ t <;> simp [hx, hxt]
  have dirac_restrict_of_not_mem (x : α) (hx : x ∉ s) :
      (Measure.dirac x).restrict s = 0 := by
    ext t ht
    have : x ∉ t ∩ s := fun h => hx h.2
    by_cases hxt : x ∈ t <;> simp [ht, hs, this]
  -- now prove the main statement by induction on the list
  cases d with
  | mk ws =>
    -- unfold observe/toMeasure for this concrete list
    revert hs
    simp_all only [toMeasure, observe]
    induction ws with
    | nil =>
        intro hs
        simp
    | cons head tail ih =>
        intro hs
        rcases head with ⟨x, w⟩
        -- split on whether the head element is kept by observe
        by_cases hp : p x = true
        · have hx : x ∈ s := by simpa [s, Set.mem_setOf_eq] using hp
          simp [hp, Measure.restrict_add, Measure.restrict_smul, s,
                dirac_restrict_of_mem x hx]
          -- goal is exactly "add (w • dirac x)" to both sides of IH
          have ih' := ih hs
          have := congrArg (fun μ : Measure α =>
            μ + (WeightModel.toENNReal w) • Measure.dirac x) ih'
          simpa [add_assoc] using this
        · have hx : x ∉ s := by
            -- membership in s is (p x = true)
            simpa [s, Set.mem_setOf_eq] using hp
          -- head is dropped; on RHS its restricted dirac becomes 0
          simp_all only [Bool.false_eq_true, not_false_eq_true,
            List.filter_cons_of_neg, List.foldr_cons, Measure.restrict_add, Measure.restrict_smul,
            smul_zero, add_zero, s]

/-- The computational mass matches the measure-theoretic mass.
-/
theorem mass_eq_toMeasure_univ (d : WDist W α) :
  WeightModel.toENNReal d.mass = d.toMeasure Set.univ := by
  rw [mass, toMeasure]
  induction d.weights with
  | nil => simp
  | cons head tail ih =>
    simp only [List.map_cons, List.sum_cons, List.foldr_cons]
    rw [WeightModel.toENNReal_add, Measure.add_apply, ih]
    simp_all only [Measure.smul_apply, measure_univ, smul_eq_mul]
    grind only

/-- Lifts to ProbabilityMeasure cleanly.
  Now takes an explicit hypothesis about the *computational* mass.
-/
noncomputable def toProbabilityMeasure (d : WDist W α)
  (h_nonzero : d.mass ≠ 0) : ProbabilityMeasure α :=
  let μ := d.toMeasure
  let c : ℝ≥0∞ := WeightModel.toENNReal d.mass
  let μ_norm := c⁻¹ • μ
  { val := μ_norm,
    property := by
      constructor
      · simp_all only [ne_eq, Measure.smul_apply, smul_eq_mul, μ_norm, c, μ]
        -- Use the lemma we proved above to bridge mass -> measure
        rw [← mass_eq_toMeasure_univ]
        change c⁻¹ * c = 1
        apply ENNReal.inv_mul_cancel
        · exact WeightModel.toENNReal_ne_zero h_nonzero
        · exact WeightModel.toENNReal_ne_top d.mass }

end Semantics

variable {β : Type*} [Semiring W]

@[simp] lemma bind_pure (x : α) (f : α → WDist W β) :
    WDist.bind (WDist.pure x) f = f x := by
  simp [WDist.bind, WDist.pure]

@[simp] lemma bind_zero (f : α → WDist W β) :
    WDist.bind (WDist.zero : WDist W α) f = WDist.zero := by
  rfl

/-- Uniform distribution over a finite list. Empty list gives zero. -/
noncomputable def uniform [Inv W] (xs : List α) : WDist W α :=
  match xs.length with
  | 0 => .zero
  | n+1 => ⟨xs.map (fun a => (a, (↑(n + 1) : W)⁻¹))⟩

end WDist
