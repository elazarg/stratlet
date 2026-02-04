import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Data.NNReal.Basic

open MeasureTheory ENNReal NNReal

/-- The Computational Core:
  A finite weighted distribution represented as an explicit list of outcomes and weights.
  This is the "Syntax" of your DSL.
-/
structure WDist (α : Type*) where
  weights : List (α × ℝ≥0)
  deriving Inhabited

namespace WDist

variable {α : Type*} [MeasurableSpace α]

/-- The Semantic Bridge:
  Converts the computational `WDist` into a standard Mathlib `Measure`.
  It maps each element to a Dirac measure scaled by its weight.
-/
noncomputable def toMeasure (d : WDist α) : Measure α :=
  d.weights.foldr (fun (x, w) μ => μ + (w : ℝ≥0∞) • Measure.dirac x) 0

/-- Lemma: The measure is finite. -/
lemma toMeasure_isFiniteMeasure (d : WDist α) : IsFiniteMeasure d.toMeasure := by
  refine { measure_univ_lt_top := ?_ }
  rw [toMeasure]
  induction d.weights with
  | nil => simp
  | cons head tail ih => simp_all only [List.foldr_cons,
      Measure.coe_add, Measure.coe_smul,
      Pi.add_apply, Pi.smul_apply,
      measure_univ, smul_eq_mul, mul_one, add_lt_top, coe_lt_top, and_self]

/-- Total mass of the distribution -/
noncomputable def mass (d : WDist α) : ℝ≥0∞ :=
  d.toMeasure Set.univ

/-- Observation (Hard Rejection) -/
def observe (p : α → Bool) (d : WDist α) : WDist α :=
  { weights := d.weights.filter (fun (x, _) => p x) }

/-- Normalization:
  Manually scales the measure by (1 / mass).
  Returns a `ProbabilityMeasure`.
-/
noncomputable def toProbabilityMeasure (d : WDist α)
  (h_nonzero : d.mass ≠ 0) : ProbabilityMeasure α :=
  let μ := d.toMeasure
  let c := d.mass
  let μ_norm := c⁻¹ • μ
  { val := μ_norm,
    property := by
      constructor
      · simp_all only [ne_eq, Measure.smul_apply, smul_eq_mul, μ_norm, c, μ]
        change c⁻¹ * c = 1
        apply ENNReal.inv_mul_cancel h_nonzero
        exact (d.toMeasure_isFiniteMeasure).measure_univ_lt_top.ne }

end WDist
