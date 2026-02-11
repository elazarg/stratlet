import Mathlib.Data.NNReal.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Weight Model

Typeclass abstracting the weight type for weighted distributions.
Allows `WDist W α` to work with different weight semirings (e.g. `ℝ≥0`, `ℚ≥0`)
while providing a uniform bridge to `ℝ`, `ℝ≥0`, and `ℝ≥0∞` for measure theory and EU.
-/

open NNReal ENNReal

/-- A `WeightModel W` equips a semiring `W` with a nonneg-real interpretation.

Order on `W` is not required; ordering lemmas go through `toReal`. -/
class WeightModel (W : Type*) extends Semiring W where
  toReal : W → ℝ
  toReal_zero : toReal 0 = 0
  toReal_one : toReal 1 = 1
  toReal_add : ∀ a b, toReal (a + b) = toReal a + toReal b
  toReal_mul : ∀ a b, toReal (a * b) = toReal a * toReal b
  toReal_nonneg : ∀ w, 0 ≤ toReal w
  toReal_eq_zero : ∀ w, toReal w = 0 → w = 0

namespace WeightModel

variable {W : Type*} [WeightModel W]

/-! ## Derived conversions -/

/-- Interpret a weight as `ℝ≥0`. -/
def toNNReal (w : W) : ℝ≥0 :=
  ⟨WeightModel.toReal w, WeightModel.toReal_nonneg w⟩

/-- Interpret a weight as `ℝ≥0∞`. -/
def toENNReal (w : W) : ℝ≥0∞ :=
  (toNNReal w : ℝ≥0∞)

/-! ## Simp lemmas for `toNNReal` -/

@[simp] lemma toNNReal_zero : toNNReal (0 : W) = 0 :=
  Subtype.ext toReal_zero

@[simp] lemma toNNReal_one : toNNReal (1 : W) = 1 :=
  Subtype.ext toReal_one

@[simp] lemma toNNReal_add (a b : W) :
    toNNReal (a + b) = toNNReal a + toNNReal b :=
  Subtype.ext (toReal_add a b)

@[simp] lemma toNNReal_mul (a b : W) :
    toNNReal (a * b) = toNNReal a * toNNReal b :=
  Subtype.ext (toReal_mul a b)

@[simp] lemma toNNReal_val (w : W) :
    (toNNReal w).val = WeightModel.toReal w := rfl

/-! ## Simp lemmas for `toENNReal` -/

@[simp] lemma toENNReal_zero : toENNReal (0 : W) = 0 := by
  simp [toENNReal]

@[simp] lemma toENNReal_one : toENNReal (1 : W) = 1 := by
  simp [toENNReal]

@[simp] lemma toENNReal_add (a b : W) :
    toENNReal (a + b) = toENNReal a + toENNReal b := by
  simp [toENNReal, ENNReal.coe_add]

@[simp] lemma toENNReal_mul (a b : W) :
    toENNReal (a * b) = toENNReal a * toENNReal b := by
  simp [toENNReal, ENNReal.coe_mul]

lemma toENNReal_ne_top (w : W) : toENNReal w ≠ ⊤ :=
  ENNReal.coe_lt_top.ne

lemma toNNReal_eq_zero_iff (w : W) : toNNReal w = 0 ↔ w = 0 := by
  constructor
  · intro h
    apply toReal_eq_zero
    have := congrArg Subtype.val h
    simpa [toNNReal] using this
  · intro h; subst h; exact toNNReal_zero

lemma toENNReal_eq_zero_iff (w : W) : toENNReal w = 0 ↔ w = 0 := by
  simp [toENNReal, ENNReal.coe_eq_zero, toNNReal_eq_zero_iff]

lemma toENNReal_ne_zero {w : W} (h : w ≠ 0) : toENNReal w ≠ 0 :=
  (toENNReal_eq_zero_iff w).not.mpr h

/-! ## `toReal` simp lemmas (forwarding) -/

@[simp] lemma toReal_toNNReal (w : W) :
    (toNNReal w : ℝ) = WeightModel.toReal w := rfl

end WeightModel

/-! ## Instances -/

instance : WeightModel ℝ≥0 where
  toReal := NNReal.toReal
  toReal_zero := NNReal.coe_zero
  toReal_one := NNReal.coe_one
  toReal_add := NNReal.coe_add
  toReal_mul := NNReal.coe_mul
  toReal_nonneg := fun w => w.coe_nonneg
  toReal_eq_zero := fun _ h => NNReal.coe_eq_zero.mp h

/-! ## ℝ≥0 bridge: `toNNReal` and `toENNReal` are the identity on ℝ≥0. -/

@[simp] lemma WeightModel.toNNReal_nnreal (w : ℝ≥0) :
    WeightModel.toNNReal w = w :=
  Subtype.ext rfl

@[simp] lemma WeightModel.toENNReal_nnreal (w : ℝ≥0) :
    WeightModel.toENNReal w = (w : ℝ≥0∞) := by
  simp [WeightModel.toENNReal]
