import distilled.Vegas
import distilled.GameSemantics
import GameTheory.Probability

/-!
# Monadic bridge: FDist → PMF

Vegas's `outcomeDist` produces `FDist Outcome` — a Finsupp-based weighted
distribution over outcomes. This file connects them to probability theory
via `FDist.toPMF`.

Note: constructing a valid `PMF` from an `FDist` requires the weights to sum
to 1 (as `ℝ≥0∞`). The `outcomeDist_totalWeight_eq_one` theorem guarantees this
when all distributions are normalized.
-/

-- ============================================================================
-- § 1. NNRat → NNReal cast
-- ============================================================================

/-- Canonical embedding ℚ≥0 → ℝ≥0. -/
noncomputable def NNRat.toNNReal (q : ℚ≥0) : NNReal :=
  ⟨((q : ℚ) : ℝ), by exact_mod_cast q.coe_nonneg⟩

-- ============================================================================
-- § 2. NNRat.toNNReal preserves algebraic structure
-- ============================================================================

theorem NNRat.toNNReal_one : NNRat.toNNReal 1 = 1 := by
  unfold NNRat.toNNReal; ext; push_cast; ring

theorem NNRat.toNNReal_mul (a b : ℚ≥0) :
    NNRat.toNNReal (a * b) = NNRat.toNNReal a * NNRat.toNNReal b := by
  unfold NNRat.toNNReal; ext; push_cast; ring

-- ============================================================================
-- § 3. FDist → PMF (sketch, requires normalization proof)
-- ============================================================================

-- TODO: Define FDist.toPMF once `outcomeDist_totalWeight_eq_one` is proved.
-- The bridge requires: given FDist with weights summing to 1,
-- construct PMF by converting weights via NNRat.toNNReal → NNReal → ENNReal
-- and proving HasSum.

-- ============================================================================
-- § 4. Vegas outcome kernel (statement)
-- ============================================================================

-- Vegas program as an outcome kernel: Profile → PMF Outcome.
-- Requires NormalizedDists p and Profile.NormalizedOn σ p
-- to guarantee the FDist output is a valid PMF.
-- noncomputable def Vegas.toKernel (p : Prog Γ) (env : Env Γ) :
--     GameTheory.Kernel Profile Outcome :=
--   fun σ => (outcomeDist σ p env).toPMF
