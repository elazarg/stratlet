import distilled.Vegas
import distilled.GameSemantics
import GameTheory.OutcomeKernel

/-!
# Monadic bridge: WDist → PMF

Vegas's `outcomeDist` produces `WDist (Player → Int)` — structurally a monadic
computation. This file connects them via a structure-preserving map `WDist.toPMF`.

Note: constructing a valid `PMF` from a `WDist` requires the weights to sum to 1
(as `ℝ≥0∞`). The `HasSum` proof is provided as sorry for now — it holds for
well-formed distributions produced by game evaluation.
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
-- § 3. WDist → PMF (requires well-formedness)
-- ============================================================================

-- TODO: Define WDist.toPMF once WDist well-formedness (weights sum to 1) is formalized.
-- The bridge requires: given WDist with rational weights summing to 1,
-- construct PMF by converting weights to ℝ≥0∞ and proving HasSum.

-- ============================================================================
-- § 4. Vegas outcome kernel (statement)
-- ============================================================================

-- Vegas program as an outcome kernel: Profile → PMF (Payoff Player).
-- Requires well-formedness of the distribution produced by outcomeDist.
-- noncomputable def Vegas.toKernel (p : Prog Γ) (env : Env Γ) :
--     GameTheory.Kernel Profile (GameTheory.Payoff Player) :=
--   fun σ => (outcomeDist σ p env).toPMF.map (fun f i => (f i : ℝ))
