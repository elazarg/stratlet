import Vegas.Equilibrium
import Vegas.GameProperties
import GameTheory.Concepts.BestResponse
import GameTheory.Concepts.NashProperties
import GameTheory.Concepts.NashPareto
import GameTheory.Concepts.CorrelatedEqProperties
import GameTheory.Concepts.NashCorrelatedEq
import GameTheory.Concepts.ApproximateNash

/-!
# Vegas equilibrium corollaries

Derived equilibrium theorems for Vegas programs.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Vegas Nash is equivalent to every player playing a Vegas best response. -/
theorem isNash_iff_bestResponse (g : WFProgram P L) (σ : StrategyProfile g) :
    IsNash g σ ↔ ∀ who, IsBestResponse g who σ (σ who) := by
  simpa [IsNash, IsBestResponse] using
    (KernelGame.isNash_iff_bestResponse (G := toKernelGame g) σ)

/-- Preference-parameterized Vegas Nash is equivalent to every player playing a
preference-parameterized Vegas best response. -/
theorem isNashFor_iff_bestResponseFor (g : WFProgram P L)
    (pref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (σ : StrategyProfile g) :
    IsNashFor g pref σ ↔ ∀ who, IsBestResponseFor g pref who σ (σ who) := by
  simpa [IsNashFor, IsBestResponseFor] using
    (KernelGame.isNashFor_iff_bestResponseFor (G := toKernelGame g) pref σ)

/-- Vegas Nash is exactly preference-parameterized Nash with EU preference. -/
theorem IsNash_iff_IsNashFor_eu (g : WFProgram P L) (σ : StrategyProfile g) :
    IsNash g σ ↔ IsNashFor g (euPref g) σ := by
  simpa [IsNash, IsNashFor, euPref] using
    (KernelGame.IsNash_iff_IsNashFor_eu (G := toKernelGame g) σ)

/-- Vegas dominant strategy is exactly preference-parameterized dominance with
EU preference. -/
theorem IsDominant_iff_IsDominantFor_eu (g : WFProgram P L)
    (who : P) (s : Strategy g who) :
    IsDominant g who s ↔ IsDominantFor g (euPref g) who s := by
  simpa [IsDominant, IsDominantFor, euPref] using
    (KernelGame.IsDominant_iff_IsDominantFor_eu (G := toKernelGame g) who s)

/-- Vegas best response is exactly preference-parameterized best response with
EU preference. -/
theorem IsBestResponse_iff_IsBestResponseFor_eu (g : WFProgram P L)
    (who : P) (σ : StrategyProfile g) (s : Strategy g who) :
    IsBestResponse g who σ s ↔ IsBestResponseFor g (euPref g) who σ s := by
  simpa [IsBestResponse, IsBestResponseFor, euPref] using
    (KernelGame.IsBestResponse_iff_IsBestResponseFor_eu
      (G := toKernelGame g) who σ s)

/-- Vegas strict Nash is exactly preference-parameterized strict Nash with EU
strict preference. -/
theorem IsStrictNash_iff_IsStrictNashFor_eu (g : WFProgram P L)
    (σ : StrategyProfile g) :
    IsStrictNash g σ ↔ IsStrictNashFor g (euStrictPref g) σ := by
  simpa [IsStrictNash, IsStrictNashFor, euStrictPref] using
    (KernelGame.IsStrictNash_iff_IsStrictNashFor_eu (G := toKernelGame g) σ)

/-- Vegas strict dominance is exactly preference-parameterized strict
dominance with EU strict preference. -/
theorem IsStrictDominant_iff_IsStrictDominantFor_eu (g : WFProgram P L)
    (who : P) (s : Strategy g who) :
    IsStrictDominant g who s ↔ IsStrictDominantFor g (euStrictPref g) who s := by
  simpa [IsStrictDominant, IsStrictDominantFor, euStrictPref] using
    (KernelGame.IsStrictDominant_iff_IsStrictDominantFor_eu
      (G := toKernelGame g) who s)

/-- Vegas weak dominance is exactly preference-parameterized weak dominance
with EU preference. -/
theorem WeaklyDominates_iff_WeaklyDominatesFor_eu (g : WFProgram P L)
    (who : P) (s t : Strategy g who) :
    WeaklyDominates g who s t ↔ WeaklyDominatesFor g (euPref g) who s t := by
  simpa [WeaklyDominates, WeaklyDominatesFor, euPref] using
    (KernelGame.WeaklyDominates_iff_WeaklyDominatesFor_eu
      (G := toKernelGame g) who s t)

/-- Vegas strict dominance is exactly preference-parameterized strict
dominance with EU strict preference. -/
theorem StrictlyDominates_iff_StrictlyDominatesFor_eu (g : WFProgram P L)
    (who : P) (s t : Strategy g who) :
    StrictlyDominates g who s t ↔
      StrictlyDominatesFor g (euStrictPref g) who s t := by
  simpa [StrictlyDominates, StrictlyDominatesFor, euStrictPref] using
    (KernelGame.StrictlyDominates_iff_StrictlyDominatesFor_eu
      (G := toKernelGame g) who s t)

/-- A Vegas profile of dominant strategies is a Vegas Nash equilibrium. -/
theorem dominant_is_nash (g : WFProgram P L) (σ : StrategyProfile g)
    (hdom : ∀ who, IsDominant g who (σ who)) :
    IsNash g σ := by
  simpa [IsNash, IsDominant] using
    (KernelGame.dominant_is_nash (G := toKernelGame g) σ hdom)

/-- A Vegas profile of preference-dominant strategies is preference-Nash. -/
theorem dominant_is_nash_for (g : WFProgram P L)
    (pref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (σ : StrategyProfile g)
    (hdom : ∀ who, IsDominantFor g pref who (σ who)) :
    IsNashFor g pref σ := by
  simpa [IsNashFor, IsDominantFor] using
    (KernelGame.dominant_is_nash_for (G := toKernelGame g) pref σ hdom)

/-- A Vegas dominant strategy is a Vegas best response against any profile. -/
theorem dominant_isBestResponse (g : WFProgram P L)
    (who : P) (s : Strategy g who) (σ : StrategyProfile g)
    (hdom : IsDominant g who s) :
    IsBestResponse g who σ s := by
  simpa [IsDominant, IsBestResponse] using
    (KernelGame.dominant_isBestResponse (G := toKernelGame g) who s σ hdom)

/-- Vegas Nash is equivalent to having no strictly improving unilateral
deviation. -/
theorem isNash_iff_no_improving (g : WFProgram P L) (σ : StrategyProfile g) :
    IsNash g σ ↔
      ¬ ∃ (who : P) (s' : Strategy g who),
        eu g (Function.update σ who s') who > eu g σ who := by
  simpa [IsNash, eu, Strategy] using
    (KernelGame.isNash_iff_no_improving (G := toKernelGame g) (σ := σ))

/-- Replacing a Vegas Nash strategy with another Vegas best response preserves
the deviator's expected utility. -/
theorem isNash_update_bestResponse (g : WFProgram P L)
    {σ : StrategyProfile g} (hN : IsNash g σ)
    {who : P} {s' : Strategy g who}
    (hbr : IsBestResponse g who σ s') :
    eu g (Function.update σ who s') who = eu g σ who := by
  simpa [IsNash, IsBestResponse, eu, Strategy] using
    (KernelGame.isNash_update_bestResponse
      (G := toKernelGame g) hN hbr)

/-- A Vegas strict Nash equilibrium is a Vegas Nash equilibrium. -/
theorem IsStrictNash.isNash {g : WFProgram P L}
    {σ : StrategyProfile g} (hstrict : IsStrictNash g σ) :
    IsNash g σ := by
  simpa [IsStrictNash, IsNash] using
    (KernelGame.IsStrictNash.isNash (G := toKernelGame g) hstrict)

/-- Vegas Pareto dominance is exactly preference-parameterized Pareto
dominance with EU preferences. -/
theorem ParetoDominates_iff_ParetoDominatesFor_eu (g : WFProgram P L)
    (σ τ : StrategyProfile g) :
    ParetoDominates g σ τ ↔
      ParetoDominatesFor g (euPref g) (euStrictPref g) σ τ := by
  simpa [ParetoDominates, ParetoDominatesFor, euPref, euStrictPref] using
    (KernelGame.ParetoDominates_iff_ParetoDominatesFor_eu
      (G := toKernelGame g) σ τ)

/-- A Vegas Pareto-dominated profile is not Pareto-efficient. -/
theorem ParetoDominates.not_paretoEfficient {g : WFProgram P L}
    {σ τ : StrategyProfile g}
    (hpd : ParetoDominates g τ σ) :
    ¬ IsParetoEfficient g σ := by
  simpa [ParetoDominates, IsParetoEfficient] using
    (KernelGame.ParetoDominates.not_paretoEfficient
      (G := toKernelGame g) hpd)

/-- Preference-parameterized Vegas Pareto dominance rules out the
corresponding notion of Pareto efficiency. -/
theorem ParetoDominatesFor.not_paretoEfficientFor {g : WFProgram P L}
    {pref spref : P → PMF (Outcome P) → PMF (Outcome P) → Prop}
    {σ τ : StrategyProfile g}
    (hpd : ParetoDominatesFor g pref spref τ σ) :
    ¬ IsParetoEfficientFor g pref spref σ := by
  simpa [ParetoDominatesFor, IsParetoEfficientFor] using
    (KernelGame.ParetoDominatesFor.not_paretoEfficientFor
      (G := toKernelGame g) hpd)

/-- Preference-parameterized Vegas Pareto dominance is transitive under the
same conditions as in `GameTheory`. -/
theorem ParetoDominatesFor.trans {g : WFProgram P L}
    {pref spref : P → PMF (Outcome P) → PMF (Outcome P) → Prop}
    {σ τ υ : StrategyProfile g}
    (htrans : ∀ i x y z, pref i x y → pref i y z → pref i x z)
    (hstrict_left : ∀ i x y z, spref i x y → pref i y z → spref i x z)
    (h1 : ParetoDominatesFor g pref spref σ τ)
    (h2 : ParetoDominatesFor g pref spref τ υ) :
    ParetoDominatesFor g pref spref σ υ := by
  simpa [ParetoDominatesFor] using
    (KernelGame.ParetoDominatesFor.trans
      (G := toKernelGame g) htrans hstrict_left h1 h2)

/-- Vegas Pareto dominance is transitive. -/
theorem ParetoDominates.trans {g : WFProgram P L}
    {σ τ υ : StrategyProfile g}
    (h1 : ParetoDominates g σ τ)
    (h2 : ParetoDominates g τ υ) :
    ParetoDominates g σ υ := by
  simpa [ParetoDominates] using
    (KernelGame.ParetoDominates.trans (G := toKernelGame g) h1 h2)

/-- Vegas correlated equilibrium is exactly preference-parameterized
correlated equilibrium with EU preference. -/
theorem IsCorrelatedEq_iff_IsCorrelatedEqFor_eu (g : WFProgram P L)
    (μ : CorrelatedProfile g) :
    IsCorrelatedEq g μ ↔ IsCorrelatedEqFor g (euPref g) μ := by
  simpa [IsCorrelatedEq, IsCorrelatedEqFor, euPref] using
    (KernelGame.IsCorrelatedEq_iff_IsCorrelatedEqFor_eu
      (G := toKernelGame g) μ)

/-- Vegas coarse correlated equilibrium is exactly preference-parameterized
coarse correlated equilibrium with EU preference. -/
theorem IsCoarseCorrelatedEq_iff_IsCoarseCorrelatedEqFor_eu
    (g : WFProgram P L) (μ : CorrelatedProfile g) :
    IsCoarseCorrelatedEq g μ ↔ IsCoarseCorrelatedEqFor g (euPref g) μ := by
  simpa [IsCoarseCorrelatedEq, IsCoarseCorrelatedEqFor, euPref] using
    (KernelGame.IsCoarseCorrelatedEq_iff_IsCoarseCorrelatedEqFor_eu
      (G := toKernelGame g) μ)

/-- Every Vegas correlated equilibrium is a Vegas coarse correlated
equilibrium. -/
theorem IsCorrelatedEq.toCoarseCorrelatedEq {g : WFProgram P L}
    {μ : CorrelatedProfile g}
    (hce : IsCorrelatedEq g μ) :
    IsCoarseCorrelatedEq g μ := by
  simpa [IsCorrelatedEq, IsCoarseCorrelatedEq] using
    (KernelGame.IsCorrelatedEq.toCoarseCorrelatedEq
      (G := toKernelGame g) hce)

/-- Every Vegas Nash equilibrium is ε-Nash for any nonnegative ε. -/
theorem IsεNash.of_isNash (g : WFProgram P L)
    {σ : StrategyProfile g} (hN : IsNash g σ)
    {ε : ℝ} (hε : ε ≥ 0) :
    IsεNash g ε σ := by
  simpa [IsεNash, IsNash] using
    (KernelGame.IsεNash.of_isNash (G := toKernelGame g) hN hε)

/-- Vegas Nash is exactly `0`-Nash. -/
theorem isNash_iff_isεNash_zero (g : WFProgram P L)
    {σ : StrategyProfile g} :
    IsNash g σ ↔ IsεNash g 0 σ := by
  simpa [IsNash, IsεNash] using
    (KernelGame.isNash_iff_isεNash_zero (G := toKernelGame g) (σ := σ))

/-- Vegas ε-Nash is monotone in ε. -/
theorem IsεNash.mono (g : WFProgram P L)
    {σ : StrategyProfile g} {ε₁ ε₂ : ℝ}
    (h : IsεNash g ε₁ σ) (hle : ε₁ ≤ ε₂) :
    IsεNash g ε₂ σ := by
  simpa [IsεNash] using
    (KernelGame.IsεNash.mono (G := toKernelGame g) h hle)

/-- Vegas ε-Nash is equivalent to every player playing a Vegas ε-best response. -/
theorem isεNash_iff_εBestResponse (g : WFProgram P L)
    {ε : ℝ} {σ : StrategyProfile g} :
    IsεNash g ε σ ↔ ∀ who, IsεBestResponse g ε who σ (σ who) := by
  simpa [IsεNash, IsεBestResponse] using
    (KernelGame.isεNash_iff_εBestResponse
      (G := toKernelGame g) (ε := ε) (σ := σ))

/-- A Vegas strict Nash equilibrium is ε-Nash for any nonnegative ε. -/
theorem IsStrictNash.isεNash {g : WFProgram P L}
    {σ : StrategyProfile g} (hstrict : IsStrictNash g σ)
    {ε : ℝ} (hε : ε ≥ 0) :
    IsεNash g ε σ := by
  simpa [IsStrictNash, IsεNash] using
    (KernelGame.IsStrictNash.isεNash (G := toKernelGame g) hstrict hε)

/-- A Vegas Nash profile, embedded as a point-mass correlated profile, is a
Vegas correlated equilibrium. -/
theorem nash_pure_isCorrelatedEq (g : WFProgram P L)
    {σ : StrategyProfile g} (hN : IsNash g σ) :
    IsCorrelatedEq g (PMF.pure σ) := by
  simpa [IsNash, IsCorrelatedEq] using
    (KernelGame.nash_pure_isCorrelatedEq (G := toKernelGame g) hN)

/-- A Vegas Nash profile, embedded as a point-mass correlated profile, is a
Vegas coarse correlated equilibrium. -/
theorem nash_pure_isCoarseCorrelatedEq (g : WFProgram P L)
    {σ : StrategyProfile g} (hN : IsNash g σ) :
    IsCoarseCorrelatedEq g (PMF.pure σ) := by
  simpa [IsNash, IsCoarseCorrelatedEq] using
    (KernelGame.nash_pure_isCoarseCorrelatedEq (G := toKernelGame g) hN)

end Vegas
