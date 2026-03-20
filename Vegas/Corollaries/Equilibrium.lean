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
theorem isNash_iff_bestResponse (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (σ : StrategyProfile p env hd) :
    IsNash p env hd σ ↔ ∀ who, IsBestResponse p env hd who σ (σ who) := by
  simpa [IsNash, IsBestResponse] using
    (KernelGame.isNash_iff_bestResponse (G := toKernelGame p env hd) σ)

/-- Preference-parameterized Vegas Nash is equivalent to every player playing a
preference-parameterized Vegas best response. -/
theorem isNashFor_iff_bestResponseFor (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (pref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (σ : StrategyProfile p env hd) :
    IsNashFor p env hd pref σ ↔
      ∀ who, IsBestResponseFor p env hd pref who σ (σ who) := by
  simpa [IsNashFor, IsBestResponseFor] using
    (KernelGame.isNashFor_iff_bestResponseFor
      (G := toKernelGame p env hd) pref σ)

/-- Vegas Nash is exactly preference-parameterized Nash with EU preference. -/
theorem IsNash_iff_IsNashFor_eu (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (σ : StrategyProfile p env hd) :
    IsNash p env hd σ ↔ IsNashFor p env hd (euPref p env hd) σ := by
  simpa [IsNash, IsNashFor, euPref] using
    (KernelGame.IsNash_iff_IsNashFor_eu (G := toKernelGame p env hd) σ)

/-- Vegas dominant strategy is exactly preference-parameterized dominance with
EU preference. -/
theorem IsDominant_iff_IsDominantFor_eu (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (who : P) (s : Strategy p env hd who) :
    IsDominant p env hd who s ↔
      IsDominantFor p env hd (euPref p env hd) who s := by
  simpa [IsDominant, IsDominantFor, euPref] using
    (KernelGame.IsDominant_iff_IsDominantFor_eu
      (G := toKernelGame p env hd) who s)

/-- Vegas best response is exactly preference-parameterized best response with
EU preference. -/
theorem IsBestResponse_iff_IsBestResponseFor_eu (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (who : P) (σ : StrategyProfile p env hd)
    (s : Strategy p env hd who) :
    IsBestResponse p env hd who σ s ↔
      IsBestResponseFor p env hd (euPref p env hd) who σ s := by
  simpa [IsBestResponse, IsBestResponseFor, euPref] using
    (KernelGame.IsBestResponse_iff_IsBestResponseFor_eu
      (G := toKernelGame p env hd) who σ s)

/-- Vegas strict Nash is exactly preference-parameterized strict Nash with EU
strict preference. -/
theorem IsStrictNash_iff_IsStrictNashFor_eu (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (σ : StrategyProfile p env hd) :
    IsStrictNash p env hd σ ↔
      IsStrictNashFor p env hd (euStrictPref p env hd) σ := by
  simpa [IsStrictNash, IsStrictNashFor, euStrictPref] using
    (KernelGame.IsStrictNash_iff_IsStrictNashFor_eu
      (G := toKernelGame p env hd) σ)

/-- Vegas strict dominance is exactly preference-parameterized strict
dominance with EU strict preference. -/
theorem IsStrictDominant_iff_IsStrictDominantFor_eu (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (who : P) (s : Strategy p env hd who) :
    IsStrictDominant p env hd who s ↔
      IsStrictDominantFor p env hd (euStrictPref p env hd) who s := by
  simpa [IsStrictDominant, IsStrictDominantFor, euStrictPref] using
    (KernelGame.IsStrictDominant_iff_IsStrictDominantFor_eu
      (G := toKernelGame p env hd) who s)

/-- Vegas weak dominance is exactly preference-parameterized weak dominance
with EU preference. -/
theorem WeaklyDominates_iff_WeaklyDominatesFor_eu (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (who : P) (s t : Strategy p env hd who) :
    WeaklyDominates p env hd who s t ↔
      WeaklyDominatesFor p env hd (euPref p env hd) who s t := by
  simpa [WeaklyDominates, WeaklyDominatesFor, euPref] using
    (KernelGame.WeaklyDominates_iff_WeaklyDominatesFor_eu
      (G := toKernelGame p env hd) who s t)

/-- Vegas strict dominance is exactly preference-parameterized strict
dominance with EU strict preference. -/
theorem StrictlyDominates_iff_StrictlyDominatesFor_eu (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (who : P) (s t : Strategy p env hd who) :
    StrictlyDominates p env hd who s t ↔
      StrictlyDominatesFor p env hd (euStrictPref p env hd) who s t := by
  simpa [StrictlyDominates, StrictlyDominatesFor, euStrictPref] using
    (KernelGame.StrictlyDominates_iff_StrictlyDominatesFor_eu
      (G := toKernelGame p env hd) who s t)

/-- A Vegas profile of dominant strategies is a Vegas Nash equilibrium. -/
theorem dominant_is_nash (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (σ : StrategyProfile p env hd)
    (hdom : ∀ who, IsDominant p env hd who (σ who)) :
    IsNash p env hd σ := by
  simpa [IsNash, IsDominant] using
    (KernelGame.dominant_is_nash (G := toKernelGame p env hd) σ hdom)

/-- A Vegas profile of preference-dominant strategies is preference-Nash. -/
theorem dominant_is_nash_for (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (pref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (σ : StrategyProfile p env hd)
    (hdom : ∀ who, IsDominantFor p env hd pref who (σ who)) :
    IsNashFor p env hd pref σ := by
  simpa [IsNashFor, IsDominantFor] using
    (KernelGame.dominant_is_nash_for (G := toKernelGame p env hd) pref σ hdom)

/-- A Vegas dominant strategy is a Vegas best response against any profile. -/
theorem dominant_isBestResponse (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (who : P) (s : Strategy p env hd who) (σ : StrategyProfile p env hd)
    (hdom : IsDominant p env hd who s) :
    IsBestResponse p env hd who σ s := by
  simpa [IsDominant, IsBestResponse] using
    (KernelGame.dominant_isBestResponse
      (G := toKernelGame p env hd) who s σ hdom)

/-- Vegas Nash is equivalent to having no strictly improving unilateral
deviation. -/
theorem isNash_iff_no_improving (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (σ : StrategyProfile p env hd) :
    IsNash p env hd σ ↔
      ¬ ∃ (who : P) (s' : Strategy p env hd who),
        eu p env hd (Function.update σ who s') who > eu p env hd σ who := by
  simpa [IsNash, eu, Strategy] using
    (KernelGame.isNash_iff_no_improving (G := toKernelGame p env hd) (σ := σ))

/-- Replacing a Vegas Nash strategy with another Vegas best response preserves
the deviator's expected utility. -/
theorem isNash_update_bestResponse (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    {σ : StrategyProfile p env hd} (hN : IsNash p env hd σ)
    {who : P} {s' : Strategy p env hd who}
    (hbr : IsBestResponse p env hd who σ s') :
    eu p env hd (Function.update σ who s') who = eu p env hd σ who := by
  simpa [IsNash, IsBestResponse, eu, Strategy] using
    (KernelGame.isNash_update_bestResponse
      (G := toKernelGame p env hd) hN hbr)

/-- A Vegas strict Nash equilibrium is a Vegas Nash equilibrium. -/
theorem IsStrictNash.isNash {p : VegasCore P L Γ}
    {env : VEnv (Player := P) L Γ} {hd : NormalizedDists p}
    {σ : StrategyProfile p env hd} (hstrict : IsStrictNash p env hd σ) :
    IsNash p env hd σ := by
  simpa [IsStrictNash, IsNash] using
    (KernelGame.IsStrictNash.isNash
      (G := toKernelGame p env hd) hstrict)

/-- Vegas Pareto dominance is exactly preference-parameterized Pareto
dominance with EU preferences. -/
theorem ParetoDominates_iff_ParetoDominatesFor_eu (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (σ τ : StrategyProfile p env hd) :
    ParetoDominates p env hd σ τ ↔
      ParetoDominatesFor p env hd (euPref p env hd) (euStrictPref p env hd) σ τ := by
  simpa [ParetoDominates, ParetoDominatesFor, euPref, euStrictPref] using
    (KernelGame.ParetoDominates_iff_ParetoDominatesFor_eu
      (G := toKernelGame p env hd) σ τ)

/-- A Vegas Pareto-dominated profile is not Pareto-efficient. -/
theorem ParetoDominates.not_paretoEfficient {p : VegasCore P L Γ}
    {env : VEnv (Player := P) L Γ} {hd : NormalizedDists p}
    {σ τ : StrategyProfile p env hd}
    (hpd : ParetoDominates p env hd τ σ) :
    ¬ IsParetoEfficient p env hd σ := by
  simpa [ParetoDominates, IsParetoEfficient] using
    (KernelGame.ParetoDominates.not_paretoEfficient
      (G := toKernelGame p env hd) hpd)

/-- Preference-parameterized Vegas Pareto dominance rules out the
corresponding notion of Pareto efficiency. -/
theorem ParetoDominatesFor.not_paretoEfficientFor {p : VegasCore P L Γ}
    {env : VEnv (Player := P) L Γ} {hd : NormalizedDists p}
    {pref spref : P → PMF (Outcome P) → PMF (Outcome P) → Prop}
    {σ τ : StrategyProfile p env hd}
    (hpd : ParetoDominatesFor p env hd pref spref τ σ) :
    ¬ IsParetoEfficientFor p env hd pref spref σ := by
  simpa [ParetoDominatesFor, IsParetoEfficientFor] using
    (KernelGame.ParetoDominatesFor.not_paretoEfficientFor
      (G := toKernelGame p env hd) hpd)

/-- Preference-parameterized Vegas Pareto dominance is transitive under the
same conditions as in `GameTheory`. -/
theorem ParetoDominatesFor.trans {p : VegasCore P L Γ}
    {env : VEnv (Player := P) L Γ} {hd : NormalizedDists p}
    {pref spref : P → PMF (Outcome P) → PMF (Outcome P) → Prop}
    {σ τ υ : StrategyProfile p env hd}
    (htrans : ∀ i x y z, pref i x y → pref i y z → pref i x z)
    (hstrict_left : ∀ i x y z, spref i x y → pref i y z → spref i x z)
    (h1 : ParetoDominatesFor p env hd pref spref σ τ)
    (h2 : ParetoDominatesFor p env hd pref spref τ υ) :
    ParetoDominatesFor p env hd pref spref σ υ := by
  simpa [ParetoDominatesFor] using
    (KernelGame.ParetoDominatesFor.trans
      (G := toKernelGame p env hd) htrans hstrict_left h1 h2)

/-- Vegas Pareto dominance is transitive. -/
theorem ParetoDominates.trans {p : VegasCore P L Γ}
    {env : VEnv (Player := P) L Γ} {hd : NormalizedDists p}
    {σ τ υ : StrategyProfile p env hd}
    (h1 : ParetoDominates p env hd σ τ)
    (h2 : ParetoDominates p env hd τ υ) :
    ParetoDominates p env hd σ υ := by
  simpa [ParetoDominates] using
    (KernelGame.ParetoDominates.trans
      (G := toKernelGame p env hd) h1 h2)

/-- Vegas correlated equilibrium is exactly preference-parameterized
correlated equilibrium with EU preference. -/
theorem IsCorrelatedEq_iff_IsCorrelatedEqFor_eu (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (μ : CorrelatedProfile p env hd) :
    IsCorrelatedEq p env hd μ ↔
      IsCorrelatedEqFor p env hd (euPref p env hd) μ := by
  simpa [IsCorrelatedEq, IsCorrelatedEqFor, euPref] using
    (KernelGame.IsCorrelatedEq_iff_IsCorrelatedEqFor_eu
      (G := toKernelGame p env hd) μ)

/-- Vegas coarse correlated equilibrium is exactly preference-parameterized
coarse correlated equilibrium with EU preference. -/
theorem IsCoarseCorrelatedEq_iff_IsCoarseCorrelatedEqFor_eu
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p) (μ : CorrelatedProfile p env hd) :
    IsCoarseCorrelatedEq p env hd μ ↔
      IsCoarseCorrelatedEqFor p env hd (euPref p env hd) μ := by
  simpa [IsCoarseCorrelatedEq, IsCoarseCorrelatedEqFor, euPref] using
    (KernelGame.IsCoarseCorrelatedEq_iff_IsCoarseCorrelatedEqFor_eu
      (G := toKernelGame p env hd) μ)

/-- Every Vegas correlated equilibrium is a Vegas coarse correlated
equilibrium. -/
theorem IsCorrelatedEq.toCoarseCorrelatedEq {p : VegasCore P L Γ}
    {env : VEnv (Player := P) L Γ} {hd : NormalizedDists p}
    {μ : CorrelatedProfile p env hd}
    (hce : IsCorrelatedEq p env hd μ) :
    IsCoarseCorrelatedEq p env hd μ := by
  simpa [IsCorrelatedEq, IsCoarseCorrelatedEq] using
    (KernelGame.IsCorrelatedEq.toCoarseCorrelatedEq
      (G := toKernelGame p env hd) hce)

/-- Every Vegas Nash equilibrium is ε-Nash for any nonnegative ε. -/
theorem IsεNash.of_isNash (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    {σ : StrategyProfile p env hd} (hN : IsNash p env hd σ)
    {ε : ℝ} (hε : ε ≥ 0) :
    IsεNash p env hd ε σ := by
  simpa [IsεNash, IsNash] using
    (KernelGame.IsεNash.of_isNash
      (G := toKernelGame p env hd) hN hε)

/-- Vegas Nash is exactly `0`-Nash. -/
theorem isNash_iff_isεNash_zero (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    {σ : StrategyProfile p env hd} :
    IsNash p env hd σ ↔ IsεNash p env hd 0 σ := by
  simpa [IsNash, IsεNash] using
    (KernelGame.isNash_iff_isεNash_zero (G := toKernelGame p env hd) (σ := σ))

/-- Vegas ε-Nash is monotone in ε. -/
theorem IsεNash.mono (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    {σ : StrategyProfile p env hd} {ε₁ ε₂ : ℝ}
    (h : IsεNash p env hd ε₁ σ) (hle : ε₁ ≤ ε₂) :
    IsεNash p env hd ε₂ σ := by
  simpa [IsεNash] using
    (KernelGame.IsεNash.mono
      (G := toKernelGame p env hd) h hle)

/-- Vegas ε-Nash is equivalent to every player playing a Vegas ε-best response. -/
theorem isεNash_iff_εBestResponse (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    {ε : ℝ} {σ : StrategyProfile p env hd} :
    IsεNash p env hd ε σ ↔
      ∀ who, IsεBestResponse p env hd ε who σ (σ who) := by
  simpa [IsεNash, IsεBestResponse] using
    (KernelGame.isεNash_iff_εBestResponse
      (G := toKernelGame p env hd) (ε := ε) (σ := σ))

/-- A Vegas strict Nash equilibrium is ε-Nash for any nonnegative ε. -/
theorem IsStrictNash.isεNash {p : VegasCore P L Γ}
    {env : VEnv (Player := P) L Γ} {hd : NormalizedDists p}
    {σ : StrategyProfile p env hd} (hstrict : IsStrictNash p env hd σ)
    {ε : ℝ} (hε : ε ≥ 0) :
    IsεNash p env hd ε σ := by
  simpa [IsStrictNash, IsεNash] using
    (KernelGame.IsStrictNash.isεNash
      (G := toKernelGame p env hd) hstrict hε)

/-- A Vegas Nash profile, embedded as a point-mass correlated profile, is a
Vegas correlated equilibrium. -/
theorem nash_pure_isCorrelatedEq (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    {σ : StrategyProfile p env hd} (hN : IsNash p env hd σ) :
    IsCorrelatedEq p env hd (PMF.pure σ) := by
  simpa [IsNash, IsCorrelatedEq] using
    (KernelGame.nash_pure_isCorrelatedEq
      (G := toKernelGame p env hd) hN)

/-- A Vegas Nash profile, embedded as a point-mass correlated profile, is a
Vegas coarse correlated equilibrium. -/
theorem nash_pure_isCoarseCorrelatedEq (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    {σ : StrategyProfile p env hd} (hN : IsNash p env hd σ) :
    IsCoarseCorrelatedEq p env hd (PMF.pure σ) := by
  simpa [IsNash, IsCoarseCorrelatedEq] using
    (KernelGame.nash_pure_isCoarseCorrelatedEq
      (G := toKernelGame p env hd) hN)

end Vegas
