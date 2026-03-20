import Vegas.PureStrategic
import GameTheory.Concepts.BestResponse
import GameTheory.Concepts.NashProperties
import GameTheory.Concepts.PotentialGame
import GameTheory.Concepts.PotentialFIP
import GameTheory.Theorems.NashExistence

/-!
# Vegas pure-strategic corollaries

Corollaries for the fixed-program pure strategic form.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- If every player has a dominant pure strategy for the fixed program,
then the program has a pure Nash equilibrium. -/
theorem pure_nash_of_all_have_dominant
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p)
    (h : ∀ who, ∃ s : ProgramPureStrategy (P := P) (L := L) who p,
      IsPureDominant p env hd who s) :
    ∃ σ : ProgramPureProfile (P := P) (L := L) p, IsPureNash p env hd σ := by
  simpa [IsPureDominant, IsPureNash] using
    (GameTheory.KernelGame.nash_of_all_have_dominant
      (G := toStrategicKernelGame p env hd) h)

/-- Pure Nash equilibrium is exactly everyone playing a pure best response. -/
theorem isPureNash_iff_bestResponse
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p)
    (σ : ProgramPureProfile (P := P) (L := L) p) :
    IsPureNash p env hd σ ↔
      ∀ who, IsPureBestResponse p env hd who σ (σ who) := by
  simpa [IsPureNash, IsPureBestResponse] using
    (GameTheory.KernelGame.isNash_iff_bestResponse
      (G := toStrategicKernelGame p env hd) σ)

/-- Any pure dominant strategy is a pure best response against every profile. -/
theorem pure_dominant_isBestResponse
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p)
    (who : P)
    (s : ProgramPureStrategy (P := P) (L := L) who p)
    (σ : ProgramPureProfile (P := P) (L := L) p)
    (hdom : IsPureDominant p env hd who s) :
    IsPureBestResponse p env hd who σ s := by
  simpa [IsPureDominant, IsPureBestResponse] using
    (GameTheory.KernelGame.dominant_isBestResponse
      (G := toStrategicKernelGame p env hd) who s σ hdom)

/-- In the fixed-program pure strategic form, pure Nash is equivalent to there
being no strictly improving pure unilateral deviation. -/
theorem isPureNash_iff_no_improving
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p)
    {σ : ProgramPureProfile (P := P) (L := L) p} :
    IsPureNash p env hd σ ↔
      ¬ ∃ (who : P) (s' : ProgramPureStrategy (P := P) (L := L) who p),
        (toStrategicKernelGame p env hd).eu (Function.update σ who s') who >
          (toStrategicKernelGame p env hd).eu σ who := by
  simpa [IsPureNash] using
    (GameTheory.KernelGame.isNash_iff_no_improving
      (G := toStrategicKernelGame p env hd) (σ := σ))

/-- Replacing a pure Nash action with another pure best response preserves the
deviator's expected utility. -/
theorem pure_nash_update_bestResponse_eu_eq
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p)
    {σ : ProgramPureProfile (P := P) (L := L) p}
    (hN : IsPureNash p env hd σ)
    {who : P} {s' : ProgramPureStrategy (P := P) (L := L) who p}
    (hbr : IsPureBestResponse p env hd who σ s') :
    (toStrategicKernelGame p env hd).eu (Function.update σ who s') who =
      (toStrategicKernelGame p env hd).eu σ who := by
  simpa [IsPureNash, IsPureBestResponse] using
    (GameTheory.KernelGame.isNash_update_bestResponse
      (G := toStrategicKernelGame p env hd) hN hbr)

/-- Every exact potential on the fixed-program pure strategic form is also an
ordinal potential. -/
theorem IsPureExactPotential.toOrdinal
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p)
    {Φ : ProgramPureProfile (P := P) (L := L) p → ℝ}
    (hΦ : IsPureExactPotential p env hd Φ) :
    IsPureOrdinalPotential p env hd Φ := by
  simpa [IsPureExactPotential, IsPureOrdinalPotential] using
    (GameTheory.KernelGame.IsExactPotential.toOrdinal
      (G := toStrategicKernelGame p env hd) hΦ)

/-- A global maximizer of an exact potential is a pure Nash equilibrium. -/
theorem IsPureExactPotential.nash_of_maximizer
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p)
    {Φ : ProgramPureProfile (P := P) (L := L) p → ℝ}
    (hΦ : IsPureExactPotential p env hd Φ)
    {σ : ProgramPureProfile (P := P) (L := L) p}
    (hmax : ∀ τ : ProgramPureProfile (P := P) (L := L) p, Φ σ ≥ Φ τ) :
    IsPureNash p env hd σ := by
  simpa [IsPureExactPotential, IsPureNash] using
    (GameTheory.KernelGame.IsExactPotential.nash_of_maximizer
      (G := toStrategicKernelGame p env hd) hΦ hmax)

/-- A global maximizer of an ordinal potential is a pure Nash equilibrium. -/
theorem IsPureOrdinalPotential.nash_of_maximizer
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p)
    {Φ : ProgramPureProfile (P := P) (L := L) p → ℝ}
    (hΦ : IsPureOrdinalPotential p env hd Φ)
    {σ : ProgramPureProfile (P := P) (L := L) p}
    (hmax : ∀ τ : ProgramPureProfile (P := P) (L := L) p, Φ σ ≥ Φ τ) :
    IsPureNash p env hd σ := by
  simpa [IsPureOrdinalPotential, IsPureNash] using
    (GameTheory.KernelGame.IsOrdinalPotential.nash_of_maximizer
      (G := toStrategicKernelGame p env hd) hΦ hmax)

/-- A strict global maximizer of an exact potential is a pure strict Nash
equilibrium. -/
theorem IsPureExactPotential.strictNash_of_strict_maximizer
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p)
    {Φ : ProgramPureProfile (P := P) (L := L) p → ℝ}
    (hΦ : IsPureExactPotential p env hd Φ)
    {σ : ProgramPureProfile (P := P) (L := L) p}
    (hmax : ∀ τ : ProgramPureProfile (P := P) (L := L) p, τ ≠ σ → Φ σ > Φ τ) :
    IsPureStrictNash p env hd σ := by
  intro who s' hs'
  have hpot := hΦ who σ s'
  have hne : Function.update σ who s' ≠ σ := by
    intro h
    apply hs'
    have := congr_fun h who
    simpa [Function.update] using this
  have hlt := hmax _ hne
  linarith

/-- In the fixed-program pure strategic form, exact-potential Nash equilibria
are exactly the local maximizers of the potential. -/
theorem IsPureExactPotential.isNash_iff_local_maximizer
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p)
    {Φ : ProgramPureProfile (P := P) (L := L) p → ℝ}
    (hΦ : IsPureExactPotential p env hd Φ)
    {σ : ProgramPureProfile (P := P) (L := L) p} :
    IsPureNash p env hd σ ↔
      ∀ who (s' : ProgramPureStrategy (P := P) (L := L) who p),
        Φ σ ≥ Φ (Function.update σ who s') := by
  constructor
  · intro hN who s'
    have hpot := hΦ who σ s'
    have hge := hN who s'
    linarith
  · intro hmax who s'
    have hpot := hΦ who σ s'
    have hge := hmax who s'
    linarith

/-- In the fixed-program pure strategic form, ordinal-potential Nash
equilibria are exactly the local maximizers of the potential. -/
theorem IsPureOrdinalPotential.isNash_iff_local_maximizer
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p)
    {Φ : ProgramPureProfile (P := P) (L := L) p → ℝ}
    (hΦ : IsPureOrdinalPotential p env hd Φ)
    {σ : ProgramPureProfile (P := P) (L := L) p} :
    IsPureNash p env hd σ ↔
      ∀ who (s' : ProgramPureStrategy (P := P) (L := L) who p),
        Φ σ ≥ Φ (Function.update σ who s') := by
  simpa [IsPureOrdinalPotential, IsPureNash] using
    (GameTheory.KernelGame.IsOrdinalPotential.isNash_iff_local_maximizer
      (G := toStrategicKernelGame p env hd) hΦ
      (σ := σ))

/-- An exact potential on the fixed-program pure strategic form guarantees a
pure Nash equilibrium, provided the pure profile space is nonempty. -/
theorem pure_exact_potential_nash_exists
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p)
    (LF : FiniteValuation L) [Finite P]
    {Φ : ProgramPureProfile (P := P) (L := L) p → ℝ}
    (hΦ : IsPureExactPotential p env hd Φ)
    [Nonempty (ProgramPureProfile (P := P) (L := L) p)] :
    ∃ σ : ProgramPureProfile (P := P) (L := L) p, IsPureNash p env hd σ := by
  let _ : Fintype P := Fintype.ofFinite P
  let _ : Fintype (ProgramPureProfile (P := P) (L := L) p) :=
    ProgramPureProfile.instFintype (P := P) (L := L) LF p
  let _ : Fintype ((toStrategicKernelGame p env hd).Profile) :=
    ProgramPureProfile.instFintype (P := P) (L := L) LF p
  let _ : Nonempty ((toStrategicKernelGame p env hd).Profile) :=
    inferInstanceAs (Nonempty (ProgramPureProfile (P := P) (L := L) p))
  simpa [IsPureExactPotential, IsPureNash] using
    (GameTheory.KernelGame.exact_potential_nash_exists
      (G := toStrategicKernelGame p env hd) (Φ := Φ) hΦ)

end Vegas
