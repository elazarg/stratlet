/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Runtime.OutcomeSimulation

/-! # Correlated-equilibrium transport

An unrestricted outcome simulation transports laws over source profiles by
compiling each recommendation. When strategy back-translation retracts
compilation, recommendation-dependent responses transport in both directions.
-/

noncomputable section

namespace Vegas.Runtime.OutcomeSimulationOn

open GameTheory GameTheory.Math.Probability

universe uPlayer uSourceStrategy uSourceOutcome uTargetStrategy uTargetOutcome

variable {Player : Type uPlayer} [DecidableEq Player]
variable {source : GameForm.{uPlayer, uSourceStrategy, uSourceOutcome} Player}
variable {target : GameForm.{uPlayer, uTargetStrategy, uTargetOutcome} Player}

variable (simulation : OutcomeSimulationOn source target (fun _ _ => True))

/-- Compile every recommendation in a law over source profiles. -/
def compileLaw (law : FinDist (Profile source.sig)) : FinDist (Profile target.sig) :=
  law.map simulation.compileProfile

theorem compileProfile_update (profile : Profile source.sig) (who : Player)
    (replacement : source.sig.Strategy who) :
    Profile.update (simulation.compileProfile profile) who
        (simulation.compileStrategy who replacement) =
      simulation.compileProfile (Profile.update profile who replacement) := by
  funext player
  by_cases hplayer : player = who
  · subst player
    simp [compileProfile, Profile.update]
  · simp [compileProfile, Profile.update, hplayer]

/-- Compiling a recommendation law preserves expected decoded utility. -/
theorem expectedUtility_compileLaw
    (utility : source.sig.Outcome → Player → ℝ)
    (law : FinDist (Profile source.sig)) (who : Player) :
    expectedUtility (fun outcome player =>
        utility (simulation.decodeOutcome outcome) player) who
        (target.outcomeLaw (simulation.compileLaw law)) =
      expectedUtility utility who (source.outcomeLaw law) := by
  rw [expectedUtility_outcomeLaw, expectedUtility_outcomeLaw]
  unfold compileLaw
  rw [FinDist.expect_map]
  apply FinDist.expect_congr
  intro profile _
  exact simulation.expect_compile profile (fun outcome => utility outcome who)

/-- Source coarse correlated equilibrium is preserved by recommendation
compilation. -/
theorem isCoarseCorrelatedEq_compileLaw_of
    (utility : source.sig.Outcome → Player → ℝ)
    (law : FinDist (Profile source.sig))
    (hsource : IsCoarseCorrelatedEq source (euPreference utility) law) :
    IsCoarseCorrelatedEq target
      (euPreference fun outcome player =>
        utility (simulation.decodeOutcome outcome) player)
      (simulation.compileLaw law) := by
  rw [isCoarseCorrelatedEq_iff] at hsource ⊢
  intro who replacement
  have h := hsource who (simulation.backtranslateStrategy who replacement)
  simp only [euPreference] at h ⊢
  rw [simulation.expectedUtility_compileLaw utility law who]
  rw [expectedUtility_bind]
  unfold compileLaw
  rw [FinDist.expect_map]
  rw [expectedUtility_bind] at h
  calc
    law.expect (fun profile => expectedUtility
        (fun outcome player => utility (simulation.decodeOutcome outcome) player) who
        (target.play (Profile.update (simulation.compileProfile profile) who replacement))) =
      law.expect (fun profile => expectedUtility utility who
        (source.play (Profile.update profile who
          (simulation.backtranslateStrategy who replacement)))) := by
            apply FinDist.expect_congr
            intro profile _
            exact simulation.expect_deviation profile who replacement trivial
              (fun outcome => utility outcome who)
    _ ≤ _ := h

/-- Coarse correlated equilibrium is invariant under recommendation
compilation. Reflection uses the honest law at a source replacement profile. -/
theorem isCoarseCorrelatedEq_compileLaw_iff
    (utility : source.sig.Outcome → Player → ℝ)
    (law : FinDist (Profile source.sig)) :
    IsCoarseCorrelatedEq target
        (euPreference fun outcome player =>
          utility (simulation.decodeOutcome outcome) player)
        (simulation.compileLaw law) ↔
      IsCoarseCorrelatedEq source (euPreference utility) law := by
  rw [isCoarseCorrelatedEq_iff, isCoarseCorrelatedEq_iff]
  constructor
  · intro htarget who replacement
    have h := htarget who (simulation.compileStrategy who replacement)
    simp only [euPreference] at h ⊢
    rw [simulation.expectedUtility_compileLaw utility law who] at h
    rw [expectedUtility_bind] at h
    unfold compileLaw at h
    rw [FinDist.expect_map] at h
    rw [expectedUtility_bind]
    calc
      law.expect (fun profile => expectedUtility utility who
          (source.play (Profile.update profile who replacement))) =
        law.expect (fun profile => expectedUtility
          (fun outcome player => utility (simulation.decodeOutcome outcome) player) who
          (target.play (Profile.update (simulation.compileProfile profile) who
            (simulation.compileStrategy who replacement)))) := by
              apply FinDist.expect_congr
              intro profile _
              symm
              rw [simulation.compileProfile_update profile who replacement]
              exact simulation.expect_compile (Profile.update profile who replacement)
                (fun outcome => utility outcome who)
      _ ≤ _ := h
  · intro hsource
    rw [← isCoarseCorrelatedEq_iff] at hsource ⊢
    exact simulation.isCoarseCorrelatedEq_compileLaw_of utility law hsource

/-- Source correlated equilibrium is preserved by recommendation compilation.
Target responses are back-translated after receiving only the compiled own
recommendation. -/
theorem isCorrelatedEq_compileLaw_of
    (utility : source.sig.Outcome → Player → ℝ)
    (law : FinDist (Profile source.sig))
    (hsource : IsCorrelatedEq source (euPreference utility) law) :
    IsCorrelatedEq target
      (euPreference fun outcome player =>
        utility (simulation.decodeOutcome outcome) player)
      (simulation.compileLaw law) := by
  rw [isCorrelatedEq_iff] at hsource ⊢
  intro who respond
  let sourceRespond : source.sig.Strategy who → source.sig.Strategy who :=
    fun recommendation => simulation.backtranslateStrategy who
      (respond (simulation.compileStrategy who recommendation))
  have h := hsource who sourceRespond
  simp only [euPreference] at h ⊢
  rw [simulation.expectedUtility_compileLaw utility law who]
  rw [expectedUtility_bind]
  unfold compileLaw
  rw [FinDist.expect_map]
  rw [expectedUtility_bind] at h
  calc
    law.expect (fun profile => expectedUtility
        (fun outcome player => utility (simulation.decodeOutcome outcome) player) who
        (target.play (Profile.update (simulation.compileProfile profile) who
          (respond (simulation.compileProfile profile who))))) =
      law.expect (fun profile => expectedUtility utility who
        (source.play (Profile.update profile who (sourceRespond (profile who))))) := by
            apply FinDist.expect_congr
            intro profile _
            exact simulation.expect_deviation profile who
              (respond (simulation.compileProfile profile who)) trivial
              (fun outcome => utility outcome who)
    _ ≤ _ := h

/-- Correlated equilibrium is invariant under recommendation compilation.
The response translator sees only that player's recommendation. -/
theorem isCorrelatedEq_compileLaw_iff
    (utility : source.sig.Outcome → Player → ℝ)
    (law : FinDist (Profile source.sig))
    (backtranslate_compile : ∀ who strategy,
      simulation.backtranslateStrategy who
        (simulation.compileStrategy who strategy) = strategy) :
    IsCorrelatedEq target
        (euPreference fun outcome player =>
          utility (simulation.decodeOutcome outcome) player)
        (simulation.compileLaw law) ↔
      IsCorrelatedEq source (euPreference utility) law := by
  rw [isCorrelatedEq_iff, isCorrelatedEq_iff]
  constructor
  · intro htarget who respond
    let targetRespond : target.sig.Strategy who → target.sig.Strategy who :=
      fun recommendation => simulation.compileStrategy who
        (respond (simulation.backtranslateStrategy who recommendation))
    have h := htarget who targetRespond
    simp only [euPreference] at h ⊢
    rw [simulation.expectedUtility_compileLaw utility law who] at h
    rw [expectedUtility_bind] at h
    unfold compileLaw at h
    rw [FinDist.expect_map] at h
    rw [expectedUtility_bind]
    calc
      law.expect (fun profile => expectedUtility utility who
          (source.play (Profile.update profile who (respond (profile who))))) =
        law.expect (fun profile => expectedUtility
          (fun outcome player => utility (simulation.decodeOutcome outcome) player) who
          (target.play (Profile.update (simulation.compileProfile profile) who
            (targetRespond (simulation.compileProfile profile who))))) := by
              apply FinDist.expect_congr
              intro profile _
              symm
              simpa only [expectedUtility, targetRespond, compileProfile,
                backtranslate_compile] using
                simulation.expect_deviation profile who
                  (targetRespond (simulation.compileProfile profile who)) trivial
                  (fun outcome => utility outcome who)
      _ ≤ _ := h
  · intro hsource
    rw [← isCorrelatedEq_iff] at hsource ⊢
    exact simulation.isCorrelatedEq_compileLaw_of utility law hsource

end Vegas.Runtime.OutcomeSimulationOn
