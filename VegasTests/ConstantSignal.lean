/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Runtime.ConstantSignal
import VegasTests.FailureObservation

/-!
# Non-quitting profiles and early signals

The first instance keeps both hidden Boolean values in support while making
the quit signal constant. The second checks strictly dominated quitting.
The earlier counterexample fails the constant-signal hypothesis.
-/

noncomputable section

namespace VegasTests.ConstantSignal

open GameTheory GameTheory.Math.Probability Vegas.Runtime

abbrev fair : FinDist Bool := FinDist.uniformOfFintype

def quitSignal : Option Bool → Bool := Option.isNone

def hiddenProfile : Profile (ConstantSignal.sourceSignature (Option Bool) Bool)
  | false => fair.map some
  | true => fair

theorem hidden_signal_constant :
    ∀ value ∈ (hiddenProfile false).support, quitSignal value = false := by
  intro value hvalue
  change value ∈ (fair.map some).support at hvalue
  rw [FinDist.support_map] at hvalue
  obtain ⟨bit, _, rfl⟩ := hvalue
  rfl

/-- Constancy of the extra signal does not mean constancy of the hidden value. -/
theorem both_hidden_values_supported (bit : Bool) :
    some bit ∈ (hiddenProfile false).support := by
  change some bit ∈ (fair.map some).support
  rw [FinDist.support_map]
  exact ⟨bit, FinDist.mem_support_uniformOfFintype bit, rfl⟩

theorem hidden_deviation_law (who : Bool)
    (replacement : (ConstantSignal.targetSignature (Option Bool) Bool Bool).Strategy who) :
    ConstantSignal.targetPlay quitSignal
        (Profile.update (ConstantSignal.compileProfile hiddenProfile) who replacement) =
      FailureObservation.play id
        (Profile.update hiddenProfile who (ConstantSignal.backtranslate false who replacement)) :=
  ConstantSignal.deviation_law quitSignal hiddenProfile false hidden_signal_constant who replacement

/-- The deviating submitter may switch the signal from completion to quit;
constancy is required of the original profile, not of its deviations. -/
theorem quit_deviation_law :
    ConstantSignal.targetPlay quitSignal
        (Profile.update (ConstantSignal.compileProfile hiddenProfile) false (FinDist.pure none)) =
      FailureObservation.play id (Profile.update hiddenProfile false (FinDist.pure none)) :=
  hidden_deviation_law false (FinDist.pure none)

theorem hidden_approximate_nash_iff (payoff : Option Bool × Bool → Bool → ℝ) (ε : ℝ) :
    IsεNash (ConstantSignal.targetGame quitSignal payoff).form payoff ε
        (ConstantSignal.compileProfile hiddenProfile) ↔
      IsεNash (FailureObservation.game (Raw := Option Bool) id payoff).form
        payoff ε hiddenProfile :=
  ConstantSignal.approximate_nash_iff quitSignal payoff hiddenProfile false hidden_signal_constant ε

/-- The fair quit/continue counterexample has a genuinely varying signal. -/
theorem counterexample_signal_not_constant :
    ¬ ∃ signal : Bool, ∀ value ∈ fair.support, id value = signal := by
  rintro ⟨signal, hconstant⟩
  have hfalse := hconstant false (FinDist.mem_support_uniformOfFintype false)
  have htrue := hconstant true (FinDist.mem_support_uniformOfFintype true)
  exact Bool.false_ne_true (hfalse.trans htrue.symm)

def quitPenalty (outcome : Bool × Bool) (who : Bool) : ℝ :=
  if who then 0 else if outcome.1 then -1 else 0

def completionProfile : Profile (ConstantSignal.sourceSignature Bool Bool)
  | false => FinDist.pure false
  | true => fair

theorem quit_strictly_dominated (action : Bool) :
    quitPenalty (true, action) false < quitPenalty (false, action) false := by
  norm_num [quitPenalty]

theorem completion_source_nash :
    IsNash (FailureObservation.game (Raw := Bool) id quitPenalty).form
      (euPreference quitPenalty) completionProfile := by
  rw [isNash_iff]
  intro who replacement
  change expectedUtility quitPenalty who
    (FailureObservation.play id (Profile.update completionProfile who replacement)) ≤
      expectedUtility quitPenalty who (FailureObservation.play id completionProfile)
  have hbaseline : expectedUtility quitPenalty who
      (FailureObservation.play id completionProfile) = 0 := by
    simp [expectedUtility, FailureObservation.play, completionProfile,
      FinDist.expect_map, quitPenalty]
  rw [hbaseline]
  apply FinDist.expect_le_of_forall
  intro outcome _
  rcases outcome with ⟨value, action⟩
  cases who <;> cases value <;> norm_num [quitPenalty]

theorem completion_target_nash :
    IsNash (ConstantSignal.targetGame id quitPenalty).form (euPreference quitPenalty)
      (ConstantSignal.compileProfile completionProfile) :=
  ConstantSignal.nash_preserved_of_dominated_quit quitPenalty quit_strictly_dominated
    completionProfile completion_source_nash

/-- info: 'VegasTests.ConstantSignal.hidden_deviation_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ConstantSignal.hidden_deviation_law

/-- info: 'VegasTests.ConstantSignal.completion_target_nash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ConstantSignal.completion_target_nash

end VegasTests.ConstantSignal
