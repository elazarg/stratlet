/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Scheduled.Equilibrium

/-! # Serialization with independent outcome valuations

The outcome interpretation and utility profile are analysis data. The same
compiled strategy and scheduler proofs work for every such interpretation.
-/

noncomputable section

namespace Vegas.Machine.Program

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}

/-- Honest outcome valuations agree for any public-data scheduler. -/
theorem expectedUtility_serializedOutcomeGame (program : Program Player L) {Outcome : Type}
    (observe : program.State → Outcome) (valuation : Outcome → Player → ℝ)
    (schedulerUtility : program.serializedArena.History → ℝ)
    (scheduler : program.serializedArena.information.BehavioralPolicy .scheduler)
    (profile : (who : Player) → program.information.BehavioralPolicy who) (who : Player) :
    expectedUtility (program.serializedOutcomeGame observe valuation schedulerUtility).utility
        (.player who)
        ((program.serializedOutcomeGame observe valuation schedulerUtility).behavioral.form.play
          (program.compileSerializedBehavioralProfile scheduler profile)) =
      expectedUtility (program.outcomeGame observe valuation).utility who
        ((program.outcomeGame observe valuation).behavioral.form.play profile) := by
  have hlaw := congrArg (fun law : FinDist program.State =>
    law.expect (fun state => valuation (observe state) who))
      (program.runBehavioral_compileSerialized scheduler profile)
  simp only [FinDist.expect_map] at hlaw
  exact hlaw

/-- Nash equivalence for every valuation of every interpreted settled outcome.
Original players ignore erased trace distinctions in their utility, but their
runtime strategies may use the complete information provided by the model. -/
theorem serializedOutcomeGame_nash_iff (program : Program Player L) {Outcome : Type}
    (observe : program.State → Outcome) (valuation : Outcome → Player → ℝ)
    (schedulerUtility : program.serializedArena.History → ℝ)
    (scheduler : program.serializedArena.information.BehavioralPolicy .scheduler)
    (profile : (who : Player) → program.information.BehavioralPolicy who) :
    Participant.IsPlayerNash
      (program.serializedOutcomeGame observe valuation schedulerUtility).behavioral
      (program.compileSerializedBehavioralProfile scheduler profile) ↔
      IsNash (program.outcomeGame observe valuation).behavioral.form
        (euPreference (program.outcomeGame observe valuation).utility) profile := by
  simp only [Participant.IsPlayerNash, Participant.IsPlayerNashAgainst,
    true_implies]
  rw [isNash_iff]
  change (∀ who replacement,
    expectedUtility (program.serializedOutcomeGame observe valuation schedulerUtility).utility
      (.player who)
      ((program.serializedOutcomeGame observe valuation schedulerUtility).behavioral.form.play
        (Profile.update (program.compileSerializedBehavioralProfile scheduler profile)
          (.player who) replacement)) ≤
    expectedUtility (program.serializedOutcomeGame observe valuation schedulerUtility).utility
      (.player who)
      ((program.serializedOutcomeGame observe valuation schedulerUtility).behavioral.form.play
        (program.compileSerializedBehavioralProfile scheduler profile))) ↔ _
  simp only [program.expectedUtility_serializedOutcomeGame observe valuation schedulerUtility]
  apply forall_congr'
  intro who
  exact program.serializedDeviation_expect_bound_iff scheduler profile who
    (fun state => valuation (observe state) who) _

end Vegas.Machine.Program
