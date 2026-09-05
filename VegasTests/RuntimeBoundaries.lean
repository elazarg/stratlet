/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.MatchingPenniesEquilibrium
import Vegas.Scheduled.PublicSubmission
import Vegas.Runtime.SelectiveAbort

/-! # Runtime obstructions for the compiled hidden-choice game -/

noncomputable section

namespace VegasTests.RuntimeBoundaries

open Vegas GameTheory GameTheory.Math.Probability MatchingPenniesEquilibrium

/-- The obstruction applies to the actual compiled source game, not merely an
unrelated matching-pennies payoff matrix or a particular failed translator. -/
theorem no_public_submission_adequacy
    (schedulerUtility : Scheduled.PublicSubmission.Values → ℝ) :
    ¬ Nonempty (Scheduled.PlayerDeviationAdequacy program.game.behavioral
      (Scheduled.PublicSubmission.game schedulerUtility)) :=
  Scheduled.PublicSubmission.no_adequacy_of_zero_equilibrium program.game.behavioral fairPolicy
    fair_isNash (fun who => expectedUtility_eq_zero_of_opponent_fair fairPolicy who
      (fun other _ => initialLaw_fair other)) schedulerUtility

theorem fair_clipped_payoff (who : TestPlayer) (abortValue : ℝ) :
    (program.game.behavioral.form.play fairPolicy).expect
      (fun history => max (program.game.behavioral.utility history who) abortValue) =
        (max 1 abortValue + max (-1) abortValue) / 2 := by
  rw [expectedPayoffObservable_eq fairPolicy who (fun value => max value abortValue)]
  simp only [initialLaw_fair]
  rw [pi_two, FinDist.expect_map, FinDist.expect_eq_sum]
  fin_cases who <;>
    simp [FinDist.prob_product, FinDist.prob_uniformOfFintype, Fintype.sum_prod_type,
      payoff, finTwoArrowEquiv, piFinTwoEquiv] <;> ring

/-- Even ideal binding does not make a losing reveal preferable to a refund. -/
theorem refund_deviation_value (last : TestPlayer) :
    expectedUtility (Runtime.SelectiveAbort.game program.game.behavioral last (fun _ => 0)).utility
      last ((Runtime.SelectiveAbort.game program.game.behavioral last (fun _ => 0)).form.play
        (Runtime.SelectiveAbort.withRule program.game.behavioral fairPolicy last
          (Runtime.SelectiveAbort.optimalRule 0))) = 1 / 2 := by
  rw [Runtime.SelectiveAbort.optimal_value, fair_clipped_payoff]
  norm_num

theorem refund_not_nash (last : TestPlayer) :
    ¬ IsNash (Runtime.SelectiveAbort.game program.game.behavioral last (fun _ => 0)).form
      (euPreference
        (Runtime.SelectiveAbort.game program.game.behavioral last (fun _ => 0)).utility)
      (Runtime.SelectiveAbort.compileProfile program.game.behavioral fairPolicy) := by
  intro hnash
  have hdev := (isNash_iff _).mp hnash last
    ⟨fairPolicy last, Runtime.SelectiveAbort.optimalRule 0⟩
  change expectedUtility _ _ _ ≤ expectedUtility _ _ _ at hdev
  change expectedUtility _ last
    ((Runtime.SelectiveAbort.game program.game.behavioral last (fun _ => 0)).form.play
      (Runtime.SelectiveAbort.withRule program.game.behavioral fairPolicy last
        (Runtime.SelectiveAbort.optimalRule 0))) ≤ _ at hdev
  rw [refund_deviation_value, Runtime.SelectiveAbort.honest_expectedUtility] at hdev
  have hzero := expectedUtility_eq_zero_of_opponent_fair fairPolicy last
    (fun other _ => initialLaw_fair other)
  rw [hzero] at hdev
  norm_num at hdev

theorem clipped_eq_payoff
    (profile : (who : TestPlayer) → program.information.BehavioralPolicy who)
    (who : TestPlayer) (abortValue : ℝ) (hbound : abortValue ≤ -1) :
    (program.game.behavioral.form.play profile).expect
      (fun history => max (program.game.behavioral.utility history who) abortValue) =
        expectedUtility program.game.behavioral.utility who
          (program.game.behavioral.form.play profile) := by
  rw [expectedPayoffObservable_eq profile who (fun value => max value abortValue),
    expectedUtility_eq]
  apply FinDist.expect_congr
  intro bits _
  apply max_eq_left
  have hlower : (-1 : ℝ) ≤ payoff bits who := by
    unfold payoff
    split <;> split <;> norm_num
  exact hbound.trans hlower

/-- Sharp net-payoff threshold for the final-veto model. This includes changes
to the player's whole source behavioral policy, not just its reveal decision.
The theorem concerns utilities; it does not implement or fund a deposit. -/
theorem abort_threshold_iff (last : TestPlayer) (abortPayoff : TestPlayer → ℝ) :
    IsNash (Runtime.SelectiveAbort.game program.game.behavioral last abortPayoff).form
      (euPreference (Runtime.SelectiveAbort.game program.game.behavioral last abortPayoff).utility)
      (Runtime.SelectiveAbort.compileProfile program.game.behavioral fairPolicy) ↔
    abortPayoff last ≤ -1 := by
  rw [Runtime.SelectiveAbort.nash_compile_iff]
  constructor
  · rintro ⟨_, hbound⟩
    have h := hbound (fairPolicy last)
    have hzero := expectedUtility_eq_zero_of_opponent_fair fairPolicy last
      (fun other _ => initialLaw_fair other)
    have hsame : Profile.update (sig := program.game.behavioral.form.sig)
        fairPolicy last (fairPolicy last) = fairPolicy := by
      exact Function.update_eq_self last fairPolicy
    rw [hsame] at h
    rw [fair_clipped_payoff, hzero] at h
    have hwin := le_max_left (1 : ℝ) (abortPayoff last)
    have habort := le_max_right (-1 : ℝ) (abortPayoff last)
    linarith
  · intro hbound
    refine ⟨fair_isNash, ?_⟩
    intro replacement
    rw [clipped_eq_payoff _ last _ hbound]
    exact (isNash_iff _).mp fair_isNash last replacement

/-- info: 'VegasTests.RuntimeBoundaries.no_public_submission_adequacy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.RuntimeBoundaries.no_public_submission_adequacy

/-- info: 'VegasTests.RuntimeBoundaries.refund_deviation_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.RuntimeBoundaries.refund_deviation_value

/-- info: 'VegasTests.RuntimeBoundaries.abort_threshold_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.RuntimeBoundaries.abort_threshold_iff

end VegasTests.RuntimeBoundaries
