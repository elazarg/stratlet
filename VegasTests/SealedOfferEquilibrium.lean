/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.SealedOffer

/-! # Incentives and an adversarial buyer guarantee for sealed offers -/

noncomputable section

namespace VegasTests.SealedOffer

open Vegas GameTheory GameTheory.Protocol GameTheory.Math.Probability
open OptionalDisclosure

theorem pair_value (seller : SenderStrategy) (buyer : ResponderStrategy) (who : TestPlayer) :
    expectedUtility game.utility who (game.form.play (pairProfile seller buyer)) =
      seller.binding.expect fun secret => fairCoin.denote.expect fun signal =>
        (seller.complete secret signal).expect fun complete =>
          (buyer signal (if complete then some secret else none)).expect fun response =>
            utility ⟨secret, signal, if complete then some secret else none, response⟩ who := by
  simp only [expectedUtility, game, finiteForm, finiteLaw, pairProfile,
    FinDist.expect_bind, FinDist.expect_map]

/-- The guarantee includes arbitrary initial binding and informed randomized
quitting. The seller need not be rational or an equilibrium participant. -/
theorem honest_buyer_nonnegative (seller : SenderStrategy) :
    0 ≤ expectedUtility game.utility 1 (game.form.play (pairProfile seller honestBuyer)) := by
  rw [pair_value]
  simp only [honestBuyer, FinDist.expect_pure]
  have hbound := FinDist.expect_mono (μ := seller.binding) (u := fun _ => (0 : ℝ))
    (v := fun secret => fairCoin.denote.expect fun signal =>
      (seller.complete secret signal).expect fun complete =>
        utility ⟨secret, signal, if complete then some secret else none,
          accept signal (if complete then some secret else none)⟩ 1) (by
      intro secret _
      have hsignal := FinDist.expect_mono (μ := fairCoin.denote) (u := fun _ => (0 : ℝ))
        (v := fun signal => (seller.complete secret signal).expect fun complete =>
          utility ⟨secret, signal, if complete then some secret else none,
            accept signal (if complete then some secret else none)⟩ 1) (by
          intro signal _
          have hcomplete := FinDist.expect_mono (μ := seller.complete secret signal)
            (u := fun _ => (0 : ℝ)) (fun complete _ =>
              buyer_nonnegative secret signal (if complete then some secret else none))
          simpa only [FinDist.expect_const] using hcomplete)
      simpa only [FinDist.expect_const] using hsignal)
  simpa only [FinDist.expect_const] using hbound

/-- Honest acceptance is a best reply to every seller policy, not only to
the designated equilibrium seller. -/
theorem honest_buyer_best_response (seller : SenderStrategy) (buyer : ResponderStrategy) :
    expectedUtility game.utility 1 (game.form.play (pairProfile seller buyer)) ≤
      expectedUtility game.utility 1 (game.form.play (pairProfile seller honestBuyer)) := by
  rw [pair_value, pair_value]
  apply FinDist.expect_mono
  intro secret _
  apply FinDist.expect_mono
  intro signal _
  apply FinDist.expect_mono
  intro complete _
  simp only [honestBuyer, FinDist.expect_pure]
  apply FinDist.expect_le_of_forall
  intro response _
  exact buyer_optimal secret signal _ response

/-- Binding before chance limits expected revenue to one, even when opening
or quitting is chosen after observing the signal. -/
theorem seller_revenue_bound (seller : SenderStrategy) :
    expectedUtility game.utility 0 (game.form.play (pairProfile seller honestBuyer)) ≤ 1 := by
  rw [pair_value]
  simp only [honestBuyer, FinDist.expect_pure]
  apply FinDist.expect_le_of_forall
  intro secret _
  calc
    _ ≤ fairCoin.denote.expect (revenueCap secret) := by
      apply FinDist.expect_mono
      intro signal _
      apply FinDist.expect_le_of_forall
      intro complete _
      exact seller_completion_bound secret signal complete
    _ = 1 := expected_revenue_cap secret

theorem honest_seller_value :
    expectedUtility game.utility 0 (game.form.play honestProfile) = 1 := by
  rw [honestProfile, pair_value]
  simp [honestSeller, honestBuyer, utility, accept, amount]

theorem honest_buyer_value :
    expectedUtility game.utility 1 (game.form.play honestProfile) = 1 / 2 := by
  rw [honestProfile, pair_value]
  simp only [honestSeller, FinDist.expect_pure, honestBuyer]
  rw [coin_expect]
  norm_num [utility, accept, amount]

theorem honest_isNash : IsNash game.form (euPreference game.utility) honestProfile := by
  change IsNash finiteForm (euPreference utility) honestProfile
  rw [isNash_iff]
  intro who replacement
  change expectedUtility _ _ _ ≤ expectedUtility _ _ _
  fin_cases who
  · have heq : Profile.update (sig := finiteForm.sig) honestProfile 0 replacement =
        pairProfile replacement honestBuyer := by
      funext player
      fin_cases player <;> simp [honestProfile, pairProfile]
    have hvalue := congrArg (fun profile : Profile finiteForm.sig =>
      expectedUtility utility 0 (finiteLaw profile)) heq
    exact hvalue.le.trans ((seller_revenue_bound replacement).trans_eq honest_seller_value.symm)
  · have heq : Profile.update (sig := finiteForm.sig) honestProfile 1 replacement =
        pairProfile honestSeller replacement := by
      funext player
      fin_cases player <;> simp [honestProfile, pairProfile]
    have hvalue := congrArg (fun profile : Profile finiteForm.sig =>
      expectedUtility utility 1 (finiteLaw profile)) heq
    exact hvalue.le.trans (honest_buyer_best_response honestSeller replacement)

theorem machine_nash_iff (profile : Profile program.game.behavioral.form.sig) :
    IsNash machine.game.behavioral.form (euPreference machine.game.behavioral.utility) profile ↔
      IsNash game.form (euPreference game.utility) (extractProfile profile) := by
  rw [nash_iff_finite]
  have heq : (finiteGame payouts).utility = game.utility :=
    funext fun data => funext fun who => utility_eq data who
  rw [heq]
  rfl

theorem compiled_honest_isNash :
    IsNash machine.game.behavioral.form (euPreference machine.game.behavioral.utility)
      (compileProfile honestProfile) := by
  rw [machine_nash_iff, extract_compile_profile]
  exact honest_isNash

theorem machine_buyer_nonnegative (replacement : program.information.BehavioralPolicy 0) :
    0 ≤ expectedUtility machine.game.behavioral.utility 1
      (machine.game.behavioral.form.play
        (Profile.update (compileProfile honestProfile) 0 replacement)) := by
  rw [expectedUtility_eq_finite, extractProfile_update, extract_compile_profile]
  have heq : Profile.update (sig := finiteForm.sig) honestProfile 0
      (extractPolicy 0 replacement) = pairProfile (extractSender replacement) honestBuyer := by
    funext player
    fin_cases player <;> simp [honestProfile, pairProfile, extractPolicy]
  have hvalue := congrArg (fun profile : Profile finiteForm.sig =>
    expectedUtility (finiteGame payouts).utility 1 (finiteLaw profile)) heq
  have hutility : (finiteGame payouts).utility = game.utility :=
    funext fun data => funext fun who => utility_eq data who
  rw [hutility] at hvalue
  rw [hutility]
  exact (honest_buyer_nonnegative (extractSender replacement)).trans_eq hvalue.symm

theorem serialized_honest_isPlayerNash
    (schedulerUtility : machine.serializedArena.History → ℝ)
    (scheduler : machine.serializedArena.information.BehavioralPolicy .scheduler) :
    Scheduled.IsPlayerNash (machine.serializedGame schedulerUtility).behavioral
      (machine.compileSerializedBehavioralProfile scheduler (compileProfile honestProfile)) :=
  machine.isPlayerNash_compileSerialized_of_isNash schedulerUtility scheduler _
    compiled_honest_isNash

theorem serialized_buyer_nonnegative
    (schedulerUtility : machine.serializedArena.History → ℝ)
    (scheduler : machine.serializedArena.information.BehavioralPolicy .scheduler)
    (replacement : machine.serializedArena.information.BehavioralPolicy (.player 0)) :
    0 ≤ expectedUtility (machine.serializedGame schedulerUtility).behavioral.utility (.player 1)
      ((machine.serializedGame schedulerUtility).behavioral.form.play
        (Profile.update (machine.compileSerializedBehavioralProfile scheduler
          (compileProfile honestProfile)) (.player 0) replacement)) := by
  obtain ⟨alternatives, hlaw⟩ := machine.serializedDeviation_eq_sourceMixture
    scheduler (compileProfile honestProfile) 0 replacement
  have hvalue := congrArg (fun law => law.expect
    (fun state => machine.payoutUtility state 1)) hlaw
  simp only [FinDist.expect_map, FinDist.expect_bind] at hvalue
  have hbound := FinDist.expect_mono (μ := alternatives) (u := fun _ => (0 : ℝ))
    (fun alternative _ => machine_buyer_nonnegative alternative)
  have hnonnegative := (FinDist.expect_const alternatives 0).symm.trans_le hbound
  exact hnonnegative.trans_eq hvalue.symm

end VegasTests.SealedOffer
