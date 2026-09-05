/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Runtime.ObservedAbort

/-!
# Hidden choices, public chance, refusal, and future chance

Two players independently fix hidden bits. A public fair coin then changes the
stakes. Player zero may quit after seeing its own bit and that public coin, but
before seeing the opponent's bit or a final independent chance draw. Completion
reveals the choices and settles a zero-sum payoff. Both original commitments
and the randomized refusal rule can deviate.

This is an explicit finite strategic kernel, not an instantiation of the
VegasCore syntax compiler or of transaction handlers. The causal-law theorem
checks that the final chance draw is made only after the completion decision.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace VegasTests.ObservedAbort

open GameTheory GameTheory.Math.Probability Vegas.Runtime

abbrev Player := Fin 2
abbrev Outcome := (Bool × Bool) × Bool × Bool
abbrev Checkpoint := (Bool × Bool) × Bool
abbrev Info := Bool × Bool
abbrev fair : FinDist Bool := FinDist.uniformOfFintype

abbrev signature : GameSignature Player where
  Strategy _ := FinDist Bool
  Outcome := Outcome

def checkpoints (profile : Profile signature) : FinDist Checkpoint :=
  (profile 0).bind fun left => (profile 1).bind fun right =>
    fair.map fun signal => ((left, right), signal)

def continuation (checkpoint : Checkpoint) : FinDist Outcome :=
  fair.map fun future => (checkpoint.1, checkpoint.2, future)

def sourcePlay (profile : Profile signature) : FinDist Outcome :=
  (checkpoints profile).bind continuation

def sign (bit : Bool) : ℝ := if bit then 1 else -1

def utility (outcome : Outcome) (who : Player) : ℝ :=
  let left := (if outcome.1.1 = outcome.1.2 then 1 else -1) +
    sign outcome.2.1 + sign outcome.2.2
  if who = 0 then left else -left

def source : UtilityGame Player where
  form := ⟨signature, sourcePlay⟩
  utility := utility

def fairProfile : Profile signature := fun _ => fair

/-- Only the player's own commitment and the public chance result are visible. -/
def observe (outcome : Outcome) : Info := (outcome.1.1, outcome.2.1)

def checkpointObserve (checkpoint : Checkpoint) : Info := (checkpoint.1.1, checkpoint.2)

/-- This executable kernel performs the quit decision before the future coin
and never supplies the hidden opponent bit to that decision. -/
def causalPlay (profile : Profile signature) (rule : Vegas.Runtime.ObservedAbort.Rule Info) :
    FinDist (Outcome ⊕ Info) :=
  (checkpoints profile).bind fun checkpoint =>
    (rule (checkpointObserve checkpoint)).bind fun complete =>
      if complete then (continuation checkpoint).map Sum.inl
      else FinDist.pure (Sum.inr (checkpointObserve checkpoint))

theorem causal_law (profile : Profile signature) (rule : Vegas.Runtime.ObservedAbort.Rule Info) :
    Vegas.Runtime.ObservedAbort.run (sourcePlay profile) observe rule =
      causalPlay profile rule := by
  apply Vegas.Runtime.ObservedAbort.run_causal
  intro checkpoint _ outcome hmem
  rw [continuation, FinDist.support_map] at hmem
  obtain ⟨future, _, rfl⟩ := hmem
  rfl

/-- A fair opponent makes both expected payoffs zero, even if the other
player's hidden commitment is drawn from an arbitrary distribution. -/
theorem deviation_zero (who victim : Player) (replacement : FinDist Bool) :
    expectedUtility source.utility victim
      (source.form.play (Profile.update fairProfile who replacement)) = 0 := by
  simp only [expectedUtility, source, sourcePlay, checkpoints, continuation,
    FinDist.expect_bind, FinDist.expect_map]
  fin_cases who <;> fin_cases victim <;>
    simp [utility, sign, Profile.update, fairProfile,
      FinDist.expect_eq_sum, FinDist.prob_uniformOfFintype] <;> ring

theorem fair_value (who : Player) :
    expectedUtility source.utility who (source.form.play fairProfile) = 0 := by
  simpa only [Profile.update_eq_self] using deviation_zero who who (fairProfile who)

theorem fair_isNash : IsNash source.form (euPreference source.utility) fairProfile := by
  rw [isNash_iff]
  intro who replacement
  change expectedUtility _ _ _ ≤ expectedUtility _ _ _
  rw [deviation_zero, fair_value]

/-- Averaging the hidden opponent and future chance leaves only the public
signal's contribution. The refusal rule remains arbitrary and randomized. -/
theorem deviation_rule_value (replacement : FinDist Bool) (abortPayoff : Info → ℝ)
    (rule : Vegas.Runtime.ObservedAbort.Rule Info) :
    Vegas.Runtime.ObservedAbort.value
      (source.form.play (Profile.update fairProfile 0 replacement)) observe
      (fun outcome => source.utility outcome 0) abortPayoff rule =
    replacement.expect fun own => fair.expect fun signal => (rule (own, signal)).expect
      (fun complete => if complete then sign signal else abortPayoff (own, signal)) := by
  simp only [Vegas.Runtime.ObservedAbort.value, source, sourcePlay, checkpoints, continuation,
    FinDist.expect_bind, FinDist.expect_map]
  simp [utility, sign, observe, Profile.update, fairProfile,
    FinDist.expect_eq_sum, FinDist.prob_uniformOfFintype]
  ring

def signalRule (abortValue : ℝ) : Vegas.Runtime.ObservedAbort.Rule Info :=
  fun info => FinDist.pure (decide (abortValue ≤ sign info.2))

theorem signal_rule_value (replacement : FinDist Bool) (abortValue : ℝ) :
    Vegas.Runtime.ObservedAbort.value
      (source.form.play (Profile.update fairProfile 0 replacement)) observe
      (fun outcome => source.utility outcome 0) (fun _ => abortValue) (signalRule abortValue) =
        (max 1 abortValue + max (-1) abortValue) / 2 := by
  rw [deviation_rule_value]
  have hmax : ∀ own signal, (signalRule abortValue (own, signal)).expect
      (fun complete => if complete then sign signal else abortValue) =
        max (sign signal) abortValue := by
    intro own signal
    by_cases hle : abortValue ≤ sign signal
    · simp [signalRule, hle]
    · simp [signalRule, hle, max_eq_right (le_of_not_ge hle)]
  simp only [hmax, FinDist.expect_const]
  simp [FinDist.expect_eq_sum, FinDist.prob_uniformOfFintype, sign]
  ring

theorem deviation_envelope (replacement : FinDist Bool) (abortValue : ℝ) :
    Vegas.Runtime.ObservedAbort.envelope
      (source.form.play (Profile.update fairProfile 0 replacement)) observe
      (fun outcome => source.utility outcome 0) (fun _ => abortValue) =
        (max 1 abortValue + max (-1) abortValue) / 2 := by
  apply le_antisymm
  · apply (Vegas.Runtime.ObservedAbort.all_rules_bound_iff _ _ _ _ _).mp
    intro rule
    rw [deviation_rule_value]
    calc
      _ ≤ replacement.expect
          (fun _ => fair.expect (fun signal => max (sign signal) abortValue)) := by
        apply FinDist.expect_mono
        intro own _
        apply FinDist.expect_mono
        intro signal _
        apply FinDist.expect_le_of_forall
        intro complete _
        cases complete
        · exact le_max_right _ _
        · exact le_max_left _ _
      _ = _ := by
        rw [FinDist.expect_const]
        simp [FinDist.expect_eq_sum, FinDist.prob_uniformOfFintype, sign]
        ring
  · rw [← signal_rule_value replacement abortValue]
    exact Vegas.Runtime.ObservedAbort.value_le_envelope _ _ _ _ _

/-- Full source-choice and refusal deviations give a sharp conditional-payoff
threshold of -1, although individual supported completion payoffs reach -3. -/
theorem abort_threshold_iff (abortPayoff : Info → Player → ℝ) (abortValue : ℝ)
    (hconstant : ∀ info, abortPayoff info 0 = abortValue) :
    IsNash (Vegas.Runtime.ObservedAbort.Game.game source observe 0 abortPayoff).form
      (euPreference (Vegas.Runtime.ObservedAbort.Game.game source observe 0 abortPayoff).utility)
      (Vegas.Runtime.ObservedAbort.Game.compileProfile source fairProfile) ↔ abortValue ≤ -1 := by
  rw [Vegas.Runtime.ObservedAbort.Game.nash_compile_iff]
  have habort : (fun info => abortPayoff info 0) = (fun _ => abortValue) := funext hconstant
  simp only [habort, deviation_envelope, fair_value]
  constructor
  · rintro ⟨_, hbound⟩
    have h := hbound fair
    have hwin := le_max_left (1 : ℝ) abortValue
    have hexit := le_max_right (-1 : ℝ) abortValue
    linarith
  · intro hbound
    refine ⟨fair_isNash, fun _ => ?_⟩
    rw [max_eq_left (by linarith : abortValue ≤ 1), max_eq_left hbound]
    norm_num

/-- The same prospective payoff law gives different exit values depending on
which information is actually available when the player acts. -/
theorem no_information_refund_value :
    Vegas.Runtime.ObservedAbort.envelope (source.form.play fairProfile) (fun _ => ())
      (fun outcome => source.utility outcome 0) (fun _ => 0) = 0 := by
  rw [Vegas.Runtime.ObservedAbort.envelope_no_information]
  change max (expectedUtility source.utility 0 (source.form.play fairProfile)) 0 = 0
  rw [fair_value]
  norm_num

theorem public_signal_refund_value :
    Vegas.Runtime.ObservedAbort.envelope (source.form.play fairProfile) observe
      (fun outcome => source.utility outcome 0) (fun _ => 0) = 1 / 2 := by
  have h := deviation_envelope (fairProfile 0) 0
  simp only [Profile.update_eq_self] at h
  rw [h]
  norm_num

/-- Remembering one's own fixed choice, without the public signal, supplies no
profitable refund decision against the fair opponent. -/
theorem own_choice_rule_value (replacement : FinDist Bool)
    (rule : Vegas.Runtime.ObservedAbort.Rule Bool) :
    Vegas.Runtime.ObservedAbort.value
      (source.form.play (Profile.update fairProfile 0 replacement)) (fun outcome => outcome.1.1)
      (fun outcome => source.utility outcome 0) (fun _ => 0) rule = 0 := by
  change Vegas.Runtime.ObservedAbort.value _ observe _ (fun _ => 0) (fun info => rule info.1) = 0
  rw [deviation_rule_value]
  simp [FinDist.expect_eq_sum, FinDist.prob_uniformOfFintype, sign]

theorem own_choice_envelope (replacement : FinDist Bool) :
    Vegas.Runtime.ObservedAbort.envelope
      (source.form.play (Profile.update fairProfile 0 replacement)) (fun outcome => outcome.1.1)
      (fun outcome => source.utility outcome 0) (fun _ => 0) = 0 := by
  apply le_antisymm
  · apply (Vegas.Runtime.ObservedAbort.all_rules_bound_iff _ _ _ _ _).mp
    intro rule
    exact le_of_eq (own_choice_rule_value replacement rule)
  · have h := Vegas.Runtime.ObservedAbort.value_le_envelope
      (source.form.play (Profile.update fairProfile 0 replacement)) (fun outcome => outcome.1.1)
      (fun outcome => source.utility outcome 0) (fun _ => 0) (fun _ => FinDist.pure true)
    rw [own_choice_rule_value] at h
    exact h

theorem own_choice_refund_isNash :
    IsNash (Vegas.Runtime.ObservedAbort.Game.game source (fun outcome => outcome.1.1)
      0 (fun _ _ => 0)).form
      (euPreference (Vegas.Runtime.ObservedAbort.Game.game source (fun outcome => outcome.1.1)
        0 (fun _ _ => 0)).utility)
      (Vegas.Runtime.ObservedAbort.Game.compileProfile source fairProfile) := by
  rw [Vegas.Runtime.ObservedAbort.Game.nash_compile_iff]
  refine ⟨fair_isNash, ?_⟩
  intro replacement
  rw [own_choice_envelope, fair_value]

theorem payoff_information_refund_value :
    Vegas.Runtime.ObservedAbort.envelope (source.form.play fairProfile)
      (fun outcome => source.utility outcome 0) (fun outcome => source.utility outcome 0)
      (fun _ => 0) = 3 / 4 := by
  rw [Vegas.Runtime.ObservedAbort.envelope_payoff_information]
  simp only [source, sourcePlay, checkpoints, continuation,
    FinDist.expect_bind, FinDist.expect_map]
  norm_num [fairProfile, utility, sign, FinDist.expect_eq_sum,
    FinDist.prob_uniformOfFintype]

theorem supported_loss :
    ((true, false), false, false) ∈ (source.form.play fairProfile).support ∧
      source.utility ((true, false), false, false) 0 = -3 := by
  constructor
  · simp [source, sourcePlay, checkpoints, continuation, fairProfile,
      FinDist.support_bind, FinDist.support_map, FinDist.mem_support_uniformOfFintype]
  · change (-1 : ℝ) + -1 + -1 = -3
    norm_num

/-- The causal runtime admits exactly the same complete strategy profiles as
the information-based model: initial hidden-choice laws plus a local quit rule. -/
def causalGame (abortPayoff : Info → Player → ℝ) : UtilityGame Player where
  form := ⟨Vegas.Runtime.ObservedAbort.Game.signature source Info,
    fun profile => causalPlay (fun who => (profile who).1) (profile 0).2⟩
  utility := (Vegas.Runtime.ObservedAbort.Game.game source observe 0 abortPayoff).utility

theorem causalGame_play_eq (abortPayoff : Info → Player → ℝ)
    (profile : Profile (Vegas.Runtime.ObservedAbort.Game.signature source Info)) :
    (causalGame abortPayoff).form.play profile =
      (Vegas.Runtime.ObservedAbort.Game.game source observe 0 abortPayoff).form.play profile :=
  (causal_law (fun who => (profile who).1) (profile 0).2).symm

/-- The sharp threshold holds in the causally ordered game, not only the
construction which samples a prospective complete outcome first. -/
theorem causal_nash_iff (abortPayoff : Info → Player → ℝ) (abortValue : ℝ)
    (hconstant : ∀ info, abortPayoff info 0 = abortValue) :
    IsNash (causalGame abortPayoff).form (euPreference (causalGame abortPayoff).utility)
      (Vegas.Runtime.ObservedAbort.Game.compileProfile source fairProfile) ↔ abortValue ≤ -1 := by
  rw [← abort_threshold_iff abortPayoff abortValue hconstant]
  simp only [isNash_iff, euPreference_apply, causalGame_play_eq]
  rfl

/-- info: 'VegasTests.ObservedAbort.causal_nash_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ObservedAbort.causal_nash_iff

/-- info: 'VegasTests.ObservedAbort.no_information_refund_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ObservedAbort.no_information_refund_value

/-- info: 'VegasTests.ObservedAbort.public_signal_refund_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ObservedAbort.public_signal_refund_value

/-- info: 'VegasTests.ObservedAbort.payoff_information_refund_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ObservedAbort.payoff_information_refund_value

/-- info: 'VegasTests.ObservedAbort.own_choice_refund_isNash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ObservedAbort.own_choice_refund_isNash

end VegasTests.ObservedAbort
