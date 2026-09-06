/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Runtime.FailureObservation

/-!
# Early-visible quitting versus delayed failure resolution

`true` denotes quit and `false` completion. In the delayed model the responder
chooses before learning this bit; in the early model it receives the bit first.
These are finite strategic kernels with explicitly different information,
not cryptographic or transaction implementations. Utility depends only on the
resolved bit and the responding action, never on event order.
-/

noncomputable section

namespace VegasTests.FailureObservation

open GameTheory GameTheory.Math.Probability Vegas.Runtime

abbrev fair : FinDist Bool := FinDist.uniformOfFintype

abbrev delayedSignature := FailureObservation.signature Bool Bool Bool

abbrev earlySignature : GameSignature Bool where
  Strategy
    | false => FinDist Bool
    | true => Bool → FinDist Bool
  Outcome := Bool × Bool

def earlyPlay (profile : Profile earlySignature) : FinDist (Bool × Bool) :=
  FailureObservation.responseLaw id (profile false) (profile true)

def utility (outcome : Bool × Bool) (who : Bool) : ℝ :=
  let correct : ℝ := if outcome.1 = outcome.2 then 1 else 0
  if who then correct else -correct

abbrev delayedGame := FailureObservation.game (Raw := Bool) id utility

def earlyGame : UtilityGame Bool where
  form := ⟨earlySignature, earlyPlay⟩
  utility := utility

def delayedFair : Profile delayedSignature
  | false => fair
  | true => fair

def compileProfile (profile : Profile delayedSignature) : Profile earlySignature
  | false => profile false
  | true => fun _ => profile true

/-- Even the complete terminal law matches for every compiled profile. -/
theorem compiled_law (profile : Profile delayedSignature) :
    earlyGame.form.play (compileProfile profile) = delayedGame.form.play profile := rfl

theorem delayed_deviation_value (who : Bool)
    (replacement : delayedSignature.Strategy who) :
    expectedUtility delayedGame.utility who
      (delayedGame.form.play (Profile.update delayedFair who replacement)) =
        if who then 1 / 2 else -(1 / 2) := by
  classical
  cases who <;>
    simp only [expectedUtility, delayedGame, FailureObservation.game, FailureObservation.play,
      Profile.update, Function.update, delayedFair, ↓reduceDIte,
      Bool.false_eq_true, Bool.true_eq_false, FinDist.expect_bind, FinDist.expect_map]
  all_goals
    have hmass : replacement.prob false + replacement.prob true = 1 := by
      simpa [add_comm] using replacement.sum_prob
    simp [utility, FinDist.expect_eq_sum, FinDist.prob_uniformOfFintype]
    linarith

theorem delayed_fair_value (who : Bool) :
    expectedUtility delayedGame.utility who (delayedGame.form.play delayedFair) =
      if who then 1 / 2 else -(1 / 2) := by
  simpa only [Profile.update_eq_self] using delayed_deviation_value who (delayedFair who)

theorem delayed_fair_isNash :
    IsNash delayedGame.form (euPreference delayedGame.utility) delayedFair := by
  rw [isNash_iff]
  intro who replacement
  change expectedUtility _ _ _ ≤ expectedUtility _ _ _
  rw [delayed_deviation_value, delayed_fair_value]

def copySignal : Bool → FinDist Bool := FinDist.pure

/-- Observing whether quitting occurred before responding allows perfect
prediction, against every submitter law. -/
theorem early_copy_value (submit : FinDist Bool) :
    (FailureObservation.responseLaw id submit copySignal).expect
      (fun outcome => utility outcome true) = 1 := by
  simp [FailureObservation.responseLaw, copySignal, FinDist.expect_bind,
    utility]

theorem early_compiled_not_nash :
    ¬ IsNash earlyGame.form (euPreference earlyGame.utility)
      (compileProfile delayedFair) := by
  intro hnash
  have hdev := (isNash_iff _).mp hnash true copySignal
  change expectedUtility _ _ _ ≤ expectedUtility _ _ _ at hdev
  have hleft : expectedUtility earlyGame.utility true
      (earlyGame.form.play (Profile.update (compileProfile delayedFair) true copySignal)) = 1 := by
    simpa [expectedUtility, earlyGame, earlyPlay, compileProfile, Profile.update, delayedFair] using
      early_copy_value fair
  have hright : expectedUtility earlyGame.utility true
      (earlyGame.form.play (compileProfile delayedFair)) = 1 / 2 := by
    rw [compiled_law]
    exact delayed_fair_value true
  rw [hleft, hright] at hdev
  norm_num at hdev

/-- No delayed responder replacement can reproduce this early responder
deviation against the same fair submitter. This includes randomized responses. -/
theorem no_delayed_response (replacement : FinDist Bool) :
    FailureObservation.responseLaw id fair copySignal ≠
      delayedGame.form.play (Profile.update delayedFair true replacement) := by
  intro hequal
  have hvalue := congrArg (fun law => law.expect (fun outcome => utility outcome true)) hequal
  rw [early_copy_value] at hvalue
  have hdelayed := delayed_deviation_value true replacement
  change (delayedGame.form.play (Profile.update delayedFair true replacement)).expect
    (fun outcome => utility outcome true) = (1 : ℝ) / 2 at hdelayed
  have hbad : (1 : ℝ) = 1 / 2 := hvalue.trans hdelayed
  norm_num at hbad

/-- Allowing a profile-local finite mixture of source replacements does not
repair the missing signal. Every component still faces the same fair sender. -/
theorem no_delayed_response_mixture (replacements : FinDist (FinDist Bool)) :
    FailureObservation.responseLaw id fair copySignal ≠
      replacements.bind (fun replacement =>
        delayedGame.form.play (Profile.update delayedFair true replacement)) := by
  intro hequal
  have hvalue := congrArg (fun law => law.expect (fun outcome => utility outcome true)) hequal
  rw [early_copy_value, FinDist.expect_bind] at hvalue
  have hcomponent (replacement : FinDist Bool) :
      (delayedGame.form.play (Profile.update delayedFair true replacement)).expect
        (fun outcome => utility outcome true) = (1 : ℝ) / 2 :=
    delayed_deviation_value true replacement
  have hmean : replacements.expect (fun replacement =>
      (delayedGame.form.play (Profile.update delayedFair true replacement)).expect
        (fun outcome => utility outcome true)) = (1 : ℝ) / 2 := by
    calc
      _ = replacements.expect (fun _ => (1 : ℝ) / 2) := by
        apply FinDist.expect_congr
        intro replacement _
        exact hcomponent replacement
      _ = _ := FinDist.expect_const _ _
  have hbad : (1 : ℝ) = 1 / 2 := hvalue.trans hmean
  norm_num at hbad

/-- A deliberately finite failure vocabulary. These labels carry no claim
that all concrete byte strings or cryptographic attacks have been abstracted. -/
inductive Failure where
  | explicitQuit
  | missingCommitment
  | malformedCommitment
  | withheldOpening
  | badOpening
  | invalidValue
  deriving DecidableEq, Fintype

abbrev Raw := Bool ⊕ Failure

def decode : Raw → Option Bool
  | .inl value => some value
  | .inr _ => none

def encode : Option Bool → Raw
  | some value => .inl value
  | none => .inr .explicitQuit

theorem decode_encode (value : Option Bool) : decode (encode value) = value := by
  cases value <;> rfl

/-- All six failures can be collapsed after the response barrier for arbitrary
utilities of the optional outcome and response, and all finite mixed actions. -/
def failure_adequacy (payoff : Option Bool × Bool → Bool → ℝ) :
    DeviationAdequacy
      (FailureObservation.game (Raw := Option Bool) id payoff)
      (FailureObservation.game decode payoff) :=
  FailureObservation.adequacy decode encode decode_encode payoff

/-- info: 'VegasTests.FailureObservation.early_compiled_not_nash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.FailureObservation.early_compiled_not_nash

/-- info: 'VegasTests.FailureObservation.no_delayed_response_mixture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.FailureObservation.no_delayed_response_mixture

/-- info: 'VegasTests.FailureObservation.failure_adequacy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.FailureObservation.failure_adequacy

end VegasTests.FailureObservation
