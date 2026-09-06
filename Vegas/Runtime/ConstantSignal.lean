/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Runtime.FailureObservation
import GameTheory.Core.Approximate

/-!
# Profile-local preservation under a constant extra signal

The source responder cannot observe the submitting value. The target responder
receives a deterministic signal about it. Compiled responders ignore the extra
signal. At a profile where the signal is constant on the submitter's support,
every unilateral target deviation has an exact source-law counterpart.

The submitter may randomize over many hidden values, and a deviating submitter
may change the signal. The signal is only required to be constant while that
player follows the designated profile. There are no subsequent submitter
choices, runtime environment, fees, or cryptographic implementation here.
-/

noncomputable section

namespace Vegas.Runtime.ConstantSignal

open GameTheory GameTheory.Math.Probability

variable {Value Signal Action : Type}

abbrev sourceSignature (Value Action : Type) :=
  FailureObservation.signature Value Action Value

abbrev targetSignature (Value Signal Action : Type) : GameSignature Bool where
  Strategy
    | false => FinDist Value
    | true => Signal → FinDist Action
  Outcome := Value × Action

def targetPlay (observe : Value → Signal)
    (profile : Profile (targetSignature Value Signal Action)) : FinDist (Value × Action) :=
  FailureObservation.responseLaw observe (profile false) (profile true)

def targetGame (observe : Value → Signal) (utility : Value × Action → Bool → ℝ) :
    UtilityGame Bool where
  form := ⟨targetSignature Value Signal Action, targetPlay observe⟩
  utility := utility

def compileStrategy : (who : Bool) → (sourceSignature Value Action).Strategy who →
    (targetSignature Value Signal Action).Strategy who
  | false, strategy => strategy
  | true, strategy => fun _ => strategy

def compileProfile (profile : Profile (sourceSignature Value Action)) :
    Profile (targetSignature Value Signal Action) :=
  fun who => compileStrategy who (profile who)

/-- This translator is local to the signal value at the designated profile.
It does not claim a uniform translator working across all source profiles. -/
def backtranslate (signal : Signal) :
    (who : Bool) → (targetSignature Value Signal Action).Strategy who →
      (sourceSignature Value Action).Strategy who
  | false, strategy => strategy
  | true, strategy => strategy signal

theorem backtranslate_compile (signal : Signal) (who : Bool)
    (strategy : (sourceSignature Value Action).Strategy who) :
    backtranslate signal who (compileStrategy who strategy) = strategy := by
  cases who <;> rfl

/-- Compiled play agrees for every profile, even those with variable signals. -/
theorem compiled_law (observe : Value → Signal)
    (profile : Profile (sourceSignature Value Action)) :
    targetPlay observe (compileProfile profile) = FailureObservation.play id profile := rfl

/-- Exact outcome-law correspondence for every unilateral replacement at a
constant-signal profile. Neither player is restricted to compiled deviations. -/
theorem deviation_law (observe : Value → Signal)
    (profile : Profile (sourceSignature Value Action)) (signal : Signal)
    (hconstant : ∀ value ∈ (profile false).support, observe value = signal)
    (who : Bool) (replacement : (targetSignature Value Signal Action).Strategy who) :
    targetPlay observe (Profile.update (compileProfile profile) who replacement) =
      FailureObservation.play id
        (Profile.update profile who (backtranslate signal who replacement)) := by
  classical
  cases who with
  | false =>
    simp [targetPlay, FailureObservation.responseLaw, FailureObservation.play,
      Profile.update, Function.update, compileProfile, compileStrategy, backtranslate]
  | true =>
    simp only [targetPlay, FailureObservation.responseLaw, FailureObservation.play,
      Profile.update, Function.update, compileProfile, compileStrategy, backtranslate,
      Bool.false_eq_true, ↓reduceDIte, id_eq]
    apply FinDist.bind_congr
    intro value hvalue
    rw [hconstant value hvalue]

/-- Every unilateral bound on a terminal observable is equivalent at the two
profiles. The observable may measure harm to another player, not the deviator's
utility. Neither equilibrium nor rationality is a premise. -/
theorem deviation_bound_iff (observe : Value → Signal)
    (profile : Profile (sourceSignature Value Action)) (signal : Signal)
    (hconstant : ∀ value ∈ (profile false).support, observe value = signal)
    (who : Bool) (observable : Value × Action → ℝ) (bound : ℝ) :
    (∀ replacement, (targetPlay observe
      (Profile.update (compileProfile profile) who replacement)).expect observable ≤ bound) ↔
    (∀ replacement, (FailureObservation.play id
      (Profile.update profile who replacement)).expect observable ≤ bound) := by
  constructor
  · intro hbound replacement
    have h := hbound (compileStrategy who replacement)
    rw [deviation_law observe profile signal hconstant,
      backtranslate_compile] at h
    exact h
  · intro hbound replacement
    rw [deviation_law observe profile signal hconstant]
    exact hbound (backtranslate signal who replacement)

/-- Same-error approximate Nash equivalence at a constant-signal profile.
The conclusion concerns the actual target policy space with its extra signal. -/
theorem approximate_nash_iff (observe : Value → Signal)
    (utility : Value × Action → Bool → ℝ)
    (profile : Profile (sourceSignature Value Action)) (signal : Signal)
    (hconstant : ∀ value ∈ (profile false).support, observe value = signal) (ε : ℝ) :
    IsεNash (targetGame observe utility).form utility ε (compileProfile profile) ↔
      IsεNash (FailureObservation.game (Raw := Value) id utility).form utility ε profile := by
  rw [isεNash_iff, isεNash_iff]
  apply forall_congr'
  intro who
  change (∀ replacement,
    (targetPlay observe (Profile.update (compileProfile profile) who replacement)).expect
      (fun outcome => utility outcome who) ≤
        (targetPlay observe (compileProfile profile)).expect
          (fun outcome => utility outcome who) + ε) ↔ _
  rw [compiled_law]
  exact deviation_bound_iff observe profile signal hconstant who
    (fun outcome => utility outcome who) _

theorem nash_iff (observe : Value → Signal) (utility : Value × Action → Bool → ℝ)
    (profile : Profile (sourceSignature Value Action)) (signal : Signal)
    (hconstant : ∀ value ∈ (profile false).support, observe value = signal) :
    IsNash (targetGame observe utility).form (euPreference utility) (compileProfile profile) ↔
      IsNash (FailureObservation.game (Raw := Value) id utility).form
        (euPreference utility) profile := by
  rw [isNash_iff_isεNash_zero, isNash_iff_isεNash_zero]
  exact approximate_nash_iff observe utility profile signal hconstant 0

/-- A profile-local strict preference for completion suffices to rule out
quitting at a source Nash profile. Global strict dominance is not needed. -/
theorem no_quit_of_completion_better (utility : Bool × Action → Bool → ℝ)
    (profile : Profile (sourceSignature Bool Action))
    (hnash : IsNash (FailureObservation.game (Raw := Bool) id utility).form
      (euPreference utility) profile)
    (hbetter : (profile true).expect (fun action => utility (true, action) false) <
      (profile true).expect (fun action => utility (false, action) false)) :
    ∀ value ∈ (profile false).support, value = false := by
  classical
  let valueOf := fun value => (profile true).expect (fun action => utility (value, action) false)
  have hbound : ∀ value ∈ (profile false).support, valueOf value ≤ valueOf false := by
    intro value _
    cases value
    · exact le_rfl
    · exact hbetter.le
  have hdev := (isNash_iff _).mp hnash false (FinDist.pure false)
  change expectedUtility utility false
      (FailureObservation.play id (Profile.update profile false (FinDist.pure false))) ≤
    expectedUtility utility false (FailureObservation.play id profile) at hdev
  simp only [FailureObservation.play, Profile.update, Function.update, ↓reduceDIte,
    Bool.true_eq_false, FinDist.pure_bind, expectedUtility, FinDist.expect_bind,
    FinDist.expect_map, id_eq] at hdev
  have hequal : (profile false).expect valueOf = valueOf false :=
    le_antisymm (FinDist.expect_le_of_forall _ _ _ hbound) hdev
  intro value hvalue
  have h := FinDist.eq_of_expect_eq_of_le
    (profile false) valueOf (valueOf false) hbound hequal hvalue
  cases value
  · rfl
  · exact False.elim (hbetter.ne h)

/-- Pointwise strict dominance of quit by completion implies the weaker
profile-local preference used above, for every finite randomized responder. -/
theorem completion_better_of_dominance (utility : Bool × Action → Bool → ℝ)
    (hdominates : ∀ action, utility (true, action) false < utility (false, action) false)
    (respond : FinDist Action) :
    respond.expect (fun action => utility (true, action) false) <
      respond.expect (fun action => utility (false, action) false) := by
  obtain ⟨action, haction⟩ := respond.support_nonempty
  have h := FinDist.expect_lt_of_mem_support respond
    (fun action => utility (true, action) false - utility (false, action) false) 0
    (fun action _ => sub_nonpos.mpr (hdominates action).le) haction
    (sub_neg.mpr (hdominates action))
  rw [FinDist.expect_sub] at h
  exact sub_neg.mp h

/-- Source strict dominance of quitting preserves each source Nash profile
under early exposure of the quit bit in this concrete compiler. -/
theorem nash_preserved_of_dominated_quit (utility : Bool × Action → Bool → ℝ)
    (hdominates : ∀ action, utility (true, action) false < utility (false, action) false)
    (profile : Profile (sourceSignature Bool Action))
    (hnash : IsNash (FailureObservation.game (Raw := Bool) id utility).form
      (euPreference utility) profile) :
    IsNash (targetGame id utility).form (euPreference utility) (compileProfile profile) :=
  (nash_iff id utility profile false (no_quit_of_completion_better utility profile hnash
    (completion_better_of_dominance utility hdominates (profile true)))).mpr hnash

/-- info: 'Vegas.Runtime.ConstantSignal.deviation_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Runtime.ConstantSignal.deviation_law

/-- info: 'Vegas.Runtime.ConstantSignal.approximate_nash_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Runtime.ConstantSignal.approximate_nash_iff

/-- info: 'Vegas.Runtime.ConstantSignal.deviation_bound_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Runtime.ConstantSignal.deviation_bound_iff

/-- info: 'Vegas.Runtime.ConstantSignal.nash_preserved_of_dominated_quit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Runtime.ConstantSignal.nash_preserved_of_dominated_quit

end Vegas.Runtime.ConstantSignal
