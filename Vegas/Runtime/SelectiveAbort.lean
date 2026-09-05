/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Runtime.DeviationAdequacy

/-!
# A final informed refusal

This runtime pass gives one designated player a final decision to complete or
abort. The decision observes only that player's prospective settlement utility;
it cannot change the already generated source outcome. Aborting produces an
explicit terminal outcome with a specified payoff vector. A last revealer who
knows its payoff and can obtain a timeout refund has precisely this capability.
This abstraction assumes that information and refusal capability; it is not a
proof that every commitment protocol provides them.

The optimal refusal rule clips the player's payoff from below at its abort
payoff. The resulting support criterion is exact for the added final decision,
including randomized refusal rules. It separates binding a commitment from
enforcing its eventual disclosure.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Vegas.Runtime.SelectiveAbort

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]

abbrev Rule := ℝ → FinDist Bool

abbrev signature (source : UtilityGame Player) : GameSignature Player where
  Strategy who := source.form.sig.Strategy who × Rule
  Outcome := Option source.form.sig.Outcome

def utility (source : UtilityGame Player) (abortPayoff : Player → ℝ) :
    Option source.form.sig.Outcome → Player → ℝ
  | some outcome, who => source.utility outcome who
  | none, who => abortPayoff who

def play (source : UtilityGame Player) (last : Player) (profile : Profile (signature source)) :
    FinDist (Option source.form.sig.Outcome) :=
  (source.form.play (fun who => (profile who).1)).bind fun outcome =>
    ((profile last).2 (source.utility outcome last)).map fun complete =>
      if complete then some outcome else none

def game (source : UtilityGame Player) (last : Player) (abortPayoff : Player → ℝ) :
    UtilityGame Player where
  form := ⟨signature source, play source last⟩
  utility := utility source abortPayoff

def alwaysComplete : Rule := fun _ => FinDist.pure true

def compileProfile (source : UtilityGame Player) (profile : Profile source.form.sig) :
    Profile (signature source) := fun who => ⟨profile who, alwaysComplete⟩

/-- Retain all source choices and change only the final refusal rule. -/
def withRule (source : UtilityGame Player) (profile : Profile source.form.sig)
    (last : Player) (rule : Rule) : Profile (signature source) :=
  Profile.update (compileProfile source profile) last ⟨profile last, rule⟩

theorem withRule_source (source : UtilityGame Player) (profile : Profile source.form.sig)
    (last : Player) (rule : Rule) :
    (fun who => (withRule source profile last rule who).1) = profile := by
  funext who
  by_cases heq : who = last
  · subst who; simp [withRule]
  · simp [withRule, Profile.update, heq, compileProfile]

theorem withRule_law (source : UtilityGame Player) (profile : Profile source.form.sig)
    (last : Player) (rule : Rule) :
    play source last (withRule source profile last rule) =
      (source.form.play profile).bind fun outcome =>
        (rule (source.utility outcome last)).map fun complete =>
          if complete then some outcome else none := by
  simp only [play, withRule_source]
  simp [withRule]

omit [DecidableEq Player] in
/-- Honest completion preserves the full source outcome law, with an explicit
successful-settlement tag. Abort is not silently decoded as a source outcome. -/
theorem honest_law (source : UtilityGame Player) (profile : Profile source.form.sig)
    (last : Player) :
    play source last (compileProfile source profile) = (source.form.play profile).map some := by
  simp [play, compileProfile, alwaysComplete, FinDist.map_eq_bind]

def optimalRule (abortValue : ℝ) : Rule := fun value =>
  FinDist.pure (decide (abortValue ≤ value))

theorem optimal_value (source : UtilityGame Player) (profile : Profile source.form.sig)
    (last : Player) (abortPayoff : Player → ℝ) :
    expectedUtility (game source last abortPayoff).utility last
      ((game source last abortPayoff).form.play
        (withRule source profile last (optimalRule (abortPayoff last)))) =
      (source.form.play profile).expect
        (fun outcome => max (source.utility outcome last) (abortPayoff last)) := by
  change (play source last _).expect (fun outcome => utility source abortPayoff outcome last) = _
  rw [withRule_law, FinDist.expect_bind]
  apply FinDist.expect_congr
  intro outcome _
  by_cases hle : abortPayoff last ≤ source.utility outcome last
  · simp [optimalRule, hle, utility]
  · simp [optimalRule, hle, utility, max_eq_right (le_of_not_ge hle)]

/-- No randomized refusal rule does better than clipping at the abort payoff. -/
theorem rule_value_le (source : UtilityGame Player) (profile : Profile source.form.sig)
    (last : Player) (abortPayoff : Player → ℝ) (rule : Rule) :
    expectedUtility (game source last abortPayoff).utility last
      ((game source last abortPayoff).form.play (withRule source profile last rule)) ≤
      (source.form.play profile).expect
        (fun outcome => max (source.utility outcome last) (abortPayoff last)) := by
  change (play source last _).expect (fun outcome => utility source abortPayoff outcome last) ≤ _
  rw [withRule_law, FinDist.expect_bind]
  apply FinDist.expect_mono
  intro outcome _
  rw [FinDist.expect_map]
  apply FinDist.expect_le_of_forall
  intro complete _
  cases complete
  · exact le_max_right _ _
  · exact le_max_left _ _

/-- The upper bound is attained by a deterministic refusal policy. -/
theorem all_rules_bound_iff (source : UtilityGame Player) (profile : Profile source.form.sig)
    (last : Player) (abortPayoff : Player → ℝ) (bound : ℝ) :
    (∀ rule, expectedUtility (game source last abortPayoff).utility last
      ((game source last abortPayoff).form.play (withRule source profile last rule)) ≤ bound) ↔
    (source.form.play profile).expect
      (fun outcome => max (source.utility outcome last) (abortPayoff last)) ≤ bound := by
  constructor
  · intro hbound
    simpa only [optimal_value] using hbound (optimalRule (abortPayoff last))
  · intro hbound rule
    exact (rule_value_le source profile last abortPayoff rule).trans hbound

omit [DecidableEq Player] in
/-- Clipping changes no expectation exactly when it changes no supported value. -/
theorem expect_max_eq_iff {Outcome : Type*} (law : FinDist Outcome)
    (payoff : Outcome → ℝ) (abortValue : ℝ) :
    law.expect (fun outcome => max (payoff outcome) abortValue) = law.expect payoff ↔
      ∀ outcome ∈ law.support, abortValue ≤ payoff outcome := by
  constructor
  · intro heq outcome hmem
    have hzero : law.expect (fun outcome =>
        payoff outcome - max (payoff outcome) abortValue) = 0 := by
      rw [FinDist.expect_sub, heq]
      ring
    have hpoint := FinDist.eq_of_expect_eq_of_le law
      (fun outcome => payoff outcome - max (payoff outcome) abortValue) 0
      (fun outcome _ => sub_nonpos.mpr (le_max_left _ _)) hzero hmem
    have hmax := le_max_right (payoff outcome) abortValue
    linarith
  · intro hbound
    exact FinDist.expect_congr fun outcome hmem => max_eq_left (hbound outcome hmem)

/-- Exact criterion for the final veto to add no profitable deviation while
upstream source choices are fixed. This is not merely a sufficient deposit bound. -/
theorem no_profitable_refusal_iff (source : UtilityGame Player)
    (profile : Profile source.form.sig) (last : Player) (abortPayoff : Player → ℝ) :
    (∀ rule, expectedUtility (game source last abortPayoff).utility last
      ((game source last abortPayoff).form.play (withRule source profile last rule)) ≤
        expectedUtility source.utility last (source.form.play profile)) ↔
    ∀ outcome ∈ (source.form.play profile).support,
      abortPayoff last ≤ source.utility outcome last := by
  rw [all_rules_bound_iff]
  change _ ≤ (source.form.play profile).expect (fun outcome => source.utility outcome last) ↔ _
  have hle : (source.form.play profile).expect (fun outcome => source.utility outcome last) ≤
      (source.form.play profile).expect
        (fun outcome => max (source.utility outcome last) (abortPayoff last)) :=
    FinDist.expect_mono fun _ _ => le_max_left _ _
  constructor
  · intro hbound
    exact (expect_max_eq_iff _ _ _).mp (le_antisymm hbound hle)
  · intro hbound
    exact le_of_eq ((expect_max_eq_iff _ _ _).mpr hbound)

omit [DecidableEq Player] in
theorem honest_expectedUtility (source : UtilityGame Player) (profile : Profile source.form.sig)
    (last : Player) (abortPayoff : Player → ℝ) (who : Player) :
    expectedUtility (game source last abortPayoff).utility who
      ((game source last abortPayoff).form.play (compileProfile source profile)) =
      expectedUtility source.utility who (source.form.play profile) := by
  change (play source last _).expect (fun outcome => utility source abortPayoff outcome who) = _
  rw [honest_law, FinDist.expect_map]
  rfl

/-- One supported loss above which abort refunds the player suffices to destroy
the honestly completed equilibrium. The source need not itself be an equilibrium. -/
theorem not_nash_of_profitable_abort (source : UtilityGame Player)
    (profile : Profile source.form.sig) (last : Player) (abortPayoff : Player → ℝ)
    (outcome : source.form.sig.Outcome) (hmem : outcome ∈ (source.form.play profile).support)
    (hprofitable : source.utility outcome last < abortPayoff last) :
    ¬ IsNash (game source last abortPayoff).form
      (euPreference (game source last abortPayoff).utility) (compileProfile source profile) := by
  intro hnash
  have hbound : ∀ rule, expectedUtility (game source last abortPayoff).utility last
      ((game source last abortPayoff).form.play (withRule source profile last rule)) ≤
        expectedUtility source.utility last (source.form.play profile) := by
    intro rule
    have h := (isNash_iff _).mp hnash last ⟨profile last, rule⟩
    change expectedUtility _ _ _ ≤ expectedUtility _ _ _ at h
    rw [honest_expectedUtility] at h
    exact h
  exact (not_le_of_gt hprofitable)
    ((no_profitable_refusal_iff source profile last abortPayoff).mp hbound outcome hmem)

theorem compile_update (source : UtilityGame Player) (profile : Profile source.form.sig)
    (who : Player) (replacement : source.form.sig.Strategy who) :
    compileProfile source (Profile.update profile who replacement) =
      Profile.update (compileProfile source profile) who ⟨replacement, alwaysComplete⟩ := by
  funext player
  by_cases heq : player = who
  · subst player; simp [compileProfile]
  · simp [compileProfile, Profile.update, heq]

theorem last_update (source : UtilityGame Player) (profile : Profile source.form.sig)
    (last : Player) (replacement : source.form.sig.Strategy last) (rule : Rule) :
    Profile.update (compileProfile source profile) last ⟨replacement, rule⟩ =
      withRule source (Profile.update profile last replacement) last rule := by
  funext player
  by_cases heq : player = last
  · subst player; simp [withRule]
  · simp [withRule, Profile.update, heq, compileProfile]

theorem other_update_law (source : UtilityGame Player) (profile : Profile source.form.sig)
    (last who : Player) (hne : who ≠ last) (replacement : source.form.sig.Strategy who)
    (rule : Rule) :
    play source last (Profile.update (compileProfile source profile) who ⟨replacement, rule⟩) =
      (source.form.play (Profile.update profile who replacement)).map some := by
  have hsource : (fun player =>
      (Profile.update (compileProfile source profile) who ⟨replacement, rule⟩ player).1) =
        Profile.update profile who replacement := by
    funext player
    by_cases heq : player = who
    · subst player; simp
    · simp [compileProfile, Profile.update, heq]
  simp only [play, hsource]
  simp [Profile.update, Ne.symm hne, compileProfile, alwaysComplete, FinDist.map_eq_bind]

/-- Exact equilibrium criterion for this pass, including deviations which
change both the upstream source strategy and the final refusal rule. Source
Nash alone is insufficient: the last player's deviation bounds must also hold
after every prospective payoff is clipped at the abort value. -/
theorem nash_compile_iff (source : UtilityGame Player) (profile : Profile source.form.sig)
    (last : Player) (abortPayoff : Player → ℝ) :
    IsNash (game source last abortPayoff).form
      (euPreference (game source last abortPayoff).utility) (compileProfile source profile) ↔
    IsNash source.form (euPreference source.utility) profile ∧
      ∀ replacement : source.form.sig.Strategy last,
        (source.form.play (Profile.update profile last replacement)).expect
          (fun outcome => max (source.utility outcome last) (abortPayoff last)) ≤
            expectedUtility source.utility last (source.form.play profile) := by
  constructor
  · intro hnash
    have htarget := (isNash_iff _).mp hnash
    constructor
    · rw [isNash_iff]
      intro who replacement
      have h := htarget who ⟨replacement, alwaysComplete⟩
      change expectedUtility _ _ _ ≤ expectedUtility _ _ _ at h
      rw [← compile_update, honest_expectedUtility, honest_expectedUtility] at h
      exact h
    · intro replacement
      have h := htarget last ⟨replacement, optimalRule (abortPayoff last)⟩
      change expectedUtility _ _ _ ≤ expectedUtility _ _ _ at h
      rw [last_update, optimal_value, honest_expectedUtility] at h
      exact h
  · rintro ⟨hsource, hlast⟩
    rw [isNash_iff]
    intro who replacement
    obtain ⟨strategy, rule⟩ := replacement
    change expectedUtility _ _ _ ≤ expectedUtility _ _ _
    rw [honest_expectedUtility]
    by_cases heq : who = last
    · subst who
      rw [last_update]
      exact (rule_value_le source (Profile.update profile last strategy) last
        abortPayoff rule).trans (hlast strategy)
    · change (play source last _).expect
        (fun outcome => utility source abortPayoff outcome who) ≤ _
      rw [other_update_law source profile last who heq, FinDist.expect_map]
      exact (isNash_iff _).mp hsource who strategy

end Vegas.Runtime.SelectiveAbort
