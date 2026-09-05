/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Runtime.DeviationAdequacy

/-!
# Refusal based on the information actually observed

An outcome law describes the prospective continuation. The quitter observes
only `observe outcome`, then either completes or takes an information-dependent
abort payoff. The rule has no access to the unobserved outcome. Sampling that
prospective outcome first is a distributional construction, not disclosure of
future chance or another player's hidden choice.

The exact refusal value clips the *conditional expected* continuation payoff,
not the realized payoff. Statements concern one designated refusal opportunity;
causality of the observation at a concrete protocol checkpoint is a separate
implementation obligation.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Vegas.Runtime.ObservedAbort

open GameTheory GameTheory.Math.Probability

variable {Outcome Info : Type*}

abbrev Rule (Info : Type*) := Info → FinDist Bool

/-- Successful completion retains the outcome; abort retains the information
used to determine its payoff. Neither branch is decoded silently as the other. -/
def run (law : FinDist Outcome) (observe : Outcome → Info) (rule : Rule Info) :
    FinDist (Outcome ⊕ Info) :=
  law.bind fun outcome => (rule (observe outcome)).map fun complete =>
    if complete then Sum.inl outcome else Sum.inr (observe outcome)

def payoff (completePayoff : Outcome → ℝ) (abortPayoff : Info → ℝ) : Outcome ⊕ Info → ℝ
  | .inl outcome => completePayoff outcome
  | .inr info => abortPayoff info

def value (law : FinDist Outcome) (observe : Outcome → Info)
    (completePayoff : Outcome → ℝ) (abortPayoff : Info → ℝ) (rule : Rule Info) : ℝ :=
  law.expect fun outcome => (rule (observe outcome)).expect fun complete =>
    if complete then completePayoff outcome else abortPayoff (observe outcome)

theorem run_expect (law : FinDist Outcome) (observe : Outcome → Info)
    (completePayoff : Outcome → ℝ) (abortPayoff : Info → ℝ) (rule : Rule Info) :
    (run law observe rule).expect (payoff completePayoff abortPayoff) =
      value law observe completePayoff abortPayoff rule := by
  simp only [run, FinDist.expect_bind, FinDist.expect_map, value]
  apply FinDist.expect_congr
  intro outcome _
  apply FinDist.expect_congr
  intro complete _
  cases complete <;> rfl

def continuationValue (law : FinDist Outcome) (observe : Outcome → Info)
    (completePayoff : Outcome → ℝ) (info : Info) : ℝ :=
  (law.condOnFibre observe info).expect completePayoff

theorem posterior_observe (law : FinDist Outcome) (observe : Outcome → Info)
    (info : Info) (hinfo : info ∈ (law.map observe).support)
    (outcome : Outcome) (hmem : outcome ∈ (law.condOnFibre observe info).support) :
    observe outcome = info := by
  rw [FinDist.support_map] at hinfo
  obtain ⟨witness, hwitness, heq⟩ := hinfo
  have hfibre : ∃ a ∈ observe ⁻¹' {info}, a ∈ law.support :=
    ⟨witness, heq, hwitness⟩
  rw [FinDist.condOnFibre, dif_pos hfibre] at hmem
  exact (FinDist.support_condOn law _ hfibre hmem).1

/-- Conditioning uses only positive-probability information values. Arbitrary
off-support posterior fallbacks cannot affect any of the expected values. -/
theorem value_eq_conditioned (law : FinDist Outcome) (observe : Outcome → Info)
    (completePayoff : Outcome → ℝ) (abortPayoff : Info → ℝ) (rule : Rule Info) :
    value law observe completePayoff abortPayoff rule =
      (law.map observe).expect fun info => (rule info).expect fun complete =>
        if complete then continuationValue law observe completePayoff info
        else abortPayoff info := by
  unfold value
  conv_lhs => rw [law.eq_bind_condOnFibre observe, FinDist.expect_bind]
  apply FinDist.expect_congr
  intro info hinfo
  calc
    _ = (law.condOnFibre observe info).expect (fun outcome => (rule info).expect
        (fun complete => if complete then completePayoff outcome else abortPayoff info)) := by
      apply FinDist.expect_congr
      intro outcome hmem
      rw [posterior_observe law observe info hinfo outcome hmem]
    _ = _ := by
      rw [FinDist.expect_comm]
      apply FinDist.expect_congr
      intro complete _
      cases complete
      · exact FinDist.expect_const _ _
      · rfl

theorem expect_continuationValue (law : FinDist Outcome) (observe : Outcome → Info)
    (completePayoff : Outcome → ℝ) :
    (law.map observe).expect (continuationValue law observe completePayoff) =
      law.expect completePayoff := by
  have h := congrArg (fun μ => μ.expect completePayoff) (law.eq_bind_condOnFibre observe)
  exact (h.trans (FinDist.expect_bind _ _ _)).symm

def envelope (law : FinDist Outcome) (observe : Outcome → Info)
    (completePayoff : Outcome → ℝ) (abortPayoff : Info → ℝ) : ℝ :=
  (law.map observe).expect fun info =>
    max (continuationValue law observe completePayoff info) (abortPayoff info)

def optimalRule (law : FinDist Outcome) (observe : Outcome → Info)
    (completePayoff : Outcome → ℝ) (abortPayoff : Info → ℝ) : Rule Info := fun info =>
  FinDist.pure (decide (abortPayoff info ≤ continuationValue law observe completePayoff info))

theorem optimal_value (law : FinDist Outcome) (observe : Outcome → Info)
    (completePayoff : Outcome → ℝ) (abortPayoff : Info → ℝ) :
    value law observe completePayoff abortPayoff
      (optimalRule law observe completePayoff abortPayoff) =
      envelope law observe completePayoff abortPayoff := by
  rw [value_eq_conditioned]
  apply FinDist.expect_congr
  intro info _
  by_cases hle : abortPayoff info ≤ continuationValue law observe completePayoff info
  · simp [optimalRule, hle]
  · simp [optimalRule, hle, max_eq_right (le_of_not_ge hle)]

theorem value_le_envelope (law : FinDist Outcome) (observe : Outcome → Info)
    (completePayoff : Outcome → ℝ) (abortPayoff : Info → ℝ) (rule : Rule Info) :
    value law observe completePayoff abortPayoff rule ≤
      envelope law observe completePayoff abortPayoff := by
  rw [value_eq_conditioned]
  apply FinDist.expect_mono
  intro info _
  apply FinDist.expect_le_of_forall
  intro complete _
  cases complete
  · exact le_max_right _ _
  · exact le_max_left _ _

/-- Exact upper envelope over every randomized information-measurable rule. -/
theorem all_rules_bound_iff (law : FinDist Outcome) (observe : Outcome → Info)
    (completePayoff : Outcome → ℝ) (abortPayoff : Info → ℝ) (bound : ℝ) :
    (∀ rule, value law observe completePayoff abortPayoff rule ≤ bound) ↔
      envelope law observe completePayoff abortPayoff ≤ bound := by
  constructor
  · intro hbound
    simpa only [optimal_value] using hbound (optimalRule law observe completePayoff abortPayoff)
  · intro hbound rule
    exact (value_le_envelope law observe completePayoff abortPayoff rule).trans hbound

/-- Completing is optimal iff the abort payoff is no greater than the
conditional expected continuation at every supported information value. -/
theorem no_profitable_refusal_iff (law : FinDist Outcome) (observe : Outcome → Info)
    (completePayoff : Outcome → ℝ) (abortPayoff : Info → ℝ) :
    (∀ rule, value law observe completePayoff abortPayoff rule ≤ law.expect completePayoff) ↔
      ∀ info ∈ (law.map observe).support,
        abortPayoff info ≤ continuationValue law observe completePayoff info := by
  rw [all_rules_bound_iff, ← expect_continuationValue law observe completePayoff]
  constructor
  · intro hbound info hinfo
    have hle : (law.map observe).expect (continuationValue law observe completePayoff) ≤
        envelope law observe completePayoff abortPayoff :=
      FinDist.expect_mono fun _ _ => le_max_left _ _
    have hzero : (law.map observe).expect (fun info =>
        continuationValue law observe completePayoff info -
          max (continuationValue law observe completePayoff info) (abortPayoff info)) = 0 := by
      rw [FinDist.expect_sub]
      exact sub_eq_zero.mpr (le_antisymm hle hbound)
    have hpoint := FinDist.eq_of_expect_eq_of_le (law.map observe)
      (fun info => continuationValue law observe completePayoff info -
        max (continuationValue law observe completePayoff info) (abortPayoff info)) 0
      (fun _ _ => sub_nonpos.mpr (le_max_left _ _)) hzero hinfo
    have hmax := le_max_right (continuationValue law observe completePayoff info) (abortPayoff info)
    linarith
  · intro hbound
    exact le_of_eq (FinDist.expect_congr fun info hinfo => max_eq_left (hbound info hinfo))

/-- Refining the quitter's information cannot reduce the value of its exit
option, when the abort payoff is unchanged under that refinement. -/
theorem envelope_mono_information {Fine : Type*} (law : FinDist Outcome)
    (observe : Outcome → Fine) (forget : Fine → Info)
    (completePayoff : Outcome → ℝ) (abortPayoff : Info → ℝ) :
    envelope law (forget ∘ observe) completePayoff abortPayoff ≤
      envelope law observe completePayoff (abortPayoff ∘ forget) := by
  rw [← optimal_value]
  exact value_le_envelope law observe completePayoff (abortPayoff ∘ forget)
    (optimalRule law (forget ∘ observe) completePayoff abortPayoff ∘ forget)

/-- Observing the exact prospective payoff specializes the envelope to
clipping realized utility. No outcome information beyond that payoff is needed. -/
theorem envelope_payoff_information (law : FinDist Outcome)
    (completePayoff : Outcome → ℝ) (abortValue : ℝ) :
    envelope law completePayoff completePayoff (fun _ => abortValue) =
      law.expect (fun outcome => max (completePayoff outcome) abortValue) := by
  unfold envelope
  calc
    _ = (law.map completePayoff).expect (fun info => max info abortValue) := by
      apply FinDist.expect_congr
      intro info hinfo
      have hmean : continuationValue law completePayoff completePayoff info = info := by
        unfold continuationValue
        calc
          _ = (law.condOnFibre completePayoff info).expect (fun _ => info) :=
            FinDist.expect_congr fun outcome hmem =>
              posterior_observe law completePayoff info hinfo outcome hmem
          _ = info := FinDist.expect_const _ _
      rw [hmean]
    _ = _ := FinDist.expect_map _ _ _

/-- With no information, the player can compare only the unconditional
expected continuation against its exit payoff. -/
theorem envelope_no_information (law : FinDist Outcome)
    (completePayoff : Outcome → ℝ) (abortValue : ℝ) :
    envelope law (fun _ => ()) completePayoff (fun _ => abortValue) =
      max (law.expect completePayoff) abortValue := by
  have hmean := expect_continuationValue law (fun _ => ()) completePayoff
  simp only [FinDist.map_const, FinDist.expect_pure] at hmean
  simp only [envelope, FinDist.map_const, FinDist.expect_pure, hmean]

/-- Execute the refusal before sampling the continuation. The information
agreement premise makes this causal kernel exactly equal to the prospective-
outcome construction, including its abort branch and all randomized rules. -/
theorem run_causal {Checkpoint : Type*} (checkpoints : FinDist Checkpoint)
    (continuation : Checkpoint → FinDist Outcome) (checkpointObserve : Checkpoint → Info)
    (observe : Outcome → Info) (rule : Rule Info)
    (hobserve : ∀ checkpoint ∈ checkpoints.support,
      ∀ outcome ∈ (continuation checkpoint).support,
        observe outcome = checkpointObserve checkpoint) :
    run (checkpoints.bind continuation) observe rule =
      checkpoints.bind fun checkpoint => (rule (checkpointObserve checkpoint)).bind fun complete =>
        if complete then (continuation checkpoint).map Sum.inl
        else FinDist.pure (Sum.inr (checkpointObserve checkpoint)) := by
  rw [run, FinDist.bind_bind]
  apply FinDist.bind_congr
  intro checkpoint hcheckpoint
  calc
    _ = (continuation checkpoint).bind (fun outcome => (rule (checkpointObserve checkpoint)).map
        (fun complete => if complete then Sum.inl outcome
          else Sum.inr (checkpointObserve checkpoint))) := by
      apply FinDist.bind_congr
      intro outcome hmem
      rw [hobserve checkpoint hcheckpoint outcome hmem]
    _ = _ := by
      simp only [FinDist.map_eq_bind]
      rw [FinDist.bind_comm]
      apply FinDist.bind_congr
      intro complete _
      cases complete
      · simp
      · rfl

namespace Game

variable {Player : Type} [DecidableEq Player] {Info : Type}

abbrev signature (source : UtilityGame Player) (Info : Type) : GameSignature Player where
  Strategy who := source.form.sig.Strategy who × Rule Info
  Outcome := source.form.sig.Outcome ⊕ Info

def play (source : UtilityGame Player) (observe : source.form.sig.Outcome → Info)
    (last : Player) (profile : Profile (signature source Info)) :
    FinDist (source.form.sig.Outcome ⊕ Info) :=
  run (source.form.play (fun who => (profile who).1)) observe (profile last).2

def game (source : UtilityGame Player) (observe : source.form.sig.Outcome → Info)
    (last : Player) (abortPayoff : Info → Player → ℝ) : UtilityGame Player where
  form := ⟨signature source Info, play source observe last⟩
  utility outcome who := payoff (fun outcome => source.utility outcome who)
    (fun info => abortPayoff info who) outcome

def alwaysComplete : Rule Info := fun _ => FinDist.pure true

def compileProfile (source : UtilityGame Player) (profile : Profile source.form.sig) :
    Profile (signature source Info) := fun who => ⟨profile who, alwaysComplete⟩

omit [DecidableEq Player] in
theorem honest_law (source : UtilityGame Player) (observe : source.form.sig.Outcome → Info)
    (profile : Profile source.form.sig) (last : Player) :
    play source observe last (compileProfile source profile) =
      (source.form.play profile).map Sum.inl := by
  simp [play, run, compileProfile, alwaysComplete, FinDist.map_eq_bind]

omit [DecidableEq Player] in
theorem honest_expectedUtility (source : UtilityGame Player)
    (observe : source.form.sig.Outcome → Info) (profile : Profile source.form.sig)
    (last who : Player) (abortPayoff : Info → Player → ℝ) :
    expectedUtility (game source observe last abortPayoff).utility who
      ((game source observe last abortPayoff).form.play (compileProfile source profile)) =
      expectedUtility source.utility who (source.form.play profile) := by
  change (play source observe last _).expect
    (payoff (fun outcome => source.utility outcome who) (fun info => abortPayoff info who)) = _
  rw [honest_law, FinDist.expect_map]
  rfl

theorem deviation_source (source : UtilityGame Player) (profile : Profile source.form.sig)
    (who : Player) (replacement : (signature source Info).Strategy who) :
    (fun player => (Profile.update (compileProfile source profile) who replacement player).1) =
      Profile.update profile who replacement.1 := by
  funext player
  by_cases heq : player = who
  · subst player; simp
  · simp [compileProfile, Profile.update, heq]

theorem last_deviation_value (source : UtilityGame Player)
    (observe : source.form.sig.Outcome → Info) (profile : Profile source.form.sig)
    (last : Player) (abortPayoff : Info → Player → ℝ)
    (replacement : (signature source Info).Strategy last) :
    expectedUtility (game source observe last abortPayoff).utility last
      ((game source observe last abortPayoff).form.play
        (Profile.update (compileProfile source profile) last replacement)) =
      value (source.form.play (Profile.update profile last replacement.1)) observe
        (fun outcome => source.utility outcome last) (fun info => abortPayoff info last)
        replacement.2 := by
  change (run _ observe _).expect (payoff _ _) = _
  rw [deviation_source]
  simp only [Profile.update_same]
  exact run_expect _ _ _ _ _

theorem other_deviation_value (source : UtilityGame Player)
    (observe : source.form.sig.Outcome → Info) (profile : Profile source.form.sig)
    (last who : Player) (hne : who ≠ last) (abortPayoff : Info → Player → ℝ)
    (replacement : (signature source Info).Strategy who) :
    expectedUtility (game source observe last abortPayoff).utility who
      ((game source observe last abortPayoff).form.play
        (Profile.update (compileProfile source profile) who replacement)) =
      expectedUtility source.utility who
        (source.form.play (Profile.update profile who replacement.1)) := by
  change (run _ observe _).expect (payoff _ _) = _
  rw [deviation_source]
  simp [Profile.update, Ne.symm hne, compileProfile, alwaysComplete, run,
    FinDist.expect_bind, payoff, expectedUtility]

theorem compile_update (source : UtilityGame Player) (profile : Profile source.form.sig)
    (who : Player) (replacement : source.form.sig.Strategy who) :
    (compileProfile source (Profile.update profile who replacement) :
      Profile (signature source Info)) =
    Profile.update (compileProfile source profile) who ⟨replacement, alwaysComplete⟩ := by
  funext player
  by_cases heq : player = who
  · subst player; simp [compileProfile]
  · simp [compileProfile, Profile.update, heq]

/-- Exact Nash criterion including combined upstream strategy and refusal
deviations. The posterior in the envelope is recomputed under each deviation;
it is not the posterior of the equilibrium profile. -/
theorem nash_compile_iff (source : UtilityGame Player)
    (observe : source.form.sig.Outcome → Info) (profile : Profile source.form.sig)
    (last : Player) (abortPayoff : Info → Player → ℝ) :
    IsNash (game source observe last abortPayoff).form
      (euPreference (game source observe last abortPayoff).utility)
      (compileProfile source profile) ↔
    IsNash source.form (euPreference source.utility) profile ∧
      ∀ replacement : source.form.sig.Strategy last,
        envelope (source.form.play (Profile.update profile last replacement)) observe
          (fun outcome => source.utility outcome last) (fun info => abortPayoff info last) ≤
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
      have h := htarget last ⟨replacement, optimalRule
        (source.form.play (Profile.update profile last replacement)) observe
        (fun outcome => source.utility outcome last) (fun info => abortPayoff info last)⟩
      change expectedUtility _ _ _ ≤ expectedUtility _ _ _ at h
      rw [last_deviation_value, optimal_value, honest_expectedUtility] at h
      exact h
  · rintro ⟨hsource, hlast⟩
    rw [isNash_iff]
    intro who replacement
    change expectedUtility _ _ _ ≤ expectedUtility _ _ _
    rw [honest_expectedUtility]
    by_cases heq : who = last
    · subst who
      rw [last_deviation_value]
      exact (value_le_envelope _ _ _ _ _).trans (hlast replacement.1)
    · rw [other_deviation_value source observe profile last who heq]
      exact (isNash_iff _).mp hsource who replacement.1

end Game

end Vegas.Runtime.ObservedAbort
