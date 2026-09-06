/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Runtime.OutcomeSimulation

/-! # Outcome observations and trace-sensitive preferences

Factoring through a decoder, matching expectations for a class of tests, and
preserving incentives with an additional trace valuation are different claims.
This module states their boundaries without imposing a particular runtime.
-/

noncomputable section

namespace Vegas.Runtime

open GameTheory GameTheory.Math.Probability

/-- A utility can be evaluated using only the decoded source outcome. -/
def FactorsThrough {Source Target : Type*} (decode : Target → Source)
    (utility : Target → ℝ) : Prop :=
  ∃ value : Source → ℝ, ∀ outcome, utility outcome = value (decode outcome)

/-- A utility descends to source outcomes exactly when it is constant on each
decoder fibre. Surjectivity is unnecessary: unused source outcomes get value
zero in the constructed extension. -/
theorem factorsThrough_iff {Source Target : Type*} (decode : Target → Source)
    (utility : Target → ℝ) :
    FactorsThrough decode utility ↔
      ∀ left right, decode left = decode right → utility left = utility right := by
  classical
  constructor
  · rintro ⟨value, hvalue⟩ left right heq
    rw [hvalue, hvalue, heq]
  · intro hfibre
    refine ⟨fun outcome => if h : ∃ trace, decode trace = outcome then
      utility h.choose else 0, ?_⟩
    intro trace
    have hex : ∃ other, decode other = decode trace := ⟨trace, rfl⟩
    simp only [dif_pos hex]
    exact hfibre trace hex.choose hex.choose_spec.symm

/-- Equality of expected tests allows specifications narrower than full trace
law equality. For example, the test class can contain just economic utilities. -/
def AgreeOnTests {Outcome : Type*} (tests : Set (Outcome → ℝ))
    (left right : FinDist Outcome) : Prop :=
  ∀ value ∈ tests, left.expect value = right.expect value

/-- Exact decoded laws preserve every utility that ignores erased distinctions. -/
theorem expect_eq_of_decoded_law {Source Target : Type*}
    (decode : Target → Source) (left right : FinDist Target)
    (hlaw : left.map decode = right.map decode)
    (utility : Target → ℝ) (hutility : FactorsThrough decode utility) :
    left.expect utility = right.expect utility := by
  obtain ⟨value, hvalue⟩ := hutility
  have heq : utility = fun outcome => value (decode outcome) := funext hvalue
  rw [heq, ← FinDist.expect_map, hlaw, FinDist.expect_map]

/-- An erased distinction that changes utility already refutes universal
expected-utility preservation for pairs of laws with the same decoded law. -/
theorem not_universal_expectation_of_fibre_difference {Source Target : Type*}
    (decode : Target → Source) (utility : Target → ℝ)
    (left right : Target) (hdecode : decode left = decode right)
    (hutility : utility left ≠ utility right) :
    ¬ (∀ first second : FinDist Target,
      first.map decode = second.map decode → first.expect utility = second.expect utility) := by
  intro h
  have heq := h (FinDist.pure left) (FinDist.pure right) (by simp [hdecode])
  exact hutility (by simpa using heq)

/-- This universal expectation property is exactly the decoder-fibre condition,
not a condition on the spelling or representation of outcomes. -/
theorem universal_expectation_iff {Source Target : Type*}
    (decode : Target → Source) (utility : Target → ℝ) :
    (∀ first second : FinDist Target,
      first.map decode = second.map decode → first.expect utility = second.expect utility) ↔
      FactorsThrough decode utility := by
  constructor
  · intro h
    rw [factorsThrough_iff]
    intro left right hdecode
    simpa using h (FinDist.pure left) (FinDist.pure right) (by simp [hdecode])
  · intro h first second hlaw
    exact expect_eq_of_decoded_law decode first second hlaw utility h

namespace OutcomeSimulationOn

universe uPlayer uSourceStrategy uSourceOutcome uTargetStrategy uTargetOutcome

variable {Player : Type uPlayer} [DecidableEq Player]
variable {source : GameForm.{uPlayer, uSourceStrategy, uSourceOutcome} Player}
variable {target : GameForm.{uPlayer, uTargetStrategy, uTargetOutcome} Player}
variable {Considered : (who : Player) → target.sig.Strategy who → Prop}
variable (simulation : OutcomeSimulationOn source target Considered)

/-- A combined utility is source valuation plus a residual on target outcomes
(which may themselves be full execution traces). This is a decomposition, not
an assumption that the residual is small or strategically irrelevant. -/
def combinedUtility (value : source.sig.Outcome → ℝ) (bonus : target.sig.Outcome → ℝ) :
    target.sig.Outcome → ℝ :=
  fun outcome => value (simulation.decodeOutcome outcome) + bonus outcome

/-- Exact incentive boundary: a runtime deviation is unprofitable precisely
when its trace-bonus gain is at most the corresponding source-value loss.
No Nash assumption is needed for this identity. -/
theorem combined_noGain_iff (profile : Profile source.sig) (who : Player)
    (replacement : target.sig.Strategy who) (hconsidered : Considered who replacement)
    (value : source.sig.Outcome → ℝ) (bonus : target.sig.Outcome → ℝ) :
    (target.play (Profile.update (simulation.compileProfile profile) who replacement)).expect
        (simulation.combinedUtility value bonus) ≤
      (target.play (simulation.compileProfile profile)).expect
        (simulation.combinedUtility value bonus) ↔
    (target.play (Profile.update (simulation.compileProfile profile) who replacement)).expect
        bonus - (target.play (simulation.compileProfile profile)).expect bonus ≤
      (source.play profile).expect value -
        (source.play (Profile.update profile who
          (simulation.backtranslateStrategy who replacement))).expect value := by
  unfold combinedUtility
  rw [FinDist.expect_add, FinDist.expect_add]
  rw [simulation.expect_deviation profile who replacement hconsidered value,
    simulation.expect_compile profile value]
  constructor <;> intro h <;> linarith

/-- Even a source-indifferent replacement becomes profitable if it has a
strictly greater trace bonus. A positive source loss can likewise be overcome
by a larger bonus, as characterized by `combined_noGain_iff`. -/
theorem profitable_of_source_indifferent (profile : Profile source.sig) (who : Player)
    (replacement : target.sig.Strategy who) (hconsidered : Considered who replacement)
    (value : source.sig.Outcome → ℝ) (bonus : target.sig.Outcome → ℝ)
    (hsource : (source.play (Profile.update profile who
      (simulation.backtranslateStrategy who replacement))).expect value =
        (source.play profile).expect value)
    (hbonus : (target.play (simulation.compileProfile profile)).expect bonus <
      (target.play (Profile.update (simulation.compileProfile profile) who replacement)).expect
        bonus) :
    (target.play (simulation.compileProfile profile)).expect
        (simulation.combinedUtility value bonus) <
      (target.play (Profile.update (simulation.compileProfile profile) who replacement)).expect
        (simulation.combinedUtility value bonus) := by
  apply lt_of_not_ge
  rw [simulation.combined_noGain_iff profile who replacement hconsidered value bonus, hsource]
  linarith

/-- A source best response remains an epsilon best response if the expected
trace-bonus gain of every considered deviation is at most epsilon. -/
theorem combined_regret_bound (profile : Profile source.sig) (who : Player)
    (value : source.sig.Outcome → ℝ) (bonus : target.sig.Outcome → ℝ) (ε : ℝ)
    (hsource : ∀ alternative : source.sig.Strategy who,
      (source.play (Profile.update profile who alternative)).expect value ≤
        (source.play profile).expect value)
    (hbonus : ∀ replacement : target.sig.Strategy who, Considered who replacement →
      (target.play (Profile.update (simulation.compileProfile profile) who replacement)).expect
          bonus - (target.play (simulation.compileProfile profile)).expect bonus ≤ ε)
    (replacement : target.sig.Strategy who) (hconsidered : Considered who replacement) :
    (target.play (Profile.update (simulation.compileProfile profile) who replacement)).expect
        (simulation.combinedUtility value bonus) ≤
      (target.play (simulation.compileProfile profile)).expect
        (simulation.combinedUtility value bonus) + ε := by
  unfold combinedUtility
  rw [FinDist.expect_add, FinDist.expect_add]
  rw [simulation.expect_deviation profile who replacement hconsidered value,
    simulation.expect_compile profile value]
  have hs := hsource (simulation.backtranslateStrategy who replacement)
  have hb := hbonus replacement hconsidered
  linarith

end OutcomeSimulationOn

end Vegas.Runtime
