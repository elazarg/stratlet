/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Runtime.DeviationAdequacy
import Vegas.Runtime.TraceUtility

/-! # A source equilibrium need not protect a player from trace incentives

Both players prefer the safe source outcome. The target adds an adversary-
controlled trace bit, rewarded only with the harmful outcome. The reward is
zero on every compiled profile. Exact outcome simulation still holds, but the
compiled equilibrium and its honest-player payoff do not survive that reward.
This is a game-form counterexample, not a claim about an EVM instruction.
-/

noncomputable section

namespace VegasTests.TraceUtility

open GameTheory GameTheory.Math.Probability Vegas.Runtime

def sourceForm : GameForm (Fin 2) where
  sig := { Strategy := fun _ => Bool, Outcome := Bool }
  play profile := FinDist.pure (profile 1)

def targetForm : GameForm (Fin 2) where
  sig := { Strategy := fun _ => Bool × Bool, Outcome := Bool × Bool }
  play profile := FinDist.pure (profile 1)

def simulation : OutcomeSimulationOn sourceForm targetForm (fun _ _ => True) where
  compileStrategy _ action := (action, false)
  backtranslateStrategy _ action := action.1
  decodeOutcome := Prod.fst
  honest_law _ := by simp [sourceForm, targetForm]
  compiled_considered _ _ := trivial
  deviation_law profile who replacement _ := by
    fin_cases who <;> simp [sourceForm, targetForm, Profile.update]

def sourceUtility (harm : Bool) (_ : Fin 2) : ℝ := if harm then 0 else 1

def targetUtility (outcome : Bool × Bool) (who : Fin 2) : ℝ :=
  sourceUtility outcome.1 who + if who = 1 ∧ outcome.1 = true ∧ outcome.2 = true then 2 else 0

def source : UtilityGame (Fin 2) := ⟨sourceForm, sourceUtility⟩
def target : UtilityGame (Fin 2) := ⟨targetForm, targetUtility⟩
def safeProfile : Profile sourceForm.sig := fun _ => false

theorem source_nash : IsNash source.form (euPreference source.utility) safeProfile := by
  rw [isNash_iff]
  intro who alternative
  change (FinDist.pure ((Function.update safeProfile who alternative) 1)).expect
    (fun harm : Bool => if harm then (0 : ℝ) else 1) ≤
      (FinDist.pure false).expect (fun harm : Bool => if harm then (0 : ℝ) else 1)
  rw [FinDist.expect_pure, FinDist.expect_pure]
  split <;> norm_num

/-- Every compiled profile has the original utilities, not merely the safe one. -/
theorem compiled_utilities (profile : Profile sourceForm.sig) (who : Fin 2) :
    expectedUtility target.utility who
      (target.form.play (simulation.compileProfile profile)) =
      expectedUtility source.utility who (source.form.play profile) := by
  simp [target, source, targetForm, sourceForm, expectedUtility,
    targetUtility, OutcomeSimulationOn.compileProfile, simulation]

theorem target_not_nash :
    ¬ IsNash target.form (euPreference target.utility)
      (simulation.compileProfile safeProfile) := by
  rw [isNash_iff]
  intro h
  have hbad := h 1 (true, true)
  change (FinDist.pure (true, true)).expect (fun outcome => targetUtility outcome 1) ≤
    (FinDist.pure (false, false)).expect (fun outcome => targetUtility outcome 1) at hbad
  norm_num [targetUtility, sourceUtility] at hbad

/-- The harmful outcome is itself supported by a target Nash equilibrium,
so the witness also applies to a utility-maximizing opponent. -/
theorem harmful_target_nash :
    IsNash target.form (euPreference target.utility)
      (Profile.update (simulation.compileProfile safeProfile) 1 (true, true)) := by
  rw [isNash_iff]
  intro who alternative
  fin_cases who
  · change (FinDist.pure (true, true)).expect (fun outcome => targetUtility outcome 0) ≤
      (FinDist.pure (true, true)).expect (fun outcome => targetUtility outcome 0)
    exact le_rfl
  · change (FinDist.pure alternative).expect (fun outcome => targetUtility outcome 1) ≤
      (FinDist.pure (true, true)).expect (fun outcome => targetUtility outcome 1)
    obtain ⟨harm, bit⟩ := alternative
    cases harm <;> cases bit <;> norm_num [targetUtility, sourceUtility]

/-- The source-oriented player's equilibrium payoff falls from one to zero;
this does not contradict guarantee transfer, since it was not a source bound
against arbitrary opponents. -/
theorem honest_payoff_drop :
    expectedUtility target.utility 0
      (target.form.play (simulation.compileProfile safeProfile)) = 1 ∧
    expectedUtility target.utility 0
      (target.form.play (Profile.update (simulation.compileProfile safeProfile) 1
        (true, true))) = 0 := by
  change (FinDist.pure (false, false)).expect (fun outcome => targetUtility outcome 0) = 1 ∧
    (FinDist.pure (true, true)).expect (fun outcome => targetUtility outcome 0) = 0
  norm_num [targetUtility, sourceUtility]

end VegasTests.TraceUtility
