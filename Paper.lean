/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Paper
import VegasTests.RuntimeBoundaries
import VegasTests.QuittingWindow
import VegasTests.DisclosureWindow

/-! # Paper audit

This default build target checks the general claims in `Vegas.Paper` and the
concrete witnesses below. Compiler preservation results quantify over all
programs satisfying their hypotheses. A counterexample refutes a universal
compiler guarantee; a case study instantiates, but does not generalize, a result.

`paper-claims.json` maps the active paper's numbered statements and tagged prose
claims to this audit surface. `scripts/check-paper-claims.py` checks coverage,
names, and axiom pins. Mathematical agreement of prose and statements remains
a review obligation; the checker does not interpret mathematical English.
-/

noncomputable section

namespace Vegas.Paper

open GameTheory GameTheory.Math.Probability VegasTests

/-- A compiler whose target for the hidden-choice witness exposes the two
choices sequentially cannot satisfy deviation adequacy for every core program. -/
theorem no_universal_public_submission_compiler
    (target : WFProgram TestPlayer simpleExpr → UtilityGame (Participant TestPlayer))
    (schedulerUtility : Scheduled.PublicSubmission.Values → ℝ)
    (hwitness : target matchingPenniesProgram = Scheduled.PublicSubmission.game schedulerUtility) :
    ¬ (∀ source : WFProgram TestPlayer simpleExpr,
      Nonempty (Scheduled.PlayerDeviationAdequacy (Machine.compile source).game.behavioral
        (target source))) :=
  RuntimeBoundaries.no_universal_public_submission_compiler target schedulerUtility hwitness

namespace Matching

open MatchingPenniesEquilibrium

theorem fair_nash :
    IsNash program.game.behavioral.form (euPreference program.game.behavioral.utility)
      fairPolicy :=
  fair_isNash

theorem serialized_nash
    (schedulerUtility : program.serializedArena.History → ℝ)
    (scheduler : program.serializedArena.information.BehavioralPolicy .scheduler) :
    Scheduled.IsPlayerNash (program.serializedGame schedulerUtility).behavioral
      (program.compileSerializedBehavioralProfile scheduler fairPolicy) :=
  fair_serialized_isPlayerNash schedulerUtility scheduler

theorem serialized_adversarial_payoff
    (scheduler : program.serializedArena.information.BehavioralPolicy .scheduler)
    (who victim : TestPlayer)
    (replacement : program.serializedArena.information.BehavioralPolicy (.player who)) :
    (program.serializedArena.information.runBehavioral
      (Function.update (program.compileSerializedBehavioralProfile scheduler fairPolicy)
        (.player who) replacement) graph.nodeCount).expect
          (fun history => program.settledPlayerUtility history.state.base victim) = 0 :=
  fair_serialized_deviation_payoff scheduler who victim replacement

theorem refund_value (last : TestPlayer) :
    expectedUtility (Runtime.SelectiveAbort.game program.game.behavioral last (fun _ => 0)).utility
      last ((Runtime.SelectiveAbort.game program.game.behavioral last (fun _ => 0)).form.play
        (Runtime.SelectiveAbort.withRule program.game.behavioral fairPolicy last
          (Runtime.SelectiveAbort.optimalRule 0))) = 1 / 2 :=
  RuntimeBoundaries.refund_deviation_value last

theorem quitting_threshold (last : TestPlayer) (abortPayoff : TestPlayer → ℝ) :
    IsNash (Runtime.SelectiveAbort.game program.game.behavioral last abortPayoff).form
      (euPreference (Runtime.SelectiveAbort.game program.game.behavioral last abortPayoff).utility)
      (Runtime.SelectiveAbort.compileProfile program.game.behavioral fairPolicy) ↔
    abortPayoff last ≤ -1 :=
  RuntimeBoundaries.abort_threshold_iff last abortPayoff

end Matching

namespace Kernel

open ObservedAbort

theorem fair_nash : IsNash source.form (euPreference source.utility) fairProfile :=
  fair_isNash

theorem own_choice_value (replacement : FinDist Bool) :
    Runtime.ObservedAbort.envelope
      (source.form.play (Profile.update fairProfile 0 replacement)) (fun outcome => outcome.1.1)
      (fun outcome => source.utility outcome 0) (fun _ => 0) = 0 :=
  own_choice_envelope replacement

theorem public_signal_value :
    Runtime.ObservedAbort.envelope (source.form.play fairProfile) observe
      (fun outcome => source.utility outcome 0) (fun _ => 0) = 1 / 2 :=
  public_signal_refund_value

theorem payoff_information_value :
    Runtime.ObservedAbort.envelope (source.form.play fairProfile)
      (fun outcome => source.utility outcome 0) (fun outcome => source.utility outcome 0)
      (fun _ => 0) = 3 / 4 :=
  payoff_information_refund_value

theorem own_choice_nash :
    IsNash (Runtime.ObservedAbort.Game.game source (fun outcome => outcome.1.1)
      0 (fun _ _ => 0)).form
      (euPreference (Runtime.ObservedAbort.Game.game source (fun outcome => outcome.1.1)
        0 (fun _ _ => 0)).utility)
      (Runtime.ObservedAbort.Game.compileProfile source fairProfile) :=
  own_choice_refund_isNash

theorem quitting_value (replacement : FinDist Bool) (abortValue : ℝ) :
    Runtime.ObservedAbort.envelope (source.form.play (Profile.update fairProfile 0 replacement))
      observe (fun outcome => source.utility outcome 0) (fun _ => abortValue) =
        (max 1 abortValue + max (-1) abortValue) / 2 :=
  deviation_envelope replacement abortValue

theorem realized_loss :
    ((true, false), false, false) ∈ (source.form.play fairProfile).support ∧
      source.utility ((true, false), false, false) 0 = -3 :=
  supported_loss

theorem causal_threshold (abortPayoff : Info → ObservedAbort.Player → ℝ) (abortValue : ℝ)
    (hconstant : ∀ info, abortPayoff info 0 = abortValue) :
    IsNash (causalGame abortPayoff).form (euPreference (causalGame abortPayoff).utility)
      (Runtime.ObservedAbort.Game.compileProfile source fairProfile) ↔ abortValue ≤ -1 :=
  causal_nash_iff abortPayoff abortValue hconstant

end Kernel

namespace Staged

open QuittingSource

theorem outcome_law (profile : ∀ who, program.information.BehavioralPolicy who) :
    (program.game.behavioral.form.play profile).map (fun history => decode history.state.1) =
      ObservedAbort.sourcePlay (fun who => extractStrategy who (profile who)) :=
  decoded_law_eq_kernel profile

theorem strategy_lift (who : TestPlayer) (law : FinDist Bool) :
    extractStrategy who (liftStrategy who law) = law :=
  extract_lift who law

theorem nash_correspondence (profile : ∀ who, program.information.BehavioralPolicy who) :
    IsNash program.game.behavioral.form (euPreference program.game.behavioral.utility) profile ↔
      IsNash ObservedAbort.source.form (euPreference ObservedAbort.source.utility)
        (fun who => extractStrategy who (profile who)) :=
  nash_iff_kernel profile

theorem serialized_nash
    (schedulerUtility : program.serializedArena.History → ℝ)
    (scheduler : program.serializedArena.information.BehavioralPolicy .scheduler) :
    Scheduled.IsPlayerNash (program.serializedGame schedulerUtility).behavioral
      (program.compileSerializedBehavioralProfile scheduler fairProfile) :=
  fair_serialized_isPlayerNash schedulerUtility scheduler

theorem serialized_adversarial_payoff
    (scheduler : program.serializedArena.information.BehavioralPolicy .scheduler)
    (who victim : TestPlayer)
    (replacement : program.serializedArena.information.BehavioralPolicy (.player who)) :
    (program.serializedArena.information.runBehavioral
      (Function.update (program.compileSerializedBehavioralProfile scheduler fairProfile)
        (.player who) replacement) graph.nodeCount).expect
          (fun history => program.settledPlayerUtility history.state.base victim) = 0 :=
  fair_serialized_deviation_payoff scheduler who victim replacement

theorem checkpoint_law (profile : ∀ who, program.information.BehavioralPolicy who) :
    (program.information.runBehavioral profile 4).map summarize =
      (FinDist.pi fun who => extractStrategy who (profile who)).bind fun bits =>
        ObservedAbort.fair.map (fun signal => prefixSummary bits signal 3) :=
  checkpoint_summary_law profile

theorem checkpoint_information (bits other : TestPlayer → Bool) (signal coin : Bool) :
    prefixInfo bits signal 3 = prefixInfo other coin 3 ↔ (bits 0, signal) = (other 0, coin) :=
  checkpoint_information_iff bits other signal coin

theorem causal_quitting_law (profile : ∀ who, program.information.BehavioralPolicy who)
    (rule : Runtime.ObservedAbort.Rule FullInfo) :
    compiledQuitPlay profile rule =
      ObservedAbort.causalPlay (fun who => extractStrategy who (profile who))
        (fun info => rule (encodeInfo info)) :=
  compiledQuitPlay_eq profile rule

theorem quitting_adequacy (abortPayoff : ObservedAbort.Info → TestPlayer → ℝ) :
    Nonempty (Runtime.DeviationAdequacy
      (Runtime.ObservedAbort.Game.game ObservedAbort.source ObservedAbort.observe 0 abortPayoff)
      (compiledQuitGame abortPayoff)) :=
  ⟨quitAdequacy abortPayoff⟩

theorem window_adequacy {Request : Type}
    (abortPayoff : ObservedAbort.Info → TestPlayer → ℝ)
    (gate : Runtime.DisclosureWindow.Gate FullInfo Request) (slots : Nat) :
    Nonempty (Runtime.DeviationAdequacy
      (Runtime.ObservedAbort.Game.game ObservedAbort.source ObservedAbort.observe 0 abortPayoff)
      (compiledWindowGame abortPayoff gate (slots + 1))) :=
  ⟨windowAdequacy abortPayoff gate slots⟩

theorem window_threshold {Request : Type}
    (abortPayoff : ObservedAbort.Info → TestPlayer → ℝ)
    (gate : Runtime.DisclosureWindow.Gate FullInfo Request) (slots : Nat)
    (abortValue : ℝ) (hconstant : ∀ info, abortPayoff info 0 = abortValue) :
    IsNash (compiledWindowGame abortPayoff gate (slots + 1)).form
      (euPreference (compiledWindowGame abortPayoff gate (slots + 1)).utility)
      ((windowAdequacy abortPayoff gate slots).compileProfile
        (Runtime.ObservedAbort.Game.compileProfile ObservedAbort.source
          ObservedAbort.fairProfile)) ↔ abortValue ≤ -1 :=
  compiled_window_threshold_iff abortPayoff gate slots abortValue hconstant

end Staged

/-- info: 'Vegas.Paper.no_universal_public_submission_compiler' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.no_universal_public_submission_compiler

/-- info: 'Vegas.Paper.Matching.fair_nash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Matching.fair_nash

/-- info: 'Vegas.Paper.Matching.serialized_nash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Matching.serialized_nash

/-- info: 'Vegas.Paper.Matching.serialized_adversarial_payoff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Matching.serialized_adversarial_payoff

/-- info: 'Vegas.Paper.Matching.refund_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Matching.refund_value

/-- info: 'Vegas.Paper.Matching.quitting_threshold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Matching.quitting_threshold

/-- info: 'Vegas.Paper.Kernel.fair_nash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Kernel.fair_nash

/-- info: 'Vegas.Paper.Kernel.own_choice_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Kernel.own_choice_value

/-- info: 'Vegas.Paper.Kernel.public_signal_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Kernel.public_signal_value

/-- info: 'Vegas.Paper.Kernel.payoff_information_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Kernel.payoff_information_value

/-- info: 'Vegas.Paper.Kernel.own_choice_nash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Kernel.own_choice_nash

/-- info: 'Vegas.Paper.Kernel.quitting_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Kernel.quitting_value

/-- info: 'Vegas.Paper.Kernel.realized_loss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Kernel.realized_loss

/-- info: 'Vegas.Paper.Kernel.causal_threshold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Kernel.causal_threshold

/-- info: 'Vegas.Paper.Staged.outcome_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Staged.outcome_law

/-- info: 'Vegas.Paper.Staged.strategy_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Staged.strategy_lift

/-- info: 'Vegas.Paper.Staged.nash_correspondence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Staged.nash_correspondence

/-- info: 'Vegas.Paper.Staged.serialized_nash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Staged.serialized_nash

/-- info: 'Vegas.Paper.Staged.serialized_adversarial_payoff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Staged.serialized_adversarial_payoff

/-- info: 'Vegas.Paper.Staged.checkpoint_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Staged.checkpoint_law

/-- info: 'Vegas.Paper.Staged.checkpoint_information' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Staged.checkpoint_information

/-- info: 'Vegas.Paper.Staged.causal_quitting_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Staged.causal_quitting_law

/-- info: 'Vegas.Paper.Staged.quitting_adequacy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Staged.quitting_adequacy

/-- info: 'Vegas.Paper.Staged.window_adequacy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Staged.window_adequacy

/-- info: 'Vegas.Paper.Staged.window_threshold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Staged.window_threshold

end Vegas.Paper
