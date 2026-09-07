/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Paper.General
import VegasTests.RuntimeBoundaries
import VegasTests.QuittingWindow
import VegasTests.DisclosureWindow
import VegasTests.SealedOfferRuntime
import VegasTests.TraceUtility
import Vegas.Scheduled.Valuation

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

namespace Valuation

open Vegas.Runtime

variable {Player : Type}
variable {source target : GameForm Player}
variable {Considered : (who : Player) → target.sig.Strategy who → Prop}

theorem nash_for_every_valuation [DecidableEq Player]
    (simulation : OutcomeSimulationOn source target (fun _ _ => True))
    (value : source.sig.Outcome → Player → ℝ) (profile : Profile source.sig) :
    IsNash target (euPreference (fun outcome who => value (simulation.decodeOutcome outcome) who))
      (simulation.compileProfile profile) ↔ IsNash source (euPreference value) profile :=
  (simulation.withUtility value).isNash_compileProfile_iff profile

theorem decoder_boundary {Source Target : Type*} (decode : Target → Source)
    (utility : Target → ℝ) :
    (∀ first second : FinDist Target,
      first.map decode = second.map decode → first.expect utility = second.expect utility) ↔
      FactorsThrough decode utility :=
  universal_expectation_iff decode utility

theorem trace_incentive [DecidableEq Player]
    (simulation : OutcomeSimulationOn source target Considered)
    (profile : Profile source.sig) (who : Player) (replacement : target.sig.Strategy who)
    (hconsidered : Considered who replacement)
    (value : source.sig.Outcome → ℝ) (bonus : target.sig.Outcome → ℝ) :
    (target.play (Profile.update (simulation.compileProfile profile) who replacement)).expect
        (simulation.combinedUtility value bonus) ≤
      (target.play (simulation.compileProfile profile)).expect
        (simulation.combinedUtility value bonus) ↔
    (target.play (Profile.update (simulation.compileProfile profile) who replacement)).expect
        bonus - (target.play (simulation.compileProfile profile)).expect bonus ≤
      (source.play profile).expect value -
        (source.play (Profile.update profile who
          (simulation.backtranslateStrategy who replacement))).expect value :=
  simulation.combined_noGain_iff profile who replacement hconsidered value bonus

theorem trace_regret [DecidableEq Player]
    (simulation : OutcomeSimulationOn source target Considered)
    (profile : Profile source.sig) (who : Player)
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
        (simulation.combinedUtility value bonus) + ε :=
  simulation.combined_regret_bound profile who value bonus ε hsource hbonus replacement hconsidered

theorem adversarial_bound [DecidableEq Player]
    (simulation : OutcomeSimulationOn source target Considered)
    (profile : Profile source.sig) (deviator : Player)
    (value : source.sig.Outcome → ℝ) (bound : ℝ)
    (hbound : ∀ replacement : source.sig.Strategy deviator,
      bound ≤ (source.play (Profile.update profile deviator replacement)).expect value)
    (replacement : target.sig.Strategy deviator) (hconsidered : Considered deviator replacement) :
    bound ≤ (target.play
      (Profile.update (simulation.compileProfile profile) deviator replacement)).expect
        (fun outcome => value (simulation.decodeOutcome outcome)) :=
  simulation.guarantee profile deviator value bound hbound replacement hconsidered

theorem context_bound {Honest : Player → Prop}
    (simulation : HonestContextSimulation source target Honest)
    (profile : Profile source.sig) (value : source.sig.Outcome → ℝ) (bound : ℝ)
    (hbound : ∀ alternative : Profile source.sig,
      (∀ who, Honest who → alternative who = profile who) →
        bound ≤ (source.play alternative).expect value)
    (context : Profile target.sig)
    (hcontext : ∀ who, Honest who →
      context who = simulation.compileStrategy who (profile who)) :
    bound ≤ (target.play context).expect
      (fun outcome => value (simulation.decodeOutcome outcome)) :=
  simulation.guarantee profile value bound hbound context hcontext

theorem serialized_valuation [DecidableEq Player] [Fintype Player] {L : IExpr}
    (program : Machine.Program Player L) {Outcome : Type}
    (observe : program.State → Outcome) (value : Outcome → Player → ℝ)
    (schedulerUtility : program.serializedArena.History → ℝ)
    (scheduler : program.serializedArena.information.BehavioralPolicy .scheduler)
    (profile : (who : Player) → program.information.BehavioralPolicy who) :
    Participant.IsPlayerNash
      (program.serializedOutcomeGame observe value schedulerUtility).behavioral
      (program.compileSerializedBehavioralProfile scheduler profile) ↔
      IsNash (program.outcomeGame observe value).behavioral.form
        (euPreference (program.outcomeGame observe value).utility) profile :=
  program.serializedOutcomeGame_nash_iff observe value schedulerUtility scheduler profile

theorem trace_counterexample :
    IsNash TraceUtility.source.form (euPreference TraceUtility.source.utility)
      TraceUtility.safeProfile ∧
    (∀ profile who, expectedUtility TraceUtility.target.utility who
      (TraceUtility.target.form.play (TraceUtility.simulation.compileProfile profile)) =
      expectedUtility TraceUtility.source.utility who (TraceUtility.source.form.play profile)) ∧
    (¬ IsNash TraceUtility.target.form (euPreference TraceUtility.target.utility)
      (TraceUtility.simulation.compileProfile TraceUtility.safeProfile)) ∧
    IsNash TraceUtility.target.form (euPreference TraceUtility.target.utility)
      (Profile.update (TraceUtility.simulation.compileProfile TraceUtility.safeProfile) 1
        (true, true)) :=
  ⟨TraceUtility.source_nash, TraceUtility.compiled_utilities,
    TraceUtility.target_not_nash, TraceUtility.harmful_target_nash⟩

theorem trace_harm :
    expectedUtility TraceUtility.target.utility 0
      (TraceUtility.target.form.play
        (TraceUtility.simulation.compileProfile TraceUtility.safeProfile)) = 1 ∧
    expectedUtility TraceUtility.target.utility 0
      (TraceUtility.target.form.play
        (Profile.update (TraceUtility.simulation.compileProfile TraceUtility.safeProfile) 1
          (true, true))) = 0 :=
  TraceUtility.honest_payoff_drop

end Valuation

/-- info: 'Vegas.Paper.Valuation.nash_for_every_valuation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Valuation.nash_for_every_valuation

/-- info: 'Vegas.Paper.Valuation.decoder_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Valuation.decoder_boundary

/-- info: 'Vegas.Paper.Valuation.trace_incentive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Valuation.trace_incentive

/-- info: 'Vegas.Paper.Valuation.trace_regret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Valuation.trace_regret

/-- info: 'Vegas.Paper.Valuation.adversarial_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Valuation.adversarial_bound

/-- info: 'Vegas.Paper.Valuation.context_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Valuation.context_bound

/-- info: 'Vegas.Paper.Valuation.serialized_valuation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Valuation.serialized_valuation

/-- info: 'Vegas.Paper.Valuation.trace_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Valuation.trace_counterexample

/-- info: 'Vegas.Paper.Valuation.trace_harm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Valuation.trace_harm


/-- A compiler whose target for the hidden-choice witness exposes the two
choices sequentially cannot satisfy deviation adequacy for every core program. -/
theorem no_universal_public_submission_compiler
    (target : WFProgram TestPlayer simpleExpr → UtilityGame (Participant TestPlayer))
    (schedulerUtility : PublicSubmission.Values → ℝ)
    (hwitness : target matchingPenniesProgram = PublicSubmission.game schedulerUtility) :
    ¬ (∀ source : WFProgram TestPlayer simpleExpr,
      Nonempty (Participant.PlayerDeviationAdequacy (Machine.compile source).game.behavioral
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
    Participant.IsPlayerNash (program.serializedGame schedulerUtility).behavioral
      (program.compileSerializedBehavioralProfile scheduler fairPolicy) :=
  fair_serialized_isPlayerNash schedulerUtility scheduler

theorem serialized_adversarial_payoff
    (scheduler : program.serializedArena.information.BehavioralPolicy .scheduler)
    (who victim : TestPlayer)
    (replacement : program.serializedArena.information.BehavioralPolicy (.player who)) :
    (program.serializedArena.information.runBehavioral
      (Function.update (program.compileSerializedBehavioralProfile scheduler fairPolicy)
        (.player who) replacement) graph.nodeCount).expect
          (fun history => program.payoutUtility history.state.base victim) = 0 :=
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
    Participant.IsPlayerNash (program.serializedGame schedulerUtility).behavioral
      (program.compileSerializedBehavioralProfile scheduler fairProfile) :=
  fair_serialized_isPlayerNash schedulerUtility scheduler

theorem serialized_adversarial_payoff
    (scheduler : program.serializedArena.information.BehavioralPolicy .scheduler)
    (who victim : TestPlayer)
    (replacement : program.serializedArena.information.BehavioralPolicy (.player who)) :
    (program.serializedArena.information.runBehavioral
      (Function.update (program.compileSerializedBehavioralProfile scheduler fairProfile)
        (.player who) replacement) graph.nodeCount).expect
          (fun history => program.payoutUtility history.state.base victim) = 0 :=
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


namespace Disclosure

open OptionalDisclosure

theorem policy_roundtrip (who : TestPlayer) (strategy : Strategy who) :
    extractPolicy who (compilePolicy who strategy) = strategy :=
  extract_compile_policy who strategy

theorem outcome_law (profile : Profile program.game.behavioral.form.sig) :
    (program.game.behavioral.form.play profile).map decodeHistory =
      finiteForm.play (extractProfile profile) :=
  all_profile_law profile

theorem expected_payoffs (payouts : Payouts)
    (profile : Profile program.game.behavioral.form.sig) (who : TestPlayer) :
    expectedUtility (programWithPayoffs payouts).game.behavioral.utility who
        ((programWithPayoffs payouts).game.behavioral.form.play profile) =
      expectedUtility (finiteGame payouts).utility who
        ((finiteGame payouts).form.play (extractProfile profile)) :=
  expectedUtility_eq_finite payouts profile who

theorem nash_correspondence (payouts : Payouts)
    (profile : Profile program.game.behavioral.form.sig) :
    IsNash (programWithPayoffs payouts).game.behavioral.form
        (euPreference (programWithPayoffs payouts).game.behavioral.utility) profile ↔
      IsNash (finiteGame payouts).form (euPreference (finiteGame payouts).utility)
        (extractProfile profile) :=
  nash_iff_finite payouts profile

end Disclosure

namespace Offer

open SealedOffer OptionalDisclosure

theorem source_nash : IsNash game.form (euPreference game.utility) honestProfile :=
  honest_isNash

theorem source_values :
    expectedUtility game.utility 0 (game.form.play honestProfile) = 1 ∧
      expectedUtility game.utility 1 (game.form.play honestProfile) = 1 / 2 :=
  ⟨honest_seller_value, honest_buyer_value⟩

theorem source_buyer_guarantee (seller : SenderStrategy) :
    0 ≤ expectedUtility game.utility 1 (game.form.play (pairProfile seller honestBuyer)) :=
  honest_buyer_nonnegative seller

theorem source_buyer_best_response (seller : SenderStrategy) (buyer : ResponderStrategy) :
    expectedUtility game.utility 1 (game.form.play (pairProfile seller buyer)) ≤
      expectedUtility game.utility 1 (game.form.play (pairProfile seller honestBuyer)) :=
  honest_buyer_best_response seller buyer

theorem source_seller_bound (seller : SenderStrategy) :
    expectedUtility game.utility 0 (game.form.play (pairProfile seller honestBuyer)) ≤ 1 :=
  seller_revenue_bound seller

theorem runtime_nash
    (schedulerUtility : machine.serializedArena.History → ℝ)
    (scheduler : machine.serializedArena.information.BehavioralPolicy .scheduler) :
    Participant.IsPlayerNash (runtimeGame schedulerUtility)
      (runtimeProfile schedulerUtility scheduler) :=
  runtime_honest_isPlayerNash schedulerUtility scheduler

theorem runtime_buyer_guarantee
    (schedulerUtility : machine.serializedArena.History → ℝ)
    (scheduler : machine.serializedArena.information.BehavioralPolicy .scheduler)
    (replacement : (runtimeGame schedulerUtility).form.sig.Strategy (.player 0)) :
    0 ≤ expectedUtility (runtimeGame schedulerUtility).utility (.player 1)
      ((runtimeGame schedulerUtility).form.play
        (Profile.update (runtimeProfile schedulerUtility scheduler) (.player 0) replacement)) :=
  runtime_buyer_nonnegative schedulerUtility scheduler replacement

theorem disclosure_timeout (secret signal : Bool) :
    (timeoutPolicy 0 (openingInfo secret signal)).1 = some (openingAction none) :=
  timeout_disclosure secret signal

end Offer

/-- info: 'Vegas.Paper.Disclosure.policy_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Disclosure.policy_roundtrip

/-- info: 'Vegas.Paper.Disclosure.outcome_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Disclosure.outcome_law

/-- info: 'Vegas.Paper.Disclosure.expected_payoffs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Disclosure.expected_payoffs

/-- info: 'Vegas.Paper.Disclosure.nash_correspondence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Disclosure.nash_correspondence

/-- info: 'Vegas.Paper.Offer.source_nash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Offer.source_nash

/-- info: 'Vegas.Paper.Offer.source_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Offer.source_values

/-- info: 'Vegas.Paper.Offer.source_buyer_guarantee' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Offer.source_buyer_guarantee

/-- info: 'Vegas.Paper.Offer.source_buyer_best_response' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Offer.source_buyer_best_response

/-- info: 'Vegas.Paper.Offer.source_seller_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Offer.source_seller_bound

/-- info: 'Vegas.Paper.Offer.runtime_nash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Offer.runtime_nash

/-- info: 'Vegas.Paper.Offer.runtime_buyer_guarantee' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Offer.runtime_buyer_guarantee

/-- info: 'Vegas.Paper.Offer.disclosure_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Offer.disclosure_timeout

end Vegas.Paper
