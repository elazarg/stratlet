/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Game.SourceCorrelated
import Vegas.Scheduled.SourceCorrespondence

/-! # Paper-facing independent-source correspondence claims -/

noncomputable section
namespace Vegas.Paper.Source
open GameTheory GameTheory.Math.Probability GameTheory.Protocol
open Vegas.EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}

theorem native_honest_law (source : WFProgram Player L)
    (profile : SourceBehavioralProfile source.core.prog) :
    (source.boundedGame.behavioralForm.play
      (source.sourceOutcomeSimulation.compileProfile profile)).map
        source.sourceOutcomeSimulation.decodeOutcome =
      (sourceGameForm source.core.prog source.core.env).play profile :=
  source.sourceOutcomeSimulation.honest_law profile

theorem native_unilateral_law (source : WFProgram Player L)
    (profile : SourceBehavioralProfile source.core.prog) (who : Player)
    (replacement : source.boundedGame.behavioralForm.sig.Strategy who) :
    (source.boundedGame.behavioralForm.play
      (Profile.update (source.sourceOutcomeSimulation.compileProfile profile)
        who replacement)).map source.sourceOutcomeSimulation.decodeOutcome =
      (sourceGameForm source.core.prog source.core.env).play
        (Profile.update profile who
          (source.sourceOutcomeSimulation.backtranslateStrategy who replacement)) :=
  source.sourceOutcomeSimulation.deviation_law profile who replacement trivial

theorem native_nash_iff (source : WFProgram Player L)
    (valuation : VEnv L (sourceTerminalCtx source.core.prog) → Player → ℝ)
    (profile : SourceBehavioralProfile source.core.prog) :
    IsNash
      ((Machine.compile source).boundedOutcomeGame
        (ToEventGraph.observeSourceOutcome source.core source.legal) valuation).behavioral.form
      (euPreference ((Machine.compile source).boundedOutcomeGame
        (ToEventGraph.observeSourceOutcome source.core source.legal) valuation).utility)
      (source.sourceOutcomeSimulation.compileProfile profile) ↔
      IsNash (sourceGameForm source.core.prog source.core.env)
        (euPreference valuation) profile :=
  source.source_native_nash_iff valuation profile

theorem native_approximate_nash_iff (source : WFProgram Player L)
    (valuation : VEnv L (sourceTerminalCtx source.core.prog) → Player → ℝ)
    (profile : SourceBehavioralProfile source.core.prog) (ε : ℝ) :
    IsεNash
      ((Machine.compile source).boundedOutcomeGame
        (ToEventGraph.observeSourceOutcome source.core source.legal) valuation).behavioral.form
      ((Machine.compile source).boundedOutcomeGame
        (ToEventGraph.observeSourceOutcome source.core source.legal) valuation).utility ε
      (source.sourceOutcomeSimulation.compileProfile profile) ↔
      IsεNash (sourceGameForm source.core.prog source.core.env) valuation ε profile :=
  source.source_native_approximate_nash_iff valuation profile ε

theorem native_correlated_preservation (source : WFProgram Player L)
    (valuation : VEnv L (sourceTerminalCtx source.core.prog) → Player → ℝ)
    (law : FinDist (Profile (sourceGameSignature source.core.prog)))
    (hsource : IsCorrelatedEq (sourceGameForm source.core.prog source.core.env)
      (euPreference valuation) law) :
    IsCorrelatedEq source.boundedGame.behavioralForm
      (euPreference fun outcome who =>
        valuation (source.sourceOutcomeSimulation.decodeOutcome outcome) who)
      (source.sourceOutcomeSimulation.compileLaw law) :=
  source.source_native_correlatedEq_of valuation law hsource

theorem native_coarse_correlated_iff (source : WFProgram Player L)
    (valuation : VEnv L (sourceTerminalCtx source.core.prog) → Player → ℝ)
    (law : FinDist (Profile (sourceGameSignature source.core.prog))) :
    IsCoarseCorrelatedEq source.boundedGame.behavioralForm
      (euPreference fun outcome who =>
        valuation (source.sourceOutcomeSimulation.decodeOutcome outcome) who)
      (source.sourceOutcomeSimulation.compileLaw law) ↔
    IsCoarseCorrelatedEq (sourceGameForm source.core.prog source.core.env)
      (euPreference valuation) law :=
  source.source_native_coarseCorrelatedEq_iff valuation law

theorem scheduled_honest_law (source : WFProgram Player L)
    (scheduler : (Machine.compile source).serializedInformation.BehavioralPolicy
      .scheduler) (profile : SourceBehavioralProfile source.core.prog) :
    ((Machine.compile source).serializedInformation.runBehavioral
      ((Machine.compile source).compileSerializedBehavioralProfile scheduler
        (fun who => ToEventGraph.compileSourceBehavioral source.core source.legal
          who (profile who))) (Machine.compile source).graph.nodeCount).map
      (fun history => ToEventGraph.observeSourceOutcome source.core source.legal
        history.state.base) =
      denoteSource source.core.prog profile source.core.env :=
  source.source_serialized_honest_law scheduler profile

theorem scheduled_deviation_mixture (source : WFProgram Player L)
    (scheduler : (Machine.compile source).serializedInformation.BehavioralPolicy
      .scheduler) (profile : SourceBehavioralProfile source.core.prog) (who : Player)
    (replacement : (Machine.compile source).serializedInformation.BehavioralPolicy
      (.player who)) :
    ∃ alternatives : FinDist (SourceBehavioralPolicy source.core.prog who),
      ((Machine.compile source).serializedInformation.runBehavioral
        (Function.update
          ((Machine.compile source).compileSerializedBehavioralProfile scheduler
            (fun player => ToEventGraph.compileSourceBehavioral source.core source.legal
              player (profile player))) (.player who) replacement)
        (Machine.compile source).graph.nodeCount).map
          (fun history => ToEventGraph.observeSourceOutcome source.core source.legal
            history.state.base) =
        alternatives.bind fun alternative =>
          denoteSource source.core.prog
            (Profile.update (sig := sourceGameSignature source.core.prog)
              profile who alternative) source.core.env :=
  source.source_serialized_deviation_law scheduler profile who replacement

theorem scheduled_request_honest_law (source : WFProgram Player L)
    [FiniteDomains source] {Request : Participant Player → Type}
    (interface : Runtime.RequestCompiler.Interface
      (Machine.compile source).serializedInformation Request)
    (schedulerUtility : (Machine.compile source).serializedExecution.History → ℝ)
    (scheduler : (Machine.compile source).serializedInformation.BehavioralPolicy
      .scheduler) (profile : SourceBehavioralProfile source.core.prog) :
    ((source.serializedRequestGame interface schedulerUtility).form.play
      (source.compileSourceSerializedRequestProfile interface schedulerUtility
        scheduler profile)).map
        (fun state => ToEventGraph.observeSourceOutcome source.core source.legal
          state.1.state.base) =
      denoteSource source.core.prog profile source.core.env :=
  source.source_serialized_request_honest_law interface schedulerUtility scheduler profile

theorem scheduled_request_deviation_mixture (source : WFProgram Player L)
    [FiniteDomains source] {Request : Participant Player → Type}
    (interface : Runtime.RequestCompiler.Interface
      (Machine.compile source).serializedInformation Request)
    (schedulerUtility : (Machine.compile source).serializedExecution.History → ℝ)
    (scheduler : (Machine.compile source).serializedInformation.BehavioralPolicy
      .scheduler) (profile : SourceBehavioralProfile source.core.prog) (who : Player)
    (replacement : (source.serializedRequestGame interface schedulerUtility).form.sig.Strategy
      (.player who)) :
    ∃ alternatives : FinDist (SourceBehavioralPolicy source.core.prog who),
      ((source.serializedRequestGame interface schedulerUtility).form.play
        (Profile.update (source.compileSourceSerializedRequestProfile interface schedulerUtility
          scheduler profile) (.player who) replacement)).map
          (fun state => ToEventGraph.observeSourceOutcome source.core source.legal
            state.1.state.base) =
        alternatives.bind fun alternative => denoteSource source.core.prog
          (Profile.update (sig := sourceGameSignature source.core.prog)
            profile who alternative) source.core.env :=
  source.source_serialized_request_deviation_law interface schedulerUtility scheduler
    profile who replacement

theorem scheduled_request_guarantee (source : WFProgram Player L)
    [FiniteDomains source] {Request : Participant Player → Type}
    (interface : Runtime.RequestCompiler.Interface
      (Machine.compile source).serializedInformation Request)
    (schedulerUtility : (Machine.compile source).serializedExecution.History → ℝ)
    (scheduler : (Machine.compile source).serializedInformation.BehavioralPolicy
      .scheduler) (profile : SourceBehavioralProfile source.core.prog) (who : Player)
    (value : VEnv L (sourceTerminalCtx source.core.prog) → ℝ) (bound : ℝ)
    (hbound : ∀ alternative : SourceBehavioralPolicy source.core.prog who,
      bound ≤ (denoteSource source.core.prog
        (Profile.update (sig := sourceGameSignature source.core.prog) profile who alternative)
        source.core.env).expect value)
    (replacement : (source.serializedRequestGame interface schedulerUtility).form.sig.Strategy
      (.player who)) :
    bound ≤ ((source.serializedRequestGame interface schedulerUtility).form.play
      (Profile.update (source.compileSourceSerializedRequestProfile interface schedulerUtility
        scheduler profile) (.player who) replacement)).expect
          (fun state => value (ToEventGraph.observeSourceOutcome source.core source.legal
            state.1.state.base)) :=
  source.source_serialized_request_guarantee interface schedulerUtility scheduler profile who
    value bound hbound replacement

theorem scheduled_request_nash_iff (source : WFProgram Player L)
    [FiniteDomains source] {Request : Participant Player → Type}
    (interface : Runtime.RequestCompiler.Interface
      (Machine.compile source).serializedInformation Request)
    (schedulerUtility : (Machine.compile source).serializedExecution.History → ℝ)
    (valuation : VEnv L (sourceTerminalCtx source.core.prog) → Player → ℝ)
    (scheduler : (Machine.compile source).serializedInformation.BehavioralPolicy
      .scheduler) (profile : SourceBehavioralProfile source.core.prog) :
    Participant.IsPlayerNash
      (source.sourceSerializedRequestGame interface schedulerUtility valuation)
      (source.compileSourceSerializedRequestProfile interface schedulerUtility
        scheduler profile) ↔
      IsNash (sourceGameForm source.core.prog source.core.env)
        (euPreference valuation) profile :=
  source.source_serialized_request_nash_iff interface schedulerUtility valuation
    scheduler profile

theorem scheduled_request_approximate_nash_iff (source : WFProgram Player L)
    [FiniteDomains source] {Request : Participant Player → Type}
    (interface : Runtime.RequestCompiler.Interface
      (Machine.compile source).serializedInformation Request)
    (schedulerUtility : (Machine.compile source).serializedExecution.History → ℝ)
    (valuation : VEnv L (sourceTerminalCtx source.core.prog) → Player → ℝ)
    (scheduler : (Machine.compile source).serializedInformation.BehavioralPolicy
      .scheduler) (profile : SourceBehavioralProfile source.core.prog) (ε : ℝ) :
    (∀ who replacement,
      expectedUtility (source.sourceSerializedRequestGame interface schedulerUtility
        valuation).utility (.player who)
        ((source.sourceSerializedRequestGame interface schedulerUtility valuation).form.play
          (Profile.update (source.compileSourceSerializedRequestProfile interface
            schedulerUtility scheduler profile) (.player who) replacement)) ≤
      expectedUtility (source.sourceSerializedRequestGame interface schedulerUtility
        valuation).utility (.player who)
        ((source.sourceSerializedRequestGame interface schedulerUtility valuation).form.play
          (source.compileSourceSerializedRequestProfile interface schedulerUtility
            scheduler profile)) + ε) ↔
      IsεNash (sourceGameForm source.core.prog source.core.env) valuation ε profile :=
  source.source_serialized_request_approximate_nash_iff interface schedulerUtility valuation
    scheduler profile ε

/-- info: 'Vegas.Paper.Source.native_honest_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.native_honest_law
/-- info: 'Vegas.Paper.Source.native_unilateral_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.native_unilateral_law
/-- info: 'Vegas.Paper.Source.native_nash_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.native_nash_iff
/-- info: 'Vegas.Paper.Source.native_approximate_nash_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.native_approximate_nash_iff
/-- info: 'Vegas.Paper.Source.native_correlated_preservation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.native_correlated_preservation
/-- info: 'Vegas.Paper.Source.native_coarse_correlated_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.native_coarse_correlated_iff

/-- info: 'Vegas.Paper.Source.scheduled_honest_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.scheduled_honest_law
/-- info: 'Vegas.Paper.Source.scheduled_deviation_mixture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.scheduled_deviation_mixture
/-- info: 'Vegas.Paper.Source.scheduled_request_honest_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.scheduled_request_honest_law
/-- info: 'Vegas.Paper.Source.scheduled_request_deviation_mixture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.scheduled_request_deviation_mixture
/-- info: 'Vegas.Paper.Source.scheduled_request_guarantee' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.scheduled_request_guarantee
/-- info: 'Vegas.Paper.Source.scheduled_request_nash_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.scheduled_request_nash_iff
/-- info: 'Vegas.Paper.Source.scheduled_request_approximate_nash_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.Source.scheduled_request_approximate_nash_iff

end Vegas.Paper.Source
