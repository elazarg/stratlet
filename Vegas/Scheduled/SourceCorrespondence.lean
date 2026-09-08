/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Game.SourceCorrespondence
import Vegas.Scheduled.Request
import Vegas.Scheduled.Valuation

/-! # Independent source laws through scheduled request execution -/

noncomputable section

namespace Vegas.WFProgram

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Vegas.Runtime

variable {Player : Type} [Fintype Player] [DecidableEq Player] {L : IExpr}
variable (source : WFProgram Player L)

/-- Scheduling compiled source policies preserves the independent source
outcome distribution under every behavioral scheduler. -/
theorem source_serialized_honest_law
    (scheduler : (Machine.compile source).serializedInformation.BehavioralPolicy .scheduler)
    (profile : SourceBehavioralProfile source.core.prog) :
    ((Machine.compile source).serializedInformation.runBehavioral
      ((Machine.compile source).compileSerializedBehavioralProfile scheduler
        (fun who => ToEventGraph.compileSourceBehavioral source.core source.legal
          who (profile who))) (Machine.compile source).graph.nodeCount).map
      (fun history => ToEventGraph.observeSourceOutcome source.core source.legal
        history.state.base) =
      denoteSource source.core.prog profile source.core.env := by
  have hnative := (Machine.compile source).runBehavioral_compileSerialized scheduler
    (fun who => ToEventGraph.compileSourceBehavioral source.core source.legal who (profile who))
  have hdecoded := congrArg
    (fun law => law.map (ToEventGraph.observeSourceOutcome source.core source.legal)) hnative
  have hsource := ToEventGraph.runBehavioral_compileSource_source source.core source.legal profile
  refine Eq.trans ?_ hsource
  simpa only [FinDist.map_comp, Function.comp_def, Machine.Program.information,
    Machine.compile, Machine.ofCompiled] using hdecoded

/-- Order-aware deviations preserve the source law as a finite mixture of
unilateral independent source-policy deviations against unchanged opponents. -/
theorem source_serialized_deviation_law
    (scheduler : (Machine.compile source).serializedInformation.BehavioralPolicy .scheduler)
    (profile : SourceBehavioralProfile source.core.prog) (who : Player)
    (replacement : (Machine.compile source).serializedInformation.BehavioralPolicy
      (.player who)) :
    ∃ alternatives : FinDist (SourceBehavioralPolicy source.core.prog who),
      ((Machine.compile source).serializedInformation.runBehavioral
        (Profile.update
          (sig := (Machine.compile source).serializedInformation.behavioralSignature)
          ((Machine.compile source).compileSerializedBehavioralProfile scheduler
            (fun player => ToEventGraph.compileSourceBehavioral source.core source.legal
              player (profile player))) (.player who) replacement)
        (Machine.compile source).graph.nodeCount).map
          (fun history => ToEventGraph.observeSourceOutcome source.core source.legal
            history.state.base) =
        alternatives.bind fun alternative =>
          denoteSource source.core.prog
            (Profile.update (sig := sourceGameSignature source.core.prog)
              profile who alternative) source.core.env := by
  obtain ⟨nativeAlternatives, hlaw⟩ :=
    (Machine.compile source).serializedDeviation_eq_sourceMixture scheduler
      (fun player => ToEventGraph.compileSourceBehavioral source.core source.legal
        player (profile player)) who replacement
  refine ⟨nativeAlternatives.map
    (ToEventGraph.backtranslateNativeBehavioral source.core source.legal who), ?_⟩
  have hdecoded := congrArg
    (fun law => law.map (ToEventGraph.observeSourceOutcome source.core source.legal)) hlaw
  simp only [FinDist.map_comp, FinDist.map_bind, Function.comp_def] at hdecoded
  refine hdecoded.trans ?_
  rw [FinDist.bind_map]
  apply FinDist.bind_congr
  intro alternative _
  exact source.sourceOutcomeSimulation.deviation_law profile who alternative trivial

/-- Source bounds on any terminal observable survive every order-aware
unilateral deviation, without assigning the scheduler a source utility. -/
theorem source_serialized_guarantee
    (scheduler : (Machine.compile source).serializedInformation.BehavioralPolicy .scheduler)
    (profile : SourceBehavioralProfile source.core.prog) (who : Player)
    (value : VEnv L (sourceTerminalCtx source.core.prog) → ℝ) (bound : ℝ)
    (hbound : ∀ alternative : SourceBehavioralPolicy source.core.prog who,
      bound ≤ (denoteSource source.core.prog
        (Profile.update (sig := sourceGameSignature source.core.prog) profile who alternative)
        source.core.env).expect value)
    (replacement : (Machine.compile source).serializedInformation.BehavioralPolicy
      (.player who)) :
    bound ≤ ((Machine.compile source).serializedInformation.runBehavioral
      (Profile.update
        (sig := (Machine.compile source).serializedInformation.behavioralSignature)
        ((Machine.compile source).compileSerializedBehavioralProfile scheduler
          (fun player => ToEventGraph.compileSourceBehavioral source.core source.legal
            player (profile player))) (.player who) replacement)
      (Machine.compile source).graph.nodeCount).expect
        (fun history => value (ToEventGraph.observeSourceOutcome source.core source.legal
          history.state.base)) := by
  obtain ⟨alternatives, hlaw⟩ := source.source_serialized_deviation_law
    scheduler profile who replacement
  rw [← FinDist.expect_map, hlaw, FinDist.expect_bind]
  calc
    bound = alternatives.expect (fun _ => bound) := (FinDist.expect_const _ _).symm
    _ ≤ _ := FinDist.expect_mono fun alternative _ => hbound alternative

/-- Independent source Nash profiles remain exactly original-player Nash
profiles after scheduling, for any source valuation and scheduler utility. -/
theorem source_serialized_nash_iff
    (valuation : VEnv L (sourceTerminalCtx source.core.prog) → Player → ℝ)
    (schedulerUtility : (Machine.compile source).serializedExecution.History → ℝ)
    (scheduler : (Machine.compile source).serializedInformation.BehavioralPolicy .scheduler)
    (profile : SourceBehavioralProfile source.core.prog) :
    Participant.IsPlayerNash
      ((Machine.compile source).serializedBoundedOutcomeGame
        (ToEventGraph.observeSourceOutcome source.core source.legal)
        valuation schedulerUtility).behavioral
      ((Machine.compile source).compileSerializedBehavioralProfile scheduler
        (source.sourceOutcomeSimulation.compileProfile profile)) ↔
      IsNash (sourceGameForm source.core.prog source.core.env) (euPreference valuation) profile :=
  ((Machine.compile source).serializedBoundedOutcomeGame_nash_iff
    (ToEventGraph.observeSourceOutcome source.core source.legal)
    valuation schedulerUtility scheduler
    (source.sourceOutcomeSimulation.compileProfile profile)).trans
      (source.source_native_nash_iff valuation profile)

/-- Scheduling preserves and reflects the same approximate-equilibrium
budget for original players under arbitrary source valuations. -/
theorem source_serialized_approximate_nash_iff
    (valuation : VEnv L (sourceTerminalCtx source.core.prog) → Player → ℝ)
    (schedulerUtility : (Machine.compile source).serializedExecution.History → ℝ)
    (scheduler : (Machine.compile source).serializedInformation.BehavioralPolicy .scheduler)
    (profile : SourceBehavioralProfile source.core.prog) (ε : ℝ) :
    (∀ who replacement,
      expectedUtility
        ((Machine.compile source).serializedBoundedOutcomeGame
          (ToEventGraph.observeSourceOutcome source.core source.legal)
          valuation schedulerUtility).utility (.player who)
        (((Machine.compile source).serializedBoundedOutcomeGame
          (ToEventGraph.observeSourceOutcome source.core source.legal)
          valuation schedulerUtility).behavioral.form.play
          (Profile.update ((Machine.compile source).compileSerializedBehavioralProfile scheduler
            (source.sourceOutcomeSimulation.compileProfile profile)) (.player who) replacement)) ≤
      expectedUtility
        ((Machine.compile source).serializedBoundedOutcomeGame
          (ToEventGraph.observeSourceOutcome source.core source.legal)
          valuation schedulerUtility).utility (.player who)
        (((Machine.compile source).serializedBoundedOutcomeGame
          (ToEventGraph.observeSourceOutcome source.core source.legal)
          valuation schedulerUtility).behavioral.form.play
          ((Machine.compile source).compileSerializedBehavioralProfile scheduler
            (source.sourceOutcomeSimulation.compileProfile profile))) + ε) ↔
      IsεNash (sourceGameForm source.core.prog source.core.env) valuation ε profile := by
  refine Iff.trans ?_ (source.source_native_approximate_nash_iff valuation profile ε)
  rw [isεNash_iff]
  simp only [(Machine.compile source).expectedUtility_serializedBoundedOutcomeGame]
  apply forall_congr'
  intro who
  exact (Machine.compile source).serializedDeviation_expect_bound_iff scheduler
    (source.sourceOutcomeSimulation.compileProfile profile) who
    (fun state => valuation
      (ToEventGraph.observeSourceOutcome source.core source.legal state) who) _

variable [FiniteDomains source]
variable {Request : Participant Player → Type}
variable (interface : RequestCompiler.Interface
  (Machine.compile source).serializedInformation Request)
variable (schedulerUtility : (Machine.compile source).serializedExecution.History → ℝ)

/-- Request execution with arbitrary valuations of the independently defined
source outcomes; scheduler utility remains arbitrary analysis data. -/
def sourceSerializedRequestGame
    (valuation : VEnv L (sourceTerminalCtx source.core.prog) → Player → ℝ) :
    UtilityGame (Participant Player) where
  form := (source.serializedRequestGame interface schedulerUtility).form
  utility state := ((Machine.compile source).serializedBoundedOutcomeGame
    (ToEventGraph.observeSourceOutcome source.core source.legal) valuation schedulerUtility).utility
      state.1

/-- Revalue the existing full-history request certificate without changing
the compiler, target controllers, or strategy reconstruction. -/
def sourceSerializedRequestAdequacy
    (valuation : VEnv L (sourceTerminalCtx source.core.prog) → Player → ℝ) :
    DeviationAdequacy
      ((Machine.compile source).serializedBoundedOutcomeGame
        (ToEventGraph.observeSourceOutcome source.core source.legal)
        valuation schedulerUtility).behavioral
      (source.sourceSerializedRequestGame interface schedulerUtility valuation) :=
  (source.serializedRequestAdequacy interface schedulerUtility).toOutcomeSimulationOn.withUtility
    ((Machine.compile source).serializedBoundedOutcomeGame
      (ToEventGraph.observeSourceOutcome source.core source.legal)
      valuation schedulerUtility).utility

/-- Compile independent source policies through native execution, scheduling,
and request windows. The scheduler is an external, arbitrary policy. -/
def compileSourceSerializedRequestProfile
    (scheduler : (Machine.compile source).serializedInformation.BehavioralPolicy .scheduler)
    (profile : SourceBehavioralProfile source.core.prog) :
    Profile (source.serializedRequestGame interface schedulerUtility).form.sig :=
  source.compileSerializedRequestProfile interface schedulerUtility scheduler
    (fun who => ToEventGraph.compileSourceBehavioral source.core source.legal who (profile who))

/-- End-to-end Nash equivalence starts at the independent source game and
quantifies over all original-player request-controller mixtures. -/
theorem source_serialized_request_nash_iff
    (valuation : VEnv L (sourceTerminalCtx source.core.prog) → Player → ℝ)
    (scheduler : (Machine.compile source).serializedInformation.BehavioralPolicy .scheduler)
    (profile : SourceBehavioralProfile source.core.prog) :
    Participant.IsPlayerNash
      (source.sourceSerializedRequestGame interface schedulerUtility valuation)
      (source.compileSourceSerializedRequestProfile
        interface schedulerUtility scheduler profile) ↔
      IsNash (sourceGameForm source.core.prog source.core.env)
        (euPreference valuation) profile := by
  let certificate := source.sourceSerializedRequestAdequacy interface schedulerUtility valuation
  refine Iff.trans ?_ (source.source_serialized_nash_iff
    valuation schedulerUtility scheduler profile)
  change Participant.IsPlayerNash _ (certificate.compileProfile _) ↔ _
  constructor
  · intro hnash who replacement _
    have h := hnash who (certificate.compileStrategy (.player who) replacement) trivial
    change expectedUtility _ _ ((source.sourceSerializedRequestGame
      interface schedulerUtility valuation).form.play
        (Profile.update (certificate.compileProfile _) _ _)) ≤ _ at h
    rw [certificate.compileProfile_update, certificate.expectedUtility_compileProfile,
      certificate.expectedUtility_compileProfile] at h
    exact h
  · intro hnash who replacement _
    rw [certificate.expectedUtility_deviation _ _ _ trivial,
      certificate.expectedUtility_compileProfile]
    exact hnash who (certificate.backtranslateStrategy (.player who) replacement) trivial

/-- End-to-end request execution preserves and reflects every approximation
budget for every valuation of independent source outcomes. -/
theorem source_serialized_request_approximate_nash_iff
    (valuation : VEnv L (sourceTerminalCtx source.core.prog) → Player → ℝ)
    (scheduler : (Machine.compile source).serializedInformation.BehavioralPolicy .scheduler)
    (profile : SourceBehavioralProfile source.core.prog) (ε : ℝ) :
    (∀ who replacement,
      expectedUtility (source.sourceSerializedRequestGame
        interface schedulerUtility valuation).utility (.player who)
        ((source.sourceSerializedRequestGame interface schedulerUtility valuation).form.play
          (Profile.update (source.compileSourceSerializedRequestProfile
            interface schedulerUtility scheduler profile) (.player who) replacement)) ≤
      expectedUtility (source.sourceSerializedRequestGame
        interface schedulerUtility valuation).utility (.player who)
        ((source.sourceSerializedRequestGame interface schedulerUtility valuation).form.play
          (source.compileSourceSerializedRequestProfile
            interface schedulerUtility scheduler profile)) + ε) ↔
      IsεNash (sourceGameForm source.core.prog source.core.env) valuation ε profile := by
  let certificate := source.sourceSerializedRequestAdequacy interface schedulerUtility valuation
  refine Iff.trans ?_ (source.source_serialized_approximate_nash_iff
    valuation schedulerUtility scheduler profile ε)
  change (∀ who replacement,
    expectedUtility _ _ ((source.sourceSerializedRequestGame
      interface schedulerUtility valuation).form.play
        (Profile.update (certificate.compileProfile _) (.player who) replacement)) ≤
    expectedUtility _ _ ((source.sourceSerializedRequestGame
      interface schedulerUtility valuation).form.play (certificate.compileProfile _)) + ε) ↔ _
  constructor
  · intro hbound who replacement
    have h := hbound who (certificate.compileStrategy (.player who) replacement)
    rw [certificate.compileProfile_update, certificate.expectedUtility_compileProfile,
      certificate.expectedUtility_compileProfile] at h
    exact h
  · intro hbound who replacement
    rw [certificate.expectedUtility_deviation _ _ _ trivial,
      certificate.expectedUtility_compileProfile]
    exact hbound who (certificate.backtranslateStrategy (.player who) replacement)

/-- Honest scheduled request execution preserves the independent source law
for every behavioral scheduler, including schedulers that use public game data. -/
theorem source_serialized_request_honest_law
    (scheduler : (Machine.compile source).serializedInformation.BehavioralPolicy .scheduler)
    (profile : SourceBehavioralProfile source.core.prog) :
    ((source.serializedRequestGame interface schedulerUtility).form.play
      (source.compileSourceSerializedRequestProfile
        interface schedulerUtility scheduler profile)).map
        (fun state => ToEventGraph.observeSourceOutcome source.core source.legal
          state.1.state.base) =
      denoteSource source.core.prog profile source.core.env := by
  have hnative := source.serialized_request_honest_law interface schedulerUtility scheduler
    (fun who => ToEventGraph.compileSourceBehavioral source.core source.legal who (profile who))
  have hdecoded := congrArg
    (fun law => law.map (ToEventGraph.observeSourceOutcome source.core source.legal)) hnative
  have hsource := ToEventGraph.runBehavioral_compileSource_source source.core source.legal profile
  refine Eq.trans ?_ hsource
  simpa only [FinDist.map_comp, Function.comp_def, Machine.Program.information,
    Machine.compile, Machine.ofCompiled, compileSourceSerializedRequestProfile] using hdecoded

/-- Every unilateral combined request and order-aware deviation is a finite
mixture of independent source-policy deviations with the same honest opponents. -/
theorem source_serialized_request_deviation_law
    (scheduler : (Machine.compile source).serializedInformation.BehavioralPolicy .scheduler)
    (profile : SourceBehavioralProfile source.core.prog) (who : Player)
    (replacement : (source.serializedRequestGame interface schedulerUtility).form.sig.Strategy
      (.player who)) :
    ∃ alternatives : FinDist (SourceBehavioralPolicy source.core.prog who),
      ((source.serializedRequestGame interface schedulerUtility).form.play
        (Profile.update
          (source.compileSourceSerializedRequestProfile
            interface schedulerUtility scheduler profile)
          (.player who) replacement)).map
            (fun state => ToEventGraph.observeSourceOutcome source.core source.legal
              state.1.state.base) =
        alternatives.bind fun alternative =>
          denoteSource source.core.prog
            (Profile.update (sig := sourceGameSignature source.core.prog)
              profile who alternative) source.core.env := by
  obtain ⟨nativeAlternatives, hlaw⟩ := source.serialized_request_deviation_law
    interface schedulerUtility scheduler
    (fun player => ToEventGraph.compileSourceBehavioral source.core source.legal
      player (profile player)) who replacement
  refine ⟨nativeAlternatives.map
    (ToEventGraph.backtranslateNativeBehavioral source.core source.legal who), ?_⟩
  have hdecoded := congrArg
    (fun law => law.map (ToEventGraph.observeSourceOutcome source.core source.legal)) hlaw
  simp only [FinDist.map_comp, FinDist.map_bind, Function.comp_def] at hdecoded
  refine hdecoded.trans ?_
  rw [FinDist.bind_map]
  apply FinDist.bind_congr
  intro alternative _
  exact source.sourceOutcomeSimulation.deviation_law profile who alternative trivial

/-- A bound on any source observable survives every target controller mixture,
uniformly over the scheduler and without assumptions on deviator utilities. -/
theorem source_serialized_request_guarantee
    (scheduler : (Machine.compile source).serializedInformation.BehavioralPolicy .scheduler)
    (profile : SourceBehavioralProfile source.core.prog) (who : Player)
    (value : VEnv L (sourceTerminalCtx source.core.prog) → ℝ) (bound : ℝ)
    (hbound : ∀ alternative : SourceBehavioralPolicy source.core.prog who,
      bound ≤ (denoteSource source.core.prog
        (Profile.update (sig := sourceGameSignature source.core.prog) profile who alternative)
        source.core.env).expect value)
    (replacement : (source.serializedRequestGame interface schedulerUtility).form.sig.Strategy
      (.player who)) :
    bound ≤ ((source.serializedRequestGame interface schedulerUtility).form.play
      (Profile.update
        (source.compileSourceSerializedRequestProfile
          interface schedulerUtility scheduler profile)
        (.player who) replacement)).expect
          (fun state => value (ToEventGraph.observeSourceOutcome source.core source.legal
            state.1.state.base)) := by
  obtain ⟨alternatives, hlaw⟩ := source.source_serialized_request_deviation_law
    interface schedulerUtility scheduler profile who replacement
  rw [← FinDist.expect_map, hlaw, FinDist.expect_bind]
  calc
    bound = alternatives.expect (fun _ => bound) := (FinDist.expect_const _ _).symm
    _ ≤ _ := FinDist.expect_mono fun alternative _ => hbound alternative

end Vegas.WFProgram
