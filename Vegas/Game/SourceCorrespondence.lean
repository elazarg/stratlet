/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.SourceExecutionLaw
import Vegas.Compile.SourceExecutionOutcome
import Vegas.Compile.SourceStrategy
import Vegas.EventGraph.KernelBehavioral
import Vegas.Game.Basic
import Vegas.Runtime.Approximate

/-! # Independent source strategies and native game forms -/

noncomputable section

namespace Vegas.ToEventGraph

open EventGraph GameTheory GameTheory.Protocol GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

/-- Written node execution under the compiled source policies preserves the
independent source denotation, including every terminal source binding. -/
theorem runPolicyNodes_compileSourcePolicy_source
    (program : GraphProgram P L) (legal : Legal program.prog)
    (profile : SourceBehavioralProfile program.prog) :
    (runPolicyNodes (compile program).graphWF (compile_guardLive program legal)
      (fun who => compileSourcePolicy program.prog program.fresh
        (BuildState.fromInitial (initialState program.Γ program.env program.wctx))
        rfl who (profile who))
      ⟨Config.initial (compile program).graph, .initial⟩
      (compile program).graph.nodeOrder).map (observeSourceOutcome program legal) =
        denoteSource program.prog profile program.env := by
  have hgraph := runPolicyNodes_observeSourceOutcome_eq_coupled program legal
    (fun who => compileSourcePolicy program.prog program.fresh
      (BuildState.fromInitial (initialState program.Γ program.env program.wctx))
      rfl who (profile who)) (compile_guardLive program legal)
  exact hgraph.trans (runCoupledSource_compileSourcePolicy_source program.prog program.fresh
    (BuildState.fromInitial (initialState program.Γ program.env program.wctx)) rfl
    (compile_guardLive program legal) profile (compiledInitialCoupled program))

/-- Native behavioral execution of the source policies has exactly the
independently defined source outcome law. -/
theorem runBehavioral_compileSource_source
    (program : GraphProgram P L) (legal : Legal program.prog)
    (profile : SourceBehavioralProfile program.prog) :
    ((toInformationModel (compile program).graph (compile program).graphWF
      (compile_guardLive program legal)).runBehavioral
      (fun who => compileSourceBehavioral program legal who (profile who))
      (compile program).graph.nodeCount).map
        (fun history => observeSourceOutcome program legal history.state) =
      denoteSource program.prog profile program.env := by
  let policies : CommitPolicyProfile (compile program).graph :=
    fun who => compileSourcePolicy program.prog program.fresh
      (BuildState.fromInitial (initialState program.Γ program.env program.wctx))
      rfl who (profile who)
  have hnative := runBehavioral_eq_nodeOrder (G := (compile program).graph)
    (compile program).graphWF
    (compile_guardLive program legal) policies
    (fun cfg who _ _ => compiled_readyCommitNode_unique program cfg who)
  have hdecoded := congrArg (fun law => law.map (observeSourceOutcome program legal)) hnative
  have hnode := runPolicyNodes_compileSourcePolicy_source program legal profile
  simpa only [FinDist.map_comp, Function.comp_def, compileSourceBehavioral, policies] using
    hdecoded.trans hnode

/-- Source compilation is a utility-independent outcome simulation against
every native behavioral deviation. Opponents retain their original policies. -/
def sourceNativeOutcomeSimulation
    (program : GraphProgram P L) (legal : Legal program.prog) :
    Runtime.OutcomeSimulationOn (sourceGameForm program.prog program.env)
      ((toInformationModel (compile program).graph (compile program).graphWF
        (compile_guardLive program legal)).toBehavioralGameForm
        (compile program).graph.nodeCount) (fun _ _ => True) where
  compileStrategy := compileSourceBehavioral program legal
  backtranslateStrategy := backtranslateNativeBehavioral program legal
  decodeOutcome history := observeSourceOutcome program legal history.state
  honest_law := runBehavioral_compileSource_source program legal
  compiled_considered _ _ := trivial
  deviation_law profile who replacement _ := by
    have hdeviation := runBehavioralFrom_compile_deviation program legal profile who replacement
      (compile program).graph.nodeCount
      (toExecutionProtocol (compile program).graph (compile program).graphWF
        (compile_guardLive program legal)).initHistory
    have hdecoded := congrArg
      (fun law => law.map (fun history => observeSourceOutcome program legal history.state))
      hdeviation
    exact hdecoded.symm.trans (runBehavioral_compileSource_source program legal
      (Profile.update (sig := sourceGameSignature program.prog) profile who
        (backtranslateNativeBehavioral program legal who replacement)))

end Vegas.ToEventGraph

namespace Vegas.WFProgram

open GameTheory

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

/-- The independent source game form simulates the checked compiler's native
behavioral game, uniformly over every source policy and native replacement. -/
def sourceOutcomeSimulation (source : WFProgram P L) :
    Runtime.OutcomeSimulationOn (sourceGameForm source.core.prog source.core.env)
      source.game.behavioralForm (fun _ _ => True) :=
  ToEventGraph.sourceNativeOutcomeSimulation source.core source.legal

/-- For every valuation of source outcomes, independent source Nash profiles
are exactly their compiled native Nash profiles. -/
theorem source_native_nash_iff (source : WFProgram P L)
    (valuation : VEnv L (sourceTerminalCtx source.core.prog) → P → ℝ)
    (profile : SourceBehavioralProfile source.core.prog) :
    IsNash
      ((Machine.compile source).outcomeGame
        (ToEventGraph.observeSourceOutcome source.core source.legal) valuation).behavioral.form
      (euPreference ((Machine.compile source).outcomeGame
        (ToEventGraph.observeSourceOutcome source.core source.legal) valuation).utility)
      (source.sourceOutcomeSimulation.compileProfile profile) ↔
      IsNash (sourceGameForm source.core.prog source.core.env) (euPreference valuation) profile :=
  (source.sourceOutcomeSimulation.withUtility valuation).isNash_compileProfile_iff profile

/-- The compiler preserves and reflects the exact approximate-equilibrium
budget for every valuation of independent source outcomes. -/
theorem source_native_approximate_nash_iff (source : WFProgram P L)
    (valuation : VEnv L (sourceTerminalCtx source.core.prog) → P → ℝ)
    (profile : SourceBehavioralProfile source.core.prog) (ε : ℝ) :
    IsεNash
      ((Machine.compile source).outcomeGame
        (ToEventGraph.observeSourceOutcome source.core source.legal) valuation).behavioral.form
      ((Machine.compile source).outcomeGame
        (ToEventGraph.observeSourceOutcome source.core source.legal) valuation).utility ε
      (source.sourceOutcomeSimulation.compileProfile profile) ↔
      IsεNash (sourceGameForm source.core.prog source.core.env) valuation ε profile :=
  (source.sourceOutcomeSimulation.withUtility valuation).isεNash_compileProfile_iff profile ε

end Vegas.WFProgram
