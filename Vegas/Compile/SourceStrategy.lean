/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.PolicyInformation
import Vegas.Compile.SourceBacktranslation
import Vegas.EventGraph.PolicyRoundtrip

/-! # Source and native strategic interfaces

This module reconstructs policies across the source/compiler boundary.
Execution-law proofs are separate: `SourceExecutionLaw` identifies the source
marginal, and `EventGraph.KernelBehavioral` identifies native graph execution.
-/

noncomputable section

namespace Vegas.ToEventGraph

open EventGraph GameTheory.Protocol

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

/-- Implement a source behavioral policy as a native event-graph policy. -/
def compileSourceBehavioral (program : GraphProgram P L)
    (legal : Legal program.prog) (who : P)
    (policy : SourceBehavioralPolicy program.prog who) :
    (toInformationModel (compile program).graph (compile program).graphWF
      (compile_guardLive program legal)).BehavioralPolicy who :=
  (compileSourcePolicy program.prog program.fresh
    (BuildState.fromInitial (initialState program.Γ program.env program.wctx))
    rfl who policy).behavioral (compile program).graphWF
      (compile_guardLive program legal)

/-- Reconstruct a source policy from an arbitrary native behavioral policy. -/
def backtranslateNativeBehavioral (program : GraphProgram P L)
    (legal : Legal program.prog) (who : P)
    (policy : (toInformationModel (compile program).graph
      (compile program).graphWF (compile_guardLive program legal)).BehavioralPolicy who) :
    SourceBehavioralPolicy program.prog who :=
  backtranslateCommitPolicy program who
    (CommitPolicy.fromBehavioral (compile program).graphWF
      (compile_guardLive program legal) who policy)

/-- Compiling the reconstructed source policy recovers an arbitrary native
policy at every realized information state. -/
theorem compile_backtranslateNativeBehavioral_at
    (program : GraphProgram P L) (legal : Legal program.prog) (who : P)
    (policy : (toInformationModel (compile program).graph
      (compile program).graphWF (compile_guardLive program legal)).BehavioralPolicy who)
    {state : (toExecutionProtocol (compile program).graph
      (compile program).graphWF (compile_guardLive program legal)).State}
    (trace : (toExecutionProtocol (compile program).graph
      (compile program).graphWF (compile_guardLive program legal)).Trace state) :
    compileSourceBehavioral program legal who
        (backtranslateNativeBehavioral program legal who policy)
        ((toInfoSignals (compile program).graph (compile program).graphWF
          (compile_guardLive program legal)).infoOf who trace) =
      policy ((toInfoSignals (compile program).graph (compile program).graphWF
        (compile_guardLive program legal)).infoOf who trace) := by
  unfold compileSourceBehavioral backtranslateNativeBehavioral
  rw [compile_backtranslateCommitPolicy]
  exact CommitPolicy.behavioral_fromBehavioral (compile program).graphWF
    (compile_guardLive program legal) (compiled_commitInformationLocal program legal)
    who policy trace (by
      intro first second hfirst hsecond
      exact compiled_readyCommitNode_unique program state.1 who hfirst hsecond)

/-- Playerwise source reconstruction preserves the complete bounded native
history law for every profile, fuel bound, and starting history. -/
theorem runBehavioralFrom_compile_backtranslate
    (program : GraphProgram P L) (legal : Legal program.prog)
    (profile : ∀ who, (toInformationModel (compile program).graph
      (compile program).graphWF (compile_guardLive program legal)).BehavioralPolicy who)
    (fuel : Nat)
    (history : (toExecutionProtocol (compile program).graph
      (compile program).graphWF (compile_guardLive program legal)).History) :
    (toInformationModel (compile program).graph (compile program).graphWF
      (compile_guardLive program legal)).runBehavioralFrom
        (fun who => compileSourceBehavioral program legal who
          (backtranslateNativeBehavioral program legal who (profile who))) fuel history =
      (toInformationModel (compile program).graph (compile program).graphWF
        (compile_guardLive program legal)).runBehavioralFrom profile fuel history := by
  apply (toInformationModel (compile program).graph (compile program).graphWF
    (compile_guardLive program legal)).runBehavioralFrom_congr
  intro later _ _ who
  exact compile_backtranslateNativeBehavioral_at program legal who (profile who) later.trace

/-- A unilateral native deviation is reconstructed without changing any
opponent's source policy. The equality preserves complete native histories. -/
theorem runBehavioralFrom_compile_deviation
    (program : GraphProgram P L) (legal : Legal program.prog)
    (profile : SourceBehavioralProfile program.prog) (who : P)
    (replacement : (toInformationModel (compile program).graph
      (compile program).graphWF (compile_guardLive program legal)).BehavioralPolicy who)
    (fuel : Nat)
    (history : (toExecutionProtocol (compile program).graph
      (compile program).graphWF (compile_guardLive program legal)).History) :
    (toInformationModel (compile program).graph (compile program).graphWF
      (compile_guardLive program legal)).runBehavioralFrom
        (fun player => compileSourceBehavioral program legal player
          (GameTheory.Profile.update (sig := sourceGameSignature program.prog) profile who
            (backtranslateNativeBehavioral program legal who replacement) player)) fuel history =
      (toInformationModel (compile program).graph (compile program).graphWF
        (compile_guardLive program legal)).runBehavioralFrom
          (GameTheory.Profile.update
            (sig := (toInformationModel (compile program).graph (compile program).graphWF
              (compile_guardLive program legal)).behavioralSignature)
            (fun player => compileSourceBehavioral program legal player (profile player))
            who replacement) fuel history := by
  apply InformationModel.runBehavioralFrom_congr
  intro later _ _ player
  by_cases heq : player = who
  · subst player
    simp only [GameTheory.Profile.update_same]
    exact compile_backtranslateNativeBehavioral_at program legal who replacement later.trace
  · simp only [GameTheory.Profile.update_of_ne _ _ heq]

end Vegas.ToEventGraph
