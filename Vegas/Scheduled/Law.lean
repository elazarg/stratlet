/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Scheduled.Backtranslation

/-! # Complete behavioral laws across automatic settlement -/

noncomputable section

namespace Vegas.Machine.Program

open GameTheory.Protocol GameTheory.Math.Probability EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}

/-- Atomic execution never changes a field whose writer has already completed. -/
theorem executionStep_extends (program : Program Player L) (state : program.State)
    (command : {joint // program.execution.Legal state joint}) {next : program.State}
    (hnext : next ∈ (program.execution.step state command).support) :
    state.1.Extends next.1 := by
  classical
  change next ∈ ((toExecutionProtocol program.graph program.graphWF program.guardLive).step
    state command).support at hnext
  by_cases hinternal : (readyInternalNodes program.graph state.1).Nonempty
  · rw [EventGraph.toExecutionProtocol_step_eq_stepReadyInternal
      program.graph program.graphWF program.guardLive state command hinternal] at hnext
    exact extends_of_stepReadyInternal program.graphWF state hinternal hnext
  · rw [toExecutionProtocol_step_eq_pure_applyFrontier
      program.graph program.graphWF program.guardLive state command
        (Finset.not_nonempty_iff_eq_empty.mp hinternal), FinDist.mem_support_pure] at hnext
    subst next
    exact extends_applyFrontier_of_legal program.graph program.graphWF program.guardLive
      state command.1 command.2

/-- Every supported continuation preserves completed field values. -/
theorem runBehavioralFrom_extends (program : Program Player L)
    (profile : (who : Player) → program.information.BehavioralPolicy who)
    (fuel : Nat) (start next : program.execution.History)
    (hnext : next ∈ (program.information.runBehavioralFrom profile fuel start).support) :
    start.state.1.Extends next.state.1 := by
  induction fuel generalizing start with
  | zero =>
      change next ∈ (FinDist.pure start).support at hnext
      rw [FinDist.mem_support_pure] at hnext
      subst next
      exact Config.Extends.refl _
  | succ fuel ih =>
      by_cases hterm : program.execution.terminal start.state
      · rw [InformationModel.runBehavioralFrom_of_terminal _ _ _ hterm,
          FinDist.mem_support_pure] at hnext
        subst next
        exact Config.Extends.refl _
      · rw [InformationModel.runBehavioralFrom_succ_of_not_terminal _ _ _ hterm,
          FinDist.support_bind] at hnext
        obtain ⟨command, _, hnext⟩ := Set.mem_iUnion₂.mp hnext
        rw [FinDist.support_bindOnSupport] at hnext
        obtain ⟨middle, hmiddle, hnext⟩ := Set.mem_iUnion₂.mp hnext
        exact (program.executionStep_extends start.state command hmiddle).trans
          (ih (start.extend command.2 hmiddle) hnext)

/-- Compile the real players and supply the scheduler as an environment policy. -/
def compileSerializedBehavioralProfile (program : Program Player L)
    (scheduler : program.serializedInformation.BehavioralPolicy .scheduler)
    (profile : (who : Player) → program.information.BehavioralPolicy who) :
    (who : Participant Player) → program.serializedInformation.BehavioralPolicy who
  | .scheduler => scheduler
  | .player who => program.compileSerializedBehavioralPolicy who (profile who)

/-- Forget the execution coordinate of a legal runtime command. -/
def serializedSourceCommand (program : Program Player L)
    {state : program.State} {log : List (List Player)}
    (command : {joint // program.serializedExecution.Legal ⟨state, log⟩ joint}) :
    {joint // program.execution.Legal state joint} :=
  ⟨fun who => command.1 (.player who), program.serializedPlayers_legal command⟩

/-- At matching information, any behavioral scheduler gives the same source
joint-action law. Its current draw is simultaneous with the players' draws. -/
theorem behavioralJoint_compileSerialized (program : Program Player L)
    (scheduler : program.serializedInformation.BehavioralPolicy .scheduler)
    (profile : (who : Player) → program.information.BehavioralPolicy who)
    (source : program.execution.History) (log : List (List Player))
    (trace : program.serializedExecution.Trace ⟨source.state, log⟩)
    (hinfo : ∀ who, program.information.infoOf who source.trace =
      program.eraseSerializedPlayerInformation who
        (program.serializedInformation.infoOf (.player who) trace))
    (hterm : ¬ program.serializedExecution.terminal ⟨source.state, log⟩) :
    (program.serializedInformation.behavioralJoint
      (program.compileSerializedBehavioralProfile scheduler profile) trace hterm).map
        program.serializedSourceCommand =
      program.information.behavioralJoint profile source.trace hterm := by
  apply FinDist.map_injective Subtype.val_injective
  simp only [InformationModel.behavioralJoint, FinDist.map_comp]
  have hplayers :
      (FinDist.pi fun i =>
        program.compileSerializedBehavioralProfile scheduler profile i
          (program.serializedInformation.infoOf i trace)).map
          (fun draws who => draws (.player who)) =
        FinDist.pi (fun who =>
          program.compileSerializedBehavioralProfile scheduler profile (.player who)
            (program.serializedInformation.infoOf (.player who) trace)) := by
    simpa using
      (FinDist.pi_map_embedding
        ⟨Participant.player, fun _ _ h => Participant.player.inj h⟩
        (fun i => program.compileSerializedBehavioralProfile scheduler profile i
          (program.serializedInformation.infoOf i trace)))
  rw [show (fun a => (a : {joint // program.execution.Legal source.state joint}).val) ∘
      program.serializedSourceCommand ∘ _ =
      (fun draws who => (draws who).val) ∘ (fun draws who => draws (.player who)) from rfl,
    ← FinDist.map_comp, hplayers, ← FinDist.pi_map]
  change _ = (FinDist.pi fun i => profile i (program.information.infoOf i source.trace)).map
    (fun draws i => (draws i).val)
  rw [← FinDist.pi_map]
  congr 1
  funext who
  simp only [compileSerializedBehavioralProfile, compileSerializedBehavioralPolicy,
    FinDist.map_comp]
  change (profile who (program.eraseSerializedPlayerInformation who
    (program.serializedInformation.infoOf (.player who) trace))).map Subtype.val = _
  rw [← hinfo who]

/-- The canonical source continuation law on terminal graph states. -/
def terminalStateLaw (program : Program Player L)
    (profile : (who : Player) → program.information.BehavioralPolicy who)
    (history : program.execution.History) : FinDist program.State :=
  (program.information.runBehavioralFrom profile program.graph.nodeCount history).map
    ExecutionProtocol.History.state

theorem terminalStateLaw_of_terminal (program : Program Player L)
    (profile : (who : Player) → program.information.BehavioralPolicy who)
    (history : program.execution.History) (hterm : program.execution.terminal history.state) :
    program.terminalStateLaw profile history = FinDist.pure history.state := by
  rw [terminalStateLaw, InformationModel.runBehavioralFrom_of_terminal _ _ _ hterm,
    FinDist.map_pure]

/-- The terminal law satisfies the source game's one-step equation without
an artificial cutoff: the graph-node horizon already guarantees absorption. -/
theorem terminalStateLaw_step (program : Program Player L)
    (profile : (who : Player) → program.information.BehavioralPolicy who)
    (history : program.execution.History) (hterm : ¬ program.execution.terminal history.state) :
    program.terminalStateLaw profile history =
      (program.information.behavioralJoint profile history.trace hterm).bind fun command =>
        (program.execution.step history.state command).bindOnSupport fun _ realized =>
          program.terminalStateLaw profile (history.extend command.2 realized) := by
  unfold terminalStateLaw
  rw [← program.information.runBehavioralFrom_bound_add profile
    program.boundedHorizon 1 history]
  rw [InformationModel.runBehavioralFrom_succ_of_not_terminal _ _ _ hterm,
    FinDist.map_bind]
  apply FinDist.bind_congr
  intro command _
  exact FinDist.map_bindOnSupport _ _ _

/-- Automatic source closure is neutral to every source continuation law. -/
theorem settleHistory_terminalStateLaw (program : Program Player L)
    (profile : (who : Player) → program.information.BehavioralPolicy who)
    (fuel : Nat) (history : program.execution.History) :
    (program.settleHistory fuel history).bind (program.terminalStateLaw profile) =
      program.terminalStateLaw profile history := by
  induction fuel generalizing history with
  | zero => exact FinDist.pure_bind _ _
  | succ fuel ih =>
      unfold settleHistory
      split
      next hinternal =>
        rw [FinDist.bind_bindOnSupport]
        have hterm := (EventGraph.sourceInternalCommand
          program.graphWF program.guardLive history.state hinternal).2.1
        rw [program.terminalStateLaw_step profile history hterm,
          InformationModel.behavioralJoint_eq_pure_of_no_active _ _ _ hterm
            (fun who hactive => (Finset.not_nonempty_iff_eq_empty.mpr hactive.2.1) hinternal),
          FinDist.pure_bind]
        exact FinDist.bindOnSupport_congr fun _ _ => ih _
      next _ => exact FinDist.pure_bind _ _

/-- One strategic frontier followed by automatic closure has the same final
law as the original atomic source game. -/
theorem expandRound_terminalStateLaw (program : Program Player L)
    (profile : (who : Player) → program.information.BehavioralPolicy who)
    (history : program.execution.History) (hterm : ¬ program.execution.terminal history.state) :
    (program.information.behavioralJoint profile history.trace hterm).bind
      (fun command => (program.expandRound history command.1 command.2).bind
        (program.terminalStateLaw profile)) = program.terminalStateLaw profile history := by
  unfold expandRound
  split
  next _ =>
    simp only [program.settleHistory_terminalStateLaw]
    exact FinDist.bind_const _ _
  next _ =>
    rw [program.terminalStateLaw_step profile history hterm]
    apply FinDist.bind_congr
    intro command _
    rw [FinDist.bind_bindOnSupport]
    exact FinDist.bindOnSupport_congr fun _ _ => program.settleHistory_terminalStateLaw profile _ _

/-- One compiled runtime round and one atomic source frontier with closure
agree on the joint state-and-information law, for any behavioral scheduler. -/
theorem compiledRound_map_summary (program : Program Player L)
    (scheduler : program.serializedInformation.BehavioralPolicy .scheduler)
    (profile : (who : Player) → program.information.BehavioralPolicy who)
    (source : program.execution.History) (target : program.serializedExecution.History)
    (hmatch : program.historySummary source = program.serializedHistorySummary target)
    (hterm : ¬ program.execution.terminal source.state) :
    ((program.information.behavioralJoint profile source.trace hterm).bind fun command =>
      program.expandRound source command.1 command.2).map program.historySummary =
    (program.serializedInformation.runBehavioralFrom
      (program.compileSerializedBehavioralProfile scheduler profile) 1 target).map
        program.serializedHistorySummary := by
  obtain ⟨⟨base, log⟩, trace⟩ := target
  have hbase := congrArg Prod.fst hmatch
  change source.state = base at hbase
  subst base
  have hinfo := congrFun (congrArg Prod.snd hmatch)
  rw [program.serializedBehavioralRound_expands source log trace hinfo _ hterm,
    ← program.behavioralJoint_compileSerialized scheduler profile source log trace hinfo hterm,
    FinDist.bind_map]
  rfl

/-- A nonterminal one-round run always appends exactly one runtime step. -/
theorem serializedRound_length (program : Program Player L)
    (profile : (who : Participant Player) →
      program.serializedInformation.BehavioralPolicy who)
    (start next : program.serializedExecution.History)
    (hterm : ¬ program.serializedExecution.terminal start.state)
    (hnext : next ∈ (program.serializedInformation.runBehavioralFrom
      profile 1 start).support) : next.trace.length = start.trace.length + 1 := by
  rw [InformationModel.runBehavioralFrom_succ_of_not_terminal _ _ _ hterm,
    FinDist.support_bind] at hnext
  obtain ⟨command, _, hnext⟩ := Set.mem_iUnion₂.mp hnext
  rw [FinDist.support_bindOnSupport] at hnext
  obtain ⟨middle, hmiddle, hnext⟩ := Set.mem_iUnion₂.mp hnext
  change next ∈ (FinDist.pure (start.extend command.2 hmiddle)).support at hnext
  rw [FinDist.mem_support_pure] at hnext
  subst next
  rfl

/-- The actual serialized execution of compiled source policies has exactly
the atomic game's terminal-state law, even with an arbitrary behavioral
scheduler observing public data. This is a complete-run statement. -/
theorem runBehavioralFrom_compileSerialized (program : Program Player L)
    (scheduler : program.serializedInformation.BehavioralPolicy .scheduler)
    (profile : (who : Player) → program.information.BehavioralPolicy who)
    (fuel : Nat) (source : program.execution.History) (target : program.serializedExecution.History)
    (hmatch : program.historySummary source = program.serializedHistorySummary target)
    (hcapacity : program.graph.nodeCount ≤ target.trace.length + fuel) :
    (program.serializedInformation.runBehavioralFrom
      (program.compileSerializedBehavioralProfile scheduler profile) fuel target).map
        (fun history => history.state.base) = program.terminalStateLaw profile source := by
  have hbase : source.state = target.state.base := congrArg Prod.fst hmatch
  induction fuel generalizing source target with
  | zero =>
      have hterminal := (program.serializedBoundedGame (fun _ => 0)).bounded
        target.state target.trace (by exact hcapacity)
      have hsource : program.execution.terminal source.state := hbase ▸ hterminal
      rw [program.terminalStateLaw_of_terminal profile source hsource]
      change (FinDist.pure target).map _ = _
      rw [FinDist.map_pure, hbase]
  | succ fuel ih =>
      by_cases hterminal : program.serializedExecution.terminal target.state
      · have hsource : program.execution.terminal source.state := hbase ▸ hterminal
        rw [program.terminalStateLaw_of_terminal profile source hsource,
          InformationModel.runBehavioralFrom_of_terminal _ _ _ hterminal,
          FinDist.map_pure, hbase]
      · have hsource : ¬ program.execution.terminal source.state := by
          intro ht
          apply hterminal
          change program.execution.terminal target.state.base
          exact hbase ▸ ht
        let targetRound := program.serializedInformation.runBehavioralFrom
          (program.compileSerializedBehavioralProfile scheduler profile) 1 target
        let sourceRound := (program.information.behavioralJoint profile source.trace hsource).bind
          fun command => program.expandRound source command.1 command.2
        have hround := program.compiledRound_map_summary scheduler profile source target
          hmatch hsource
        have hcontinuation : targetRound.bind (fun next =>
            (program.serializedInformation.runBehavioralFrom
              (program.compileSerializedBehavioralProfile scheduler profile) fuel next).map
                (fun history => history.state.base)) =
            sourceRound.bind (program.terminalStateLaw profile) := by
          apply FinDist.bind_eq_of_map_eq targetRound sourceRound
            program.serializedHistorySummary program.historySummary hround.symm
          intro next hnext middle _ heq
          apply ih middle next heq.symm
          · have hlength := program.serializedRound_length _ target next hterminal hnext
            omega
          · exact congrArg Prod.fst heq.symm
        rw [show fuel + 1 = 1 + fuel by omega,
          InformationModel.runBehavioralFrom_add, FinDist.map_bind]
        change targetRound.bind _ = _
        rw [hcontinuation]
        exact (FinDist.bind_bind _ _ _).trans
          (program.expandRound_terminalStateLaw profile source hsource)

/-- Honest compilation preserves the full terminal-state distribution from
initial play, uniformly over public-data behavioral scheduler policies. -/
theorem runBehavioral_compileSerialized (program : Program Player L)
    (scheduler : program.serializedInformation.BehavioralPolicy .scheduler)
    (profile : (who : Player) → program.information.BehavioralPolicy who) :
    (program.serializedInformation.runBehavioral
      (program.compileSerializedBehavioralProfile scheduler profile) program.graph.nodeCount).map
        (fun history => history.state.base) =
      (program.information.runBehavioral profile program.graph.nodeCount).map
        ExecutionProtocol.History.state := by
  exact program.runBehavioralFrom_compileSerialized scheduler profile _
    program.execution.initHistory program.serializedExecution.initHistory rfl (by simp)

end Vegas.Machine.Program
