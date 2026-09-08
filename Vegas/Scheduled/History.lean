/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Scheduled.Game

/-!
# Expanding serialized execution into atomic histories

Automatic settlement batches several atomic internal transitions. Its history
expansion retains their individual random draws and observations. Pushing the
expanded law forward to its endpoint recovers the runtime settlement law
exactly, including its probabilities.
-/

noncomputable section

namespace Vegas.Machine.Program

open GameTheory.Protocol GameTheory.Math.Probability EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}

/-- Execute automatic closure while recording every atomic source step. -/
def settleHistory (program : Program Player L) :
    Nat → program.execution.History → FinDist program.execution.History
  | 0, history => FinDist.pure history
  | fuel + 1, history =>
      if hinternal : (readyInternalNodes program.graph history.state.1).Nonempty then
        let command := EventGraph.sourceInternalCommand
          program.graphWF program.guardLive history.state hinternal
        (program.execution.step history.state command).bindOnSupport
          fun _ realized => program.settleHistory fuel
            (history.extend command.2 realized)
      else FinDist.pure history

/-- Expanding automatic closure preserves its exact endpoint probability law. -/
theorem settleHistory_map_state (program : Program Player L) (fuel : Nat)
    (history : program.execution.History) :
    (program.settleHistory fuel history).map ExecutionProtocol.History.state =
      EventGraph.settleInternal program.graphWF fuel history.state := by
  induction fuel generalizing history with
  | zero => exact FinDist.map_pure _ _
  | succ fuel ih =>
      unfold settleHistory
      split
      next hinternal =>
        rw [FinDist.map_bindOnSupport,
          EventGraph.settleInternal_succ_eq_source_step
            program.graphWF program.guardLive fuel history.state hinternal]
        exact FinDist.bindOnSupport_eq_bind_of_eq_on_support
          (fun _next _realized => ih _)
      next hinternal =>
        rw [EventGraph.settleInternal_of_no_internal program.graphWF (fuel + 1)
          history.state (Finset.not_nonempty_iff_eq_empty.mp hinternal)]
        exact FinDist.map_pure _ _

/-- Automatic source steps do not add a decision to any player's own memory. -/
theorem settleHistory_own (program : Program Player L) (fuel : Nat)
    (history : program.execution.History) (who : Player)
    {next : program.execution.History}
    (hnext : next ∈ (program.settleHistory fuel history).support) :
    (program.information.infoOf who next.trace).own =
      (program.information.infoOf who history.trace).own := by
  induction fuel generalizing history with
  | zero =>
      rw [settleHistory, FinDist.mem_support_pure] at hnext
      subst next
      rfl
  | succ fuel ih =>
      unfold settleHistory at hnext
      split at hnext
      next hinternal =>
        rw [FinDist.support_bindOnSupport] at hnext
        obtain ⟨state, hstate, hnext⟩ := Set.mem_iUnion₂.mp hnext
        rw [ih _ hnext]
        rfl
      next _ =>
        rw [FinDist.mem_support_pure] at hnext
        subst next
        rfl

/-- The original players' coordinates of a legal runtime submission are a
legal atomic submission at the same base state. -/
theorem serializedPlayers_legal (program : Program Player L)
    {state : program.serializedSystem.State}
    (command : {joint // program.serializedExecution.Legal state joint}) :
    program.execution.Legal state.base (fun who => command.1 (.player who)) := by
  refine ⟨command.2.1, ?_⟩
  intro who
  have hlocal := command.2.2 (.player who)
  dsimp only
  cases hchoice : command.1 (.player who) with
  | none =>
      rw [hchoice] at hlocal
      exact hlocal
  | some action =>
      rw [hchoice] at hlocal
      exact hlocal

/-- Expand one complete runtime round from an existing source history. At an
internal checkpoint the round only performs closure; at a strategic checkpoint
it first performs the atomic joint submission and then closure. -/
def expandRound (program : Program Player L)
    (history : program.execution.History)
    (joint : ∀ who, Option (FrontierAction program.graph who))
    (hlegal : program.execution.Legal history.state joint) :
    FinDist program.execution.History :=
  if _hinternal : (readyInternalNodes program.graph history.state.1).Nonempty then
    program.settleHistory program.graph.nodeCount history
  else
    (program.execution.step history.state ⟨joint, hlegal⟩).bindOnSupport
      fun _ realized => program.settleHistory program.graph.nodeCount
        (history.extend hlegal realized)

/-- The exact endpoint law of an expanded round is the atomic frontier
followed by internal closure, including at an internal-only starting state. -/
theorem expandRound_map_state (program : Program Player L)
    (history : program.execution.History)
    (joint : ∀ who, Option (FrontierAction program.graph who))
    (hlegal : program.execution.Legal history.state joint) :
    (program.expandRound history joint hlegal).map ExecutionProtocol.History.state =
      program.serializedSystem.settle
        (applyFrontier program.graph program.graphWF history.state joint) := by
  classical
  unfold expandRound
  split
  next hinternal =>
    rw [settleHistory_map_state]
    have hjoint : joint = fun _ => none := by
      funext who
      have hlocal := hlegal.2 who
      cases hchoice : joint who with
      | none => rfl
      | some action =>
          rw [hchoice] at hlocal
          exact False.elim
            ((Finset.not_nonempty_iff_eq_empty.mpr hlocal.1.2.1) hinternal)
    subst joint
    have hempty : applyFrontier program.graph program.graphWF
        history.state (fun _ => none) = history.state := by
      apply Subtype.ext
      rw [applyFrontier_val_of_available program.graph program.graphWF
        history.state (fun _ => none) (by intros; contradiction)]
      have hwrites : EventGraph.playerWrites
          (G := program.graph) (fun _ => none) = fun _ => [] := by
        funext who
        rfl
      unfold EventGraph.roundWrites
      rw [hwrites]
      have hflat : (Finset.univ.toList : List Player).flatMap
          (fun _ => ([] : List (Fin program.graph.nodeCount × TypedValue L))) = [] := by
        induction (Finset.univ.toList : List Player) with
        | nil => rfl
        | cons who rest ih => simpa only [List.flatMap_cons, List.nil_append] using ih
      rw [hflat]
      rfl
    rw [hempty]
    rfl
  next hinternal =>
    rw [FinDist.map_bindOnSupport]
    simp_rw [program.settleHistory_map_state]
    simp only [ExecutionProtocol.History.extend_state]
    rw [FinDist.bindOnSupport_eq_bind]
    change ((toExecutionProtocol program.graph program.graphWF program.guardLive).step
      history.state ⟨joint, hlegal⟩).bind
        (EventGraph.settleInternal program.graphWF program.graph.nodeCount) = _
    rw [EventGraph.toExecutionProtocol_step_eq_pure_applyFrontier
      program.graph program.graphWF program.guardLive history.state
      ⟨joint, hlegal⟩ (Finset.not_nonempty_iff_eq_empty.mp hinternal),
      FinDist.pure_bind]
    rfl

/-- Expanding a round remembers precisely the player's submitted frontier,
and no decisions for its automatic internal steps. -/
theorem expandRound_own (program : Program Player L)
    (history : program.execution.History)
    (joint : ∀ who, Option (FrontierAction program.graph who))
    (hlegal : program.execution.Legal history.state joint) (who : Player)
    {next : program.execution.History}
    (hnext : next ∈ (program.expandRound history joint hlegal).support) :
    (program.information.infoOf who next.trace).own =
      match joint who with
      | none => (program.information.infoOf who history.trace).own
      | some action =>
          ((program.information.infoOf who history.trace).current, action) ::
            (program.information.infoOf who history.trace).own := by
  unfold expandRound at hnext
  split at hnext
  next hinternal =>
    rw [program.settleHistory_own _ _ who hnext]
    have hlocal := hlegal.2 who
    cases hchoice : joint who with
    | none => rfl
    | some action =>
        rw [hchoice] at hlocal
        exact False.elim
          ((Finset.not_nonempty_iff_eq_empty.mpr hlocal.1.2.1) hinternal)
  next _ =>
    rw [FinDist.support_bindOnSupport] at hnext
    obtain ⟨state, hstate, hnext⟩ := Set.mem_iUnion₂.mp hnext
    rw [program.settleHistory_own _ _ who hnext]
    change ((toInfoSignals program.graph program.graphWF program.guardLive).infoOf
      who (.extend history.trace joint hlegal hstate)).own = _
    rw [InfoSignals.infoOf_extend]
    cases joint who <;> rfl

/-- The expansion uses exactly the actual runtime transition law, after
discarding the runtime order log. The scheduler order is arbitrary and legal. -/
theorem expandRound_map_state_eq_serialized_step (program : Program Player L)
    (history : program.execution.History) (log : List (List Player))
    (command : {joint // program.serializedExecution.Legal
      ⟨history.state, log⟩ joint}) :
    (program.expandRound history (fun who => command.1 (.player who))
        (program.serializedPlayers_legal command)).map ExecutionProtocol.History.state =
      (program.serializedExecution.step ⟨history.state, log⟩ command).map
        ScheduledSystem.State.base := by
  rw [program.expandRound_map_state]
  change _ = (program.serializedSystem.toExecutionProtocol.step
    ⟨history.state, log⟩ command).map ScheduledSystem.State.base
  rw [program.serializedSystem.step_map_base]
  let players := fun who => command.1 (.player who)
  let order := program.serializedSystem.scheduledOrder command.1
  have hplayers : program.execution.Legal history.state players :=
    program.serializedPlayers_legal command
  have horder : order ∈ program.serializedSystem.schedules
      (publicObserve program.graph history.state.1) :=
    program.serializedSystem.scheduledOrder_mem_schedules command
  have hresolve := EventGraph.serializedSystem_resolveOrder_eq_settle_atomicFrontier
    program.graph program.graphWF program.guardLive history.state players hplayers horder
  have hcongr := program.serializedSystem.resolveOrder_congr
    (left := command.1)
    (right := program.serializedSystem.withSchedule order players)
    (fun _ => rfl) order history.state
  exact (hcongr.trans hresolve).symm

/-- Erasure commutes with one published runtime observation and the player's
own decision. Extra public order memory is discarded at every snapshot. -/
theorem eraseSerializedPlayerInformation_push (program : Program Player L)
    (who : Player) (info : program.serializedSystem.RevealingInfo (.player who))
    (choice : Option (FrontierAction program.graph who))
    (current : LocalSnapshot program.graph who) (order : List Player) :
    program.eraseSerializedPlayerInformation who
        (ScheduledSystem.RevealingInfo.push program.serializedSystem
          info choice current order) =
      (program.eraseSerializedPlayerInformation who info).push choice current := by
  cases choice <;> rfl

/-- Every realized runtime round extends a matching source history. All players'
erased information states match, including their earlier decisions. -/
theorem exists_sourceHistory_of_serialized_step (program : Program Player L)
    (history : program.execution.History)
    {state : program.serializedExecution.State}
    (trace : program.serializedExecution.Trace state)
    (hbase : history.state = state.base)
    (hinfo : ∀ who, program.information.infoOf who history.trace =
      program.eraseSerializedPlayerInformation who
        (program.serializedInformation.infoOf (.player who) trace))
    (command : {joint // program.serializedExecution.Legal state joint})
    {next : program.serializedExecution.State}
    (hnext : next ∈ (program.serializedExecution.step state command).support) :
    ∃ expanded : program.execution.History,
      expanded.state = next.base ∧
      ∀ who, program.information.infoOf who expanded.trace =
        program.eraseSerializedPlayerInformation who
          (program.serializedInformation.infoOf (.player who)
            (.extend trace command.1 command.2 hnext)) := by
  rcases history with ⟨base, sourceTrace⟩
  rcases state with ⟨runtimeBase, log⟩
  dsimp only at hbase
  subst runtimeBase
  let history : program.execution.History := ⟨base, sourceTrace⟩
  have hmap := program.expandRound_map_state_eq_serialized_step history log command
  have hbaseSupport : next.base ∈
      ((program.serializedExecution.step ⟨base, log⟩ command).map
        ScheduledSystem.State.base).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  rw [← hmap, FinDist.support_map] at hbaseSupport
  obtain ⟨expanded, hexpanded, hstate⟩ := hbaseSupport
  refine ⟨expanded, hstate, ?_⟩
  intro who
  have hown := program.expandRound_own history
    (fun who => command.1 (.player who))
    (program.serializedPlayers_legal command) who hexpanded
  have hcurrent := EventGraph.infoOf_toInfoSignals_current
    program.graph program.graphWF program.guardLive who expanded.trace
  have hprior := hinfo who
  change program.information.infoOf who expanded.trace =
    program.eraseSerializedPlayerInformation who
      (ScheduledSystem.RevealingInfo.push program.serializedSystem
        (program.serializedInformation.infoOf (.player who) trace)
        (command.1 (.player who))
        (publicObserve program.graph next.base.1,
          observe program.graph next.base.1 who) (next.log.headD []))
  rw [program.eraseSerializedPlayerInformation_push]
  have hcur : (program.information.infoOf who expanded.trace).current =
      (publicObserve program.graph next.base.1,
        observe program.graph next.base.1 who) := by
    rw [← hstate]
    exact hcurrent
  cases hchoice : command.1 (.player who) with
  | none =>
      rw [hchoice] at hown
      rw [hprior] at hown
      exact PlayerInformation.ext hcur hown
  | some action =>
      rw [hchoice] at hown
      rw [hprior] at hown
      exact PlayerInformation.ext hcur hown

/-- Every serialized trace has an atomic source history with the same
graph endpoint and exactly the erased information of every original player.
The theorem quantifies over all legal runtime traces, including all scheduler
choices and all player deviations. -/
theorem serializedTrace_has_sourceHistory (program : Program Player L)
    {state : program.serializedExecution.State}
    (trace : program.serializedExecution.Trace state) :
    ∃ source : program.execution.History,
      source.state = state.base ∧
      ∀ who, program.information.infoOf who source.trace =
        program.eraseSerializedPlayerInformation who
          (program.serializedInformation.infoOf (.player who) trace) := by
  induction trace with
  | start => exact ⟨program.execution.initHistory, rfl, fun _ => rfl⟩
  | extend prior joint legal realized ih =>
      obtain ⟨history, hbase, hinfo⟩ := ih
      exact program.exists_sourceHistory_of_serialized_step
        history prior hbase hinfo ⟨joint, legal⟩ realized

/-- Player utility agrees on matching atomic and serialized endpoints. -/
theorem utility_eq_serializedUtility_of_state_eq (program : Program Player L)
    (source : program.execution.History) (target : program.serializedExecution.History)
    (hstate : source.state = target.state.base)
    (schedulerUtility : program.serializedExecution.History → ℝ) (who : Player) :
    program.utility source who =
      program.serializedUtility schedulerUtility target (.player who) := by
  change program.payoutUtility source.state who =
    program.payoutUtility target.state.base who
  rw [hstate]

/-- Every actual runtime history has a source counterpart preserving both
player information and utility. This includes nonterminal histories and all
legal adversarial choices; no equilibrium restriction is used. -/
theorem serializedHistory_has_source (program : Program Player L)
    (target : program.serializedExecution.History)
    (schedulerUtility : program.serializedExecution.History → ℝ) :
    ∃ source : program.execution.History,
      source.state = target.state.base ∧
      (∀ who, program.information.infoOf who source.trace =
        program.eraseSerializedPlayerInformation who
          (program.serializedInformation.infoOf (.player who) target.trace)) ∧
      ∀ who, program.utility source who =
        program.serializedUtility schedulerUtility target (.player who) := by
  obtain ⟨source, hstate, hinfo⟩ := program.serializedTrace_has_sourceHistory target.trace
  exact ⟨source, hstate, hinfo,
    program.utility_eq_serializedUtility_of_state_eq
      source target hstate schedulerUtility⟩

/-- The complete source information after an expanded round is the prior
information updated by its one strategic submission and final observation. -/
theorem expandRound_information (program : Program Player L)
    (history : program.execution.History)
    (joint : ∀ who, Option (FrontierAction program.graph who))
    (hlegal : program.execution.Legal history.state joint) (who : Player)
    {next : program.execution.History}
    (hnext : next ∈ (program.expandRound history joint hlegal).support) :
    program.information.infoOf who next.trace =
      (program.information.infoOf who history.trace).push (joint who)
        (publicObserve program.graph next.state.1,
          observe program.graph next.state.1 who) := by
  apply PlayerInformation.ext
  · exact EventGraph.infoOf_toInfoSignals_current
      program.graph program.graphWF program.guardLive who next.trace
  · have hown := program.expandRound_own history joint hlegal who hnext
    cases hchoice : joint who <;> rw [hchoice] at hown <;> exact hown

/-- The source state and the information used by every original player to
choose its next action. -/
def historySummary (program : Program Player L) (history : program.execution.History) :
    program.State × ((who : Player) → PlayerInformation program.graph who) :=
  (history.state, fun who => program.information.infoOf who history.trace)

/-- Erase runtime ordering from a history while keeping the underlying state
and every original player's source information. -/
def serializedHistorySummary (program : Program Player L)
    (history : program.serializedExecution.History) :
    program.State × ((who : Player) → PlayerInformation program.graph who) :=
  (history.state.base, fun who => program.eraseSerializedPlayerInformation who
    (program.serializedInformation.infoOf (.player who) history.trace))

/-- Exact one-round law on both underlying state and all original players'
information. This is the history simulation needed for strategy compilation;
it records which information each policy will receive, not only payoffs. -/
theorem expandRound_map_summary (program : Program Player L)
    (source : program.execution.History) (log : List (List Player))
    (trace : program.serializedExecution.Trace ⟨source.state, log⟩)
    (hinfo : ∀ who, program.information.infoOf who source.trace =
      program.eraseSerializedPlayerInformation who
        (program.serializedInformation.infoOf (.player who) trace))
    (command : {joint // program.serializedExecution.Legal
      ⟨source.state, log⟩ joint}) :
    (program.expandRound source (fun who => command.1 (.player who))
        (program.serializedPlayers_legal command)).map program.historySummary =
      ((program.serializedExecution.step ⟨source.state, log⟩ command).bindOnSupport
        fun _ realized => FinDist.pure
          ((⟨⟨source.state, log⟩, trace⟩ : program.serializedExecution.History).extend
            command.2 realized)).map program.serializedHistorySummary := by
  let update := fun state : program.State =>
    (state, fun who => (program.information.infoOf who source.trace).push
      (command.1 (.player who))
      (publicObserve program.graph state.1, observe program.graph state.1 who))
  have hsource :
      (program.expandRound source (fun who => command.1 (.player who))
        (program.serializedPlayers_legal command)).map program.historySummary =
      ((program.expandRound source (fun who => command.1 (.player who))
        (program.serializedPlayers_legal command)).map ExecutionProtocol.History.state).map
          update := by
    rw [FinDist.map_comp]
    apply FinDist.map_congr_of_eq_on_support
    intro next hnext
    apply Prod.ext
    · rfl
    · funext who
      exact program.expandRound_information source _ _ who hnext
  rw [hsource, program.expandRound_map_state_eq_serialized_step,
    FinDist.map_comp, FinDist.map_bindOnSupport]
  symm
  rw [FinDist.map_eq_bind]
  apply FinDist.bindOnSupport_eq_bind_of_eq_on_support
  intro next realized
  rw [FinDist.map_pure]
  apply congrArg FinDist.pure
  apply Prod.ext
  · rfl
  funext who
  change program.eraseSerializedPlayerInformation who
      (ScheduledSystem.RevealingInfo.push program.serializedSystem
        (program.serializedInformation.infoOf (.player who) trace)
        (command.1 (.player who))
        (publicObserve program.graph next.base.1, observe program.graph next.base.1 who)
        (next.log.headD [])) = _
  rw [program.eraseSerializedPlayerInformation_push, ← hinfo who]
  rfl

/-- One actual behavioral runtime round, including arbitrary randomized
player and scheduler policies, has exactly the law of its source-history
expansion. The joint submission is drawn using the *runtime* information
model. This does not assert that its distribution is induced by a source
behavioral profile: that is the separate strategy back-translation problem. -/
theorem serializedBehavioralRound_expands (program : Program Player L)
    (source : program.execution.History) (log : List (List Player))
    (trace : program.serializedExecution.Trace ⟨source.state, log⟩)
    (hinfo : ∀ who, program.information.infoOf who source.trace =
      program.eraseSerializedPlayerInformation who
        (program.serializedInformation.infoOf (.player who) trace))
    (policies : (who : Participant Player) →
      program.serializedInformation.BehavioralPolicy who)
    (hterm : ¬ program.serializedExecution.terminal ⟨source.state, log⟩) :
    (program.serializedInformation.runBehavioralFrom policies 1
        ⟨⟨source.state, log⟩, trace⟩).map program.serializedHistorySummary =
      ((program.serializedInformation.behavioralJoint policies trace hterm).bind
        fun command => program.expandRound source
          (fun who => command.1 (.player who))
          (program.serializedPlayers_legal command)).map program.historySummary := by
  rw [InformationModel.runBehavioralFrom_succ_of_not_terminal _ _ _ hterm,
    FinDist.map_bind, FinDist.map_bind]
  apply FinDist.bind_congr
  intro command _
  exact (program.expandRound_map_summary source log trace hinfo command).symm

end Vegas.Machine.Program
