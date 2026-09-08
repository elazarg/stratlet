/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.Information
import Vegas.Scheduled.Skeleton
import Vegas.Scheduled.Replay

/-! # Compact scheduled information -/

noncomputable section

namespace Vegas.Machine.Program

open GameTheory.Protocol GameTheory.Math.Probability EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}

theorem serializedStep_settle_support (program : Program Player L)
    (source : program.execution.History) (log : List (List Player))
    (command : {joint // program.serializedExecution.Legal ⟨source.state, log⟩ joint})
    {next : program.serializedExecution.State}
    (hnext : next ∈ (program.serializedExecution.step ⟨source.state, log⟩ command).support) :
    next.base ∈ (EventGraph.settleInternal program.graphWF program.graph.nodeCount
      (applyFrontier program.graph program.graphWF source.state
        (fun who => command.1 (.player who)))).support := by
  have hbase : next.base ∈
      ((program.serializedExecution.step ⟨source.state, log⟩ command).map
        ScheduledSystem.State.base).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  rw [← program.expandRound_map_state_eq_serialized_step source log command,
    program.expandRound_map_state] at hbase
  exact hbase

theorem serializedStep_extends (program : Program Player L)
    {state : program.serializedExecution.State}
    (trace : program.serializedExecution.Trace state)
    (command : {joint // program.serializedExecution.Legal state joint})
    {next : program.serializedExecution.State}
    (hnext : next ∈ (program.serializedExecution.step state command).support) :
    state.base.1.Extends next.base.1 := by
  obtain ⟨source, hstate, _⟩ := program.serializedTrace_has_sourceHistory trace
  rcases state with ⟨base, log⟩
  dsimp only at hstate
  subst base
  exact (extends_applyFrontier_of_legal program.graph program.graphWF program.guardLive
    source.state _ (program.serializedPlayers_legal command)).trans
      (extends_of_settleInternal program.graphWF program.graph.nodeCount _
        (program.serializedStep_settle_support source log command hnext))

theorem serializedStep_readyCommit_of_none (program : Program Player L)
    {state : program.serializedExecution.State}
    (trace : program.serializedExecution.Trace state)
    (command : {joint // program.serializedExecution.Legal state joint})
    {next : program.serializedExecution.State}
    (hnext : next ∈ (program.serializedExecution.step state command).support)
    (who : Player) (hnone : command.1 (.player who) = none)
    {node : Fin program.graph.nodeCount}
    (hready : ReadyCommitNode program.graph state.base.1 who node) :
    ReadyCommitNode program.graph next.base.1 who node := by
  obtain ⟨source, hstate, _⟩ := program.serializedTrace_has_sourceHistory trace
  rcases state with ⟨base, log⟩
  dsimp only at hstate
  subst base
  exact (hready.after_applyFrontier_of_none program.graphWF program.guardLive _
    (program.serializedPlayers_legal command) hnone).after_settleInternal
      program.graphWF program.graph.nodeCount
      (program.serializedStep_settle_support source log command hnext)

/-- Matching compact information after a round determines both the preceding
compact information and the player's submission. No hidden state is inspected
by a reconstructed policy; this is a relation between legal histories. -/
theorem serializedStep_compact_injective (program : Program Player L) (who : Player)
    {left right nextLeft nextRight : program.serializedExecution.State}
    (first : program.serializedExecution.Trace left)
    (second : program.serializedExecution.Trace right)
    (leftCommand : {joint // program.serializedExecution.Legal left joint})
    (rightCommand : {joint // program.serializedExecution.Legal right joint})
    (leftRealized : nextLeft ∈
      (program.serializedExecution.step left leftCommand).support)
    (rightRealized : nextRight ∈
      (program.serializedExecution.step right rightCommand).support)
    (hdone : left.base.1.done = right.base.1.done)
    (hcompact : program.eraseSerializedPlayerInformation who
        (program.serializedInformation.infoOf (.player who)
          (.extend first leftCommand.1 leftCommand.2 leftRealized)) =
      program.eraseSerializedPlayerInformation who
        (program.serializedInformation.infoOf (.player who)
          (.extend second rightCommand.1 rightCommand.2 rightRealized))) :
    program.eraseSerializedPlayerInformation who
        (program.serializedInformation.infoOf (.player who) first) =
      program.eraseSerializedPlayerInformation who
        (program.serializedInformation.infoOf (.player who) second) ∧
      leftCommand.1 (.player who) = rightCommand.1 (.player who) := by
  change program.eraseSerializedPlayerInformation who
      (ScheduledSystem.RevealingInfo.push program.serializedSystem
        (program.serializedInformation.infoOf (.player who) first)
        (leftCommand.1 (.player who)) _ _) =
    program.eraseSerializedPlayerInformation who
      (ScheduledSystem.RevealingInfo.push program.serializedSystem
        (program.serializedInformation.infoOf (.player who) second)
        (rightCommand.1 (.player who)) _ _) at hcompact
  rw [program.eraseSerializedPlayerInformation_push,
    program.eraseSerializedPlayerInformation_push] at hcompact
  have hactive : program.serializedSystem.active left.base who ↔
      program.serializedSystem.active right.base who :=
    EventGraph.activeAt_iff_of_done_eq hdone
  have hlocalLeft := leftCommand.2.2 (.player who)
  have hlocalRight := rightCommand.2.2 (.player who)
  have hown := congrArg PlayerInformation.own hcompact
  have hcurrent := congrArg PlayerInformation.current hcompact
  change (publicObserve program.graph nextLeft.base.1, observe program.graph nextLeft.base.1 who) =
    (publicObserve program.graph nextRight.base.1, observe program.graph nextRight.base.1 who)
      at hcurrent
  cases hleft : leftCommand.1 (.player who) <;>
    cases hright : rightCommand.1 (.player who)
  · simp only [PlayerInformation.push, hleft, hright] at hown
    refine ⟨PlayerInformation.ext ?_ hown, rfl⟩
    have hExtLeft := program.serializedStep_extends first leftCommand leftRealized
    have hExtRight := program.serializedStep_extends second rightCommand rightRealized
    have hpublic := publicObserve_eq_of_extensions hExtLeft hExtRight hdone
      (congrArg Prod.fst hcurrent)
    have hprivate := observe_eq_of_extensions program.graphWF who hExtLeft hExtRight hdone
      (fun node hready =>
        (program.serializedStep_readyCommit_of_none first leftCommand leftRealized who
          hleft hready).ready.1)
      (fun node hready =>
        (program.serializedStep_readyCommit_of_none second rightCommand rightRealized who
          hright hready).ready.1)
      (congrArg Prod.snd hcurrent)
    change (program.serializedSystem.revealingSignals.infoOf (.player who) first).current =
      (program.serializedSystem.revealingSignals.infoOf (.player who) second).current
    rw [program.serializedSystem.revealing_infoOf_current,
      program.serializedSystem.revealing_infoOf_current]
    exact Prod.ext hpublic hprivate
  · rw [hleft] at hlocalLeft
    rw [hright] at hlocalRight
    exact False.elim (hlocalLeft (hactive.mpr hlocalRight.1))
  · rw [hleft] at hlocalLeft
    rw [hright] at hlocalRight
    exact False.elim (hlocalRight (hactive.mp hlocalLeft.1))
  · simp only [PlayerInformation.push, hleft, hright] at hown
    have hpairs := List.cons.inj hown
    refine ⟨PlayerInformation.ext (congrArg Prod.fst hpairs.1) hpairs.2, ?_⟩
    exact congrArg some (congrArg Prod.snd hpairs.1)

/-- The canonical source's compact player information loses no order-free
runtime information. In particular, every passive observation is recoverable
from the current immutable snapshot and remembered own decisions. -/
theorem serializedBlindInfo_eq_of_compact_eq (program : Program Player L) (who : Player)
    {left right : program.serializedExecution.State}
    (first : program.serializedExecution.Trace left)
    (second : program.serializedExecution.Trace right)
    (hcompact : program.eraseSerializedPlayerInformation who
        (program.serializedInformation.infoOf (.player who) first) =
      program.eraseSerializedPlayerInformation who
        (program.serializedInformation.infoOf (.player who) second)) :
    program.serializedSystem.blindSignals.infoOf (.player who) first =
      program.serializedSystem.blindSignals.infoOf (.player who) second := by
  have hdone : left.base.1.done = right.base.1.done := by
    have hcurrent := congrArg (fun info : PlayerInformation program.graph who =>
      info.current.1.done) hcompact
    change (program.serializedSystem.revealingSignals.infoOf (.player who) first).current.1.done =
      (program.serializedSystem.revealingSignals.infoOf (.player who) second).current.1.done
        at hcurrent
    rw [program.serializedSystem.revealing_infoOf_current,
      program.serializedSystem.revealing_infoOf_current] at hcurrent
    exact hcurrent
  have hlength := program.serializedTrace_length_eq_of_done_eq first second hdone
  induction first generalizing right with
  | start =>
      cases second with
      | start => rfl
      | extend _ _ _ _ => simp only [ExecutionProtocol.Trace.length] at hlength; omega
  | @extend left nextLeft first leftJoint leftLegal leftRealized ih =>
      cases second with
      | start => simp only [ExecutionProtocol.Trace.length] at hlength; omega
      | @extend right nextRight second rightJoint rightLegal rightRealized =>
          have hpriorLength : first.length = second.length := by
            simpa only [ExecutionProtocol.Trace.length, Nat.add_right_cancel_iff] using hlength
          have hpriorDone : left.base.1.done = right.base.1.done := by
            rw [program.serializedTrace_done first,
              program.serializedTrace_done second, hpriorLength]
          obtain ⟨hpriorCompact, hchoice⟩ :=
            program.serializedStep_compact_injective who first second
              ⟨leftJoint, leftLegal⟩ ⟨rightJoint, rightLegal⟩
              leftRealized rightRealized hpriorDone hcompact
          have hprior := ih second hpriorCompact hpriorDone hpriorLength
          have hcurrent := congrArg PlayerInformation.current hcompact
          rw [InfoSignals.infoOf_extend, InfoSignals.infoOf_extend]
          change ScheduledSystem.BlindInfo.push program.serializedSystem
            (program.serializedSystem.blindSignals.infoOf (.player who) first)
            (leftJoint (.player who)) _ =
              ScheduledSystem.BlindInfo.push program.serializedSystem
                (program.serializedSystem.blindSignals.infoOf (.player who) second)
                (rightJoint (.player who)) _
          congr 1

end Vegas.Machine.Program
