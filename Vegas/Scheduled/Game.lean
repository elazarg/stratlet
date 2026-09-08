/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Game.Basic
import Vegas.Scheduled.Compiled

/-!
# Games implemented by the serialized graph runtime

This file relates `Machine.Program.boundedGame` to the
actual scheduled execution protocol. The target game uses the serializer's
states, public order log, player-local menus, and transition law directly.

The scheduler remains an execution coordinate. Its utility is supplied only so
the generic `UtilityGame` carrier is well typed; player-equilibrium claims do
not quantify over scheduler deviations. Every original player's utility reads
only the settled graph configuration and is definitionally blind to the order
log.
-/

noncomputable section

namespace Vegas

open GameTheory
open GameTheory.Protocol

namespace Machine.Program

variable {Player : Type} [DecidableEq Player] [Fintype Player]
variable {L : IExpr}

/-- The permissive serialized state machine generated from a compiled machine
program. -/
@[reducible] def serializedSystem (program : Program Player L) :
    ScheduledSystem Player :=
  EventGraph.serializedSystem program.graph program.graphWF program.guardLive

/-- Native execution semantics of the serializer. -/
def serializedExecution (program : Program Player L) :
    ExecutionProtocol (Participant Player) :=
  program.serializedSystem.toExecutionProtocol

/-- Recipient-local information over native serialized execution. -/
def serializedInformation (program : Program Player L) :
    InformationModel program.serializedExecution :=
  program.serializedSystem.revealingInformation

/-- Erase runtime order observations from one original player's serialized
information while retaining the current source observation and every earlier
decision by that player. -/
def eraseSerializedPlayerInformation (program : Program Player L)
    (who : Player)
    (info : program.serializedSystem.RevealingInfo (.player who)) :
    EventGraph.PlayerInformation program.graph who where
  current := info.current
  own := info.own.map fun remembered =>
    (remembered.1.1, remembered.2)

/-- Erasure changes information, not the action menu. Both semantics totalize
unreachable observations with the idle choice, so this equality also holds at
counterfactual information values that no execution reaches. -/
theorem serializedPlayerMenu_eq (program : Program Player L) (who : Player)
    (info : program.serializedSystem.RevealingInfo (.player who)) :
    program.serializedInformation.menu (.player who) info =
      program.information.menu who
        (program.eraseSerializedPlayerInformation who info) := by
  change program.serializedSystem.menuAt who info.current =
    EventGraph.localMenu program.graph program.graphWF program.guardLive who
      { current := info.current,
        own := info.own.map fun remembered =>
          (remembered.1.1, remembered.2) }
  exact Vegas.EventGraph.serializedSystem_playerMenu_eq_localMenu
    program.graph program.graphWF program.guardLive who info.current _

/-- Source and serialized choices are equivalent at corresponding player
information. Only their menu certificates differ. -/
def serializedPlayerChoiceEquiv (program : Program Player L) (who : Player)
    (info : program.serializedSystem.RevealingInfo (.player who)) :
    program.information.Choice who
        (program.eraseSerializedPlayerInformation who info) ≃
      program.serializedInformation.Choice (.player who) info where
  toFun choice := ⟨choice.1, by
    rw [program.serializedPlayerMenu_eq who info]
    exact choice.2⟩
  invFun choice := ⟨choice.1, by
    rw [← program.serializedPlayerMenu_eq who info]
    exact choice.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Compile a source behavioral policy to the real serialized information
model. The compiled policy ignores order history; target deviations need not. -/
def compileSerializedBehavioralPolicy (program : Program Player L)
    (who : Player) (policy : program.information.BehavioralPolicy who) :
    program.serializedInformation.BehavioralPolicy (.player who) :=
  fun info =>
    (policy (program.eraseSerializedPlayerInformation who info)).map
      (program.serializedPlayerChoiceEquiv who info)

/-- The serialized information held initially by an original player. -/
def serializedInitialPlayerInformation (program : Program Player L)
    (who : Player) :
    program.serializedSystem.RevealingInfo (.player who) where
  current :=
    (EventGraph.publicObserve program.graph (EventGraph.Config.initial _),
      EventGraph.observe program.graph (EventGraph.Config.initial _) who)
  past := []
  own := []

@[simp] theorem eraseSerializedInitialPlayerInformation
    (program : Program Player L) (who : Player) :
    program.eraseSerializedPlayerInformation who
        (program.serializedInitialPlayerInformation who) =
      { current :=
          (EventGraph.publicObserve program.graph (EventGraph.Config.initial _),
            EventGraph.observe program.graph (EventGraph.Config.initial _) who),
        own := [] } := by
  rfl

@[simp] theorem serializedInfoOf_start_player
    (program : Program Player L) (who : Player) :
    program.serializedInformation.infoOf (.player who)
        (ExecutionProtocol.Trace.start :
          program.serializedExecution.Trace
            program.serializedExecution.init) =
      program.serializedInitialPlayerInformation who := by
  rfl

@[simp] theorem sourceInfoOf_start_eq_erasedSerialized
    (program : Program Player L) (who : Player) :
    program.information.infoOf who
        (ExecutionProtocol.Trace.start :
          program.execution.Trace program.execution.init) =
      program.eraseSerializedPlayerInformation who
        (program.serializedInitialPlayerInformation who) := by
  rfl

/-- At the first strategic frontier, the real serialized policy draws exactly
the compiled source choice law. The current scheduler order is selected
simultaneously and is not present in this information state. -/
theorem compileSerializedBehavioralPolicy_initial
    (program : Program Player L) (who : Player)
    (policy : program.information.BehavioralPolicy who) :
    program.compileSerializedBehavioralPolicy who policy
        (program.serializedInitialPlayerInformation who) =
      (policy (program.information.infoOf who
        (ExecutionProtocol.Trace.start :
          program.execution.Trace program.execution.init))).map
        (program.serializedPlayerChoiceEquiv who
          (program.serializedInitialPlayerInformation who)) := by
  rfl

/-- Any economic outcome interpretation of the settled source state can be
valued independently of the payout expressions. The scheduler may value the
full runtime history. Trace-sensitive original-player utilities can instead be
attached directly to `serializedInformation`; their preservation needs a separate
utility relation, not merely an outcome decoder. -/
def serializedBoundedOutcomeGame (program : Program Player L) {Outcome : Type}
    (observe : program.State → Outcome) (valuation : Outcome → Player → ℝ)
    (schedulerUtility : program.serializedExecution.History → ℝ) :
    BoundedGame (Participant Player) where
  execution := program.serializedExecution
  information := program.serializedInformation
  utility history
    | .scheduler => schedulerUtility history
    | .player who => valuation (observe history.state.base) who
  horizon := program.graph.nodeCount
  bounded := Vegas.EventGraph.serializedSystem_boundedHorizon
    program.graph program.graphWF program.guardLive

def serializedUtility (program : Program Player L)
    (schedulerUtility : program.serializedExecution.History → ℝ) :
    program.serializedExecution.History → Participant Player → ℝ :=
  (program.serializedBoundedOutcomeGame id program.payoutUtility schedulerUtility).utility

@[simp] theorem serializedUtility_player
    (program : Program Player L)
    (schedulerUtility : program.serializedExecution.History → ℝ)
    (history : program.serializedExecution.History) (who : Player) :
    program.serializedUtility schedulerUtility history (.player who) =
      program.payoutUtility history.state.base who := by
  rfl

/-- Original-player utility cannot distinguish order logs, trace witnesses, or
the scheduler's utility when the settled graph state is the same. -/
theorem serializedUtility_player_eq_of_base_eq
    (program : Program Player L)
    (schedulerUtility : program.serializedExecution.History → ℝ)
    (left right : program.serializedExecution.History) (who : Player)
    (hbase : left.state.base = right.state.base) :
    program.serializedUtility schedulerUtility left (.player who) =
      program.serializedUtility schedulerUtility right (.player who) := by
  simp only [serializedUtility_player]
  rw [hbase]

/-- The serializer is a finite Vegas game with the same graph-node horizon as
the canonical atomic game. -/
def serializedBoundedGame (program : Program Player L)
    (schedulerUtility : program.serializedExecution.History → ℝ) :
    BoundedGame (Participant Player) :=
  program.serializedBoundedOutcomeGame id program.payoutUtility schedulerUtility

/-- The actual serialized arena has perfect recall, including for policies
that condition on earlier public orders. -/
theorem serializedPerfectRecall (program : Program Player L) :
    program.serializedInformation.PerfectRecall :=
  program.serializedSystem.revealingInformation_perfectRecall

/-- At every actual runtime history, each original player's information
determines the scheduler's complete information.  The scheduler may use all
public data and prior orders, but has no additional state signal. -/
theorem serializedSchedulerInfo_eq_fromPlayer
    (program : Program Player L) (who : Player)
    {state : program.serializedExecution.State}
    (trace : ExecutionProtocol.Trace program.serializedExecution state) :
    program.serializedSystem.schedulerInfoFromPlayer
        (fun seen : EventGraph.PublicObservation program.graph ×
          EventGraph.Observation program.graph who => seen.1)
        (program.serializedSystem.revealingSignals.infoOf
          (.player who) trace) =
      program.serializedSystem.revealingSignals.infoOf
        (.scheduler : Participant Player) trace :=
  EventGraph.serializedSystem_schedulerInfo_eq_fromPlayer
    program.graph program.graphWF program.guardLive who trace

/-- The actual serialized game is bounded independently of the scheduler
strategy and of every player strategy. -/
theorem serializedBoundedHorizon (program : Program Player L)
    (schedulerUtility : program.serializedExecution.History → ℝ) :
    (program.serializedBoundedGame schedulerUtility).execution.BoundedHorizon
      program.graph.nodeCount :=
  (program.serializedBoundedGame schedulerUtility).bounded

end Machine.Program

end Vegas
