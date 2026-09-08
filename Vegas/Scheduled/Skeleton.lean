/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.Skeleton
import Vegas.Scheduled.History

noncomputable section

namespace Vegas.Machine.Program

open GameTheory.Protocol GameTheory.Math.Probability EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}

theorem serializedStep_done (program : Program Player L)
    (source : program.execution.History) (log : List (List Player))
    (command : {joint // program.serializedArena.execution.Legal ⟨source.state, log⟩ joint})
    {next : program.serializedArena.execution.State}
    (hnext : next ∈ (program.serializedArena.execution.step ⟨source.state, log⟩ command).support) :
    next.base.1.done = serializedDoneStep program.graph source.state.1.done := by
  have hbase : next.base ∈
      ((program.serializedArena.execution.step ⟨source.state, log⟩ command).map
        ScheduledSystem.State.base).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  rw [← program.expandRound_map_state_eq_serialized_step source log command,
    program.expandRound_map_state] at hbase
  have hdone := settleInternal_done program.graphWF program.graph.nodeCount _ hbase
  rw [applyFrontier_done_of_legal program.graph program.graphWF program.guardLive
    source.state _ (program.serializedPlayers_legal command)] at hdone
  exact hdone

/-- All legal serialized traces follow the same completed-node timeline,
regardless of player choices, chance outcomes, or scheduler policy. -/
theorem serializedTrace_done (program : Program Player L)
    {state : program.serializedArena.execution.State}
    (trace : program.serializedArena.execution.Trace state) :
    state.base.1.done = serializedDoneAt program.graph trace.length := by
  induction trace with
  | start => rfl
  | @extend priorState next prior joint legal realized ih =>
      obtain ⟨source, hstate, _⟩ := program.serializedTrace_has_sourceHistory prior
      rcases priorState with ⟨base, log⟩
      dsimp only at hstate
      subst base
      rw [program.serializedStep_done source log ⟨joint, legal⟩ realized]
      rw [ih]
      rfl

/-- A realized nonterminal prefix is structurally distinct from every later
checkpoint of the same execution. -/
theorem serializedTrace_done_ne_of_lt (program : Program Player L)
    {state : program.serializedArena.execution.State}
    (trace : program.serializedArena.execution.Trace state)
    (rounds : Nat) (hlt : rounds < trace.length) :
    serializedDoneAt program.graph rounds ≠ state.base.1.done := by
  cases trace with
  | start => exact False.elim (Nat.not_lt_zero _ hlt)
  | extend prior joint legal realized =>
      have hle : rounds ≤ prior.length := by
        change rounds < prior.length + 1 at hlt
        omega
      have hsubset := serializedDoneAt_monotone program.graph hle
      rw [← program.serializedTrace_done prior] at hsubset
      have hstrict := EventGraph.serializedSystem_step_done_ssubset
        program.graph program.graphWF program.guardLive _ ⟨joint, legal⟩ realized
      exact (Finset.ssubset_of_subset_of_ssubset hsubset hstrict).ne

/-- The public completed-node set determines the number of runtime rounds.
The result is independent of hidden values and the scheduler policy. -/
theorem serializedTrace_length_eq_of_done_eq (program : Program Player L)
    {left right : program.serializedArena.execution.State}
    (first : program.serializedArena.execution.Trace left)
    (second : program.serializedArena.execution.Trace right)
    (hdone : left.base.1.done = right.base.1.done) : first.length = second.length := by
  apply Nat.le_antisymm
  · by_contra hle
    have hne := program.serializedTrace_done_ne_of_lt first second.length (by omega)
    exact hne ((program.serializedTrace_done second).symm.trans hdone.symm)
  · by_contra hle
    have hne := program.serializedTrace_done_ne_of_lt second first.length (by omega)
    exact hne ((program.serializedTrace_done first).symm.trans hdone)

end Vegas.Machine.Program
