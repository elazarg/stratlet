/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Scheduled.History

/-!
# The data-independent graph execution skeleton

Readiness depends only on completed nodes. Legal strategic frontiers complete
every ready commitment, and automatic closure uses the canonical internal
selection. Consequently the completed-node sequence does not depend on values,
player policies, chance outcomes, or the scheduler's accepted order.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- A configuration used only to compute structural readiness. Its store is
irrelevant to readiness and is not passed to a player or to execution. -/
def skeletonConfig (G : Graph Player L) (done : Finset (Fin G.nodeCount)) : Config G :=
  ⟨done, G.initialStore⟩

theorem readyInternalNodes_eq_of_done_eq {G : Graph Player L}
    {left right : Config G} (hdone : left.done = right.done) :
    readyInternalNodes G left = readyInternalNodes G right := by
  ext node
  simp only [readyInternalNodes, Finset.mem_filter, Finset.mem_univ, true_and,
    ReadyInternalNode, Ready, hdone]

theorem readyCommitNodes_eq_of_done_eq {G : Graph Player L}
    {left right : Config G} (hdone : left.done = right.done) (who : Player) :
    readyCommitNodes G left who = readyCommitNodes G right who := by
  ext node
  simp only [readyCommitNodes, Finset.mem_filter, Finset.mem_univ, true_and,
    ReadyCommitNode, Ready, hdone]

/-- Compute the completed nodes after canonical automatic closure, without
examining any stored value. -/
def settleDone (G : Graph Player L) : Nat → Finset (Fin G.nodeCount) → Finset (Fin G.nodeCount)
  | 0, done => done
  | fuel + 1, done =>
      if hready : (readyInternalNodes G (skeletonConfig G done)).Nonempty then
        settleDone G fuel (insert (Classical.choose hready) done)
      else done

theorem stepReadyInternal_done {G : Graph Player L} (hwf : G.WF)
    (state : ReachableConfig G)
    (hinternal : (readyInternalNodes G state.1).Nonempty)
    {next : ReachableConfig G}
    (hnext : next ∈ (Compiled.stepReadyInternal hwf state hinternal).support) :
    next.1.done = insert (Classical.choose hinternal) state.1.done := by
  have hraw : next.1 ∈
      ((Compiled.stepReadyInternal hwf state hinternal).map Subtype.val).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  unfold Compiled.stepReadyInternal at hraw
  simp only [map_val_stepAvailable] at hraw
  obtain ⟨written, hwritten⟩ := stepAvailableEvent_support_completeNode _ hraw
  rw [hwritten]
  rfl

theorem settleInternal_done {G : Graph Player L} (hwf : G.WF)
    (fuel : Nat) (state : ReachableConfig G) {next : ReachableConfig G}
    (hnext : next ∈ (Compiled.settleInternal hwf fuel state).support) :
    next.1.done = settleDone G fuel state.1.done := by
  induction fuel generalizing state with
  | zero =>
      rw [Compiled.settleInternal_zero, FinDist.mem_support_pure] at hnext
      subst next
      rfl
  | succ fuel ih =>
      have hready : readyInternalNodes G state.1 =
          readyInternalNodes G (skeletonConfig G state.1.done) :=
        readyInternalNodes_eq_of_done_eq rfl
      unfold Compiled.settleInternal at hnext
      split at hnext
      next hinternal =>
        rw [FinDist.support_bind] at hnext
        obtain ⟨middle, hmiddle, hnext⟩ := Set.mem_iUnion₂.mp hnext
        rw [ih _ hnext, stepReadyInternal_done hwf state hinternal hmiddle]
        have hcanonical : (readyInternalNodes G (skeletonConfig G state.1.done)).Nonempty :=
          hready ▸ hinternal
        have hchoose : Classical.choose hinternal = Classical.choose hcanonical := by
          congr 1
        rw [settleDone, dif_pos hcanonical, hchoose]
      next hinternal =>
        rw [FinDist.mem_support_pure] at hnext
        subst next
        rw [settleDone, dif_neg (by simpa only [← hready] using hinternal)]

variable [Fintype Player]

/-- Complete every ready commitment, unless internal work has priority. -/
def frontierDone (G : Graph Player L) (done : Finset (Fin G.nodeCount)) :
    Finset (Fin G.nodeCount) :=
  if (readyInternalNodes G (skeletonConfig G done)).Nonempty then done
  else done ∪ Finset.univ.filter (fun node =>
    ∃ who, ReadyCommitNode G (skeletonConfig G done) who node)

theorem applyFrontier_done_of_legal (G : Graph Player L) (hwf : G.WF)
    (hguards : GuardLive G) (state : ReachableConfig G)
    (joint : ∀ who, Option (FrontierAction G who))
    (hlegal : (toExecutionProtocol G hwf hguards).Legal state joint) :
    (applyFrontier G hwf state joint).1.done = frontierDone G state.1.done := by
  classical
  have havailable : ∀ who action, joint who = some action →
      FrontierAction.Available G state.1 who action := by
    intro who action haction
    have hlocal := hlegal.2 who
    rw [haction] at hlocal
    exact hlocal.2
  rw [applyFrontier_val_of_available G hwf state joint havailable,
    Config.completeNodes_done]
  have hinternalEq : readyInternalNodes G state.1 =
      readyInternalNodes G (skeletonConfig G state.1.done) :=
    readyInternalNodes_eq_of_done_eq rfl
  unfold frontierDone
  split
  next hinternal =>
    have hjoint : joint = fun _ => none := by
      funext who
      cases hchoice : joint who with
      | none => rfl
      | some action =>
          have hlocal := hlegal.2 who
          rw [hchoice] at hlocal
          have hempty := hlocal.1.2.1
          exact False.elim ((Finset.not_nonempty_iff_eq_empty.mpr hempty)
            (hinternalEq.symm ▸ hinternal))
    rw [hjoint]
    have hwrites : playerWrites (G := G) (fun _ => none) = fun _ => [] := by
      funext who
      rfl
    unfold roundWrites
    rw [hwrites]
    have hempty : (Finset.univ.toList : List Player).flatMap
        (fun _ => ([] : List (Fin G.nodeCount × TypedValue L))) = [] := by
      induction (Finset.univ.toList : List Player) with
      | nil => rfl
      | cons who rest ih => simpa only [List.flatMap_cons, List.nil_append] using ih
    rw [hempty]
    simp
  next hinternal =>
    congr 1
    ext node
    rw [List.mem_toFinset, List.mem_map, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    constructor
    · rintro ⟨written, hwritten, hnode⟩
      obtain ⟨who, _, hwho⟩ := (mem_roundWrites_iff joint _ written).mp hwritten
      obtain ⟨action, haction, hwrite⟩ := (mem_playerWrites_iff joint who written).mp hwho
      have hready := readyCommitNode_of_mem_actionWrites (havailable who action haction) hwrite
      rw [hnode] at hready
      exact ⟨who, hready⟩
    · rintro ⟨who, hready⟩
      have hready' : ReadyCommitNode G state.1 who node := hready
      have hactive : (toExecutionProtocol G hwf hguards).active state who := by
        refine ⟨hlegal.1, ?_, ?_⟩
        · exact Finset.not_nonempty_iff_eq_empty.mp (hinternalEq ▸ hinternal)
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ who,
            node, Finset.mem_filter.mpr ⟨Finset.mem_univ node, hready'⟩⟩
      cases haction : joint who with
      | none =>
          have hlocal := hlegal.2 who
          rw [haction] at hlocal
          exact False.elim (hlocal hactive)
      | some action =>
          obtain ⟨value, hvalue⟩ :=
            (havailable who action haction).value?_isSome_iff_readyCommitNode.mpr hready'
          refine ⟨(node, G.nodeTypedValue node value), ?_, rfl⟩
          exact (mem_roundWrites_iff joint _ _).mpr ⟨who, by simp,
            (mem_playerWrites_iff joint who _).mpr ⟨action, haction,
              (mem_actionWrites_iff action _).mpr ⟨value, hvalue, rfl⟩⟩⟩

/-- The completed-node set after one serialized round. -/
def serializedDoneStep (G : Graph Player L) (done : Finset (Fin G.nodeCount)) :
    Finset (Fin G.nodeCount) :=
  settleDone G G.nodeCount (frontierDone G done)

/-- The public structural checkpoint after a given number of runtime rounds. -/
def serializedDoneAt (G : Graph Player L) : Nat → Finset (Fin G.nodeCount)
  | 0 => ∅
  | rounds + 1 => serializedDoneStep G (serializedDoneAt G rounds)

omit [Fintype Player] in
theorem subset_settleDone (G : Graph Player L) (fuel : Nat)
    (done : Finset (Fin G.nodeCount)) : done ⊆ settleDone G fuel done := by
  induction fuel generalizing done with
  | zero => exact Finset.Subset.refl _
  | succ fuel ih =>
      unfold settleDone
      split
      · exact (Finset.subset_insert _ _).trans (ih _)
      · exact Finset.Subset.refl _

theorem subset_serializedDoneStep (G : Graph Player L)
    (done : Finset (Fin G.nodeCount)) : done ⊆ serializedDoneStep G done := by
  apply Finset.Subset.trans (s₂ := frontierDone G done)
  · unfold frontierDone
    split
    · exact Finset.Subset.refl _
    · exact Finset.subset_union_left
  · exact subset_settleDone G _ _

theorem serializedDoneAt_monotone (G : Graph Player L) : Monotone (serializedDoneAt G) :=
  monotone_nat_of_le_succ fun _ => subset_serializedDoneStep G _

end Vegas.EventGraph

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
      have hstrict := Compiled.serializedSystem_step_done_ssubset
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
