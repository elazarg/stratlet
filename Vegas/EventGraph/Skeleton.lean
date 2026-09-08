/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.Protocol
import Vegas.EventGraph.SourceOrder

/-!
# The data-independent graph execution skeleton

Readiness depends only on completed nodes. Legal strategic frontiers complete
every ready commitment, and automatic closure uses the canonical internal
selection. Consequently the completed-node sequence does not depend on values,
player policies, chance outcomes, or scheduler order.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- Execute the ready internal event selected by the canonical graph protocol. -/
noncomputable def stepReadyInternal {G : Graph Player L} (hwf : G.WF)
    (state : ReachableConfig G)
    (hinternal : (readyInternalNodes G state.1).Nonempty) :
    FinDist (ReachableConfig G) := by
  let node := Classical.choose hinternal
  have hready : ReadyInternalNode G state.1 node :=
    (Finset.mem_filter.mp (Classical.choose_spec hinternal)).2
  have havailable : InternalAvailable G state.1 { node := node } :=
    InternalAvailable.of_readyInternalNode hwf
      (reachable_storeCoherent hwf state.2) hready
  exact stepAvailable G state
    (.internal { node := node } (Classical.choice havailable))

/-- Run at most `fuel` canonically selected ready internal nodes. -/
noncomputable def settleInternal {G : Graph Player L} (hwf : G.WF) :
    Nat → ReachableConfig G → FinDist (ReachableConfig G)
  | 0, state => FinDist.pure state
  | fuel + 1, state =>
      if hinternal : (readyInternalNodes G state.1).Nonempty then
        (stepReadyInternal hwf state hinternal).bind
          (settleInternal hwf fuel)
      else
        FinDist.pure state

@[simp] theorem settleInternal_zero {G : Graph Player L} (hwf : G.WF)
    (state : ReachableConfig G) :
    settleInternal hwf 0 state = FinDist.pure state := rfl

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
    (hnext : next ∈ (EventGraph.stepReadyInternal hwf state hinternal).support) :
    next.1.done = insert (Classical.choose hinternal) state.1.done := by
  have hraw : next.1 ∈
      ((EventGraph.stepReadyInternal hwf state hinternal).map Subtype.val).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  unfold EventGraph.stepReadyInternal at hraw
  simp only [map_val_stepAvailable] at hraw
  obtain ⟨written, hwritten⟩ := stepAvailableEvent_support_completeNode _ hraw
  rw [hwritten]
  rfl

theorem settleInternal_done {G : Graph Player L} (hwf : G.WF)
    (fuel : Nat) (state : ReachableConfig G) {next : ReachableConfig G}
    (hnext : next ∈ (EventGraph.settleInternal hwf fuel state).support) :
    next.1.done = settleDone G fuel state.1.done := by
  induction fuel generalizing state with
  | zero =>
      rw [EventGraph.settleInternal_zero, FinDist.mem_support_pure] at hnext
      subst next
      rfl
  | succ fuel ih =>
      have hready : readyInternalNodes G state.1 =
          readyInternalNodes G (skeletonConfig G state.1.done) :=
        readyInternalNodes_eq_of_done_eq rfl
      unfold EventGraph.settleInternal at hnext
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

/-- The completed-node update of one raw graph-protocol transition. -/
def protocolDoneStep (G : Graph Player L)
    (done : Finset (Fin G.nodeCount)) : Finset (Fin G.nodeCount) :=
  if hinternal :
      (readyInternalNodes G (skeletonConfig G done)).Nonempty then
    insert (Classical.choose hinternal) done
  else
    frontierDone G done

/-- The canonical completed-node set after a raw trace length. -/
def protocolDoneAt (G : Graph Player L) : Nat → Finset (Fin G.nodeCount)
  | 0 => ∅
  | steps + 1 => protocolDoneStep G (protocolDoneAt G steps)

theorem subset_protocolDoneStep (G : Graph Player L)
    (done : Finset (Fin G.nodeCount)) : done ⊆ protocolDoneStep G done := by
  unfold protocolDoneStep
  split
  · exact Finset.subset_insert _ _
  · unfold frontierDone
    split
    · exact Finset.Subset.refl _
    · exact Finset.subset_union_left

theorem protocolDoneAt_monotone (G : Graph Player L) :
    Monotone (protocolDoneAt G) :=
  monotone_nat_of_le_succ fun _ => subset_protocolDoneStep G _

theorem ReadyCommitNode.mem_protocolDoneStep_of_no_internal
    {G : Graph Player L} {cfg : Config G} {who : Player}
    {node : Fin G.nodeCount} (hready : ReadyCommitNode G cfg who node)
    (hinternal : readyInternalNodes G cfg = ∅) :
    node ∈ protocolDoneStep G cfg.done := by
  have hinternalSkeleton :
      readyInternalNodes G (skeletonConfig G cfg.done) = ∅ := by
    rw [← readyInternalNodes_eq_of_done_eq (G := G) rfl]
    exact hinternal
  have hreadySkeleton :
      ReadyCommitNode G (skeletonConfig G cfg.done) who node := by
    have heq := readyCommitNodes_eq_of_done_eq (G := G)
      (left := cfg) (right := skeletonConfig G cfg.done) rfl who
    have hmem : node ∈ readyCommitNodes G cfg who := by
      simp only [readyCommitNodes, Finset.mem_filter, Finset.mem_univ,
        true_and, hready]
    rw [heq] at hmem
    exact (Finset.mem_filter.mp hmem).2
  unfold protocolDoneStep
  rw [dif_neg (Finset.not_nonempty_iff_eq_empty.mpr hinternalSkeleton)]
  unfold frontierDone
  rw [if_neg (Finset.not_nonempty_iff_eq_empty.mpr hinternalSkeleton),
    Finset.mem_union]
  exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ node,
    ⟨who, hreadySkeleton⟩⟩)

theorem toExecutionProtocol_step_done (G : Graph Player L) (hwf : G.WF)
    (hguards : GuardLive G) (state : ReachableConfig G)
    (legal : { joint // (toExecutionProtocol G hwf hguards).Legal state joint })
    {next : ReachableConfig G}
    (hnext : next ∈
      ((toExecutionProtocol G hwf hguards).step state legal).support) :
    next.1.done = protocolDoneStep G state.1.done := by
  classical
  have hready : readyInternalNodes G state.1 =
      readyInternalNodes G (skeletonConfig G state.1.done) :=
    readyInternalNodes_eq_of_done_eq rfl
  unfold toExecutionProtocol at hnext
  change next ∈ (if hinternal : (readyInternalNodes G state.1).Nonempty then
    stepReadyInternal hwf state hinternal
  else FinDist.pure (applyFrontier G hwf state legal.1)).support at hnext
  by_cases hinternal : (readyInternalNodes G state.1).Nonempty
  · rw [dif_pos hinternal] at hnext
    rw [stepReadyInternal_done hwf state hinternal hnext]
    unfold protocolDoneStep
    have hcanonical :
        (readyInternalNodes G (skeletonConfig G state.1.done)).Nonempty :=
      hready ▸ hinternal
    rw [dif_pos hcanonical]
  · rw [dif_neg hinternal, FinDist.mem_support_pure] at hnext
    subst next
    rw [applyFrontier_done_of_legal G hwf hguards state legal.1 legal.2]
    unfold protocolDoneStep
    rw [dif_neg (by simpa only [← hready] using hinternal)]

/-- All raw graph traces follow the same completed-node timeline. -/
theorem toExecutionProtocol_trace_done (G : Graph Player L) (hwf : G.WF)
    (hguards : GuardLive G) {state : ReachableConfig G}
    (trace : (toExecutionProtocol G hwf hguards).Trace state) :
    state.val.done = protocolDoneAt G trace.length := by
  exact @GameTheory.Protocol.ExecutionProtocol.Trace.rec Player
    (toExecutionProtocol G hwf hguards)
    (fun state trace => state.val.done = protocolDoneAt G trace.length)
    rfl
    (by
      intro source target prior joint legal realized ih
      rw [toExecutionProtocol_step_done G hwf hguards source
        ⟨joint, legal⟩ realized]
      change protocolDoneStep G source.val.done =
        protocolDoneStep G (protocolDoneAt G prior.length)
      rw [ih])
    state trace

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
