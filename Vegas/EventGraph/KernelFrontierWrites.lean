/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.KernelRound

/-! # Reconstructing frontier writes from ready-node projections -/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Protocol

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}

/-- The typed value submitted at every ready commitment node. -/
def frontierProjection {G : Graph Player L} (cfg : Config G)
    (joint : ∀ who, Option (FrontierAction G who)) :
    {node : Fin G.nodeCount // ∃ who, ReadyCommitNode G cfg who node} →
      Option (TypedValue L) :=
  fun node => (joint (readyCommitOwner cfg node)).bind fun packet =>
    (packet.value? node.1).map (G.nodeTypedValue node.1)

/-- Decode one typed write for each ready commitment node, in graph order. -/
def projectedFrontierWrites {G : Graph Player L} (cfg : Config G)
    (values : {node : Fin G.nodeCount //
      ∃ who, ReadyCommitNode G cfg who node} → Option (TypedValue L)) :
    List (Fin G.nodeCount × TypedValue L) :=
  G.nodeOrder.filterMap fun node =>
    if hready : ∃ who, ReadyCommitNode G cfg who node then
      (values ⟨node, hready⟩).map fun value => (node, value)
    else none

theorem mem_projectedFrontierWrites_iff {G : Graph Player L}
    (cfg : Config G) (joint : ∀ who, Option (FrontierAction G who))
    (havailable : ∀ who action, joint who = some action →
      FrontierAction.Available G cfg who action)
    (step : Fin G.nodeCount × TypedValue L) :
    step ∈ projectedFrontierWrites cfg (frontierProjection cfg joint) ↔
      step ∈ roundWrites joint (Finset.univ.toList : List Player) := by
  classical
  constructor
  · intro hstep
    rw [projectedFrontierWrites, List.mem_filterMap] at hstep
    obtain ⟨node, _hnode, hmap⟩ := hstep
    by_cases hready : ∃ who, ReadyCommitNode G cfg who node
    · simp only [dif_pos hready] at hmap
      let indexed : {node : Fin G.nodeCount //
          ∃ who, ReadyCommitNode G cfg who node} := ⟨node, hready⟩
      let who := readyCommitOwner cfg indexed
      cases haction : joint who with
      | none => simp [frontierProjection, indexed, who, haction] at hmap
      | some action =>
        cases hvalue : action.value? node with
        | none => simp [frontierProjection, indexed, who, haction, hvalue] at hmap
        | some value =>
          have hmap' : (node, G.nodeTypedValue node value) = step := by
            simpa [frontierProjection, indexed, who, haction, hvalue] using hmap
          subst step
          exact (mem_roundWrites_iff joint _ _).mpr ⟨who, by simp,
            (mem_playerWrites_iff joint who _).mpr ⟨action, haction,
              (mem_actionWrites_iff action _).mpr ⟨value, hvalue, rfl⟩⟩⟩
    · simp [hready] at hmap
  · intro hstep
    obtain ⟨who, _hwho, hplayer⟩ :=
      (mem_roundWrites_iff joint _ step).mp hstep
    obtain ⟨action, haction, hwrite⟩ :=
      (mem_playerWrites_iff joint who step).mp hplayer
    obtain ⟨value, hvalue, hwritten⟩ :=
      (mem_actionWrites_iff action step).mp hwrite
    have havailable := havailable who action haction
    have hready : ReadyCommitNode G cfg who step.1 :=
      readyCommitNode_of_mem_actionWrites havailable
        ((mem_actionWrites_iff action step).mpr ⟨value, hvalue, hwritten⟩)
    unfold projectedFrontierWrites
    apply List.mem_filterMap.mpr
    refine ⟨step.1, G.mem_nodeOrder step.1, ?_⟩
    change (if h : ∃ actor, ReadyCommitNode G cfg actor step.1 then
      (frontierProjection cfg joint ⟨step.1, h⟩).map
        (fun written => (step.1, written)) else none) = some step
    rw [dif_pos ⟨who, hready⟩]
    have howner : ∀ h : ∃ actor, ReadyCommitNode G cfg actor step.1,
        readyCommitOwner cfg ⟨step.1, h⟩ = who := fun h =>
      (readyCommitOwner_spec cfg ⟨step.1, h⟩).owner_unique hready
    unfold frontierProjection
    rw [howner, haction]
    simpa [hvalue] using
      (show (step.1, G.nodeTypedValue step.1 value) = step from
        Prod.ext rfl hwritten.symm)


end Vegas.EventGraph
