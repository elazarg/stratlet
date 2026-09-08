/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.KernelExecution

/-! # Commutation of actual policy-driven ready-node execution -/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}

theorem policyNodeStep_of_ready [Fintype Player]
    {G : Graph Player L} (hwf : G.WF) (hguards : GuardLive G)
    (policies : CommitPolicyProfile G) (state : ReachableConfig G)
    (node : Fin G.nodeCount) (hready : Ready G state.1 node) :
    policyNodeStep hwf hguards policies state node =
      (policyValueLaw hwf hguards policies state node hready).map
        PolicyWrite.next := by
  unfold policyNodeStep
  rw [dif_pos hready]
  rfl

/-- Policy-driven execution of two distinct simultaneously ready nodes commutes. -/
theorem policyNodeStep_comm [Fintype Player]
    {G : Graph Player L} (hwf : G.WF) (hguards : GuardLive G)
    (policies : CommitPolicyProfile G) (state : ReachableConfig G)
    (left right : Fin G.nodeCount)
    (hleft : Ready G state.1 left) (hright : Ready G state.1 right)
    (hne : left ≠ right) :
    (policyNodeStep hwf hguards policies state left).bind
        (fun after => policyNodeStep hwf hguards policies after right) =
      (policyNodeStep hwf hguards policies state right).bind
        (fun after => policyNodeStep hwf hguards policies after left) := by
  apply FinDist.map_injective (f := Subtype.val) Subtype.val_injective
  rw [FinDist.map_bind, FinDist.map_bind,
    policyNodeStep_of_ready hwf hguards policies state left hleft,
    policyNodeStep_of_ready hwf hguards policies state right hright]
  simp only [FinDist.map_eq_bind, FinDist.bind_bind, FinDist.pure_bind]
  let leftLaw :=
    (policyValueLaw hwf hguards policies state left hleft).map PolicyWrite.written
  let rightLaw :=
    (policyValueLaw hwf hguards policies state right hright).map PolicyWrite.written
  calc
    _ = leftLaw.bind fun leftWritten => rightLaw.bind fun rightWritten =>
          FinDist.pure ((state.1.completeNode left leftWritten).completeNode
            right rightWritten) := by
      dsimp [leftLaw]
      rw [FinDist.bind_map]
      apply FinDist.bind_congr
      intro leftWrite _
      have hrightAfter : Ready G leftWrite.next.1 right := by
        apply hright.completeNode_of_ne
        intro heq
        apply hne
        rw [← leftWrite.event_node]
        exact heq.symm
      rw [← FinDist.map_eq_bind,
        map_val_policyNodeStep_of_ready hwf hguards policies
          leftWrite.next right hrightAfter]
      calc
        _ = ((policyValueLaw hwf hguards policies leftWrite.next right
              hrightAfter).map PolicyWrite.written).map
              (fun written => (state.1.completeNode left leftWrite.written).completeNode
                right written) := by
            rw [FinDist.map_comp]
            apply FinDist.map_congr_of_eq_on_support
            intro write _
            simp [PolicyWrite.next, leftWrite.event_node]
        _ = rightLaw.map
              (fun written => (state.1.completeNode left leftWrite.written).completeNode
                right written) := by
            rw [map_written_policyValueLaw_after_other hwf hguards policies state
              right left hright hleft hne.symm leftWrite]
        _ = _ := by rw [FinDist.map_eq_bind]
    _ = rightLaw.bind fun rightWritten => leftLaw.bind fun leftWritten =>
          FinDist.pure ((state.1.completeNode left leftWritten).completeNode
            right rightWritten) := FinDist.bind_comm _ _ _
    _ = _ := by
      dsimp [rightLaw]
      rw [FinDist.bind_map]
      symm
      apply FinDist.bind_congr
      intro rightWrite _
      have hleftAfter : Ready G rightWrite.next.1 left := by
        apply hleft.completeNode_of_ne
        intro heq
        apply hne
        rw [← rightWrite.event_node]
        exact heq
      rw [← FinDist.map_eq_bind,
        map_val_policyNodeStep_of_ready hwf hguards policies
          rightWrite.next left hleftAfter]
      calc
        _ = ((policyValueLaw hwf hguards policies rightWrite.next left
              hleftAfter).map PolicyWrite.written).map
              (fun written => (state.1.completeNode right rightWrite.written).completeNode
                left written) := by
            rw [FinDist.map_comp]
            apply FinDist.map_congr_of_eq_on_support
            intro write _
            simp [PolicyWrite.next, rightWrite.event_node]
        _ = leftLaw.map
              (fun written => (state.1.completeNode right rightWrite.written).completeNode
                left written) := by
            rw [map_written_policyValueLaw_after_other hwf hguards policies state
              left right hleft hright hne rightWrite]
        _ = _ := by
            rw [FinDist.map_eq_bind]
            apply FinDist.bind_congr
            intro leftWritten _
            rw [Config.completeNode_comm state.1 leftWritten rightWrite.written hne]

/-- The ready-node adjacent swap remains valid before any continuation. -/
theorem policyNodeStep_pair_bind_comm [Fintype Player]
    {G : Graph Player L} (hwf : G.WF) (hguards : GuardLive G)
    (policies : CommitPolicyProfile G) (state : ReachableConfig G)
    (left right : Fin G.nodeCount)
    (hleft : Ready G state.1 left) (hright : Ready G state.1 right)
    (hne : left ≠ right) {Outcome : Type}
    (continuation : ReachableConfig G → FinDist Outcome) :
    ((policyNodeStep hwf hguards policies state left).bind fun afterLeft =>
        (policyNodeStep hwf hguards policies afterLeft right).bind continuation) =
      ((policyNodeStep hwf hguards policies state right).bind fun afterRight =>
        (policyNodeStep hwf hguards policies afterRight left).bind continuation) := by
  simp only [← FinDist.bind_bind]
  rw [policyNodeStep_comm hwf hguards policies state left right
    hleft hright hne]

end Vegas.EventGraph
