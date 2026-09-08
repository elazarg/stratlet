/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.KernelExecution
import Vegas.EventGraph.TopologicalOrder

/-! # Structural invariants of policy-driven node schedules -/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}

/-- Every supported ready policy step performs precisely the requested node
write in the actual graph configuration. -/
theorem policyNodeStep_support_completeNode {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G) (policies : CommitPolicyProfile G)
    (state : ReachableConfig G) (node : Fin G.nodeCount)
    (hready : Ready G state.1 node) (next : ReachableConfig G)
    (hnext : next ∈ (policyNodeStep hwf hguards policies state node).support) :
    ∃ written, next.1 = state.1.completeNode node written := by
  classical
  unfold policyNodeStep at hnext
  rw [dif_pos hready, FinDist.support_map] at hnext
  obtain ⟨write, _, rfl⟩ := hnext
  refine ⟨write.written, ?_⟩
  change state.1.completeNode write.event.node write.written = _
  rw [write.event_node]

/-- Completion after a requested node step depends on readiness and the node
alone, independently of the sampled value or player policy. -/
theorem policyNodeStep_support_done {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G) (policies : CommitPolicyProfile G)
    (state : ReachableConfig G) (node : Fin G.nodeCount) (next : ReachableConfig G)
    (hnext : next ∈ (policyNodeStep hwf hguards policies state node).support) :
    next.1.done = if Ready G state.1 node then insert node state.1.done else state.1.done := by
  classical
  by_cases hready : Ready G state.1 node
  · obtain ⟨written, hwritten⟩ :=
      policyNodeStep_support_completeNode hwf hguards policies state node hready next hnext
    rw [hwritten, if_pos hready]
    rfl
  · rw [policyNodeStep_of_not_ready hwf hguards policies state node hready] at hnext
    have heq := FinDist.mem_support_pure.mp hnext
    subst next
    rw [if_neg hready]

/-- A distinct simultaneously ready node remains ready after every supported
policy write. -/
theorem policyNodeStep_preserves_ready {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G) (policies : CommitPolicyProfile G)
    (state : ReachableConfig G) (node other : Fin G.nodeCount)
    (hready : Ready G state.1 node) (hother : Ready G state.1 other) (hne : other ≠ node)
    (next : ReachableConfig G)
    (hnext : next ∈ (policyNodeStep hwf hguards policies state node).support) :
    Ready G next.1 other := by
  obtain ⟨written, heq⟩ :=
    policyNodeStep_support_completeNode hwf hguards policies state node hready next hnext
  rw [heq]
  exact hother.completeNode_of_ne hne

/-- A legal policy-driven order completes exactly its listed nodes. In
particular, it never takes the total executor's non-ready no-op branch. -/
theorem runPolicyNodes_support_done {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G) (policies : CommitPolicyProfile G)
    (state : ReachableConfig G) (order : List (Fin G.nodeCount))
    (horder : G.ReadyOrder state.1.done order) (next : ReachableConfig G)
    (hnext : next ∈ (runPolicyNodes hwf hguards policies state order).support) :
    next.1.done = state.1.done ∪ order.toFinset := by
  induction order generalizing state with
  | nil =>
      have heq := FinDist.mem_support_pure.mp hnext
      subst next
      simp
  | cons node rest ih =>
      rw [runPolicyNodes_cons, FinDist.support_bind] at hnext
      simp only [Set.mem_iUnion] at hnext
      obtain ⟨middle, hmiddle, hnext⟩ := hnext
      have hready : Ready G state.1 node := ⟨horder.1, horder.2.1⟩
      have hdone := policyNodeStep_support_done hwf hguards policies state node middle hmiddle
      rw [if_pos hready] at hdone
      have htail : G.ReadyOrder middle.1.done rest := by rw [hdone]; exact horder.2.2
      rw [ih middle htail hnext, hdone]
      simp [Finset.insert_union, Finset.union_insert]

/-- A complete legal order terminates for every policy and supported chance
realization. -/
theorem runPolicyNodes_terminal {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G) (policies : CommitPolicyProfile G)
    (state : ReachableConfig G) (order : List (Fin G.nodeCount))
    (horder : G.ReadyOrder state.1.done order)
    (hcomplete : ∀ node, node ∈ state.1.done ∨ node ∈ order)
    (next : ReachableConfig G)
    (hnext : next ∈ (runPolicyNodes hwf hguards policies state order).support) :
    Terminal G next.1 := by
  intro node
  rw [runPolicyNodes_support_done hwf hguards policies state order horder next hnext]
  simpa only [Finset.mem_union, List.mem_toFinset] using hcomplete node

end Vegas.EventGraph
