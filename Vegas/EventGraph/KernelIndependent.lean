/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.IndependentWrites
import Vegas.EventGraph.KernelCommutation

/-! # Freezing the write laws of a simultaneous ready frontier -/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}

/-- The actual typed write law at a ready node. The supplied value merely
totalizes this observation at nodes that cannot currently execute. -/
def policyWriteLaw {G : Graph Player L} (hwf : G.WF) (hguards : GuardLive G)
    (policies : CommitPolicyProfile G) (state : ReachableConfig G)
    (fallback : TypedValue L) (node : Fin G.nodeCount) : FinDist (TypedValue L) :=
  if hready : Ready G state.1 node then
    (policyValueLaw hwf hguards policies state node hready).map PolicyWrite.written
  else FinDist.pure fallback

theorem policyWriteLaw_of_ready {G : Graph Player L} (hwf : G.WF)
    (hguards : GuardLive G) (policies : CommitPolicyProfile G) (state : ReachableConfig G)
    (fallback : TypedValue L) (node : Fin G.nodeCount) (hready : Ready G state.1 node) :
    policyWriteLaw hwf hguards policies state fallback node =
      (policyValueLaw hwf hguards policies state node hready).map PolicyWrite.written := by
  rw [policyWriteLaw, dif_pos hready]

/-- Executing a duplicate-free simultaneously ready list uses exactly the
write laws at its starting state. Dependencies prevent peer writes from
changing any of these laws. -/
theorem runPolicyNodes_eq_independentWrites {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G) (policies : CommitPolicyProfile G)
    (state : ReachableConfig G) (order : List (Fin G.nodeCount))
    (hnodup : order.Nodup) (hready : ∀ node ∈ order, Ready G state.1 node)
    (laws : Fin G.nodeCount → FinDist (TypedValue L))
    (hlaws : ∀ node (hmem : node ∈ order),
      (policyValueLaw hwf hguards policies state node (hready node hmem)).map
        PolicyWrite.written = laws node) :
    (runPolicyNodes hwf hguards policies state order).map Subtype.val =
      runIndependentWrites laws state.1 order := by
  induction order generalizing state with
  | nil => simp [runIndependentWrites]
  | cons head tail ih =>
      obtain ⟨hheadNot, htailNodup⟩ := List.nodup_cons.mp hnodup
      have hhead := hready head List.mem_cons_self
      rw [runPolicyNodes_cons, FinDist.map_bind,
        policyNodeStep_of_ready hwf hguards policies state head hhead, FinDist.bind_map]
      calc
        _ = (policyValueLaw hwf hguards policies state head hhead).bind
            (fun write => runIndependentWrites laws write.next.1 tail) := by
          apply FinDist.bind_congr
          intro write _
          have htailReady : ∀ node ∈ tail, Ready G write.next.1 node := by
            intro node hmem
            apply (hready node (List.mem_cons_of_mem _ hmem)).completeNode_of_ne
            intro heq
            apply hheadNot
            have heq' : node = head := heq.trans write.event_node
            exact heq' ▸ hmem
          apply ih write.next htailNodup htailReady
          intro node hmem
          have hne : node ≠ head := fun heq => hheadNot (heq ▸ hmem)
          rw [map_written_policyValueLaw_after_other hwf hguards policies state node head
            (hready node (List.mem_cons_of_mem _ hmem)) hhead hne write]
          exact hlaws node (List.mem_cons_of_mem _ hmem)
        _ = ((policyValueLaw hwf hguards policies state head hhead).map
            PolicyWrite.written).bind
            (fun written =>
              runIndependentWrites laws (state.1.completeNode head written) tail) := by
          rw [FinDist.bind_map]
          apply FinDist.bind_congr
          intro write _
          congr 1
          change state.1.completeNode write.event.node write.written = _
          rw [write.event_node]
        _ = _ := by rw [hlaws head List.mem_cons_self]; rfl

end Vegas.EventGraph
