/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.IndependentWriteProduct
import Vegas.EventGraph.KernelIndependent

/-! # The exact product law of a simultaneously ready node set -/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}

omit [Fintype Player] in
theorem runIndependentWrites_finset_eq_pi {G : Graph Player L}
    (laws : Fin G.nodeCount → FinDist (TypedValue L)) (cfg : Config G)
    (nodes : Finset (Fin G.nodeCount)) :
    runIndependentWrites laws cfg nodes.toList =
      (FinDist.pi fun node : nodes => laws node.1).map
        (fun draw => cfg.completeNodes (nodes.toList.attach.map fun node =>
          (node.1, draw ⟨node.1, Finset.mem_toList.mp node.2⟩))) := by
  rw [runIndependentWrites_eq_pi laws cfg _ (Finset.nodup_toList _)]
  let equiv : {node : Fin G.nodeCount // node ∈ nodes.toList.toFinset} ≃ nodes :=
    { toFun := fun node => ⟨node.1, by simpa only [Finset.toList_toFinset] using node.2⟩
      invFun := fun node => ⟨node.1, by simp [node.2]⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hpi :
      (FinDist.pi fun node : {node // node ∈ nodes.toList.toFinset} => laws node.1) =
        (FinDist.pi fun node : nodes => laws node.1).map
          (fun draw node => draw (equiv node)) :=
    (FinDist.pi_reindex (fun _ : nodes => TypedValue L) equiv
      (fun node => laws node.1)).symm
  rw [hpi, FinDist.map_comp]
  rfl

/-- A set of simultaneously ready nodes executes with the independent product
of its initial typed write laws. The fallback does not occur in this product. -/
theorem runPolicyNodes_readySet_eq_pi {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G) (policies : CommitPolicyProfile G)
    (state : ReachableConfig G) (nodes : Finset (Fin G.nodeCount))
    (hready : ∀ node ∈ nodes, Ready G state.1 node) (fallback : TypedValue L) :
    (runPolicyNodes hwf hguards policies state nodes.toList).map Subtype.val =
      (FinDist.pi fun node : nodes =>
        (policyValueLaw hwf hguards policies state node.1 (hready node.1 node.2)).map
          PolicyWrite.written).map
        (fun draw => state.1.completeNodes (nodes.toList.attach.map fun node =>
          (node.1, draw ⟨node.1, Finset.mem_toList.mp node.2⟩))) := by
  rw [runPolicyNodes_eq_independentWrites hwf hguards policies state _
    (Finset.nodup_toList _) (fun node hmem => hready node (Finset.mem_toList.mp hmem))
    (policyWriteLaw hwf hguards policies state fallback)
    (fun node hmem => (policyWriteLaw_of_ready hwf hguards policies state fallback node
      (hready node (Finset.mem_toList.mp hmem))).symm)]
  rw [runIndependentWrites_finset_eq_pi]
  congr 1
  congr 1
  funext node
  exact policyWriteLaw_of_ready hwf hguards policies state fallback node.1
    (hready node.1 node.2)

end Vegas.EventGraph
