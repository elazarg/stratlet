/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.KernelFrontierComplete

/-! # Projected frontier writes in ready-set product order -/

noncomputable section

namespace Vegas.EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}

/-- Completing the node-order decoding of a total ready-frontier assignment is
the same as completing the ready finset in its canonical list order. -/
theorem completeNodes_projectedFrontierWrites_some {G : Graph Player L}
    (cfg : Config G)
    (values : {node : Fin G.nodeCount //
      ∃ who, ReadyCommitNode G cfg who node} → TypedValue L) :
    cfg.completeNodes (projectedFrontierWrites cfg (fun node => some (values node))) =
      cfg.completeNodes
        (((Finset.univ.filter (fun node : Fin G.nodeCount =>
            ∃ who, ReadyCommitNode G cfg who node)).toList.attach.map fun node =>
          (node.1, values ⟨node.1,
            by
              have hm := Finset.mem_toList.mp node.2
              exact (Finset.mem_filter.mp hm).2⟩))) := by
  classical
  let nodes := Finset.univ.filter (fun node : Fin G.nodeCount =>
    ∃ who, ReadyCommitNode G cfg who node)
  let productWrites := nodes.toList.attach.map fun node =>
    (node.1, values ⟨node.1,
      by
        have hm : node.1 ∈ nodes := Finset.mem_toList.mp node.2
        exact (Finset.mem_filter.mp hm).2⟩)
  have hprojected := projectedFrontierWrites_nodes_nodup cfg
    (fun node => some (values node))
  have hproductNodes : (productWrites.map Prod.fst).Nodup := by
    simpa [productWrites] using nodes.nodup_toList
  apply Config.completeNodes_perm cfg _ hprojected
  apply (List.perm_ext_iff_of_nodup hprojected.of_map hproductNodes.of_map).mpr
  intro step
  constructor
  · intro hstep
    rw [projectedFrontierWrites, List.mem_filterMap] at hstep
    obtain ⟨node, _hnode, hmap⟩ := hstep
    by_cases hready : ∃ who, ReadyCommitNode G cfg who node
    · simp only [dif_pos hready, Option.map_some, Option.some.injEq] at hmap
      subst step
      simp [productWrites, nodes, hready]
    · simp [hready] at hmap
  · intro hstep
    have hstep' : ∃ node, ∃ hready : ∃ who, ReadyCommitNode G cfg who node,
        (node, values ⟨node, hready⟩) = step := by
      simpa [productWrites, nodes] using hstep
    obtain ⟨node, hready, rfl⟩ := hstep'
    rw [projectedFrontierWrites, List.mem_filterMap]
    refine ⟨node, G.mem_nodeOrder node, ?_⟩
    simp [hready]

end Vegas.EventGraph
