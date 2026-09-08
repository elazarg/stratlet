/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.KernelFrontierWrites
import Vegas.EventGraph.Confluence

/-! # Applying projected frontier writes to the actual configuration -/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Protocol

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}

theorem projectedFrontierWrites_nodes_nodup {G : Graph Player L} (cfg : Config G)
    (values : {node : Fin G.nodeCount //
      ∃ who, ReadyCommitNode G cfg who node} → Option (TypedValue L)) :
    ((projectedFrontierWrites cfg values).map Prod.fst).Nodup := by
  unfold projectedFrontierWrites
  rw [List.map_filterMap]
  apply List.Nodup.filterMap _ (List.nodup_finRange G.nodeCount)
  intro first second node hfirst hsecond
  have hfirstEq : node = first := by
    split at hfirst
    next hready =>
      cases hvalue : values ⟨first, hready⟩ <;> simp_all
    next => simp at hfirst
  have hsecondEq : node = second := by
    split at hsecond
    next hready =>
      cases hvalue : values ⟨second, hready⟩ <;> simp_all
    next => simp at hsecond
  exact hfirstEq.symm.trans hsecondEq

/-- Atomic frontier application is exactly the graph update reconstructed
from the ready-node typed-value projection. -/
theorem applyFrontier_val_eq_projectedWrites {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G) (state : ReachableConfig G)
    (command : {joint : ∀ who, Option (FrontierAction G who) //
      (toExecutionProtocol G hwf hguards).Legal state joint}) :
    (applyFrontier G hwf state command.1).1 =
      state.1.completeNodes (projectedFrontierWrites state.1
        (frontierProjection state.1 command.1)) := by
  have havailable : ∀ who action, command.1 who = some action →
      FrontierAction.Available G state.1 who action := by
    intro who action haction
    have hlocal := command.2.2 who
    rw [haction] at hlocal
    exact hlocal.2
  rw [applyFrontier_val_of_available G hwf state command.1 havailable]
  have hround := roundWrites_nodes_nodup havailable Finset.univ.nodup_toList
  have hprojected := projectedFrontierWrites_nodes_nodup state.1
    (frontierProjection state.1 command.1)
  apply Config.completeNodes_perm _ _ hround
  apply (List.perm_ext_iff_of_nodup hround.of_map hprojected.of_map).mpr
  intro step
  exact (mem_projectedFrontierWrites_iff state.1 command.1 havailable step).symm

end Vegas.EventGraph
