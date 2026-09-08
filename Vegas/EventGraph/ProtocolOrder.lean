/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.Skeleton
import Vegas.EventGraph.TopologicalOrder
import Vegas.EventGraph.Linearization

/-! # Structural node orders for canonical protocol rounds

Each canonical round expands to a legal list of nodes. The expansion depends
only on the completed-node set, not on values, policies, or sampled outcomes.
-/

noncomputable section

namespace Vegas.EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr}

namespace Graph.ReadyOrder

theorem append {G : Graph Player L} {done : Finset (Fin G.nodeCount)}
    {first second : List (Fin G.nodeCount)} (hfirst : G.ReadyOrder done first)
    (hsecond : G.ReadyOrder (done ∪ first.toFinset) second) :
    G.ReadyOrder done (first ++ second) := by
  induction first generalizing done with
  | nil => simpa using hsecond
  | cons node rest ih =>
      refine ⟨hfirst.1, hfirst.2.1, ih hfirst.2.2 ?_⟩
      simpa only [List.toFinset_cons, Finset.union_insert, Finset.insert_union] using hsecond

/-- Any enumeration of distinct simultaneously ready nodes is a legal order. -/
theorem of_ready {G : Graph Player L} {done : Finset (Fin G.nodeCount)}
    {order : List (Fin G.nodeCount)} (hnodup : order.Nodup)
    (hready : ∀ node ∈ order, node ∉ done ∧ G.prereqs node ⊆ done) :
    G.ReadyOrder done order := by
  induction order generalizing done with
  | nil => trivial
  | cons head tail ih =>
      obtain ⟨hhead, htail⟩ := List.nodup_cons.mp hnodup
      obtain ⟨hnot, hdeps⟩ := hready head List.mem_cons_self
      refine ⟨hnot, hdeps, ih htail ?_⟩
      intro node hnode
      obtain ⟨hnot, hdeps⟩ := hready node (List.mem_cons_of_mem _ hnode)
      refine ⟨?_, hdeps.trans (Finset.subset_insert head done)⟩
      simp only [Finset.mem_insert, not_or]
      exact ⟨fun heq => hhead (heq ▸ hnode), hnot⟩

theorem not_mem_of_mem {G : Graph Player L} {done : Finset (Fin G.nodeCount)}
    {order : List (Fin G.nodeCount)} (horder : G.ReadyOrder done order)
    {node : Fin G.nodeCount} (hnode : node ∈ order) : node ∉ done := by
  induction order generalizing done with
  | nil => simp at hnode
  | cons head tail ih =>
      rcases List.mem_cons.mp hnode with rfl | htail
      · exact horder.1
      · exact fun hmem => ih horder.2.2 htail (Finset.mem_insert_of_mem hmem)

theorem nodup {G : Graph Player L} {done : Finset (Fin G.nodeCount)}
    {order : List (Fin G.nodeCount)} (horder : G.ReadyOrder done order) : order.Nodup := by
  induction order generalizing done with
  | nil => exact List.nodup_nil
  | cons head tail ih =>
      refine List.nodup_cons.mpr ⟨?_, ih horder.2.2⟩
      intro hmem
      exact horder.2.2.not_mem_of_mem hmem (Finset.mem_insert_self _ _)

end Graph.ReadyOrder

variable [Fintype Player]

/-- Canonical internal singleton, or an enumeration of the simultaneous
commitment frontier when there is no internal work. -/
def protocolNodeRound (G : Graph Player L) (done : Finset (Fin G.nodeCount)) :
    List (Fin G.nodeCount) :=
  if hinternal : (readyInternalNodes G (skeletonConfig G done)).Nonempty then
    [Classical.choose hinternal]
  else
    (Finset.univ.filter (fun node =>
      ∃ who, ReadyCommitNode G (skeletonConfig G done) who node)).toList

theorem protocolNodeRound_readyOrder (G : Graph Player L)
    (done : Finset (Fin G.nodeCount)) : G.ReadyOrder done (protocolNodeRound G done) := by
  unfold protocolNodeRound
  split
  next hinternal =>
    have hready := (Finset.mem_filter.mp (Classical.choose_spec hinternal)).2
    obtain ⟨_, _, _, hnot, hdeps⟩ := hready
    exact ⟨hnot, hdeps, trivial⟩
  next =>
    apply Graph.ReadyOrder.of_ready (Finset.nodup_toList _)
    intro node hnode
    obtain ⟨who, _, _, _, hready⟩ :=
      (Finset.mem_filter.mp (Finset.mem_toList.mp hnode)).2
    exact hready.2

theorem protocolNodeRound_done (G : Graph Player L)
    (done : Finset (Fin G.nodeCount)) :
    done ∪ (protocolNodeRound G done).toFinset = protocolDoneStep G done := by
  unfold protocolNodeRound protocolDoneStep
  split
  · simp
  next hinternal => simp [frontierDone, hinternal]

/-- Expand a bounded sequence of canonical rounds into individual nodes. -/
def protocolNodePlan (G : Graph Player L) :
    Nat → Finset (Fin G.nodeCount) → List (Fin G.nodeCount)
  | 0, _ => []
  | fuel + 1, done => protocolNodeRound G done ++
      protocolNodePlan G fuel (protocolDoneStep G done)

theorem protocolNodePlan_readyOrder (G : Graph Player L) (fuel : Nat)
    (done : Finset (Fin G.nodeCount)) :
    G.ReadyOrder done (protocolNodePlan G fuel done) := by
  induction fuel generalizing done with
  | zero => trivial
  | succ fuel ih =>
      apply (protocolNodeRound_readyOrder G done).append
      rw [protocolNodeRound_done]
      exact ih _

theorem protocolDoneStep_ssubset (G : Graph Player L)
    (done : Finset (Fin G.nodeCount)) (hnot : done ≠ Finset.univ) :
    done ⊂ protocolDoneStep G done := by
  have hterminal : ¬ Terminal G (skeletonConfig G done) := by
    intro hterm
    exact hnot (Finset.eq_univ_iff_forall.mpr hterm)
  obtain ⟨node, hready⟩ := exists_ready_of_not_terminal G _ hterminal
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨subset_protocolDoneStep G done, ?_⟩
  intro heq
  by_cases hinternal : (readyInternalNodes G (skeletonConfig G done)).Nonempty
  · have hmem := (Finset.mem_filter.mp (Classical.choose_spec hinternal)).2
    obtain ⟨_, _, _, hnot, _⟩ := hmem
    apply hnot
    have hchosen : Classical.choose hinternal ∈ protocolDoneStep G done := by
      rw [protocolDoneStep, dif_pos hinternal]
      exact Finset.mem_insert_self _ _
    exact (Finset.ext_iff.mp heq _).mpr hchosen
  · have hcommit : ∃ who, ReadyCommitNode G (skeletonConfig G done) who node := by
      cases hsem : (G.nodeRow node).sem with
      | commit who guard => exact ⟨who, G.nodeRow node, guard, G.nodes_get?_nodeRow node,
          hsem, hready⟩
      | sample dist =>
          exact False.elim (hinternal ⟨node, Finset.mem_filter.mpr ⟨Finset.mem_univ node,
            G.nodeRow node, G.nodes_get?_nodeRow node, by simp [hsem], hready⟩⟩)
      | reveal source =>
          exact False.elim (hinternal ⟨node, Finset.mem_filter.mpr ⟨Finset.mem_univ node,
            G.nodeRow node, G.nodes_get?_nodeRow node, by simp [hsem], hready⟩⟩)
    apply hready.1
    change node ∈ done
    rw [heq, protocolDoneStep, dif_neg hinternal, frontierDone, if_neg hinternal]
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ node, hcommit⟩)

/-- At most one round per remaining node suffices; simultaneous frontiers may
finish sooner. This bound is purely structural. -/
theorem protocolNodePlan_complete (G : Graph Player L) (fuel : Nat)
    (done : Finset (Fin G.nodeCount)) (hbound : G.nodeCount ≤ done.card + fuel) :
    ∀ node, node ∈ done ∨ node ∈ protocolNodePlan G fuel done := by
  induction fuel generalizing done with
  | zero =>
      have heq : done = Finset.univ := Finset.eq_univ_of_card done
        (Nat.le_antisymm (Finset.card_le_univ done) (by simpa using hbound))
      intro node
      exact Or.inl (heq ▸ Finset.mem_univ node)
  | succ fuel ih =>
      by_cases heq : done = Finset.univ
      · intro node
        exact Or.inl (heq ▸ Finset.mem_univ node)
      · have hcard := Finset.card_lt_card (protocolDoneStep_ssubset G done heq)
        have hnext := ih (protocolDoneStep G done) (by omega)
        intro node
        rcases hnext node with hmem | hmem
        · rw [← protocolNodeRound_done, Finset.mem_union, List.mem_toFinset] at hmem
          exact hmem.imp_right (fun h => List.mem_append_left _ h)
        · exact Or.inr (List.mem_append_right _ hmem)

theorem protocolNodePlan_isFullOrder (G : Graph Player L) :
    G.IsFullOrder (protocolNodePlan G G.nodeCount ∅) := by
  refine ⟨(protocolNodePlan_readyOrder G _ _).nodup, ?_⟩
  intro node
  exact (protocolNodePlan_complete G G.nodeCount ∅ (by simp) node).resolve_left
    (Finset.notMem_empty _)

end Vegas.EventGraph
