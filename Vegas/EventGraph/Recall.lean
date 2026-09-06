/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.Protocol

/-! # Relating remembered decisions to completed graph nodes -/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability GameTheory.Protocol

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}

/-- A submitted node value is completed by the realized strategic round. -/
theorem submitted_node_done (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G)
    (state : ReachableConfig G)
    (command : { joint // (toExecutionProtocol G hwf hguards).Legal state joint })
    {who : Player} {action : FrontierAction G who} {index : Fin G.nodeCount}
    {value : L.Val (G.nodeRow index).ty}
    (haction : command.1 who = some action) (hvalue : action.value? index = some value)
    {target : ReachableConfig G}
    (hnext : target ∈ ((toExecutionProtocol G hwf hguards).step state command).support) :
    index ∈ target.1.done := by
  classical
  have hlocal := command.2.2 who
  rw [haction] at hlocal
  rw [toExecutionProtocol_step_eq_pure_applyFrontier G hwf hguards state command
    hlocal.1.2.1, FinDist.mem_support_pure] at hnext
  subst target
  have havailable : ∀ player packet, command.1 player = some packet →
      FrontierAction.Available G state.1 player packet := by
    intro player packet hpacket
    have h := command.2.2 player
    rw [hpacket] at h
    exact h.2
  rw [applyFrontier_val_of_available G hwf state command.1 havailable,
    Config.completeNodes_done]
  apply Finset.mem_union_right
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  refine ⟨(index, G.nodeTypedValue index value), ?_, rfl⟩
  apply (mem_roundWrites_iff _ _ _).mpr
  refine ⟨who, by simp, (mem_playerWrites_iff _ _ _).mpr ⟨action, haction, ?_⟩⟩
  exact (mem_actionWrites_iff _ _).mpr ⟨value, hvalue, rfl⟩

/-- Before any of a player's commit nodes has completed, its remembered
decision record is empty. This quantifies over actual protocol traces. -/
theorem own_eq_nil_of_no_completed_choice
    (G : Graph Player L) (hwf : G.WF) (hguards : GuardLive G) (who : Player)
    {state : (toExecutionProtocol G hwf hguards).State}
    (trace : (toExecutionProtocol G hwf hguards).Trace state)
    (hnot : ∀ index row guard, G.nodes[index]? = some row →
      row.sem = .commit who guard → index ∉ state.1.done) :
    ((toInfoSignals G hwf hguards).infoOf who trace).own = [] := by
  induction trace with
  | start => rfl
  | @extend source target prior joint isLegal realized ih =>
    have hsubset := (toExecutionProtocol_step_done_ssubset G hwf hguards source
      ⟨joint, isLegal⟩ realized).subset
    have hprior := ih (fun index row guard hrow hsem hdone =>
      hnot index row guard hrow hsem (hsubset hdone))
    cases hchoice : joint who with
    | none =>
      change (PlayerInformation.push _ (joint who) _).own = []
      simpa only [hchoice, PlayerInformation.push] using hprior
    | some action =>
      have hlocal := isLegal.2 who
      rw [hchoice] at hlocal
      obtain ⟨index, hindex⟩ := (Finset.mem_filter.mp hlocal.1.2.2).2
      have hready := (Finset.mem_filter.mp hindex).2
      obtain ⟨value, hvalue⟩ := hlocal.2.value?_isSome_iff_readyCommitNode.mpr hready
      obtain ⟨row, guard, hrow, hsem, _⟩ := hready
      exact False.elim (hnot index row guard hrow hsem
        (submitted_node_done G hwf hguards source ⟨joint, isLegal⟩ hchoice hvalue realized))

/-- info: 'Vegas.EventGraph.own_eq_nil_of_no_completed_choice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.own_eq_nil_of_no_completed_choice

end Vegas.EventGraph
