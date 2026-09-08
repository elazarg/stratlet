/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.KernelExecution
import Vegas.EventGraph.PolicyRoundtrip

/-! # One-round correspondence for graph kernels -/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- In an internal round, the canonical protocol step is exactly the kernel
step at the canonical ready internal node. -/
theorem canonical_internal_step_eq_policyNodeStep [Fintype Player]
    {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G) (policies : CommitPolicyProfile G)
    (state : ReachableConfig G)
    (legal : { joint : ∀ who,
      Option ((toExecutionProtocol G hwf hguards).Action who) //
      ¬(toExecutionProtocol G hwf hguards).terminal state ∧
        IsLegalJoint ((toExecutionProtocol G hwf hguards).active state)
          ((toExecutionProtocol G hwf hguards).available state) joint })
    (hinternal : (readyInternalNodes G state.1).Nonempty) :
    (toExecutionProtocol G hwf hguards).step state legal =
      policyNodeStep hwf hguards policies state (Classical.choose hinternal) := by
  classical
  simp only [toExecutionProtocol, dif_pos hinternal]
  let node := Classical.choose hinternal
  have hreadyInternal : ReadyInternalNode G state.1 node :=
    (Finset.mem_filter.mp (Classical.choose_spec hinternal)).2
  rcases hreadyInternal with ⟨row, hrow, hkind, hready⟩
  have hinternalSem : NodeSem.isInternal (G.nodeRow node).sem = true := by
    have hrowEq := Option.some.inj ((G.nodes_get?_nodeRow node).symm.trans hrow)
    rw [hrowEq]
    cases hsem : row.sem <;> simp_all [NodeSem.isInternal]
  have havailable : InternalAvailable G state.1 { node := node } :=
    InternalAvailable.of_readyInternalNode hwf
      (reachable_storeCoherent hwf state.2) ⟨row, hrow, hkind, hready⟩
  let event : AvailableEvent G state.1 :=
    .internal { node := node } (Classical.choice havailable)
  apply FinDist.map_injective Subtype.val_injective
  rw [map_val_policyNodeStep_of_ready hwf hguards policies state node hready]
  change ((stepAvailable G state event).map Subtype.val) = _
  rw [map_val_stepAvailable, event.stepAvailableEvent_eq_writeLaw_map]
  have heventNode : event.node = node := rfl
  have hlaw : event.writeLaw =
      (readyEvent hwf hguards state node hready).writeLaw := by
    apply AvailableEvent.writeLaw_eq_of_node_eq_of_internal
    · simp [event]
    · exact hinternalSem
  calc
    event.writeLaw.map (fun written => state.1.completeNode event.node written) =
        event.writeLaw.map (fun written => state.1.completeNode node written) := by
          rw [heventNode]
    _ = (readyEvent hwf hguards state node hready).writeLaw.map
        (fun written => state.1.completeNode node written) := by rw [hlaw]
    _ = ((policyValueLaw hwf hguards policies state node hready).map
          PolicyWrite.written).map
        (fun written => state.1.completeNode node written) := by
          rw [map_written_policyValueLaw_of_internal hwf hguards policies
            state node hready hinternalSem]
    _ = _ := by
      rw [FinDist.map_comp]
      rfl

/-- The owner carried by a ready commitment node. -/
noncomputable def readyCommitOwner {G : Graph Player L}
    (cfg : Config G) (node : {node : Fin G.nodeCount //
      ∃ who, ReadyCommitNode G cfg who node}) : Player :=
  Classical.choose node.2

theorem readyCommitOwner_spec {G : Graph Player L}
    (cfg : Config G) (node : {node : Fin G.nodeCount //
      ∃ who, ReadyCommitNode G cfg who node}) :
    ReadyCommitNode G cfg (readyCommitOwner cfg node) node.1 :=
  Classical.choose_spec node.2

/-- When each player has at most one ready commitment, ownership embeds the
ready commitment frontier into the player index. -/
def readyCommitOwnerEmbedding {G : Graph Player L} (cfg : Config G)
    (hsingle : ∀ who first second,
      ReadyCommitNode G cfg who first → ReadyCommitNode G cfg who second →
        first = second) :
    {node : Fin G.nodeCount // ∃ who, ReadyCommitNode G cfg who node} ↪ Player where
  toFun := readyCommitOwner cfg
  inj' := by
    intro left right howner
    apply Subtype.ext
    exact hsingle (readyCommitOwner cfg left) left.1 right.1
      (readyCommitOwner_spec cfg left)
      (howner ▸ readyCommitOwner_spec cfg right)

/-- Projecting the independently sampled native joint command to ready
commitment coordinates is the product of the corresponding playerwise
coordinate laws. -/
theorem behavioralJoint_readyCommit_projection [Fintype Player]
    {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G) (kernels : CommitPolicyProfile G)
    {state : (toExecutionProtocol G hwf hguards).State}
    (trace : (toExecutionProtocol G hwf hguards).Trace state)
    (hterm : ¬(toExecutionProtocol G hwf hguards).terminal state)
    (hsingle : ∀ who first second,
      ReadyCommitNode G state.1 who first → ReadyCommitNode G state.1 who second →
        first = second) :
    ((toInformationModel G hwf hguards).behavioralJoint
      (fun who => (kernels who).behavioral hwf hguards) trace hterm).map
        (fun command node => (command.1 (readyCommitOwner state.1 node)).bind
          (fun packet => (packet.value? node.1).map (G.nodeTypedValue node.1))) =
      FinDist.pi (fun node =>
        ((kernels (readyCommitOwner state.1 node)).behavioral hwf hguards
          ((toInfoSignals G hwf hguards).infoOf
            (readyCommitOwner state.1 node) trace)).map
          (fun choice => choice.1.bind
            (fun packet => (packet.value? node.1).map (G.nodeTypedValue node.1)))) := by
  classical
  unfold InformationModel.behavioralJoint
  rw [FinDist.map_comp]
  let laws := fun who => (kernels who).behavioral hwf hguards
    ((toInfoSignals G hwf hguards).infoOf who trace)
  let owner := readyCommitOwnerEmbedding state.1 hsingle
  let project := fun node
      (choice : (toInformationModel G hwf hguards).Choice (owner node)
        ((toInfoSignals G hwf hguards).infoOf (owner node) trace)) =>
    choice.1.bind fun packet =>
      (packet.value? node.1).map (G.nodeTypedValue node.1)
  change (FinDist.pi laws).map
      (fun choices node => project node (choices (owner node))) = _
  calc
    _ = (FinDist.pi (fun node => laws (owner node))).map
        (fun choices node => project node (choices node)) := by
          have h := congrArg
            (FinDist.map (fun choices node => project node (choices node)))
            (FinDist.pi_map_embedding owner laws)
          simpa only [FinDist.map_comp, Function.comp_def] using h
    _ = FinDist.pi (fun node => (laws (owner node)).map (project node)) := by
          rw [FinDist.pi_map]
    _ = _ := rfl

/-- Each selected ready-node coordinate of the native behavioral packet is
the corresponding typed policy-write marginal. -/
theorem readyCommit_behavioral_projection_eq_policyValueLaw [Fintype Player]
    {G : Graph Player L} (hwf : G.WF) (hguards : GuardLive G)
    (kernels : CommitPolicyProfile G)
    {state : (toExecutionProtocol G hwf hguards).State}
    (trace : (toExecutionProtocol G hwf hguards).Trace state)
    (hinternal : readyInternalNodes G state.1 = ∅)
    (node : {node : Fin G.nodeCount // ∃ who, ReadyCommitNode G state.1 who node}) :
    ((kernels (readyCommitOwner state.1 node)).behavioral hwf hguards
      ((toInfoSignals G hwf hguards).infoOf (readyCommitOwner state.1 node) trace)).map
        (fun choice => choice.1.bind fun packet =>
          (packet.value? node.1).map (G.nodeTypedValue node.1)) =
      (policyValueLaw hwf hguards kernels state node.1
        (readyCommitOwner_spec state.1 node).ready).map
          (fun write => some write.written) := by
  classical
  let who := readyCommitOwner state.1 node
  have hcommit := readyCommitOwner_spec state.1 node
  have hactive : (toExecutionProtocol G hwf hguards).active state who := by
    refine ⟨?_, hinternal, ?_⟩
    · intro hterminal
      exact hcommit.ready.1 (hterminal node.1)
    · simp only [activePlayers, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨node.1, by
        simp only [readyCommitNodes, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hcommit⟩
  have hfront := congrArg
    (FinDist.map (fun action : Option (FrontierAction G who) =>
      action.bind fun packet =>
        (packet.value? node.1).map (G.nodeTypedValue node.1)))
    ((kernels who).behavioral_at_active hwf hguards trace hactive)
  simp only [FinDist.map_comp, Function.comp_def, Option.bind_some] at hfront
  change ((kernels who).behavioral hwf hguards
      ((toInfoSignals G hwf hguards).infoOf who trace)).map _ = _
  rcases hcommit with ⟨row, guard, hrow, hsem, hready⟩
  have hrowEq := Option.some.inj ((G.nodes_get?_nodeRow node.1).symm.trans hrow)
  have hcanonicalSem : (G.nodeRow node.1).sem = .commit who guard :=
    (congrArg EventNode.sem hrowEq).trans hsem
  have htyped := congrArg (FinDist.map some)
    (map_written_policyValueLaw_of_commit hwf hguards kernels state node.1
      hready who guard hcanonicalSem)
  calc
    _ = (frontierLaw hwf state.1 (reachable_storeCoherent hwf state.2)
          who (kernels who)).map
        (fun action => (action.1.value? node.1).map
          (G.nodeTypedValue node.1)) := hfront
    _ = (commitValueLaw hwf state.1 (reachable_storeCoherent hwf state.2)
          who (kernels who) node.1 ⟨row, guard, hrow, hsem, hready⟩).map
        (fun value => some (G.nodeTypedValue node.1 value.1)) :=
      frontierLaw_node hwf state.1 _ who (kernels who) node.1
        ⟨row, guard, hrow, hsem, hready⟩
    _ = _ := by
      simpa only [FinDist.map_comp, Function.comp_def] using htyped.symm

/-- The native simultaneous frontier draw factors into the independent typed
write laws of all ready commitment nodes. -/
theorem behavioralJoint_readyCommit_policyValueLaw [Fintype Player]
    {G : Graph Player L} (hwf : G.WF) (hguards : GuardLive G)
    (kernels : CommitPolicyProfile G)
    {state : (toExecutionProtocol G hwf hguards).State}
    (trace : (toExecutionProtocol G hwf hguards).Trace state)
    (hterm : ¬(toExecutionProtocol G hwf hguards).terminal state)
    (hinternal : readyInternalNodes G state.1 = ∅)
    (hsingle : ∀ who first second,
      ReadyCommitNode G state.1 who first → ReadyCommitNode G state.1 who second →
        first = second) :
    ((toInformationModel G hwf hguards).behavioralJoint
      (fun who => (kernels who).behavioral hwf hguards) trace hterm).map
        (fun command node => (command.1 (readyCommitOwner state.1 node)).bind
          (fun packet => (packet.value? node.1).map (G.nodeTypedValue node.1))) =
      FinDist.pi (fun node =>
        (policyValueLaw hwf hguards kernels state node.1
          (readyCommitOwner_spec state.1 node).ready).map
            (fun write => some write.written)) := by
  rw [behavioralJoint_readyCommit_projection hwf hguards kernels trace hterm hsingle]
  congr 1
  funext node
  exact readyCommit_behavioral_projection_eq_policyValueLaw hwf hguards kernels
    trace hinternal node

end Vegas.EventGraph
