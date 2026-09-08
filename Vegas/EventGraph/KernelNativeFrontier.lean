/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.KernelFrontierComplete
import Vegas.EventGraph.KernelFrontierProduct
import Vegas.EventGraph.KernelProduct
import Vegas.EventGraph.KernelNative

/-! # Native frontier transitions as independent typed writes -/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}

theorem behavioralJoint_frontier_eq_projectedProduct {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G) (policies : CommitPolicyProfile G)
    (state : ReachableConfig G) (trace : (toExecutionProtocol G hwf hguards).Trace state)
    (hterm : ¬ (toExecutionProtocol G hwf hguards).terminal state)
    (hinternal : readyInternalNodes G state.1 = ∅)
    (hsingle : ∀ who first second,
      ReadyCommitNode G state.1 who first → ReadyCommitNode G state.1 who second →
        first = second) :
    (((toInformationModel G hwf hguards).behavioralJoint
      (fun who => (policies who).behavioral hwf hguards) trace hterm).bind
      ((toExecutionProtocol G hwf hguards).step state)).map Subtype.val =
      (FinDist.pi fun node : {node : Fin G.nodeCount //
          ∃ who, ReadyCommitNode G state.1 who node} =>
        (policyValueLaw hwf hguards policies state node.1
          (readyCommitOwner_spec state.1 node).ready).map PolicyWrite.written).map
        (fun draw => state.1.completeNodes
          (projectedFrontierWrites state.1 (fun node => some (draw node)))) := by
  let joint := (toInformationModel G hwf hguards).behavioralJoint
    (fun who => (policies who).behavioral hwf hguards) trace hterm
  let laws (node : {node : Fin G.nodeCount //
      ∃ who, ReadyCommitNode G state.1 who node}) :=
    (policyValueLaw hwf hguards policies state node.1
      (readyCommitOwner_spec state.1 node).ready).map PolicyWrite.written
  have hprojection : joint.map (fun command => frontierProjection state.1 command.1) =
      (FinDist.pi laws).map (fun draw node => some (draw node)) := by
    have h := behavioralJoint_readyCommit_policyValueLaw hwf hguards policies trace
      hterm hinternal hsingle
    change joint.map (fun command => frontierProjection state.1 command.1) =
      FinDist.pi (fun node => (policyValueLaw hwf hguards policies state node.1
        (readyCommitOwner_spec state.1 node).ready).map (fun write => some write.written)) at h
    calc
      _ = FinDist.pi (fun node => (laws node).map some) := by
        simpa only [laws, FinDist.map_comp, Function.comp_def] using h
      _ = _ := FinDist.pi_map (fun _ => some) laws
  have hno : ¬ (readyInternalNodes G state.1).Nonempty := by simp [hinternal]
  calc
    _ = joint.map (fun command => state.1.completeNodes
          (projectedFrontierWrites state.1 (frontierProjection state.1 command.1))) := by
      rw [FinDist.map_bind, FinDist.map_eq_bind]
      apply FinDist.bind_congr
      intro command _
      change ((if hint : (readyInternalNodes G state.1).Nonempty then
          stepReadyInternal hwf state hint
        else FinDist.pure (applyFrontier G hwf state command.1)).map Subtype.val) = _
      rw [dif_neg hno, FinDist.map_pure, applyFrontier_val_eq_projectedWrites]
    _ = (joint.map (fun command => frontierProjection state.1 command.1)).map
          (fun values => state.1.completeNodes (projectedFrontierWrites state.1 values)) := by
      rw [FinDist.map_comp]
      rfl
    _ = _ := by rw [hprojection, FinDist.map_comp]; rfl

theorem runPolicyNodes_frontier_eq_projectedProduct {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G) (policies : CommitPolicyProfile G)
    (state : ReachableConfig G) (fallback : TypedValue L) :
    (runPolicyNodes hwf hguards policies state
      (Finset.univ.filter (fun node =>
        ∃ who, ReadyCommitNode G state.1 who node)).toList).map Subtype.val =
      (FinDist.pi fun node : {node : Fin G.nodeCount //
          ∃ who, ReadyCommitNode G state.1 who node} =>
        (policyValueLaw hwf hguards policies state node.1
          (readyCommitOwner_spec state.1 node).ready).map PolicyWrite.written).map
        (fun draw => state.1.completeNodes
          (projectedFrontierWrites state.1 (fun node => some (draw node)))) := by
  classical
  let nodes := Finset.univ.filter (fun node : Fin G.nodeCount =>
    ∃ who, ReadyCommitNode G state.1 who node)
  let index := {node : Fin G.nodeCount // ∃ who, ReadyCommitNode G state.1 who node}
  let equiv : nodes ≃ index :=
    { toFun := fun node => ⟨node.1, (Finset.mem_filter.mp node.2).2⟩
      invFun := fun node => ⟨node.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, node.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let laws (node : index) :=
    (policyValueLaw hwf hguards policies state node.1
      (readyCommitOwner_spec state.1 node).ready).map PolicyWrite.written
  have hready : ∀ node ∈ nodes, Ready G state.1 node := by
    intro node hmem
    obtain ⟨who, hcommit⟩ := (Finset.mem_filter.mp hmem).2
    exact hcommit.ready
  rw [runPolicyNodes_readySet_eq_pi hwf hguards policies state nodes hready fallback]
  have hpi : (FinDist.pi fun node : nodes =>
      (policyValueLaw hwf hguards policies state node.1 (hready node.1 node.2)).map
        PolicyWrite.written) =
      (FinDist.pi laws).map (fun draw node => draw (equiv node)) :=
    (FinDist.pi_reindex (fun _ : index => TypedValue L) equiv laws).symm
  rw [hpi, FinDist.map_comp]
  apply FinDist.map_congr_of_eq_on_support
  intro draw _
  exact (completeNodes_projectedFrontierWrites_some state.1 draw).symm

/-- A complete native behavioral round equals the corresponding typed node
round, including internal priority and simultaneous commitment submissions. -/
theorem behavioralJoint_eq_policyNodeRound {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G) (policies : CommitPolicyProfile G)
    (state : ReachableConfig G) (trace : (toExecutionProtocol G hwf hguards).Trace state)
    (hterm : ¬ (toExecutionProtocol G hwf hguards).terminal state)
    (hsingle : ∀ who first second,
      ReadyCommitNode G state.1 who first → ReadyCommitNode G state.1 who second →
        first = second) :
    ((toInformationModel G hwf hguards).behavioralJoint
      (fun who => (policies who).behavioral hwf hguards) trace hterm).bind
      ((toExecutionProtocol G hwf hguards).step state) =
        runPolicyNodes hwf hguards policies state (protocolNodeRound G state.1.done) := by
  by_cases hinternal : (readyInternalNodes G state.1).Nonempty
  · exact behavioralJoint_internal_eq_policyNodeRound hwf hguards policies state trace
      hterm hinternal
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp hinternal
    have hround : protocolNodeRound G state.1.done =
        (Finset.univ.filter (fun node =>
          ∃ who, ReadyCommitNode G state.1 who node)).toList := by
      have hnodes : readyInternalNodes G state.1 =
          readyInternalNodes G (skeletonConfig G state.1.done) :=
        readyInternalNodes_eq_of_done_eq rfl
      unfold protocolNodeRound
      rw [dif_neg (by simpa only [← hnodes] using hinternal)]
      rfl
    obtain ⟨node, hready⟩ := exists_ready_of_not_terminal G state.1 hterm
    let fallback :=
      ((policyValueLaw hwf hguards policies state node hready).support_nonempty.choose).written
    apply FinDist.map_injective Subtype.val_injective
    rw [hround, behavioralJoint_frontier_eq_projectedProduct hwf hguards policies state trace
      hterm hempty hsingle, runPolicyNodes_frontier_eq_projectedProduct hwf hguards policies
        state fallback]

end Vegas.EventGraph
