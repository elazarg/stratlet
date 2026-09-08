/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.SourceExecution

/-! # Graph projection of coupled source execution -/

noncomputable section
namespace Vegas.ToEventGraph
open EventGraph GameTheory.Math.Probability
variable {P : Type} [DecidableEq P] {L : IExpr}

private theorem nodeOrder_drop_eq_cons {G : Graph P L} (offset : Nat)
    (hoffset : offset < G.nodeCount) (node : Fin G.nodeCount)
    (hnode : (node : Nat) = offset) :
    G.nodeOrder.drop offset = node :: G.nodeOrder.drop (offset + 1) := by
  rw [Graph.nodeOrder, List.drop_eq_getElem_cons (by simpa using hoffset)]
  congr
  apply Fin.ext
  simpa [Graph.nodeOrder] using hnode.symm

private theorem map_supported_advance_graph [Fintype P]
    {Γ Δ : VCtx P L} {G : Graph P L} {state : BuildState P L Γ}
    (nextState : BuildState P L Δ) (hwf : G.WF) (hguards : GuardLive G)
    (policies : CommitPolicyProfile G) (current : CoupledState G state)
    (node : Fin G.nodeCount) (hready : Ready G current.graph.1 node)
    (advance : ∀ write ∈
      (policyValueLaw hwf hguards policies current.graph node hready).support,
        CoupledAt G nextState)
    (hgraph : ∀ write hwrite,
      (advance write hwrite).current.graph = write.next) :
    ((policyValueLaw hwf hguards policies current.graph node hready).bindOnSupport
      fun write hwrite => FinDist.pure (advance write hwrite)).map
        (fun next => next.current.graph) =
      policyNodeStep hwf hguards policies current.graph node := by
  rw [FinDist.map_bindOnSupport]
  rw [FinDist.bindOnSupport_eq_bind_of_eq_on_support
    (g := fun write => FinDist.pure write.next)]
  · unfold policyNodeStep
    rw [dif_pos hready, FinDist.map_eq_bind]
    apply FinDist.bind_congr
    intro write _
    apply congrArg FinDist.pure
    apply Subtype.ext
    rfl
  · intro write hwrite
    simp [hgraph write hwrite]

theorem coupledSampleStep_graph [Fintype P]
    {Γ : VCtx P L} {name : VarId} {ty : L.Ty}
    (dist : L.DistExpr (erasePubVCtx Γ) ty)
    (tail : VegasCore P L ((name, .pub ty) :: Γ))
    (fresh : FreshBindings (.sample name dist tail))
    (state : BuildState P L Γ)
    (policies : CommitPolicyProfile (compileCore (.sample name dist tail) fresh state).graph)
    (hguards : GuardLive (compileCore (.sample name dist tail) fresh state).graph)
    (current : CoupledAt (compileCore (.sample name dist tail) fresh state).graph state)
    (hprefix : state.nodes ++ [state.sampleEvent dist] <+:
      (compileCore (.sample name dist tail) fresh state).nodes) :
    (coupledSampleStep dist tail fresh state policies hguards current).map
        (fun next => next.current.graph) =
      policyNodeStep (compileCore (.sample name dist tail) fresh state).graphWF
        hguards policies current.current.graph
        (compiledNext state (compileCore (.sample name dist tail) fresh state)
          (state.sampleEvent dist) hprefix).node := by
  unfold coupledSampleStep
  apply map_supported_advance_graph
  intro write hwrite
  apply Subtype.ext
  rfl

theorem coupledCommitStep_graph [Fintype P]
    {Γ : VCtx P L} {name : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((name, .sealed who ty) :: Γ))
    (fresh : FreshBindings (.commit name who guard tail))
    (state : BuildState P L Γ)
    (policies : CommitPolicyProfile (compileCore (.commit name who guard tail) fresh state).graph)
    (hguards : GuardLive (compileCore (.commit name who guard tail) fresh state).graph)
    (current : CoupledAt (compileCore (.commit name who guard tail) fresh state).graph state)
    (hprefix : state.nodes ++ [state.commitEvent who guard] <+:
      (compileCore (.commit name who guard tail) fresh state).nodes) :
    (coupledCommitStep guard tail fresh state policies hguards current).map
        (fun next => next.current.graph) =
      policyNodeStep (compileCore (.commit name who guard tail) fresh state).graphWF
        hguards policies current.current.graph
        (compiledNext state (compileCore (.commit name who guard tail) fresh state)
          (state.commitEvent who guard) hprefix).node := by
  unfold coupledCommitStep
  apply map_supported_advance_graph
  intro write hwrite
  apply Subtype.ext
  rfl

theorem coupledRevealStep_graph [Fintype P]
    {Γ : VCtx P L} {name sourceName : VarId} {who : P} {ty : L.Ty}
    (source : VHasVar Γ sourceName (.sealed who ty))
    (tail : VegasCore P L ((name, .pub ty) :: Γ))
    (fresh : FreshBindings (.reveal name who sourceName source tail))
    (state : BuildState P L Γ)
    (policies : CommitPolicyProfile
      (compileCore (.reveal name who sourceName source tail) fresh state).graph)
    (hguards : GuardLive
      (compileCore (.reveal name who sourceName source tail) fresh state).graph)
    (current : CoupledAt
      (compileCore (.reveal name who sourceName source tail) fresh state).graph state)
    (hprefix : state.nodes ++ [state.revealEvent who source] <+:
      (compileCore (.reveal name who sourceName source tail) fresh state).nodes) :
    (coupledRevealStep source tail fresh state policies hguards current).map
        (fun next => next.current.graph) =
      policyNodeStep
        (compileCore (.reveal name who sourceName source tail) fresh state).graphWF
        hguards policies current.current.graph
        (compiledNext state
          (compileCore (.reveal name who sourceName source tail) fresh state)
          (state.revealEvent who source) hprefix).node := by
  unfold coupledRevealStep
  apply map_supported_advance_graph
  intro write hwrite
  apply Subtype.ext
  rfl

/-- Forgetting the source environment from coupled written-order execution is
exactly execution of the remaining canonical graph-node suffix. -/
theorem runCoupledSource_graph [Fintype P] :
    {Γ : VCtx P L} → (prog : VegasCore P L Γ) →
    (fresh : FreshBindings prog) → (state : BuildState P L Γ) →
    (policies : CommitPolicyProfile (compileCore prog fresh state).graph) →
    (hguards : GuardLive (compileCore prog fresh state).graph) →
    (current : CoupledAt (compileCore prog fresh state).graph state) →
    (runCoupledSource prog fresh state policies hguards current).map
        (fun out => out.current.graph) =
      runPolicyNodes (compileCore prog fresh state).graphWF hguards policies
        current.current.graph
        ((compileCore prog fresh state).graph.nodeOrder.drop state.nodes.length) := by
  intro Γ prog
  induction prog with
  | ret result =>
      intro fresh state policies hguards current
      rw [runCoupledSource, FinDist.map_pure]
      have hempty :
          (compileCore (.ret result) fresh state).graph.nodeOrder.drop
            state.nodes.length = [] := by
        apply List.drop_eq_nil_of_le
        simp [Graph.nodeOrder, compileCore, BuildResult.graph, Graph.nodeCount]
      rw [hempty, runPolicyNodes_nil]
  | sample name dist tail ih =>
      intro fresh state policies hguards current
      let added := state.addSampleEvent name dist fresh.1
      let result := compileCore (.sample name dist tail) fresh state
      let event := state.sampleEvent dist
      have hprefix : state.nodes ++ [event] <+: result.nodes := by
        change state.nodes ++ [event] <+: (compileCore tail fresh.2 added.1).nodes
        simpa [added, event, BuildState.sampleEvent] using
          compileCore_nodes_prefix tail fresh.2 added.1
      let next := compiledNext state result event hprefix
      have hlt : state.nodes.length < result.nodes.length := by
        rcases hprefix with ⟨suffix, hsuffix'⟩
        rw [← hsuffix']
        simp
      have hsuffix : result.graph.nodeOrder.drop state.nodes.length =
          next.node :: result.graph.nodeOrder.drop added.1.nodes.length := by
        rw [nodeOrder_drop_eq_cons state.nodes.length
          (by simpa [BuildResult.graph, Graph.nodeCount] using hlt)
          next.node next.index]
        simp [added]
      rw [runCoupledSource, FinDist.map_bind]
      apply Eq.trans (FinDist.bind_congr (μ := coupledSampleStep dist tail fresh state
        policies hguards current) fun after _ => ih fresh.2 added.1 policies hguards after)
      rw [hsuffix, runPolicyNodes_cons,
        ← coupledSampleStep_graph dist tail fresh state policies hguards current hprefix,
        FinDist.bind_map]
      apply FinDist.bind_congr
      intro after _
      rfl
  | commit name who guard tail ih =>
      intro fresh state policies hguards current
      let added := state.addCommitEvent name who guard fresh.1
      let result := compileCore (.commit name who guard tail) fresh state
      let event := state.commitEvent who guard
      have hprefix : state.nodes ++ [event] <+: result.nodes := by
        change state.nodes ++ [event] <+: (compileCore tail fresh.2 added.1).nodes
        simpa [added, event, BuildState.commitEvent] using
          compileCore_nodes_prefix tail fresh.2 added.1
      let next := compiledNext state result event hprefix
      have hlt : state.nodes.length < result.nodes.length := by
        rcases hprefix with ⟨suffix, hsuffix'⟩
        rw [← hsuffix']
        simp
      have hsuffix : result.graph.nodeOrder.drop state.nodes.length =
          next.node :: result.graph.nodeOrder.drop added.1.nodes.length := by
        rw [nodeOrder_drop_eq_cons state.nodes.length
          (by simpa [BuildResult.graph, Graph.nodeCount] using hlt)
          next.node next.index]
        simp [added]
      rw [runCoupledSource, FinDist.map_bind]
      apply Eq.trans (FinDist.bind_congr (μ := coupledCommitStep guard tail fresh state
        policies hguards current) fun after _ => ih fresh.2 added.1 policies hguards after)
      rw [hsuffix, runPolicyNodes_cons,
        ← coupledCommitStep_graph guard tail fresh state policies hguards current hprefix,
        FinDist.bind_map]
      apply FinDist.bind_congr
      intro after _
      rfl
  | reveal name who sourceName source tail ih =>
      intro fresh state policies hguards current
      let added := state.addRevealEvent name who source fresh.1
      let result := compileCore (.reveal name who sourceName source tail) fresh state
      let event := state.revealEvent who source
      have hprefix : state.nodes ++ [event] <+: result.nodes := by
        change state.nodes ++ [event] <+: (compileCore tail fresh.2 added.1).nodes
        simpa [added, event, BuildState.revealEvent] using
          compileCore_nodes_prefix tail fresh.2 added.1
      let next := compiledNext state result event hprefix
      have hlt : state.nodes.length < result.nodes.length := by
        rcases hprefix with ⟨suffix, hsuffix'⟩
        rw [← hsuffix']
        simp
      have hsuffix : result.graph.nodeOrder.drop state.nodes.length =
          next.node :: result.graph.nodeOrder.drop added.1.nodes.length := by
        rw [nodeOrder_drop_eq_cons state.nodes.length
          (by simpa [BuildResult.graph, Graph.nodeCount] using hlt)
          next.node next.index]
        simp [added]
      rw [runCoupledSource, FinDist.map_bind]
      apply Eq.trans (FinDist.bind_congr (μ := coupledRevealStep source tail fresh state
        policies hguards current) fun after _ => ih fresh.2 added.1 policies hguards after)
      rw [hsuffix, runPolicyNodes_cons,
        ← coupledRevealStep_graph source tail fresh state policies hguards current hprefix,
        FinDist.bind_map]
      apply FinDist.bind_congr
      intro after _
      rfl

end Vegas.ToEventGraph
