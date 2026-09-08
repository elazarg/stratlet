import Vegas.EventGraph.KernelExecution

noncomputable section
namespace Vegas.EventGraph
open GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- At a ready commit node, the typed policy-write marginal is exactly the
declared-read guard kernel supplied by that player. -/
theorem map_written_policyValueLaw_of_commitKernel [Fintype Player]
    {G : Graph Player L} (hwf : G.WF) (hguards : GuardLive G)
    (policies : CommitPolicyProfile G) (state : ReachableConfig G)
    (node : Fin G.nodeCount) (hready : Ready G state.1 node)
    (who : Player) (guard : EventGuard L)
    (hsem : (G.nodeRow node).sem = .commit who guard)
    (reads : ReadEnv L guard.choiceReads)
    (hreads : ReadEnv.ofStore? state.1.store guard.choiceReads = some reads) :
    (policyValueLaw hwf hguards policies state node hready).map
        PolicyWrite.written =
      (policies who node guard hsem reads).map fun value =>
        (⟨guard.ty, value.1⟩ : TypedValue L) := by
  rw [map_written_policyValueLaw_of_commit hwf hguards policies state node
    hready who guard hsem]
  exact commitValueLaw_typed hwf state.1
    (reachable_storeCoherent hwf state.2) who (policies who) node
    ⟨G.nodeRow node, guard, G.nodes_get?_nodeRow node, hsem, hready⟩
    guard hsem reads hreads

/-- At a ready sample node, the policy law is exactly the declared distribution
evaluated on the supplied canonical read environment. -/
theorem map_written_policyValueLaw_of_sample [Fintype Player]
    {G : Graph Player L} (hwf : G.WF) (hguards : GuardLive G)
    (policies : CommitPolicyProfile G) (state : ReachableConfig G)
    (node : Fin G.nodeCount) (hready : Ready G state.1 node)
    (row : EventNode Player L) (dist : EventDist L)
    (hrow : G.nodes[node]? = some row) (hsem : row.sem = .sample dist)
    (reads : ReadEnv L dist.reads)
    (hreads : ReadEnv.ofStore? state.1.store dist.reads = some reads) :
    (policyValueLaw hwf hguards policies state node hready).map
        PolicyWrite.written =
      (dist.eval reads).map fun value => (⟨dist.ty, value⟩ : TypedValue L) := by
  have hcanonical : G.nodeRow node = row :=
    Option.some.inj ((G.nodes_get?_nodeRow node).symm.trans hrow)
  have hcanonicalSem : (G.nodeRow node).sem = .sample dist :=
    (congrArg EventNode.sem hcanonical).trans hsem
  rw [map_written_policyValueLaw_of_internal hwf hguards policies state node
    hready (by simp [hcanonicalSem, NodeSem.isInternal])]
  let explicit : AvailableEvent G state.1 := .internal ⟨node⟩
    (.sample row dist hrow hsem hready reads hreads)
  calc
    (readyEvent hwf hguards state node hready).writeLaw = explicit.writeLaw := by
      apply AvailableEvent.writeLaw_eq_of_node_eq_of_internal
      · simp [explicit]
      · simp [hcanonicalSem, NodeSem.isInternal]
    _ = _ := rfl

/-- At a ready reveal node, the policy law is the point law at the value read
from the declared source field. -/
theorem map_written_policyValueLaw_of_reveal [Fintype Player]
    {G : Graph Player L} (hwf : G.WF) (hguards : GuardLive G)
    (policies : CommitPolicyProfile G) (state : ReachableConfig G)
    (node : Fin G.nodeCount) (hready : Ready G state.1 node)
    (row : EventNode Player L) (source : Nat)
    (hrow : G.nodes[node]? = some row) (hsem : row.sem = .reveal source)
    (value : L.Val row.ty)
    (hvalue : Store.getAs state.1.store source row.ty = some value) :
    (policyValueLaw hwf hguards policies state node hready).map
        PolicyWrite.written =
      FinDist.pure (⟨row.ty, value⟩ : TypedValue L) := by
  have hcanonical : G.nodeRow node = row :=
    Option.some.inj ((G.nodes_get?_nodeRow node).symm.trans hrow)
  have hcanonicalSem : (G.nodeRow node).sem = .reveal source :=
    (congrArg EventNode.sem hcanonical).trans hsem
  rw [map_written_policyValueLaw_of_internal hwf hguards policies state node
    hready (by simp [hcanonicalSem, NodeSem.isInternal])]
  let explicit : AvailableEvent G state.1 := .internal ⟨node⟩
    (.reveal row source hrow hsem hready value hvalue)
  calc
    (readyEvent hwf hguards state node hready).writeLaw = explicit.writeLaw := by
      apply AvailableEvent.writeLaw_eq_of_node_eq_of_internal
      · simp [explicit]
      · simp [hcanonicalSem, NodeSem.isInternal]
    _ = _ := rfl

namespace AvailableEvent

theorem exists_nodeValue_of_mem_writeLaw {G : Graph Player L} {cfg : Config G}
    (hwf : G.WF) (event : AvailableEvent G cfg) (written : TypedValue L)
    (hmem : written ∈ event.writeLaw.support) :
    ∃ value : L.Val (G.nodeRow event.node).ty,
      written = G.nodeTypedValue event.node value := by
  cases event with
  | commit who action step =>
      rw [writeLaw, FinDist.mem_support_pure] at hmem
      have hrow : G.nodeRow action.node = step.row :=
        Option.some.inj ((G.nodes_get?_nodeRow action.node).symm.trans step.row_get)
      have hty : (G.nodeRow action.node).ty = step.guard.ty := by
        have hnodeWF := hwf action.node step.row step.row_get
        unfold Graph.nodeWFAt at hnodeWF
        rw [step.sem_eq] at hnodeWF
        exact (congrArg EventNode.ty hrow).trans hnodeWF.2.1
      subst written
      exact ⟨cast (congrArg L.Val hty.symm) step.value, by
        simp [Graph.nodeTypedValue, hty]⟩
  | internal event step =>
      cases step with
      | sample row dist rowGet semEq ready env envOk =>
          rw [writeLaw, FinDist.support_map] at hmem
          obtain ⟨value, _, rfl⟩ := hmem
          have hrow : G.nodeRow event.node = row :=
            Option.some.inj ((G.nodes_get?_nodeRow event.node).symm.trans rowGet)
          have hty : (G.nodeRow event.node).ty = dist.ty := by
            have hnodeWF := hwf event.node row rowGet
            unfold Graph.nodeWFAt at hnodeWF
            rw [semEq] at hnodeWF
            exact (congrArg EventNode.ty hrow).trans hnodeWF.2.1
          exact ⟨cast (congrArg L.Val hty.symm) value, by
            simp [Graph.nodeTypedValue, hty]⟩
      | reveal row source rowGet semEq ready value valueOk =>
          rw [writeLaw, FinDist.mem_support_pure] at hmem
          have hrow : G.nodeRow event.node = row :=
            Option.some.inj ((G.nodes_get?_nodeRow event.node).symm.trans rowGet)
          subst written
          exact ⟨cast (congrArg L.Val (congrArg EventNode.ty hrow).symm) value, by
            simp [Graph.nodeTypedValue, hrow]⟩

end AvailableEvent

namespace PolicyWrite

private theorem exists_value_of_ty_eq (written : TypedValue L) (ty : L.Ty)
    (hty : written.ty = ty) :
    ∃ value : L.Val ty, written = (⟨ty, value⟩ : TypedValue L) := by
  cases written with
  | mk writtenTy writtenValue =>
      cases hty
      exact ⟨writtenValue, rfl⟩

theorem exists_nodeValue [Fintype Player] {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G)
    (policies : CommitPolicyProfile G) (state : ReachableConfig G)
    (node : Fin G.nodeCount) (hready : Ready G state.1 node)
    (write : PolicyWrite state node)
    (hmem : write ∈ (policyValueLaw hwf hguards policies state node hready).support) :
    ∃ value : L.Val (G.nodeRow node).ty,
      write.written = G.nodeTypedValue node value := by
  cases hsem : (G.nodeRow node).sem with
  | commit who guard =>
      have hwritten : write.written ∈
          ((policyValueLaw hwf hguards policies state node hready).map
            PolicyWrite.written).support := by
        rw [FinDist.support_map]
        exact ⟨write, hmem, rfl⟩
      rw [map_written_policyValueLaw_of_commit hwf hguards policies state node
        hready who guard hsem, FinDist.support_map] at hwritten
      obtain ⟨selected, _, heq⟩ := hwritten
      exact ⟨selected.1, heq.symm⟩
  | sample dist =>
      have hwritten : write.written ∈
          (readyEvent hwf hguards state node hready).writeLaw.support := by
        rw [← map_written_policyValueLaw_of_internal hwf hguards policies state
          node hready (by simp [hsem, NodeSem.isInternal]), FinDist.support_map]
        exact ⟨write, hmem, rfl⟩
      obtain ⟨value, heq⟩ :=
        AvailableEvent.exists_nodeValue_of_mem_writeLaw hwf _ _ hwritten
      have hnode := readyEvent_node hwf hguards state node hready
      have hty : write.written.ty = (G.nodeRow node).ty := by
        rw [heq]
        simp [Graph.nodeTypedValue, hnode]
      obtain ⟨value, heq⟩ := exists_value_of_ty_eq write.written _ hty
      exact ⟨value, by simpa [Graph.nodeTypedValue] using heq⟩
  | reveal source =>
      have hwritten : write.written ∈
          (readyEvent hwf hguards state node hready).writeLaw.support := by
        rw [← map_written_policyValueLaw_of_internal hwf hguards policies state
          node hready (by simp [hsem, NodeSem.isInternal]), FinDist.support_map]
        exact ⟨write, hmem, rfl⟩
      obtain ⟨value, heq⟩ :=
        AvailableEvent.exists_nodeValue_of_mem_writeLaw hwf _ _ hwritten
      have hnode := readyEvent_node hwf hguards state node hready
      have hty : write.written.ty = (G.nodeRow node).ty := by
        rw [heq]
        simp [Graph.nodeTypedValue, hnode]
      obtain ⟨value, heq⟩ := exists_value_of_ty_eq write.written _ hty
      exact ⟨value, by simpa [Graph.nodeTypedValue] using heq⟩

/-- Canonical node-typed projection of a supported policy write. -/
noncomputable def nodeValue [Fintype Player] {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G)
    (policies : CommitPolicyProfile G) (state : ReachableConfig G)
    (node : Fin G.nodeCount) (hready : Ready G state.1 node)
    (write : PolicyWrite state node)
    (hmem : write ∈ (policyValueLaw hwf hguards policies state node hready).support) :
    L.Val (G.nodeRow node).ty :=
  Classical.choose (exists_nodeValue hwf hguards policies state node hready write hmem)

theorem written_eq_nodeValue [Fintype Player] {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G)
    (policies : CommitPolicyProfile G) (state : ReachableConfig G)
    (node : Fin G.nodeCount) (hready : Ready G state.1 node)
    (write : PolicyWrite state node)
    (hmem : write ∈ (policyValueLaw hwf hguards policies state node hready).support) :
    write.written = G.nodeTypedValue node
      (nodeValue hwf hguards policies state node hready write hmem) :=
  Classical.choose_spec
    (exists_nodeValue hwf hguards policies state node hready write hmem)

/-- Choosing the node-typed witness on support and injecting it back into
`TypedValue` recovers exactly the original written-value marginal. -/
theorem map_nodeValue_bindOnSupport [Fintype Player] {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G)
    (policies : CommitPolicyProfile G) (state : ReachableConfig G)
    (node : Fin G.nodeCount) (hready : Ready G state.1 node) :
    ((policyValueLaw hwf hguards policies state node hready).bindOnSupport
      fun write hmem => FinDist.pure
        (nodeValue hwf hguards policies state node hready write hmem)).map
          (G.nodeTypedValue node) =
      (policyValueLaw hwf hguards policies state node hready).map
        PolicyWrite.written := by
  rw [FinDist.map_bindOnSupport]
  rw [FinDist.bindOnSupport_eq_bind_of_eq_on_support
    (g := fun write => FinDist.pure write.written)]
  · rw [FinDist.map_eq_bind]
  · intro write hmem
    simp [written_eq_nodeValue hwf hguards policies state node hready write hmem]

end PolicyWrite
end Vegas.EventGraph
