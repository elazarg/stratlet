/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.DecisionSite
import Vegas.Compile.SourceLaw
import Vegas.EventGraph.KernelPolicy

/-! # Compiling source policies to declared-read graph kernels

Each compiled commitment is assigned its structural source decision policy.
The construction is playerwise: compiling one policy does not inspect the
policies of its opponents.
-/

noncomputable section

namespace Vegas.ToEventGraph

open EventGraph GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Source instruction positions agree with the compiler's append-only node
allocation, including when the compiler starts with a nonempty prefix. -/
theorem decisionSiteState_nodes_length {who : P} {Γ Δ : VCtx P L}
    {prog : VegasCore P L Γ} {x : VarId} {ty : L.Ty}
    {guard : L.Expr ((x, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    (site : SourceDecisionSite who prog Δ x ty guard)
    (fresh : FreshBindings prog) (state : BuildState P L Γ) :
    (decisionSiteState site fresh state).nodes.length = state.nodes.length + site.depth := by
  induction site with
  | here => simp [decisionSiteState, SourceDecisionSite.depth]
  | sample site ih =>
      rw [decisionSiteState, ih fresh.2]
      simp [SourceDecisionSite.depth, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  | commit site ih =>
      rw [decisionSiteState, ih fresh.2]
      simp [SourceDecisionSite.depth, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  | reveal site ih =>
      rw [decisionSiteState, ih fresh.2]
      simp [SourceDecisionSite.depth, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- A typed source occurrence assigned to one actual compiled commitment row. -/
private structure DecisionAt {Γ : VCtx P L} (prog : VegasCore P L Γ)
    (fresh : FreshBindings prog) (state : BuildState P L Γ)
    (who : P) (node : Fin (compileCore prog fresh state).graph.nodeCount) where
  ctx : VCtx P L
  name : VarId
  ty : L.Ty
  guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who ctx)) L.bool
  site : SourceDecisionSite who prog ctx name ty guard
  index : (node : Nat) = (decisionSiteState site fresh state).nodes.length
  row : (compileCore prog fresh state).graph.nodes[node]? =
    some ((decisionSiteState site fresh state).commitEvent who guard)

private theorem DecisionAt.unique {Γ : VCtx P L} {prog : VegasCore P L Γ}
    {fresh : FreshBindings prog} {state : BuildState P L Γ}
    {who : P} {node : Fin (compileCore prog fresh state).graph.nodeCount}
    (first second : DecisionAt prog fresh state who node) : first = second := by
  have hdepth : first.site.depth = second.site.depth := by
    have h := first.index.symm.trans second.index
    rw [decisionSiteState_nodes_length, decisionSiteState_nodes_length] at h
    exact Nat.add_left_cancel h
  obtain ⟨hctx, hname, hty, hguard, hsite⟩ :=
    first.site.indices_eq_of_depth_eq second.site hdepth
  cases first
  cases second
  dsimp only at hctx hname hty hguard hsite
  cases hctx
  cases hname
  cases hty
  cases eq_of_heq hguard
  cases eq_of_heq hsite
  rfl

private def DecisionAt.law {Γ : VCtx P L} {prog : VegasCore P L Γ}
    {fresh : FreshBindings prog} {state : BuildState P L Γ}
    {who : P} {node : Fin (compileCore prog fresh state).graph.nodeCount}
    (decision : DecisionAt prog fresh state who node)
    (policy : {Δ : VCtx P L} → {x : VarId} → {b : L.Ty} →
      {guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Δ)) L.bool} →
      (site : SourceDecisionSite who prog Δ x b guard) →
      (visible : Env L.Val (eraseVCtx (viewVCtx who Δ))) →
        FinDist {value : L.Val b // evalGuard guard value visible = true}) :
    (input : ReadEnv L
      (eventGuardOf (decisionSiteState decision.site fresh state)
        who decision.guard).choiceReads) →
      FinDist {value : L.Val
          (eventGuardOf (decisionSiteState decision.site fresh state)
            who decision.guard).ty //
        (eventGuardOf (decisionSiteState decision.site fresh state)
          who decision.guard).eval value input = true} :=
  compileSourceDecision (decisionSiteState decision.site fresh state)
    who decision.guard (policy decision.site)

private theorem DecisionAt.law_transport_external {Γ : VCtx P L}
    {prog : VegasCore P L Γ} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} {who : P}
    {node : Fin (compileCore prog fresh state).graph.nodeCount}
    (first second : DecisionAt prog fresh state who node)
    (hdecision : first = second)
    (policy : {Δ : VCtx P L} → {x : VarId} → {b : L.Ty} →
      {guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Δ)) L.bool} →
      (site : SourceDecisionSite who prog Δ x b guard) →
      (visible : Env L.Val (eraseVCtx (viewVCtx who Δ))) →
        FinDist {value : L.Val b // evalGuard guard value visible = true})
    (external : EventGuard L)
    (hfirst : external = eventGuardOf
      (decisionSiteState first.site fresh state) who first.guard)
    (hsecond : external = eventGuardOf
      (decisionSiteState second.site fresh state) who second.guard)
    (reads : ReadEnv L external.choiceReads) :
    (hfirst.symm ▸ first.law policy) reads =
      (hsecond.symm ▸ second.law policy) reads := by
  subst second
  have heq : hfirst = hsecond := Subsingleton.elim _ _
  subst hsecond
  rfl

/-- Recover the unique source occurrence of a commitment emitted by a compiler
started with initial fields but no previous events. -/
private def locateDecision {Γ : VCtx P L} (prog : VegasCore P L Γ)
    (fresh : FreshBindings prog) (state : BuildState P L Γ)
    (hempty : state.nodes = []) (who : P)
    (node : Fin (compileCore prog fresh state).graph.nodeCount)
    (guard : EventGuard L)
    (hsem : ((compileCore prog fresh state).graph.nodeRow node).sem = .commit who guard) :
    DecisionAt prog fresh state who node := by
  classical
  have hcovered := compileCore_commitNode_covered prog fresh state node
    (by simp [hempty])
    ⟨_, who, guard, (compileCore prog fresh state).graph.nodes_get?_nodeRow node, hsem⟩
  choose actor ctx name ty sourceGuard site hindex hrow using hcovered
  have hrowEq := Option.some.inj
    (((compileCore prog fresh state).graph.nodes_get?_nodeRow node).symm.trans hrow)
  have hcommit : NodeSem.commit who guard =
      NodeSem.commit actor (eventGuardOf (decisionSiteState site fresh state) actor sourceGuard) :=
    hsem.symm.trans (congrArg EventNode.sem hrowEq)
  have hactor := (NodeSem.commit.inj hcommit).1
  subst actor
  exact ⟨ctx, name, ty, sourceGuard, site, hindex, hrow⟩

/-- Compile a source player's complete policy into guarded kernels at every
commitment owned by that player. The initial compiler state has no events;
initial source bindings are allowed. -/
def compileSourcePolicy {Γ : VCtx P L} (prog : VegasCore P L Γ)
    (fresh : FreshBindings prog) (state : BuildState P L Γ)
    (hempty : state.nodes = []) (who : P)
    (policy : SourceBehavioralPolicy prog who) :
    CommitPolicy (compileCore prog fresh state).graph who := by
  classical
  intro node guard hsem reads
  let decision := locateDecision prog fresh state hempty who node guard hsem
  have hrowEq := Option.some.inj
    (((compileCore prog fresh state).graph.nodes_get?_nodeRow node).symm.trans decision.row)
  have hcommit : NodeSem.commit who guard =
      NodeSem.commit who
        (eventGuardOf (decisionSiteState decision.site fresh state) who decision.guard) :=
    hsem.symm.trans (congrArg EventNode.sem hrowEq)
  have hguard := (NodeSem.commit.inj hcommit).2
  let translated : (input : ReadEnv L guard.choiceReads) →
      FinDist {value : L.Val guard.ty // guard.eval value input = true} :=
    hguard.symm ▸ decision.law policy
  exact translated reads

/-- The policy at a specified compiled source occurrence is exactly its source
decision kernel, including the guard evidence carried by the graph action. -/
theorem compileSourcePolicy_at {Γ Δ : VCtx P L} (prog : VegasCore P L Γ)
    (fresh : FreshBindings prog) (state : BuildState P L Γ)
    (hempty : state.nodes = []) (who : P)
    (policy : {Δ : VCtx P L} → {x : VarId} → {b : L.Ty} →
      {guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Δ)) L.bool} →
      (site : SourceDecisionSite who prog Δ x b guard) →
      (visible : Env L.Val (eraseVCtx (viewVCtx who Δ))) →
        FinDist {value : L.Val b // evalGuard guard value visible = true})
    {name : VarId} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool)
    (site : SourceDecisionSite who prog Δ name ty guard)
    (node : Fin (compileCore prog fresh state).graph.nodeCount)
    (hindex : (node : Nat) = (decisionSiteState site fresh state).nodes.length)
    (hrow : (compileCore prog fresh state).graph.nodes[node]? =
      some ((decisionSiteState site fresh state).commitEvent who guard))
    (hsem : ((compileCore prog fresh state).graph.nodeRow node).sem =
      .commit who (eventGuardOf (decisionSiteState site fresh state) who guard))
    (reads : ReadEnv L (eventGuardOf (decisionSiteState site fresh state) who guard).choiceReads) :
    compileSourcePolicy prog fresh state hempty who policy node
        (eventGuardOf (decisionSiteState site fresh state) who guard) hsem reads =
      compileSourceDecision (decisionSiteState site fresh state) who guard (policy site) reads := by
  have hdecision := DecisionAt.unique
    (locateDecision prog fresh state hempty who node _ hsem)
    (⟨Δ, name, ty, guard, site, hindex, hrow⟩ : DecisionAt prog fresh state who node)
  let first := locateDecision prog fresh state hempty who node _ hsem
  have hrowEq := Option.some.inj
    (((compileCore prog fresh state).graph.nodes_get?_nodeRow node).symm.trans
      first.row)
  have hcommit : NodeSem.commit who _ = NodeSem.commit who
      (eventGuardOf (decisionSiteState first.site fresh state) who first.guard) :=
    hsem.symm.trans (congrArg EventNode.sem hrowEq)
  have hguard := (NodeSem.commit.inj hcommit).2
  unfold compileSourcePolicy
  change (hguard.symm ▸ first.law policy) reads = _
  exact DecisionAt.law_transport_external
    first
    (⟨Δ, name, ty, guard, site, hindex, hrow⟩ : DecisionAt prog fresh state who node)
    hdecision policy _ hguard rfl reads

end Vegas.ToEventGraph
