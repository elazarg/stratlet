/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.SourcePolicy

/-! # Back-translating compiled commitment policies -/

noncomputable section

namespace Vegas.ToEventGraph

open EventGraph GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

private def sourceSiteNode {Γ Δ : VCtx P L} {prog : VegasCore P L Γ}
    {who : P} {name : VarId} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    (site : SourceDecisionSite who prog Δ name ty guard)
    (fresh : FreshBindings prog) (state : BuildState P L Γ) :
    Fin (compileCore prog fresh state).graph.nodeCount :=
  Classical.choose (decisionSite_compiledRow site fresh state)

private theorem sourceSiteNode_spec {Γ Δ : VCtx P L} {prog : VegasCore P L Γ}
    {who : P} {name : VarId} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    (site : SourceDecisionSite who prog Δ name ty guard)
    (fresh : FreshBindings prog) (state : BuildState P L Γ) :
    ((sourceSiteNode site fresh state : Nat) =
        (decisionSiteState site fresh state).nodes.length) ∧
      (compileCore prog fresh state).graph.nodes[sourceSiteNode site fresh state]? =
        some ((decisionSiteState site fresh state).commitEvent who guard) :=
  Classical.choose_spec (decisionSite_compiledRow site fresh state)

/-- Back-translate every kernel of one compiled player's commitment policy to
the corresponding structural source decision. -/
def backtranslateCommitPolicy (program : GraphProgram P L) (who : P)
    (policy : CommitPolicy (compile program).graph who) :
    SourceBehavioralPolicy program.prog who := by
  intro Δ name ty guard site visible
  let state := BuildState.fromInitial
    (initialState program.Γ program.env program.wctx)
  let siteState := decisionSiteState site program.fresh state
  let node := sourceSiteNode site program.fresh state
  have hrow := (sourceSiteNode_spec site program.fresh state).2
  have hrowEq := Option.some.inj
    (((compile program).graph.nodes_get?_nodeRow node).symm.trans hrow)
  have hsem : ((compile program).graph.nodeRow node).sem =
      .commit who (eventGuardOf siteState who guard) := by
    exact congrArg EventNode.sem hrowEq
  exact backtranslateSourceDecision siteState who guard
    (decisionSiteState_fieldOfNameInjective site program.fresh state
      (BuildState.fromInitial_fieldOfNameInjective
        (initialState program.Γ program.env program.wctx)
        (initialState_fieldOfNameInjective program.env program.wctx)))
    (fun reads => policy node (eventGuardOf siteState who guard) hsem reads) visible

/-- Compiling the playerwise source back-translation recovers the original
compiled commitment policy at every node and declared-read environment. -/
theorem compile_backtranslateCommitPolicy (program : GraphProgram P L) (who : P)
    (policy : CommitPolicy (compile program).graph who) :
    compileSourcePolicy program.prog program.fresh
      (BuildState.fromInitial (initialState program.Γ program.env program.wctx))
      rfl who (backtranslateCommitPolicy program who policy) = policy := by
  classical
  funext node graphGuard hsem reads
  let state := BuildState.fromInitial
    (initialState program.Γ program.env program.wctx)
  let result := compileCore program.prog program.fresh state
  have hcovered := compileCore_commitNode_covered program.prog program.fresh state node
    (by simp [state])
    ⟨result.graph.nodeRow node, who, graphGuard,
      result.graph.nodes_get?_nodeRow node, hsem⟩
  obtain ⟨actor, Δ, name, ty, sourceGuard, site, hindex, hrow⟩ := hcovered
  have hrowEq := Option.some.inj
    ((result.graph.nodes_get?_nodeRow node).symm.trans hrow)
  have hcommit : NodeSem.commit who graphGuard =
      NodeSem.commit actor
        (eventGuardOf (decisionSiteState site program.fresh state) actor sourceGuard) :=
    hsem.symm.trans (congrArg EventNode.sem hrowEq)
  have hactor := (NodeSem.commit.inj hcommit).1
  subst actor
  have hguard := (NodeSem.commit.inj hcommit).2
  subst graphGuard
  have hsiteNode : sourceSiteNode site program.fresh state = node := by
    apply Fin.ext
    exact (sourceSiteNode_spec site program.fresh state).1.trans hindex.symm
  rw [compileSourcePolicy_at program.prog program.fresh state rfl who
    (backtranslateCommitPolicy program who policy) sourceGuard site node hindex hrow hsem reads]
  have hinjective : FieldOfNameInjective
      (decisionSiteState site program.fresh state).fieldOf :=
    decisionSiteState_fieldOfNameInjective site program.fresh state
      (BuildState.fromInitial_fieldOfNameInjective
        (initialState program.Γ program.env program.wctx)
        (initialState_fieldOfNameInjective program.env program.wctx))
  change compileSourceDecision (decisionSiteState site program.fresh state) who
    sourceGuard
    (backtranslateSourceDecision (decisionSiteState site program.fresh state)
      who sourceGuard hinjective
      (fun input => policy (sourceSiteNode site program.fresh state)
        (eventGuardOf (decisionSiteState site program.fresh state)
          who sourceGuard) _ input)) reads = _
  rw [compile_backtranslateSourceDecision]
  subst node
  rfl

end Vegas.ToEventGraph
