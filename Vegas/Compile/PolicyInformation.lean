/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.SourceInformation
import Vegas.EventGraph.PolicyLocalization

/-! # Information locality of compiled commitment policies -/

noncomputable section

namespace Vegas.ToEventGraph

open EventGraph GameTheory.Protocol

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

/-- In a compiled source program, the declared reads of a ready commitment
determine the player's complete perfect-recall information. -/
theorem compiled_commitInformationLocal (program : GraphProgram P L)
    (legal : Legal program.prog) :
    CommitInformationLocal (compile program).graph (compile program).graphWF
      (compile_guardLive program legal) := by
  classical
  intro who node graphGuard hsem reads left right first second
    hactiveLeft hactiveRight hreadyLeft hreadyRight hreadsLeft hreadsRight
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
  have hvisible := decisionSite_visibleStoreEq program who site left.2 right.2
    hindex hreadyLeft hreadyRight (by
      intro ref href
      rw [ReadEnv.ofStore?_read hreadsLeft href,
        ReadEnv.ofStore?_read hreadsRight href])
  have hlength := trace_length_eq_of_readyCommitNode (compile program).graphWF
    (compile_guardLive program legal) who node first second hreadyLeft hreadyRight
      hactiveLeft hactiveRight
  exact infoOf_eq_of_length_eq_of_visibleStoreEq (compile program).graphWF
    (compile_guardLive program legal) who first second hlength hvisible

end Vegas.ToEventGraph
