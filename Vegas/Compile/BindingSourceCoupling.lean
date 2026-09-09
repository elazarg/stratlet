/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.SourceExecution
import Vegas.Compile.ApplicationImageBindingInclusion
import Vegas.Compile.ApplicationImageStateRefinement
import Vegas.Compile.BindingImageController

/-! # Source continuations after opaque binding acceptance

An accepted generated binding completes one source commitment without
publishing its value.  The exact source successor and graph write remain
proof objects; the runtime sees only the canonical handle and freezes the
already prepared private value.
-/

noncomputable section

namespace Vegas.SourceDecisionSite

open EventGraph ToEventGraph Interaction GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- At an exact source-prefix checkpoint, the head commitment is graph-ready.
Completion refinement supplies the executable binding handler's unfinished
node and completed-prerequisite tests. -/
theorem binding_ready_at_source_prefix
    {Γ : VCtx P L} {name : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((name, .sealed who ty) :: Γ))
    (fresh : FreshBindings (.commit name who guard tail))
    (build : BuildState P L Γ)
    (current : CoupledAt
      (compileCore (.commit name who guard tail) fresh build).graph build)
    (done : Nat → Bool)
    (hcompleted : ∀ node : Fin
        (compileCore (.commit name who guard tail) fresh build).graph.nodeCount,
      done node.val = true ↔ node ∈ current.current.graph.1.done) :
    let site : SourceDecisionSite who (.commit name who guard tail) Γ name ty guard :=
      .here guard tail
    let node := site.compiledNode fresh build
    Ready (compileCore (.commit name who guard tail) fresh build).graph
        current.current.graph.1 node ∧
      done node.val = false ∧
      (site.bindingCode fresh build (site.compiledField fresh build)).requires.all done = true := by
  dsimp only
  let site : SourceDecisionSite who (.commit name who guard tail) Γ name ty guard :=
    .here guard tail
  let G := (compileCore (.commit name who guard tail) fresh build).graph
  let node := site.compiledNode fresh build
  have hnode : node.val = build.nodes.length := rfl
  have hready := current.current.nextReady current.completedPrefix node hnode
  have hdone (query : Fin G.nodeCount) : done query.val = true ↔
      query.val < build.nodes.length :=
    (hcompleted query).trans (current.completedPrefix query)
  have hnotDone : done node.val = false := by
    apply Bool.eq_false_iff.mpr
    intro htrue
    exact (Nat.lt_irrefl build.nodes.length) (hnode ▸ (hdone node).mp htrue)
  refine ⟨hready, hnotDone, ?_⟩
  apply List.all_eq_true.mpr
  intro prior hprior
  change prior ∈ G.messagePrerequisites node at hprior
  simp only [Graph.messagePrerequisites, List.mem_map, List.mem_filter,
    decide_eq_true_eq] at hprior
  obtain ⟨earlier, ⟨_, hearlier⟩, rfl⟩ := hprior
  exact (hcompleted earlier).mpr (hready.2 hearlier)

/-- A legal head commitment has the exact one-node source successor.  The
successor fixes both the extended source environment and the graph
configuration written by the primitive commit step. -/
theorem binding_source_successor
    {Γ : VCtx P L} {name : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((name, .sealed who ty) :: Γ))
    (fresh : FreshBindings (.commit name who guard tail))
    (build : BuildState P L Γ)
    (current : CoupledAt
      (compileCore (.commit name who guard tail) fresh build).graph build)
    (value : L.Val ty)
    (hlegal : evalGuard guard value
      ((current.current.source.toView who).eraseEnv) = true) :
    ∃ next : CoupledAt
        (compileCore (.commit name who guard tail) fresh build).graph
        (build.addCommitEvent name who guard fresh.1).1,
      next.current.source = current.current.source.cons value ∧
      next.current.graph.1 =
        current.current.graph.1.completeNode
          ((.here guard tail : SourceDecisionSite who
            (.commit name who guard tail) Γ name ty guard).compiledNode fresh build)
          ⟨ty, value⟩ := by
  let site : SourceDecisionSite who (.commit name who guard tail) Γ name ty guard :=
    .here guard tail
  let G := (compileCore (.commit name who guard tail) fresh build).graph
  let committed := (build.addCommitEvent name who guard fresh.1).1
  let node := site.compiledNode fresh build
  have hnode : node.val = build.nodes.length := rfl
  have hrow : G.nodes[node]? = some (build.commitEvent who guard) := by
    rcases decisionSite_compiledRow site fresh build with ⟨located, hlocated, hlocatedRow⟩
    have heq : located = node := by
      apply Fin.ext
      exact hlocated
    subst located
    exact hlocatedRow
  have htarget : G.nodeTarget node = build.nextField := by
    simp [G, Graph.nodeTarget, BuildResult.graph, compileCore_initialFields,
      hnode, BuildState.nextField, BuildState.nextNode]
  have hready := current.current.nextReady current.completedPrefix node hnode
  let step := build.sourceCommitStep who guard current.current.graph.1
    current.current.source current.current.agrees node hrow hready value hlegal
  let write : PolicyWrite current.current.graph node :=
    { written := ⟨ty, value⟩
      event := .commit who ⟨node, ⟨ty, value⟩⟩ step
      event_node := rfl
      supported := by
        change _ ∈ (stepCommit G current.current.graph.1 step).support
        simp only [stepCommit, step.written_eq_action, FinDist.mem_support_pure]
        rfl }
  let next := current.completeCons committed node hnode write value rfl htarget
    (BuildState.addCommitEvent_fieldOf_here build name who guard fresh.1)
    (BuildState.addCommitEvent_fieldOf_there build name who guard fresh.1)
    (by simp [committed])
  exact ⟨next, rfl, rfl⟩

/-- Actual inclusion of a canonical, prepared binding advances to the exact
legal source successor.  Handler readiness and absence of an earlier accepted
handle follow from the source-prefix coupling and native refinement. -/
theorem include_binding_source_coupling
    {Γ : VCtx P L} {name : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((name, .sealed who ty) :: Γ))
    (fresh : FreshBindings (.commit name who guard tail))
    (build : BuildState P L Γ)
    (current : CoupledAt
      (compileCore (.commit name who guard tail) fresh build).graph build)
    (image : ApplicationImage P L) (execution : image.application.State)
    (hrefines : execution.application.Refines current.current.graph.1)
    (address serial : Nat)
    (hcode : image.lookup address = some (.bind
      ((.here guard tail : SourceDecisionSite who
        (.commit name who guard tail) Γ name ty guard).bindingCode fresh build
          ((.here guard tail : SourceDecisionSite who
            (.commit name who guard tail) Γ name ty guard).compiledField fresh build))))
    (value : L.Val ty)
    (hprepared : execution.application.prepared.lookup
      (who, (.here guard tail : SourceDecisionSite who
        (.commit name who guard tail) Γ name ty guard).compiledField fresh build) =
          some ⟨ty, value⟩)
    (hlookup : execution.pool.lookup (who, serial) = some
      ⟨(who, serial), .binding address
        (who, (.here guard tail : SourceDecisionSite who
          (.commit name who guard tail) Γ name ty guard).compiledField fresh build)⟩)
    (hlegal : evalGuard guard value
      ((current.current.source.toView who).eraseEnv) = true) :
    ∃ next : CoupledAt
        (compileCore (.commit name who guard tail) fresh build).graph
        (build.addCommitEvent name who guard fresh.1).1,
      next.current.source = current.current.source.cons value ∧
      (image.application.includePending execution (who, serial)).application.Refines
          next.current.graph.1 ∧
      ApplicationImage.AcceptedSnapshot
        ((.here guard tail : SourceDecisionSite who
          (.commit name who guard tail) Γ name ty guard).compiledField fresh build)
        (who, (.here guard tail : SourceDecisionSite who
          (.commit name who guard tail) Γ name ty guard).compiledField fresh build)
        (some ⟨ty, value⟩)
        (image.application.includePending execution (who, serial)).application := by
  let site : SourceDecisionSite who (.commit name who guard tail) Γ name ty guard :=
    .here guard tail
  let G := (compileCore (.commit name who guard tail) fresh build).graph
  let node := site.compiledNode fresh build
  let field := site.compiledField fresh build
  let code := site.bindingCode fresh build field
  have hpreparedField : execution.application.prepared.lookup (who, field) =
      some ⟨ty, value⟩ := by
    simpa only [field, site] using hprepared
  have hreadyData := binding_ready_at_source_prefix guard tail fresh build current
    execution.application.memory.done hrefines.memory.completed
  have hready : Ready G current.current.graph.1 node := hreadyData.1
  have hnotDone : execution.application.memory.done code.node = false := hreadyData.2.1
  have hrequires : code.requires.all execution.application.memory.done = true :=
    hreadyData.2.2
  have hfield : code.sourceField = G.nodeTarget node := rfl
  have hsourceField : code.sourceField = field :=
    site.bindingCode_sourceField fresh build field
  have haccepted : execution.application.memory.accepted code.sourceField = none := by
    cases haccepted : execution.application.memory.accepted code.sourceField with
    | none => rfl
    | some handle =>
        obtain ⟨spec, stored, _, _, hstored, _⟩ :=
          hrefines.bindings code.sourceField handle haccepted
        have habsent := reachable_getAs_nodeTarget_eq_none hrefines.reachable node
          hready.1 spec.ty
        rw [hfield] at hstored
        rw [habsent] at hstored
        contradiction
  have hhandler : image.handle execution.application
      ⟨(who, serial), .binding address (who, field)⟩ =
        some (execution.application.bind code (who, field)) := by
    rw [image.handle_binding execution.application address code hcode
      (who, serial) (who, field)]
    rw [if_pos]
    exact ⟨rfl, rfl, haccepted, hnotDone, hrequires⟩
  have hincluded := image.include_accepted execution (who, serial)
    ⟨(who, serial), .binding address (who, field)⟩
    (execution.application.bind code (who, field)) hlookup hhandler
  obtain ⟨next, hsource, hgraph⟩ :=
    binding_source_successor guard tail fresh build current value hlegal
  have hrow : G.nodes[node]? = some (build.commitEvent who guard) := by
    rcases decisionSite_compiledRow site fresh build with ⟨located, hlocated, hlocatedRow⟩
    have heq : located = node := by
      apply Fin.ext
      exact hlocated
    subst located
    exact hlocatedRow
  let step := build.sourceCommitStep who guard current.current.graph.1
    current.current.source current.current.agrees node hrow hready value hlegal
  have hrefinesNext : (execution.application.bind code (who, field)).Refines
      (current.current.graph.1.completeNode node ⟨ty, value⟩) := by
    apply hrefines.bind (compileCore (.commit name who guard tail) fresh build).graphWF
      code node rfl hfield (who, field) rfl ⟨ty, value⟩ step
    intro recovered hrecovered
    rw [hprepared] at hrecovered
    simpa [TypedValue.as?] using hrecovered.symm
  refine ⟨next, hsource, ?_, ?_⟩
  · rw [hgraph, hincluded.1]
    exact hrefinesNext
  · rw [hincluded.1]
    constructor
    · change (execution.application.bind code (who, field)).memory.accepted field =
        some (who, field)
      simp [ApplicationImage.State.bind, hsourceField]
    · change (execution.application.bind code (who, field)).frozen field =
        some ⟨ty, value⟩
      simpa [ApplicationImage.State.bind, hsourceField] using hpreparedField

end Vegas.SourceDecisionSite

/-- info: 'Vegas.SourceDecisionSite.binding_ready_at_source_prefix' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceDecisionSite.binding_ready_at_source_prefix

/-- info: 'Vegas.SourceDecisionSite.binding_source_successor' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceDecisionSite.binding_source_successor

/-- info: 'Vegas.SourceDecisionSite.include_binding_source_coupling' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceDecisionSite.include_binding_source_coupling
