/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.SourceExecution
import Vegas.Compile.PublicationStateRefinement

/-! # Source continuations after public-choice publication

A generated publication advances both adjacent source instructions. Its
successor retains the exact source environment and completed compiler prefix,
so the next source instruction can use the same native refinement relation.
These witnesses are proof data, not inputs to the public handler or a player.
-/

noncomputable section

namespace Vegas.PublicChoiceSite

open EventGraph ToEventGraph Interaction GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- At a source-order checkpoint, both adjacent nodes are unfinished and all
external publication prerequisites are complete. The native readiness test
therefore follows from completion refinement, including reveal-only dependencies. -/
theorem ready_at_source_prefix
    {Γ : VCtx P L} {name publicName : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ))
    (fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail)))
    (build : BuildState P L Γ)
    (current : CoupledAt
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh build).graph build)
    (done : Nat → Bool)
    (hcompleted : ∀ node : Fin
        (compileCore (.commit name who guard (.reveal publicName who name .here tail))
          fresh build).graph.nodeCount,
      done node.val = true ↔ node ∈ current.current.graph.1.done) :
    ((atHead name publicName who guard tail).runtimeSite fresh build).ready done = true := by
  let site := atHead name publicName who guard tail
  let G := (compileCore (.commit name who guard (.reveal publicName who name .here tail))
    fresh build).graph
  let choice := site.choiceNode fresh build
  let publication := site.publicationNode fresh build
  have hchoice : choice.val = build.nodes.length := rfl
  have hpublication : publication.val = build.nodes.length + 1 := rfl
  have hdone (node : Fin G.nodeCount) : done node.val = true ↔
      node.val < build.nodes.length := (hcompleted node).trans (current.completedPrefix node)
  have hunfinished (node : Fin G.nodeCount) (hnode : build.nodes.length ≤ node.val) :
      done node.val = false := by
    apply Bool.eq_false_iff.mpr
    intro htrue
    exact (Nat.not_lt_of_ge hnode) ((hdone node).mp htrue)
  change (!done choice.val && !done publication.val &&
    (G.publicationPrerequisites choice publication).all done) = true
  rw [hunfinished choice (by omega), hunfinished publication (by omega)]
  simp only [Bool.not_false, Bool.true_and]
  apply List.all_eq_true.mpr
  intro prior hprior
  simp only [Graph.publicationPrerequisites, List.mem_filter, List.mem_append,
    bne_iff_ne] at hprior
  obtain ⟨hprior, hne⟩ := hprior
  have hmember : ∃ node : Fin G.nodeCount,
      prior ∈ G.messagePrerequisites node ∧ node.val ≤ build.nodes.length + 1 := by
    rcases hprior with hprior | hprior
    · exact ⟨choice, hprior, by omega⟩
    · exact ⟨publication, hprior, by omega⟩
  obtain ⟨node, hmember, hbound⟩ := hmember
  simp only [Graph.messagePrerequisites, List.mem_map, List.mem_filter,
    decide_eq_true_eq] at hmember
  obtain ⟨earlier, ⟨_, hearlier⟩, rfl⟩ := hmember
  apply (hdone earlier).mpr
  have hlt := G.prereq_lt hearlier
  omega

/-- Complete an adjacent source choice/reveal pair with the chosen legal value.
Both writes use the primitive graph semantics; the result fixes the source
continuation as well as the exact completed graph configuration. -/
theorem source_successor
    {Γ : VCtx P L} {name publicName : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ))
    (fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail)))
    (build : BuildState P L Γ)
    (current : CoupledAt
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh build).graph build)
    (value : L.Val ty)
    (hlegal : evalGuard guard value ((current.current.source.toView who).eraseEnv) = true) :
    ∃ next : CoupledAt
        (compileCore (.commit name who guard (.reveal publicName who name .here tail))
          fresh build).graph
        (((build.addCommitEvent name who guard fresh.1).1).addRevealEvent
          publicName who .here fresh.2.1).1,
      next.current.source = (current.current.source.cons value).cons value ∧
      next.current.graph.1 =
        (atHead name publicName who guard tail).completePublication fresh build
          current.current.graph.1 value := by
  let site := atHead name publicName who guard tail
  let G := (compileCore (.commit name who guard (.reveal publicName who name .here tail))
    fresh build).graph
  let committed := (build.addCommitEvent name who guard fresh.1).1
  let revealed := (committed.addRevealEvent publicName who .here fresh.2.1).1
  let choice := site.choiceNode fresh build
  let publication := site.publicationNode fresh build
  have hchoice : choice.val = build.nodes.length := rfl
  have hpublication : publication.val = committed.nodes.length := by
    simp [publication, site, atHead, siteState, decisionSiteState, committed]
  have htargetChoice : G.nodeTarget choice = build.nextField := by
    simp [G, Graph.nodeTarget, BuildResult.graph, compileCore_initialFields,
      hchoice, BuildState.nextField, BuildState.nextNode]
  have htargetPublication : G.nodeTarget publication = committed.nextField := by
    simp [G, Graph.nodeTarget, BuildResult.graph, compileCore_initialFields,
      hpublication, committed, BuildState.nextField, BuildState.nextNode]
  have hready := current.current.nextReady current.completedPrefix choice hchoice
  let step := build.sourceCommitStep who guard current.current.graph.1
    current.current.source current.current.agrees choice (site.choiceNode_row fresh build)
    hready value hlegal
  let write : PolicyWrite current.current.graph choice :=
    { written := ⟨ty, value⟩
      event := .commit who ⟨choice, ⟨ty, value⟩⟩ step
      event_node := rfl
      supported := by
        change _ ∈ (stepCommit G current.current.graph.1 step).support
        simp only [stepCommit, step.written_eq_action, FinDist.mem_support_pure]
        rfl }
  let middle := current.completeCons committed choice hchoice write value rfl htargetChoice
    (BuildState.addCommitEvent_fieldOf_here build name who guard fresh.1)
    (BuildState.addCommitEvent_fieldOf_there build name who guard fresh.1) (by simp [committed])
  have hreadyPublication :=
    middle.current.nextReady middle.completedPrefix publication hpublication
  let revealStep : InternalStep G middle.current.graph.1 ⟨publication⟩ :=
    .reveal (committed.revealEvent who .here) (committed.fieldOf .here)
      (site.publicationNode_row fresh build) rfl hreadyPublication value
      (middle.current.agrees .here)
  let revealWrite : PolicyWrite middle.current.graph publication :=
    { written := ⟨ty, value⟩
      event := .internal ⟨publication⟩ revealStep
      event_node := rfl
      supported := FinDist.mem_support_pure.mpr rfl }
  let next := middle.completeCons revealed publication hpublication revealWrite value rfl
    htargetPublication
    (BuildState.addRevealEvent_fieldOf_here committed publicName who .here fresh.2.1)
    (BuildState.addRevealEvent_fieldOf_there committed publicName who .here fresh.2.1)
    (by simp [revealed])
  exact ⟨next, rfl, rfl⟩

/-- Actual inclusion of a legal source choice preserves its matching source
continuation. Refinement supplies public-store agreement; the generated guard
and handler establish acceptance, without an assumed successful resolution. -/
theorem include_source_coupling
    {Γ : VCtx P L} {name publicName : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ))
    (fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail)))
    (build : BuildState P L Γ)
    (current : CoupledAt
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh build).graph build)
    (image : ApplicationImage P L) (execution : image.application.State)
    (hrefines : execution.application.Refines current.current.graph.1)
    (heligible : (atHead name publicName who guard tail).PubliclyValidatable fresh build)
    (address serial : Nat)
    (hcode : image.lookup address =
      some (.publicChoice ((atHead name publicName who guard tail).code fresh build)))
    (value : L.Val ty)
    (hlookup : execution.pool.lookup (who, serial) =
      some ⟨(who, serial), .choice address ⟨ty, value⟩⟩)
    (hlegal : evalGuard guard value ((current.current.source.toView who).eraseEnv) = true) :
    ∃ next : CoupledAt
        (compileCore (.commit name who guard (.reveal publicName who name .here tail))
          fresh build).graph
        (((build.addCommitEvent name who guard fresh.1).1).addRevealEvent
          publicName who .here fresh.2.1).1,
      next.current.source = (current.current.source.cons value).cons value ∧
      (image.application.includePending execution (who, serial)).application.Refines
        next.current.graph.1 := by
  let site := atHead name publicName who guard tail
  have hready := ready_at_source_prefix guard tail fresh build current
    execution.application.memory.done hrefines.memory.completed
  obtain ⟨next, hsource, hgraph⟩ := source_successor guard tail fresh build current value hlegal
  have hresolve := (site.code_resolves_iff_source_legal fresh build
    current.current.graph.1.store execution.application.memory.store current.current.source
    heligible current.current.agrees hrefines.memory.publicFields
    execution.application.memory.done hready serial value).mpr hlegal
  have hincluded := image.include_source_choice site fresh build current.current.graph.1.store
    current.current.source execution heligible current.current.agrees
    hrefines.memory.publicFields hready address serial hcode value hlookup hlegal
  refine ⟨next, hsource, ?_⟩
  rw [hgraph]
  have hstate : (image.application.includePending execution (who, serial)).application =
      execution.application.publish (site.code fresh build) value := hincluded.1
  exact hstate.symm ▸ site.resolution_refines fresh build execution.application
    current.current.graph.1 hrefines heligible ⟨(who, serial), value⟩ value hresolve

end Vegas.PublicChoiceSite

/-- info: 'Vegas.PublicChoiceSite.ready_at_source_prefix' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.PublicChoiceSite.ready_at_source_prefix

/-- info: 'Vegas.PublicChoiceSite.source_successor' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.PublicChoiceSite.source_successor

/-- info: 'Vegas.PublicChoiceSite.include_source_coupling' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.PublicChoiceSite.include_source_coupling
