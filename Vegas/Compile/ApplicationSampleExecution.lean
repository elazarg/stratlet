/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationPlanCoverage
import Vegas.Compile.SampleImageRefinement
import Interaction.MessageApplicationPolicies

/-! # Source-coupled native chance phases

A native chance invocation samples the written source distribution and advances
the related source prefix with that same value. The law retains the complete
policy execution, including local histories and the native trace. The source
checkpoint is proof-only; neither the environment action nor the runtime
distribution evaluator receives its environment or a chosen random outcome.
-/

noncomputable section

namespace Vegas.ApplicationImage

open EventGraph Interaction Interaction.MessageApplication

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Reconstruct the full result of an environment sample from its kernel draw.
This is a proof-side reconstruction, not an action allowing the environment
to select the draw. `environmentPolicyStep` remains the execution semantics. -/
def sampleExecution (image : ApplicationImage P L)
    (execution : image.application.PolicyExecution) (code : SampleCode L)
    (value : L.Val code.dist.ty) : image.application.PolicyExecution :=
  { execution with
    native := { execution.native with application :=
      execution.native.application.sample code value }
    environmentHistory := execution.environmentHistory ++
      [⟨MessageApplication.State.environmentView image.application execution.native,
        .application (.sample code.node)⟩]
    nativeTrace := execution.nativeTrace ++ [.environment (.sample code.node)] }

end Vegas.ApplicationImage

namespace Vegas.ApplicationPlan

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- An actual sample phase has the source probability law on full native
executions. Every supported draw also advances the matching written source
prefix and preserves native refinement at that specific successor, rather
than merely providing some reachable graph witness. -/
theorem sample_phase_source_coupling
    {Γ : VCtx P L} {name : VarId} {ty : L.Ty}
    (dist : L.DistExpr (erasePubVCtx Γ) ty)
    (tail : VegasCore P L ((name, .pub ty) :: Γ))
    (fresh : FreshBindings (.sample name dist tail)) (state : BuildState P L Γ)
    (image : ApplicationImage P L)
    (hcode : image.lookup state.nodes.length = some (.sample (headSampleCode fresh state)))
    (current : CoupledAt (compileCore (.sample name dist tail) fresh state).graph state)
    (execution : image.application.PolicyExecution)
    (hrefines : execution.native.application.Refines current.current.graph.1) :
    image.application.environmentPolicyStep execution
        (.application (.sample state.nodes.length)) =
      (L.evalDist dist current.current.source.eraseSampleEnv).map
        (image.sampleExecution execution (headSampleCode fresh state)) ∧
    ∀ value, value ∈ (L.evalDist dist current.current.source.eraseSampleEnv).support →
      ∃ next : CoupledAt (compileCore (.sample name dist tail) fresh state).graph
          (state.addSampleEvent name dist fresh.1).1,
        next.current.source = current.current.source.cons value ∧
        ApplicationImage.State.Refines
          (image.sampleExecution execution (headSampleCode fresh state) value).native.application
          next.current.graph.1 := by
  let result := compileCore (.sample name dist tail) fresh state
  let event := state.sampleEvent dist
  have hprefix : state.nodes ++ [event] <+: result.nodes := by
    exact compileCore_nodes_prefix tail fresh.2 (state.addSampleEvent name dist fresh.1).1
  let located := compiledNext state result event hprefix
  let code := headSampleCode fresh state
  have hnode : code.node = located.node.val := located.index.symm
  have houtput : code.outputField = result.graph.nodeTarget located.node := by
    rw [headSampleCode_outputField, located.nodeTarget_eq (compileCore_initialFields _ fresh state)]
  have hrequiresCode : code.requires = result.graph.messagePrerequisites located.node :=
    headSampleCode_requires fresh state located.node located.index
  have hready := current.current.nextReady current.completedPrefix located.node located.index
  have hnotDone : execution.native.application.memory.done code.node = false := by
    apply Bool.eq_false_iff.mpr
    intro hdone
    apply hready.1
    exact (hrefines.memory.completed located.node).mp (hnode ▸ hdone)
  have hrequires : code.requires.all execution.native.application.memory.done = true := by
    rw [hrequiresCode]
    apply List.all_eq_true.mpr
    intro prior hprior
    simp only [Graph.messagePrerequisites, List.mem_map, List.mem_filter,
      decide_eq_true_eq] at hprior
    obtain ⟨node, ⟨_, hnodePrereq⟩, rfl⟩ := hprior
    exact (hrefines.memory.completed node).mpr (hready.2 hnodePrereq)
  obtain ⟨reads, hreads, _, hlaw, hstep⟩ := image.sample_law_refines
    execution.native.application current.current.graph.1 hrefines result.graphWF
    state.nodes.length code hcode located.node hnode houtput hrequiresCode
    event located.row rfl hnotDone hrequires
  have hsourceLaw : code.dist.eval reads =
      L.evalDist dist current.current.source.eraseSampleEnv :=
    eventDistOf_eval_eq_source state dist current.current.graph.1.store
      current.current.source current.current.agrees reads hreads
  constructor
  · simp only [MessageApplication.environmentPolicyStep, EnvironmentPolicyCommand.toAction,
      MessageApplication.advance, MessageApplication.step, FinDist.bind_map,
      FinDist.bind_bind]
    change (image.sample execution.native.application state.nodes.length).bind _ = _
    rw [hlaw, hsourceLaw, FinDist.bind_map, FinDist.map_eq_bind]
    apply FinDist.bind_congr
    intro value _
    simp only [FinDist.pure_bind]
    rfl
  · intro value hvalue
    have hdraw : value ∈ (code.dist.eval reads).support := by
      simpa only [hsourceLaw] using hvalue
    let step : InternalStep result.graph current.current.graph.1 ⟨located.node⟩ :=
      .sample event code.dist located.row rfl hready reads hreads
    let write : PolicyWrite current.current.graph located.node :=
      { written := ⟨ty, value⟩
        event := .internal ⟨located.node⟩ step
        event_node := rfl
        supported := by
          change current.current.graph.1.completeNode located.node ⟨ty, value⟩ ∈
            ((code.dist.eval reads).map fun chosen =>
              current.current.graph.1.completeNode located.node ⟨ty, chosen⟩).support
          rw [FinDist.support_map]
          exact ⟨value, hdraw, rfl⟩ }
    let next := current.completeCons (state.addSampleEvent name dist fresh.1).1
      located.node located.index write value rfl
      (located.nodeTarget_eq (compileCore_initialFields _ fresh state))
      (BuildState.addSampleEvent_fieldOf_here state name dist fresh.1)
      (BuildState.addSampleEvent_fieldOf_there state name dist fresh.1)
      (by simp)
    exact ⟨next, rfl, hstep value hdraw⟩

end Vegas.ApplicationPlan

/-- info: 'Vegas.ApplicationPlan.sample_phase_source_coupling' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.sample_phase_source_coupling
