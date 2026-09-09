/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationSampleExecution
import VegasTests.ApplicationImage

/-! # Native chance law and source-continuation regression

The existing sample-only compilation fixture runs through the shared policy
runner. Its source law and continuation refinement come from the general
phase-coupling theorem, rather than evaluation of a second source runner.
-/

noncomputable section

namespace VegasTests.ApplicationSampleExecution

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction
  Interaction.MessageApplication GameTheory.Math.Probability
open VegasTests.ApplicationImage (sampleCore sampleFresh sampleState samplePlan)

def image := samplePlan.image (fun _ => 0)

def checkpoint : CoupledAt (compileCore sampleCore sampleFresh sampleState).graph sampleState :=
  initialCoupledAt sampleState (VEnv.empty simpleExpr) (by
    intro name bindTy binding
    cases binding) rfl

def initial : image.application.PolicyExecution :=
  PolicyExecution.initial image.application
    (MessageApplication.State.initial image.application
      (Vegas.ApplicationImage.State.initial
        (Vegas.ApplicationImage.Memory.initial
          (compileCore sampleCore sampleFresh sampleState).graph)))

def service : image.application.EnvironmentPolicy :=
  fun _ _ => FinDist.pure (.application (.sample 0))

theorem sample_source_law (players : Fin 2 → image.application.PlayerPolicy) :
    image.application.runPolicies players service [.environment] initial =
      fairCoin.denote.map
        (image.sampleExecution initial
          (ApplicationPlan.headSampleCode sampleFresh sampleState)) := by
  have hphase := ApplicationPlan.sample_phase_source_coupling (P := Fin 2) (L := simpleExpr)
    (.weighted (b := .bool) fairCoin) (.ret []) sampleFresh sampleState image
    (by rfl) checkpoint initial
    (Vegas.ApplicationImage.State.initial_refines _)
  have hlaw : image.application.environmentPolicyStep initial (.application (.sample 0)) =
      fairCoin.denote.map
        (image.sampleExecution initial (ApplicationPlan.headSampleCode sampleFresh sampleState)) :=
    hphase.1
  simpa only [MessageApplication.runPolicies, MessageApplication.invoke, service,
    FinDist.pure_bind, FinDist.bind_pure] using hlaw

/-- Every supported native draw extends the actual source environment by that
same draw and refines the corresponding successor, with the prefix advanced. -/
theorem sample_source_successor (value : Bool) (hvalue : value ∈ fairCoin.denote.support) :
    ∃ next : CoupledAt (compileCore sampleCore sampleFresh sampleState).graph
        (sampleState.addSampleEvent 0 (.weighted (b := .bool) fairCoin) sampleFresh.1).1,
      next.current.source = (VEnv.empty simpleExpr).cons value ∧
      Vegas.ApplicationImage.State.Refines
        (image.sampleExecution initial
          (ApplicationPlan.headSampleCode sampleFresh sampleState) value).native.application
        next.current.graph.1 := by
  exact (ApplicationPlan.sample_phase_source_coupling (P := Fin 2) (L := simpleExpr)
    (.weighted (b := .bool) fairCoin) (.ret []) sampleFresh sampleState image
    (by rfl) checkpoint initial
    (Vegas.ApplicationImage.State.initial_refines _)).2 value hvalue

end VegasTests.ApplicationSampleExecution

/-- info: 'VegasTests.ApplicationSampleExecution.sample_source_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ApplicationSampleExecution.sample_source_law

/-- info: 'VegasTests.ApplicationSampleExecution.sample_source_successor' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ApplicationSampleExecution.sample_source_successor
