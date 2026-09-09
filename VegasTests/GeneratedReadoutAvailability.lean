/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationPlanRefinement
import Vegas.Compile.SourceReadoutAvailability
import VegasTests.GeneratedApplicationPolicy

/-! # Generated readout availability at a real conditional checkpoint

The actual lifted persistent-disclosure prefix reaches its first conditional
decision after the public chance event. Graph readiness, whole-run coverage,
and typed binding provenance then discharge executable owner-readout success
through the general application-plan theorem.
-/

noncomputable section

namespace VegasTests.GeneratedReadoutAvailability

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction
  Interaction.MessageApplication GameTheory.Math.Probability
open VegasTests.PersistentDisclosure
open VegasTests.GeneratedPersistentDisclosure
open VegasTests.GeneratedBindingPolicy (initial)
open VegasTests.GeneratedApplicationPolicy

def firstConditionalSite : SourceDecisionSite (P := TestPlayer) (L := simpleExpr)
    0 source.prog FirstContext 4 (.option .bool) firstGuard :=
  .commit (.commit (.reveal (.sample (.here _ _))))

@[simp] theorem firstConditionalSite_node :
    (firstConditionalSite.compiledNode source.fresh compilerInitial).val = 4 := rfl

private abbrev prefixSchedule : List (@Invocation TestPlayer) :=
  [.player 0, .player 0, .environment, .player 0, .environment, .environment]

private theorem firstConditional_ready
    (secret signal : Bool)
    (cfg : Config GeneratedPersistentDisclosure.compiled.graph)
    (hrefines : (afterChance secret signal).native.application.Refines cfg) :
    Ready GeneratedPersistentDisclosure.compiled.graph cfg
      (firstConditionalSite.compiledNode source.fresh compilerInitial) := by
  constructor
  · intro hdone
    have hnative := hrefines.memory.completed
      (firstConditionalSite.compiledNode source.fresh compilerInitial) |>.mpr hdone
    change false = true at hnative
    contradiction
  · intro prior hprior
    apply (hrefines.memory.completed prior).mp
    have hlt := GeneratedPersistentDisclosure.compiled.graph.prereq_lt hprior
    rw [firstConditionalSite_node] at hlt
    have hpriorCases :
        prior.val = 0 ∨ prior.val = 1 ∨ prior.val = 2 ∨ prior.val = 3 := by
      omega
    rcases hpriorCases with hzero | hone | htwo | hthree
    · rw [hzero]
      rfl
    · rw [hone]
      rfl
    · rw [htwo]
      rfl
    · rw [hthree]
      rfl

/-- Every supported result of the real binding/marker/chance prefix has an
actual executable owner readout for the first conditional source decision.
The hidden earlier binding is recovered from authenticated local history, not
from the public observation. -/
theorem first_conditional_readout_available
    (profile : SourceBehavioralProfile source.prog)
    (next : image.application.PolicyExecution)
    (hnext : next ∈ (image.application.runPolicies
      (applicationPlan.liftProfile (fun _ => 10) profile) service
      prefixSchedule initial).support) :
    ∃ reads : ReadEnv simpleExpr
        (eventGuardOf
          (decisionSiteState firstConditionalSite source.fresh compilerInitial)
          0 firstGuard).choiceReads,
      image.ownerReadout? 0
          (eventGuardOf
            (decisionSiteState firstConditionalSite source.fresh compilerInitial)
            0 firstGuard).choiceReads
          (next.principalHistory 0)
          (MessageApplication.State.observe image.application next.native 0) = some reads := by
  obtain ⟨cfg, hrefines⟩ := applicationPlan.runPolicies_refines
    (fun _ => 10) source.env legal
    (applicationPlan.liftProfile (fun _ => 10) profile) service prefixSchedule
    initial next (by
      refine ⟨Config.initial GeneratedPersistentDisclosure.compiled.graph, ?_⟩
      exact ApplicationImage.State.initial_refines
        GeneratedPersistentDisclosure.compiled.graph) hnext
  have hshape := hnext
  rw [through_chance_law] at hshape
  simp only [FinDist.support_bind, Set.mem_iUnion] at hshape
  obtain ⟨secret, _, hshape⟩ := hshape
  simp only [FinDist.support_map, Set.mem_image] at hshape
  obtain ⟨signal, _, rfl⟩ := hshape
  apply applicationPlan.runPolicies_ownerReadout?_of_ready
    (fun _ => 10) profile 0
    (applicationPlan.liftProfile (fun _ => 10) profile) rfl service
    prefixSchedule (afterChance secret signal) hnext firstConditionalSite cfg hrefines
  · exact firstConditional_ready secret signal cfg hrefines
  · intro ref href spec hfield value hsource
    have hinitialFields :
        (compileCore core source.fresh compilerInitial).graph.initialFields.length = 0 := by
      change (compileCore core source.fresh compilerInitial).initialFields.length = 0
      rw [compileCore_initialFields]
      rfl
    unfold Graph.field? at hfield
    simp only [hinitialFields, Nat.not_lt_zero, ↓reduceDIte, Nat.sub_zero] at hfield
    cases hrow : (compileCore core source.fresh compilerInitial).graph.nodes[ref.field]?
    · simp only [hrow] at hfield
      cases hfield
    · simp only [hrow, Option.some.injEq] at hfield
      cases hfield
      cases hsource

end VegasTests.GeneratedReadoutAvailability

/-- info: 'VegasTests.GeneratedReadoutAvailability.first_conditional_readout_available'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  VegasTests.GeneratedReadoutAvailability.first_conditional_readout_available
