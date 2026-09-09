/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationPolicy
import Vegas.Compile.PublicChoiceImageExecution
import Vegas.Compile.SourceExecutionOutcome
import VegasTests.ApplicationImage

/-! # Generated public-choice phase execution

The first guarded choice in the mixed-type generated image is exercised by
the structurally lifted source profile and the real owner-local readout.  A
one-step service includes the controller's freshly submitted envelope through
the shared policy runner.
-/

noncomputable section

namespace VegasTests.PublicChoiceImageExecution

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction
  Interaction.MessageApplication GameTheory.Math.Probability
open VegasTests.ApplicationImage

def initialPolicyExecution : image.application.PolicyExecution :=
  PolicyExecution.initial image.application initialExecution

def includeFirst : image.application.EnvironmentPolicy := fun _ _ =>
  FinDist.pure (.include (0, 0))

private theorem initialReadout :
    ∃ reads : ReadEnv simpleExpr
        (firstSite.compiledGuard source.fresh compilerInitial).choiceReads,
      image.ownerReadout? 0
          (firstSite.compiledGuard source.fresh compilerInitial).choiceReads []
          (MessageApplication.State.observe image.application initialExecution 0) = some reads ∧
        ReadEnv.ofStore? compiled.graph.initialStore
          (firstSite.compiledGuard source.fresh compilerInitial).choiceReads = some reads := by
  let refs := (firstSite.compiledGuard source.fresh compilerInitial).choiceReads
  let available : ∀ ref, ref ∈ refs →
      ∃ value, Store.getAs compiled.graph.initialStore ref.field ref.ty = some value := by
    intro ref href
    have href' : ref = ({ field := 0, ty := .bool } : FieldRef simpleExpr) := by
      change ref ∈ ({({ field := 0, ty := .bool } : FieldRef simpleExpr)} :
        Finset (FieldRef simpleExpr)) at href
      simpa using href
    subst ref
    exact ⟨true, rfl⟩
  let reads := ReadEnv.ofStore compiled.graph.initialStore refs available
  have hreads : ReadEnv.ofStore? compiled.graph.initialStore refs = some reads := by
    unfold ReadEnv.ofStore?
    rw [dif_pos available]
  refine ⟨reads, ?_, hreads⟩
  unfold ApplicationImage.ownerReadout?
  rw [show (MessageApplication.State.observe image.application initialExecution 0).application =
      initialMemory by rfl]
  apply ReadEnv.ofStoreExec?_eq_some_of_ofStore?_eq_some
  apply ReadEnv.ofStore?_eq_of_getAs_eq hreads
  intro ref href
  have href' : ref = ({ field := 0, ty := .bool } : FieldRef simpleExpr) := by
    change ref ∈ ({({ field := 0, ty := .bool } : FieldRef simpleExpr)} :
      Finset (FieldRef simpleExpr)) at href
    simpa using href
  subst ref
  rfl

/-- The real lifted first choice has its exact source decision law through
submission and successful inclusion.  The equality retains complete native
state and policy histories rather than projecting only the chosen Boolean. -/
theorem first_publicChoice_phase_source_law
    (profile : SourceBehavioralProfile source.prog) :
    image.application.runPolicies (applicationPlan.liftProfile (fun _ => 0) profile)
        includeFirst [.player 0, .environment] initialPolicyExecution =
      (profile 0 firstSite.decision ((source.env.toView 0).eraseEnv)).bind fun chosen =>
        (image.application.playerStep 0 initialPolicyExecution
          (.submit ((ApplicationImage.choiceEncoding
            (P := VegasTests.ApplicationImage.Player) (L := simpleExpr)
            firstAddress BaseTy.bool).encode chosen.1))).bind
            fun submitted => image.application.environmentPolicyStep submitted
              (.include (0, 0)) := by
  obtain ⟨reads, hreadout, hreads⟩ := initialReadout
  have hagrees : (firstSite.siteState source.fresh compilerInitial).Agrees
      compiled.graph.initialStore source.env := by
    exact (compiledInitialCoupled source).current.agrees
  have hlaw := firstSite.publicChoice_phase_source_law source.fresh compilerInitial image
    (image.ownerReadout? 0 (firstSite.compiledGuard source.fresh compilerInitial).choiceReads)
    (profile 0 firstSite.decision) (fun _ _ => false)
    (applicationPlan.liftProfile (fun _ => 0) profile) includeFirst initialPolicyExecution
    compiled.graph.initialStore source.env reads
    (by rfl) (by intro chosen hchosen submitted hsubmitted; rfl) (by rfl)
    first_publicly_validatable hagrees
    (ApplicationImage.State.initial_refines compiled.graph).memory.publicFields
    image_lookup_first (by rfl) (by rfl) hreadout hreads
  exact hlaw.1

end VegasTests.PublicChoiceImageExecution

/-- info: 'VegasTests.PublicChoiceImageExecution.first_publicChoice_phase_source_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  VegasTests.PublicChoiceImageExecution.first_publicChoice_phase_source_law
