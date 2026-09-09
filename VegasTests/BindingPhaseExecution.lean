/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.BindingPhaseExecution
import Vegas.Compile.SourceExecutionOutcome
import VegasTests.GeneratedBindingPolicy

/-! # Full generated binding phase

The persistent-disclosure fixture runs the generated source kernel through
private registration, opaque submission, and actual environment inclusion.
Every supported source draw reaches its exact one-commit source successor.
-/

noncomputable section

namespace VegasTests.BindingPhaseExecution

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction
  Interaction.MessageApplication GameTheory.Math.Probability
open VegasTests.PersistentDisclosure
open VegasTests.GeneratedPersistentDisclosure
open VegasTests.GeneratedBindingPolicy

def checkpoint : CoupledAt GeneratedPersistentDisclosure.compiled.graph compilerInitial :=
  compiledInitialCoupled source

private theorem image_lookup_binding : image.lookup code.node = some (.bind code) := by
  have hmem : (ApplicationInstruction.bind code) ∈
      applicationPlan.instructions (fun _ => 10) := by
    change _ ∈ [ApplicationInstruction.bind code, _, _, _, _, _]
    simp
  change (applicationPlan.image (fun _ => 10)).lookup
    (ApplicationInstruction.bind (L := simpleExpr) code).address = some (.bind code)
  exact applicationPlan.image_lookup_of_mem (fun _ => 10) _ hmem

/-- The exact phase law specializes to the fixture's full execution, and each
supported secret has the corresponding source successor and native snapshot. -/
theorem generated_binding_phase (law : FinDist Bool) :
    image.application.runPolicies (players law) environment
        [.player 0, .player 0, .environment] initial = law.map included ∧
      ∀ secret ∈ law.support,
        ∃ next : CoupledAt GeneratedPersistentDisclosure.compiled.graph
            (compilerInitial.addCommitEvent (actionName := 0)
              (actionTy := BaseTy.bool) 0 0 (.constBool true) source.fresh.1).1,
          next.current.source = source.env.cons secret ∧
          (included secret).native.application.Refines next.current.graph.1 ∧
          ApplicationImage.AcceptedSnapshot (L := simpleExpr) 0 (0, 0)
            (some ⟨.bool, secret⟩) (included secret).native.application := by
  obtain ⟨reads, hreadout, hview⟩ := initial_readout
  have hrefines : initial.native.application.Refines checkpoint.current.graph.1 := by
    exact ApplicationImage.State.initial_refines
      GeneratedPersistentDisclosure.compiled.graph
  have hconsistent : image.RegistrationConsistent initial := by
    intro who slot
    rfl
  have hphase := SourceDecisionSite.binding_phase_source_law
    (P := TestPlayer) (L := simpleExpr) (.constBool true) _ source.fresh
    compilerInitial checkpoint image (sourcePolicy law) (players law) environment
    initial hrefines hconsistent image_lookup_binding reads
    (by
      intro history
      change (if (0 : TestPlayer) = 0 then
        site.bindingPolicy source.fresh compilerInitial image (sourcePolicy law) history
          (MessageApplication.State.observe image.application initial.native 0)
        else FinDist.pure .wait) = _
      rw [if_pos rfl]
      rfl)
    (by
      intro chosen _ registered _ submitted _
      rfl)
    (by rfl) (by rfl) (by rfl) hreadout hview
  constructor
  · exact binding_source_law law
  · intro secret hsecret
    let chosen : { value : Bool // evalGuard
        (L := simpleExpr) (Γ := ([] : VCtx TestPlayer simpleExpr))
          (.constBool true (Γ := [(0, .bool)])) value
          ((source.env.toView 0).eraseEnv) = true } := ⟨secret, rfl⟩
    have hchosen : chosen ∈
        (sourcePolicy law ((checkpoint.current.source.toView 0).eraseEnv)).support := by
      unfold sourcePolicy
      rw [FinDist.support_map]
      exact ⟨secret, hsecret, rfl⟩
    have hregistered : registered secret ∈
        (image.application.playerStep 0 initial
          (.privateCommand (.register 0 ⟨.bool, secret⟩))).support := by
      simp only [MessageApplication.playerStep, PlayerCommand.toAction,
        MessageApplication.advance, MessageApplication.step,
        ApplicationImage.application, FinDist.pure_bind,
        FinDist.mem_support_pure]
      rfl
    have hsubmitted : submitted secret ∈
        (image.application.playerStep 0 (registered secret)
          (.submit (.binding code.node (0, 0)))).support := by
      rw [show code.node = 0 by rfl]
      simp only [MessageApplication.playerStep, MessageApplication.advance,
        PlayerCommand.toAction, MessageApplication.step, FinDist.pure_bind,
        FinDist.mem_support_pure]
      rfl
    have hincluded : included secret ∈
        (image.application.environmentPolicyStep (submitted secret)
          (.include (0, 0))).support := by
      simp only [MessageApplication.environmentPolicyStep,
        MessageApplication.advance, EnvironmentPolicyCommand.toAction,
        MessageApplication.step, FinDist.pure_bind, FinDist.mem_support_pure]
      rfl
    obtain ⟨next, hsource, hrefinesNext, hsnapshot⟩ :=
      hphase.2 chosen hchosen (registered secret) hregistered
      (submitted secret) hsubmitted (included secret) hincluded
    refine ⟨next, ?_, hrefinesNext, ?_⟩
    · have hcheckpointSource : checkpoint.current.source = source.env := rfl
      rw [← hcheckpointSource]
      exact hsource
    · change ApplicationImage.AcceptedSnapshot (L := simpleExpr) 0 (0, 0)
        (some ⟨.bool, secret⟩) (included secret).native.application at hsnapshot
      exact hsnapshot

end VegasTests.BindingPhaseExecution

/-- info: 'VegasTests.BindingPhaseExecution.generated_binding_phase' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.BindingPhaseExecution.generated_binding_phase
