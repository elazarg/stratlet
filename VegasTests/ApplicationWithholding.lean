/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationWithholding
import VegasTests.GeneratedPersistentDisclosure

/-! # Withholding in a generated multistage application

The generated persistent-disclosure plan contains both an opaque binding and
a later public response owned by different players.  Their submission
requirements are derived from the emitted instructions.  Either owner can
therefore prevent completion by permanently waiting, for every environment
policy and finite invocation schedule.
-/

noncomputable section

namespace VegasTests.ApplicationWithholding

open Vegas Interaction Interaction.MessageApplication GameTheory
  GameTheory.Math.Probability
open VegasTests.GeneratedPersistentDisclosure

private theorem binding_instruction :
    ∃ code : BindingCode PersistentDisclosure.Player,
      ApplicationInstruction.bind code ∈
          applicationPlan.instructions (fun _ => 10) ∧
        code.owner = 0 ∧
          0 ∈ (ApplicationInstruction.bind (L := simpleExpr) code).coveredNodes := by
  change ∃ code, ApplicationInstruction.bind code ∈ [_, _, _, _, _, _] ∧
    code.owner = 0 ∧
      0 ∈ (ApplicationInstruction.bind (L := simpleExpr) code).coveredNodes
  simp only [Fin.isValue, erasePubVCtx_cons_pub, erasePubVCtx_cons_sealed, erasePubVCtx_nil,
    List.mem_cons, ApplicationInstruction.bind.injEq, reduceCtorEq, List.not_mem_nil,
    or_self, or_false, exists_eq_left]
  decide

private theorem response_instruction :
    ∃ code : PublicChoiceCode PersistentDisclosure.Player simpleExpr,
      ApplicationInstruction.publicChoice code ∈
          applicationPlan.instructions (fun _ => 10) ∧
        code.endpoint.owner = 1 ∧
          6 ∈ (ApplicationInstruction.publicChoice code).coveredNodes := by
  change ∃ code, ApplicationInstruction.publicChoice code ∈ [_, _, _, _, _, _] ∧
    code.endpoint.owner = 1 ∧
      6 ∈ (ApplicationInstruction.publicChoice code).coveredNodes
  simp only [Fin.isValue, erasePubVCtx_cons_pub, erasePubVCtx_cons_sealed, erasePubVCtx_nil,
    List.mem_cons, reduceCtorEq, ApplicationInstruction.publicChoice.injEq, List.not_mem_nil,
    or_self, or_false, false_or, exists_eq_or_imp, ↓existsAndEq, true_and]
  decide

theorem binding_requires_owner_submission : image.RequiresSubmission 0 0 := by
  obtain ⟨code, hmem, howner, hnode⟩ := binding_instruction
  exact applicationPlan.requiresSubmission (fun _ => 10) (.bind code) hmem 0 hnode 0 howner

theorem response_requires_owner_submission : image.RequiresSubmission 6 1 := by
  obtain ⟨code, hmem, howner, hnode⟩ := response_instruction
  exact applicationPlan.requiresSubmission
    (fun _ => 10) (.publicChoice code) hmem 6 hnode 1 howner

/-- Withholding the generated opaque binding keeps the completion flag false,
independently of all other player policies and of the environment. -/
theorem binding_withholding_finished_law
    (players : Profile (policySignature PersistentDisclosure.Player image.application))
    (environment : image.application.EnvironmentPolicy)
    (schedule : List (@Invocation PersistentDisclosure.Player)) :
    ((image.application.runPolicies
      (Profile.update players 0 (fun _ _ => FinDist.pure .wait)) environment schedule
      (applicationPlan.initialExecution (fun _ => 10))).map
        (fun out => out.native.application.memory.finished compiled.graph.nodeCount)) =
      FinDist.pure false := by
  exact applicationPlan.withholding_finished_law DisclosureAccounting.persistentChecked
    (fun _ => 10) 0 0 binding_requires_owner_submission (by decide)
    players environment schedule

/-- The later responder can likewise withhold its generated public choice;
earlier binding, chance, and disclosure phases do not supply that signature. -/
theorem response_withholding_finished_law
    (players : Profile (policySignature PersistentDisclosure.Player image.application))
    (environment : image.application.EnvironmentPolicy)
    (schedule : List (@Invocation PersistentDisclosure.Player)) :
    ((image.application.runPolicies
      (Profile.update players 1 (fun _ _ => FinDist.pure .wait)) environment schedule
      (applicationPlan.initialExecution (fun _ => 10))).map
        (fun out => out.native.application.memory.finished compiled.graph.nodeCount)) =
      FinDist.pure false := by
  exact applicationPlan.withholding_finished_law DisclosureAccounting.persistentChecked
    (fun _ => 10) 6 1 response_requires_owner_submission (by decide)
    players environment schedule

end VegasTests.ApplicationWithholding

/-- info: 'VegasTests.ApplicationWithholding.binding_withholding_finished_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ApplicationWithholding.binding_withholding_finished_law

/-- info: 'VegasTests.ApplicationWithholding.response_withholding_finished_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ApplicationWithholding.response_withholding_finished_law
