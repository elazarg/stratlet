/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationService
import Vegas.Compile.BindingPhaseExecution
import Vegas.Compile.ConditionalPhaseExecution
import Vegas.Compile.SourceExecutionOutcome
import VegasTests.ConditionalPhaseExecution

/-! # Complete generated application under the reference service

The checked binding--conditional-publication fixture is run with the player
policies obtained from its original `ApplicationPlan`, the source-ordered
service generated from its emitted image, and the image's generated invocation
list.  The resulting executable public-terminal law is exactly the independent
written-order source denotation.  This is a concrete integration test, not a
general compilation or progress theorem.
-/

noncomputable section

namespace VegasTests.ApplicationServiceSource

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction
  Interaction.MessageApplication GameTheory.Math.Probability
open VegasTests.ConditionalApplicationImage
open VegasTests.ConditionalSourceCoupling
open VegasTests.ConditionalPhaseExecution

private def initialLaw (profile : SourceBehavioralProfile source.prog) : FinDist Bool :=
  (profile 0 initialSite ((source.env.toView 0).eraseEnv)).map Subtype.val

private theorem initial_readout : ∃ reads,
    (image 10).ownerReadout? (0 : Fin 2)
        (eventGuardOf (decisionSiteState initialSite source.fresh compilerInitial)
          0 (.constBool true (Γ := [(0, .bool)]))).choiceReads
        (initial.principalHistory 0)
        (MessageApplication.State.observe (image 10).application initial.native 0) = some reads ∧
      viewEnvOfReadEnv (decisionSiteState initialSite source.fresh compilerInitial) 0 reads =
        (source.env.toView 0).eraseEnv := by
  have havailable : ∀ ref, ref ∈ visibleFieldRefs compilerInitial 0 →
      ∃ value, Store.getAs
        ((image 10).ownerReadStore 0 (initial.principalHistory 0)
          initial.native.application.memory) ref.field ref.ty = some value := by
    intro ref href
    change ref ∈ (∅ : Finset (FieldRef simpleExpr)) at href
    exact False.elim (Finset.notMem_empty ref href)
  let reads := ReadEnv.ofStore _ _ havailable
  have hreads : ReadEnv.ofStore?
      ((image 10).ownerReadStore 0 (initial.principalHistory 0)
        initial.native.application.memory) (visibleFieldRefs compilerInitial 0) = some reads := by
    unfold ReadEnv.ofStore?
    rw [dif_pos havailable]
  refine ⟨reads, ReadEnv.ofStoreExec?_eq_some_of_ofStore?_eq_some hreads, ?_⟩
  apply viewEnvOfReadEnv_eq_sourceView compilerInitial 0 _ source.env _ reads hreads
  intro name bindTy binding
  cases binding

/-- The first emitted instruction is executed by the whole-plan lifted policy
and by the generated service, retaining the arbitrary source choice law. -/
private theorem binding_prefix_law (profile : SourceBehavioralProfile source.prog) :
    (image 10).application.runPolicies
        (applicationPlan.liftProfile (fun _ => 10) profile) (image 10).serialService
        [.player 0, .player 0, .environment] initial =
      (initialLaw profile).map boundExecution := by
  obtain ⟨reads, hreadout, hview⟩ := initial_readout
  have hphase := SourceDecisionSite.binding_phase_source_law
    (P := Fin 2) (L := simpleExpr) (.constBool true) _ source.fresh
    compilerInitial checkpoint (image 10) (profile 0 initialSite)
    (applicationPlan.liftProfile (fun _ => 10) profile) (image 10).serialService
    initial (ApplicationImage.State.initial_refines compiled.graph) (by
      intro who slot
      rfl) (image_lookup_binding 10) reads (by
      intro history
      rfl) (by
      intro chosen _ registered hregistered submitted hsubmitted
      exact (image 10).serialService_after_private_submit initial registered submitted
        (.bind bindingCode) 0 (.register 0 ⟨.bool, chosen.1⟩) bindingPayload
        rfl rfl rfl hregistered hsubmitted) (by rfl) (by rfl) (by rfl)
    hreadout hview
  rw [hphase.1]
  rw [initialLaw, FinDist.map_comp, FinDist.map_eq_bind]
  apply FinDist.bind_congr
  intro chosen _
  simp only [MessageApplication.playerStep, PlayerCommand.toAction,
    MessageApplication.environmentPolicyStep, EnvironmentPolicyCommand.toAction,
    MessageApplication.advance, MessageApplication.step, FinDist.pure_bind]
  rfl

private def conditionalHead : ConditionalPublicationSite initialSite.continuation := by
  change ConditionalPublicationSite
    (.commit 1 0 openingGuard (.reveal 2 0 1 .here tail))
  exact ConditionalPublicationSite.atHead
    (P := Fin 2) (L := simpleExpr) (Γ := OpeningContext) (ty := .option .bool)
    1 2 0 openingGuard tail specification

private def openingLaw (profile : SourceBehavioralProfile source.prog) (secret : Bool) :=
  profile.afterCommit 0 conditionalHead.choice.decision
    (((source.env.cons secret).toView 0).eraseEnv)

private def publicOutcome (execution : (image 10).application.PolicyExecution) :=
  (execution.native.application.memory.finished compiled.graph.nodeCount,
    compiled.readPublicTerminal? execution.native.application.memory)

/-- After a supported binding value, the same whole-plan lifted policy and
generated service execute the remaining conditional publication. -/
private theorem conditional_public_law (profile : SourceBehavioralProfile source.prog)
    (secret : Bool) :
    ((image 10).application.runPolicies
        (applicationPlan.liftProfile (fun _ => 10) profile) (image 10).serialService
        [.player 0, .environment] (boundExecution secret)).map publicOutcome =
      (openingLaw profile secret).map fun chosen =>
        (true, some (Env.cons chosen.1 (Env.empty simpleExpr.Val))) := by
  obtain ⟨current, hsource, hrefines, hsnapshot⟩ := bound_source_successor secret
  let view := MessageApplication.State.observe (image 10).application
    (boundExecution secret).native 0
  have hsome : ((image 10).ownerReadout? 0
      (conditionalSite.choice.compiledGuard source.fresh compilerInitial).choiceReads
      ((boundExecution secret).principalHistory 0) view).isSome := by
    cases secret <;> decide
  obtain ⟨reads, hreadout⟩ := Option.isSome_iff_exists.mp hsome
  have hmatches : (image 10).RegistrationMatches 0
      ((boundExecution secret).principalHistory 0)
      (boundExecution secret).native.application := by
    intro field value _hprivate _haccepted hcache
    by_cases hfield : field = 0
    · subst field
      have hvalue : (⟨.bool, secret⟩ : TypedValue simpleExpr) = value :=
        Option.some.inj hcache
      exact hsnapshot.2.trans (congrArg some hvalue)
    · have hempty : (image 10).registrationCache field
          ((boundExecution secret).principalHistory 0) = none := by
        simp [ApplicationImage.registrationCache, boundExecution, submitted, registered,
          initial, ApplicationImage.registrationEncoding, Ne.symm hfield]
      rw [hempty] at hcache
      contradiction
  have hreads := conditionalSite.choice.decision.ownerReadout?_graph_reads source.fresh
    compilerInitial (image 10) ((boundExecution secret).principalHistory 0) view
    (boundExecution secret).native.application rfl current.current.graph.1 hrefines
    hmatches reads hreadout
  have hphase := ConditionalPublicationSite.conditional_phase_source_law
    (P := Fin 2) (L := simpleExpr) (Γ := OpeningContext)
    (name := 1) (publicName := 2) (who := 0) (ty := .option .bool)
    openingGuard tail specification source.fresh.2 boundBuild 0 10 current (image 10)
    (profile.afterCommit 0 conditionalHead.choice.decision)
    (applicationPlan.liftProfile (fun _ => 10) profile) (image 10).serialService
    (boundExecution secret) hrefines opening_publicly_validatable hsnapshot.1
    (image_lookup_conditional 10) reads (by
      intro history
      rfl) (by
      intro chosen _ submitted hsubmitted
      exact (image 10).serialService_after_submit (boundExecution secret) submitted
        (.conditional (conditionalCode 10)) 0
        ((ApplicationImage.conditionalTransport (P := Fin 2) (L := simpleExpr) .bool).encode
          ((conditionalCode 10).endpoint.publicationNode,
            (conditionalCode 10).endpoint.requestPayload chosen.1))
        rfl rfl rfl hsubmitted) (by rfl) (by rfl) hreadout hreads (by
      intro chosen _ value hvalue
      have heq := specification.successful_value_eq_binding
        current.current.source chosen.1 value chosen.2 hvalue
      rw [hsource] at heq
      change value = secret at heq
      rw [heq]
      change ((bound secret).application.frozen 0).bind
        (fun typed => typed.as? (L := simpleExpr) .bool) = some secret
      rw [hsnapshot.2]
      rfl)
  have hlocal :
      ((image 10).application.runPolicies
          (applicationPlan.liftProfile (fun _ => 10) profile) (image 10).serialService
          [.player 0, .environment] (boundExecution secret)).map publicOutcome =
        (profile.afterCommit 0 conditionalHead.choice.decision
          ((current.current.source.toView 0).eraseEnv)).map fun chosen =>
            (true, some (Env.cons chosen.1 (Env.empty simpleExpr.Val))) := by
    rw [hphase.1, FinDist.map_bind]
    rw [show (profile.afterCommit 0 conditionalHead.choice.decision
        ((current.current.source.toView 0).eraseEnv)).map
          (fun chosen => (true, some (Env.cons chosen.1 (Env.empty simpleExpr.Val)))) =
        (profile.afterCommit 0 conditionalHead.choice.decision
          ((current.current.source.toView 0).eraseEnv)).bind
            (fun chosen => FinDist.pure
              (true, some (Env.cons chosen.1 (Env.empty simpleExpr.Val)))) by
          rfl]
    apply FinDist.bind_congr
    intro chosen hchosen
    rw [FinDist.map_bind]
    refine (FinDist.bind_congr (fun submitted hsubmitted => ?_)).trans
      (FinDist.bind_const _ (FinDist.pure
        (true, some (Env.cons chosen.1 (Env.empty simpleExpr.Val)))))
    exact (FinDist.map_congr_of_eq_on_support (fun included hincluded => by
      obtain ⟨next, hnextSource, hnextRefines⟩ :=
        hphase.2 chosen hchosen submitted hsubmitted included hincluded
      have hout := next.finished_public_readout compiled included.native.application hnextRefines
      rw [hnextSource] at hout
      exact Prod.ext hout.1 hout.2)).trans
        (FinDist.map_const _
          (true, some (Env.cons chosen.1 (Env.empty simpleExpr.Val))))
  exact hlocal.trans (congrArg (fun env : VEnv simpleExpr OpeningContext =>
    (profile.afterCommit 0 conditionalHead.choice.decision ((env.toView 0).eraseEnv)).map
      (fun chosen => (true, some (Env.cons chosen.1 (Env.empty simpleExpr.Val))))) hsource)

private theorem source_public_law (profile : SourceBehavioralProfile source.prog) :
    (denoteSource source.prog profile source.env).map (fun terminal =>
        (true, some terminal.erasePubEnv)) =
      (initialLaw profile).bind fun secret =>
        (openingLaw profile secret).map fun chosen =>
          (true, some (Env.cons chosen.1 (Env.empty simpleExpr.Val))) := by
  simp only [source, core, tail, denoteSource, initialLaw, openingLaw,
    FinDist.map_bind, FinDist.map_pure, FinDist.bind_map]
  rfl

/-- Complete concrete source/public law for the generated plan and its finite
source-ordered service. The player profile is arbitrary; only this checked
three-node source and the explicitly generated service script are claimed. -/
theorem complete_generated_source_public_law
    (profile : SourceBehavioralProfile source.prog) :
    ((image 10).application.runPolicies
        (applicationPlan.liftProfile (fun _ => 10) profile) (image 10).serialService
        (image 10).serviceInvocations initial).map publicOutcome =
      (denoteSource source.prog profile source.env).map fun terminal =>
        (true, some terminal.erasePubEnv) := by
  rw [source_public_law]
  rw [show (image 10).serviceInvocations =
      ([.player 0, .player 0, .environment] ++ [.player 0, .environment] :
        List (@Invocation (Fin 2))) by rfl,
    MessageApplication.runPolicies_append, binding_prefix_law, FinDist.bind_map,
    FinDist.map_bind]
  apply FinDist.bind_congr
  intro chosen _
  exact conditional_public_law profile chosen

end VegasTests.ApplicationServiceSource

/-- info: 'VegasTests.ApplicationServiceSource.complete_generated_source_public_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ApplicationServiceSource.complete_generated_source_public_law
