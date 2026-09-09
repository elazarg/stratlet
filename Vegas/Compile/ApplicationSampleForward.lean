/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationForwardCheckpoint
import Vegas.Compile.ApplicationPhaseCaches
import Vegas.Compile.ApplicationSampleExecution

/-! # Composing a generated chance phase with its source continuation

The native prefix is an actual invocation of the original generated service.
The post-phase law is arbitrary; the theorem composes it with the source
chance law whenever it agrees at every genuine successor checkpoint.
-/

noncomputable section

namespace Vegas.ApplicationPlan.ForwardCheckpoint

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

theorem sample_bind
    {rootContext Γ : VCtx P L} {rootPending pending : Finset VarId}
    {rootProg : VegasCore P L rootContext}
    {rootAccounted : CommitmentAccounting rootPending rootProg}
    {rootFresh : FreshBindings rootProg} {rootState : BuildState P L rootContext}
    {root : ApplicationPlan rootAccounted rootFresh rootState}
    {rootProfile : SourceBehavioralProfile rootProg} {deadlineOf : Nat → Nat}
    {name : VarId} {ty : L.Ty} {dist : L.DistExpr (erasePubVCtx Γ) ty}
    {tail : VegasCore P L ((name, .pub ty) :: Γ)}
    {accounted : CommitmentAccounting pending tail}
    {fresh : FreshBindings (.sample name dist tail)} {state : BuildState P L Γ}
    (nextPlan : ApplicationPlan accounted fresh.2 (state.addSampleEvent name dist fresh.1).1)
    (profile : SourceBehavioralProfile (.sample name dist tail))
    (current : CoupledAt (compileCore (.sample name dist tail) fresh state).graph state)
    (execution : (root.image deadlineOf).application.PolicyExecution)
    (checkpoint : ForwardCheckpoint root rootProfile deadlineOf
      (.sample (fresh := fresh) nextPlan) profile current execution)
    {Ω : Type*} (after : (root.image deadlineOf).application.PolicyExecution → FinDist Ω)
    (sourceAfter : VEnv L ((name, .pub ty) :: Γ) → FinDist Ω)
    (hafter : ∀ next native,
      ForwardCheckpoint root rootProfile deadlineOf nextPlan profile.afterSample next native →
        after native = sourceAfter next.current.source) :
    (((root.image deadlineOf).application.runPolicies
      (root.liftProfile deadlineOf rootProfile) (root.image deadlineOf).serialService
      [.environment] execution).bind after) =
      (L.evalDist dist current.current.source.eraseSampleEnv).bind
        (fun value => sourceAfter (current.current.source.cons value)) := by
  let image := root.image deadlineOf
  let code := headSampleCode fresh state
  have hhead : (ApplicationPlan.sample (fresh := fresh) nextPlan).instructions deadlineOf =
      .sample code :: nextPlan.instructions deadlineOf := rfl
  have hmem := checkpoint.instruction_mem (.sample code)
    (hhead ▸ List.mem_cons_self)
  have hlookup : image.lookup state.nodes.length = some (.sample code) :=
    root.image_lookup_of_mem deadlineOf (.sample code) hmem
  have hphase := sample_phase_source_coupling dist tail fresh state image hlookup current
    execution checkpoint.refines
  have hrun : image.application.runPolicies (root.liftProfile deadlineOf rootProfile)
      image.serialService [.environment] execution =
      (L.evalDist dist current.current.source.eraseSampleEnv).map
        (image.sampleExecution execution code) := by
    simp only [MessageApplication.runPolicies, MessageApplication.invoke]
    rw [image.serialService_at execution.environmentHistory _ (.sample code)
      (checkpoint.head_lookup (.sample code) _ hhead)]
    simp only [ApplicationImage.serviceCommand, FinDist.pure_bind, FinDist.bind_pure]
    exact hphase.1
  rw [hrun, FinDist.bind_map]
  apply FinDist.bind_congr
  intro value hvalue
  obtain ⟨next, hsource, hrefines⟩ := hphase.2 value hvalue
  let native := image.sampleExecution execution code value
  have hnative : native ∈ (image.application.runPolicies
      (root.liftProfile deadlineOf rootProfile) image.serialService
      [.environment] execution).support := by
    rw [hrun, FinDist.support_map]
    exact ⟨value, hvalue, rfl⟩
  have hfresh : nextPlan.RemainingCachesEmpty image deadlineOf execution :=
    (List.forall_cons _ _ _).mp checkpoint.caches |>.2
  have haccepted := ApplicationImage.AcceptedBindingPrefix.runPolicies image state.nodes.length
    (root.liftProfile deadlineOf rootProfile) image.serialService
    [.environment] execution native checkpoint.accepted hnative
  have hnext : ForwardCheckpoint root rootProfile deadlineOf nextPlan
      profile.afterSample next native := by
    refine ⟨.sample checkpoint.continuation, hrefines,
      checkpoint.reached_after [.environment] native hnative,
      checkpoint.aligned_after_phase (.sample code) _ hhead native hnative, ?_, ?_⟩
    · exact nextPlan.environment_phase_preserves_remainingCaches image deadlineOf
        (root.liftProfile deadlineOf rootProfile) image.serialService
        execution native hfresh hnative
    · apply ApplicationImage.AcceptedBindingPrefix.advance_of_coveredNonbinding
        root deadlineOf state.nodes.length _ native.native.application (.sample code)
        haccepted hmem
      · intro binding hbinding
        cases hbinding
      · intro node hlower hupper
        simp only [BuildState.addSampleEvent_nodes, List.length_append,
          List.length_singleton] at hupper
        have hnode : node = state.nodes.length := by omega
        simp only [ApplicationInstruction.coveredNodes, List.mem_singleton, hnode]
        rfl
  rw [hafter next native hnext, hsource]

end Vegas.ApplicationPlan.ForwardCheckpoint

/-- info: 'Vegas.ApplicationPlan.ForwardCheckpoint.sample_bind' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.ForwardCheckpoint.sample_bind
