/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationForwardCheckpoint
import Vegas.Compile.ApplicationInitialReads
import Vegas.Compile.ApplicationPhaseCaches
import Vegas.Compile.BindingPhaseExecution

/-! # Forward composition at an opaque-binding head

This module packages one source-ordered binding phase as an induction step.
The operational side remains the shared message-application policy runner with
the original whole-plan lifted profile and serial service.  The source side is
the existing behavioral-profile kernel followed by an abstract continuation;
no alternate evaluator is introduced.
-/

noncomputable section

namespace Vegas.ApplicationPlan.ForwardCheckpoint

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Compose the exact generated binding phase with any already-proved law for
the structural tail.  The only input-read assumption is the head guard's
public initial footprint; registration provenance, fresh envelope identity,
service selection, cache freshness, and the successor checkpoint are derived
from the supplied `ForwardCheckpoint`. -/
theorem binding_bind
    {rootContext Γ : VCtx P L} {rootPending pending : Finset VarId}
    {rootProg : VegasCore P L rootContext}
    {rootAccounted : CommitmentAccounting rootPending rootProg}
    {rootFresh : FreshBindings rootProg} {rootState : BuildState P L rootContext}
    {name : VarId} {who : P} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool}
    {tail : VegasCore P L ((name, .sealed who ty) :: Γ)}
    {newName : name ∉ pending}
    {accounted : CommitmentAccounting (insert name pending) tail}
    {fresh : FreshBindings (.commit name who guard tail)}
    {state : BuildState P L Γ}
    {root : ApplicationPlan rootAccounted rootFresh rootState}
    {rootProfile : SourceBehavioralProfile rootProg} {deadlineOf : Nat → Nat}
    (unrestricted : UnrestrictedBinding guard)
    (nextPlan : ApplicationPlan accounted fresh.2
      (state.addCommitEvent name who guard fresh.1).1)
    (profile : SourceBehavioralProfile (.commit name who guard tail))
    (current : CoupledAt (compileCore (.commit name who guard tail) fresh state).graph state)
    (execution : (root.image deadlineOf).application.PolicyExecution)
    (checkpoint : ForwardCheckpoint root rootProfile deadlineOf
      (.binding (newName := newName) (fresh := fresh) unrestricted nextPlan)
      profile current execution)
    (hinitial : BuildResult.InitialReadsPublic
      (compileCore (.commit name who guard tail) fresh state)
      (eventGuardOf state who guard).choiceReads)
    {Ω : Type*} (after : (root.image deadlineOf).application.PolicyExecution → FinDist Ω)
    (sourceAfter : VEnv L ((name, .sealed who ty) :: Γ) → FinDist Ω)
    (hafter : ∀ (nextCurrent : CoupledAt
          (compileCore tail fresh.2 (state.addCommitEvent name who guard fresh.1).1).graph
          (state.addCommitEvent name who guard fresh.1).1)
        (nextExecution : (root.image deadlineOf).application.PolicyExecution),
      ForwardCheckpoint root rootProfile deadlineOf nextPlan profile.afterCommit
          nextCurrent nextExecution →
        after nextExecution = sourceAfter nextCurrent.current.source) :
    (((root.image deadlineOf).application.runPolicies
        (root.liftProfile deadlineOf rootProfile)
        (root.image deadlineOf).serialService
        [.player who, .player who, .environment] execution).bind after) =
      (profile who (.here guard tail)
        ((current.current.source.toView who).eraseEnv)).bind fun chosen =>
          sourceAfter (current.current.source.cons chosen.1) := by
  let plan : ApplicationPlan (.commit newName accounted) fresh state :=
    .binding unrestricted nextPlan
  let image := root.image deadlineOf
  let site : SourceDecisionSite who (.commit name who guard tail) Γ name ty guard :=
    .here guard tail
  let field := site.compiledField fresh state
  let code := site.bindingCode fresh state field
  let phase : List (@Invocation P) := [.player who, .player who, .environment]
  have hreadyData := SourceDecisionSite.binding_ready_at_source_prefix guard tail fresh state
    current execution.native.application.memory.done checkpoint.refines.memory.completed
  have hready : Ready (compileCore (.commit name who guard tail) fresh state).graph
      current.current.graph.1 (site.compiledNode fresh state) := hreadyData.1
  have hunresolved : execution.native.application.memory.done state.nodes.length = false := by
    exact hreadyData.2.1
  obtain ⟨previous, hreached⟩ := checkpoint.reached
  obtain ⟨reads, hreadout, _hreads, hview⟩ :=
    checkpoint.continuation.runPolicies_ownerReadout?_of_ready_source_view deadlineOf who
      (root.liftProfile deadlineOf rootProfile) rfl image.serialService previous execution
      hreached site current.current.graph.1 checkpoint.refines hready hinitial
      current.current.source (BuildState.Agrees.view current.current.agrees who)
  have hconsistent : image.RegistrationConsistent execution := by
    apply image.runPolicies_registrationConsistent
      (root.liftProfile deadlineOf rootProfile) image.serialService previous
      (root.initialExecution deadlineOf) execution
    · intro owner slot
      rfl
    · exact hreached
  have hhead : plan.instructions deadlineOf =
      .bind code :: nextPlan.instructions deadlineOf := by
    rfl
  have hcodeMem : (ApplicationInstruction.bind code : ApplicationInstruction P L) ∈
      root.instructions deadlineOf := by
    exact checkpoint.instruction_mem (.bind code) (hhead ▸ List.mem_cons_self)
  have hcode : image.lookup code.node = some (.bind code) := by
    exact root.image_lookup_of_mem deadlineOf (.bind code) hcodeMem
  have hserviceCode : image.instructions[execution.environmentHistory.length]? =
      some (.bind code) := checkpoint.head_lookup (.bind code)
        (nextPlan.instructions deadlineOf) hhead
  have hheadCache : (ApplicationInstruction.bind code).CacheEmpty image execution := by
    apply (List.forall_iff_forall_mem.mp checkpoint.caches)
    exact hhead ▸ List.mem_cons_self
  have hcache : image.registrationCache field
      (execution.principalHistory who) = none := hheadCache.1
  have hsubmitted : ChoiceEncoding.cachedValue image.application
      (code.encoding.submission image.application)
      (execution.principalHistory who) = none := hheadCache.2
  have htailCaches : nextPlan.RemainingCachesEmpty image deadlineOf execution := by
    exact (List.forall_cons _ _ _).mp checkpoint.caches |>.2
  have hpolicy (history : List image.application.PlayerEntry) :
      (root.liftProfile deadlineOf rootProfile who) history
          (MessageApplication.State.observe image.application execution.native who) =
        site.bindingPolicy fresh state image (profile who site) history
          (MessageApplication.State.observe image.application execution.native who) := by
    change root.liftProfileIn image deadlineOf rootProfile who history
      (MessageApplication.State.observe image.application execution.native who) = _
    rw [checkpoint.continuation.liftProfileIn_eq_of_refines image deadlineOf current
      execution.native checkpoint.refines who history]
    have hdoneView :
        (MessageApplication.State.observe image.application execution.native who).application.done
          state.nodes.length = false := hunresolved
    simp only [ApplicationPlan.liftProfileIn, hdoneView, Bool.false_eq_true,
      ↓reduceIte, site]
  have henvironment : ∀ chosen ∈
      (profile who site ((current.current.source.toView who).eraseEnv)).support,
      ∀ registered ∈ (image.application.playerStep who execution
        (.privateCommand (.register field ⟨ty, chosen.1⟩))).support,
      ∀ submittedExecution ∈ (image.application.playerStep who registered
        (.submit (.binding code.node (who, field)))).support,
      image.serialService submittedExecution.environmentHistory
          (MessageApplication.State.environmentView image.application
            submittedExecution.native) =
        FinDist.pure (.include (who, execution.native.pool.nextSerial who)) := by
    intro chosen _ registered hregistered submittedExecution hsubmittedExecution
    exact image.serialService_after_private_submit execution registered submittedExecution
      (.bind code) who (.register field ⟨ty, chosen.1⟩)
      (.binding code.node (who, field)) hserviceCode rfl
      (checkpoint.lookup_nextSerial_eq_none who) hregistered hsubmittedExecution
  have hphase := SourceDecisionSite.binding_phase_source_law guard tail fresh state current image
    (profile who site) (root.liftProfile deadlineOf rootProfile) image.serialService execution
    checkpoint.refines hconsistent hcode reads hpolicy henvironment
    (checkpoint.lookup_nextSerial_eq_none who) hcache hsubmitted hreadout hview
  rw [hphase.1, FinDist.bind_bind]
  apply FinDist.bind_congr
  intro chosen hchosen
  rw [FinDist.bind_bind]
  let target := sourceAfter (current.current.source.cons chosen.1)
  refine (FinDist.bind_congr (fun registered hregistered => ?_)).trans
    (FinDist.bind_const _ target)
  rw [FinDist.bind_bind]
  refine (FinDist.bind_congr (fun submittedExecution hsubmittedExecution => ?_)).trans
    (FinDist.bind_const _ target)
  refine (FinDist.bind_congr (fun included hincluded => ?_)).trans
    (FinDist.bind_const _ target)
  obtain ⟨nextCurrent, hsource, hrefinesNext, hsnapshot⟩ :=
    hphase.2 chosen hchosen registered hregistered submittedExecution
      hsubmittedExecution included hincluded
  have hincludedPhase : included ∈ (image.application.runPolicies
      (root.liftProfile deadlineOf rootProfile) image.serialService phase execution).support := by
    simp only [phase, hphase.1, FinDist.support_bind, Set.mem_iUnion]
    exact ⟨chosen, hchosen, registered, hregistered, submittedExecution,
      hsubmittedExecution, hincluded⟩
  have hprefixPreserved := ApplicationImage.AcceptedBindingPrefix.runPolicies image
    state.nodes.length
    (root.liftProfile deadlineOf rootProfile) image.serialService phase execution included
    checkpoint.accepted hincludedPhase
  have haccepted : image.AcceptedBindingPrefix (state.nodes.length + 1)
      included.native.application := by
    apply ApplicationImage.AcceptedBindingPrefix.extend root deadlineOf state.nodes.length
      included.native.application code hprefixPreserved hcodeMem rfl
      (some ⟨ty, chosen.1⟩)
    change ApplicationImage.AcceptedSnapshot code.sourceField (who, field)
      (some ⟨ty, chosen.1⟩) included.native.application
    rw [site.bindingCode_sourceField fresh state field]
    exact hsnapshot
  have hcaches := checkpoint.continuation.binding_phase_preserves_nextCaches root rootProfile
    unrestricted nextPlan profile deadlineOf image.serialService current execution included
    checkpoint.refines hunresolved htailCaches hincludedPhase
  have hnextCheckpoint : ForwardCheckpoint root rootProfile deadlineOf nextPlan
      profile.afterCommit nextCurrent included := by
    refine ⟨.binding checkpoint.continuation, hrefinesNext,
      checkpoint.reached_after phase included hincludedPhase, ?_, hcaches, ?_⟩
    · exact checkpoint.aligned_after_phase (.bind code)
        (nextPlan.instructions deadlineOf) hhead included hincludedPhase
    · simpa only [BuildState.addCommitEvent_nodes, List.length_append,
        List.length_singleton] using haccepted
  rw [hafter nextCurrent included hnextCheckpoint, hsource]

end Vegas.ApplicationPlan.ForwardCheckpoint

/-- info: 'Vegas.ApplicationPlan.ForwardCheckpoint.binding_bind' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.ForwardCheckpoint.binding_bind
