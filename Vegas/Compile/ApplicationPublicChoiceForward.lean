/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationForwardCheckpoint
import Vegas.Compile.ApplicationInitialReads
import Vegas.Compile.ApplicationPhaseCaches
import Vegas.Compile.PublicChoicePhaseExecution

/-! # Composing a public-choice phase with its source continuation -/

noncomputable section

namespace Vegas.ApplicationPlan.ForwardCheckpoint

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

theorem publicChoice_bind
    {rootContext Γ : VCtx P L} {rootPending pending : Finset VarId}
    {rootProg : VegasCore P L rootContext}
    {rootAccounted : CommitmentAccounting rootPending rootProg}
    {rootFresh : FreshBindings rootProg} {rootState : BuildState P L rootContext}
    {root : ApplicationPlan rootAccounted rootFresh rootState}
    {rootProfile : SourceBehavioralProfile rootProg} {deadlineOf : Nat → Nat}
    {name publicName : VarId} {who : P} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool}
    {tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ)}
    {newName : name ∉ pending} {unresolved : name ∈ insert name pending}
    {accounted : CommitmentAccounting ((insert name pending).erase name) tail}
    {fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail))}
    {state : BuildState P L Γ}
    (publicGuard : (PublicChoiceSite.atHead name publicName who guard tail).PubliclyValidatable
      fresh state)
    (nextPlan : ApplicationPlan accounted fresh.2.2
      (((state.addCommitEvent name who guard fresh.1).1).addRevealEvent
        publicName who .here fresh.2.1).1)
    (profile : SourceBehavioralProfile
      (.commit name who guard (.reveal publicName who name .here tail)))
    (current : CoupledAt
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh state).graph state)
    (execution : (root.image deadlineOf).application.PolicyExecution)
    (checkpoint : ForwardCheckpoint root rootProfile deadlineOf
      (.publicChoice (newName := newName) (unresolved := unresolved)
        (fresh := fresh) publicGuard nextPlan) profile current execution)
    (hinitial : ToEventGraph.BuildResult.InitialReadsPublic
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh state) (eventGuardOf state who guard).choiceReads)
    {Ω : Type*} (after : (root.image deadlineOf).application.PolicyExecution → FinDist Ω)
    (sourceAfter : VEnv L
      ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ) → FinDist Ω)
    (hafter : ∀ next native,
      ForwardCheckpoint root rootProfile deadlineOf nextPlan
          profile.afterCommit.afterReveal next native →
        after native = sourceAfter next.current.source) :
    (((root.image deadlineOf).application.runPolicies
      (root.liftProfile deadlineOf rootProfile) (root.image deadlineOf).serialService
      [.player who, .environment] execution).bind after) =
      (profile who (.here guard (.reveal publicName who name .here tail))
        ((current.current.source.toView who).eraseEnv)).bind fun chosen =>
          sourceAfter ((current.current.source.cons chosen.1).cons chosen.1) := by
  let image := root.image deadlineOf
  let site := PublicChoiceSite.atHead name publicName who guard tail
  let code := site.code fresh state
  have hhead : (ApplicationPlan.publicChoice (newName := newName)
      (unresolved := unresolved) (fresh := fresh) publicGuard nextPlan).instructions deadlineOf =
      .publicChoice code :: nextPlan.instructions deadlineOf := rfl
  have hmem := checkpoint.instruction_mem (.publicChoice code)
    (hhead ▸ List.mem_cons_self)
  have hcode : image.lookup code.endpoint.publicationNode = some (.publicChoice code) :=
    root.image_lookup_of_mem deadlineOf (.publicChoice code) hmem
  have hready := current.current.nextReady current.completedPrefix
    (site.choiceNode fresh state) rfl
  obtain ⟨previous, hprevious⟩ := checkpoint.reached
  obtain ⟨reads, hreadout, hreads, hview⟩ :=
    checkpoint.continuation.runPolicies_ownerReadout?_of_ready_source_view deadlineOf who
      (root.liftProfile deadlineOf rootProfile) rfl image.serialService previous execution
      hprevious site.decision current.current.graph.1 checkpoint.refines hready hinitial
      current.current.source (BuildState.Agrees.view current.current.agrees who)
  have hunresolved : execution.native.application.memory.done (state.nodes.length + 1) =
      false := by
    apply Bool.eq_false_iff.mpr
    intro hdone
    have hdoneGraph := (checkpoint.refines.memory.completed
      (site.publicationNode fresh state)).mp hdone
    have hlt := (current.completedPrefix _).mp hdoneGraph
    change state.nodes.length + 1 < state.nodes.length at hlt
    omega
  have hdoneView : (MessageApplication.State.observe image.application
      execution.native who).application.done (state.nodes.length + 1) = false :=
    hunresolved
  have hpolicy : ∀ history,
      root.liftProfile deadlineOf rootProfile who history
          (MessageApplication.State.observe image.application execution.native who) =
        (site.imageController fresh state image
          (image.ownerReadout? who (eventGuardOf state who guard).choiceReads)
          (profile who site.decision) (fun _ _ => false)).policy
            image.application history
              (MessageApplication.State.observe image.application execution.native who) := by
    intro history
    unfold ApplicationPlan.liftProfile
    rw [checkpoint.continuation.liftProfileIn_eq_of_refines image deadlineOf current
      execution.native checkpoint.refines who history]
    simp only [ApplicationPlan.liftProfileIn, hdoneView, Bool.false_eq_true,
      ↓reduceIte]
    rfl
  have hfreshHead := (List.forall_cons _ _ _).mp checkpoint.caches |>.1
  have hcache : ChoiceEncoding.cachedValue image.application
      ((ApplicationImage.choiceEncoding code.endpoint.publicationNode ty).submission
        image.application) (execution.principalHistory who) = none := by
    exact hfreshHead
  have hphase := PublicChoiceSite.publicChoice_head_phase_source_law guard tail fresh state
    current image (profile who site.decision) (root.liftProfile deadlineOf rootProfile)
    image.serialService execution checkpoint.refines publicGuard hcode reads hpolicy (by
      intro chosen hchosen submitted hsubmitted
      exact image.serialService_after_submit execution submitted (.publicChoice code) who _
        (checkpoint.head_lookup (.publicChoice code) _ hhead) rfl
        (checkpoint.lookup_nextSerial_eq_none who) hsubmitted)
      (checkpoint.lookup_nextSerial_eq_none who) hcache hreadout hreads
  rw [hphase.1, FinDist.bind_bind]
  apply FinDist.bind_congr
  intro chosen hchosen
  rw [FinDist.bind_bind]
  let target := sourceAfter ((current.current.source.cons chosen.1).cons chosen.1)
  refine (FinDist.bind_congr (fun submitted hsubmitted => ?_)).trans
    (FinDist.bind_const _ target)
  refine (FinDist.bind_congr (fun included hincluded => ?_)).trans
    (FinDist.bind_const _ target)
  obtain ⟨next, hsource, hrefines⟩ := hphase.2 chosen hchosen submitted hsubmitted
    included hincluded
  have hnative : included ∈ (image.application.runPolicies
      (root.liftProfile deadlineOf rootProfile) image.serialService
      [.player who, .environment] execution).support := by
    simp only [hphase.1, FinDist.support_bind, Set.mem_iUnion]
    exact ⟨chosen, hchosen, submitted, hsubmitted, hincluded⟩
  have hnext : ForwardCheckpoint root rootProfile deadlineOf nextPlan
      profile.afterCommit.afterReveal next included := by
    refine ⟨.publicChoice checkpoint.continuation, hrefines,
      checkpoint.reached_after _ included hnative,
      checkpoint.aligned_after_phase (.publicChoice code) _ hhead included hnative, ?_, ?_⟩
    · exact ProfileContinuation.publicChoice_phase_preserves_nextCaches root rootProfile
        publicGuard nextPlan profile checkpoint.continuation deadlineOf image.serialService
        current execution included
        checkpoint.refines hunresolved ((List.forall_cons _ _ _).mp checkpoint.caches).2 hnative
    · have haccepted := ApplicationImage.AcceptedBindingPrefix.runPolicies image
          state.nodes.length (root.liftProfile deadlineOf rootProfile) image.serialService
          [.player who, .environment] execution included checkpoint.accepted hnative
      have hadvance := ApplicationImage.AcceptedBindingPrefix.advance_of_coveredNonbinding root
        deadlineOf state.nodes.length (state.nodes.length + 2) included.native.application
        (.publicChoice code) haccepted hmem
        (by intro binding hbinding; cases hbinding) (by
          intro node hlower hupper
          change node ∈ [state.nodes.length, state.nodes.length + 1]
          simp only [List.mem_cons]
          omega)
      simpa only [BuildState.addRevealEvent_nodes, BuildState.addCommitEvent_nodes,
        List.length_append, List.length_singleton, Nat.add_assoc] using hadvance
  rw [hafter next included hnext, hsource]

end Vegas.ApplicationPlan.ForwardCheckpoint

/--
info: 'Vegas.ApplicationPlan.ForwardCheckpoint.publicChoice_bind' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.ForwardCheckpoint.publicChoice_bind
