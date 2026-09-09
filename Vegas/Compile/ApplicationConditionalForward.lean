/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationForwardCheckpoint
import Vegas.Compile.ApplicationInitialReads
import Vegas.Compile.ApplicationPhaseCaches
import Vegas.Compile.ConditionalPhaseExecution
import Vegas.Compile.ConditionalSnapshot

/-! # Forward composition at conditional-publication heads

The two conditional plan constructors have the same operational endpoint and
source continuation.  This module factors their common phase proof and exposes
one induction step for each accounting constructor.  Runtime execution remains
the original whole-plan lifted profile paired with its serial service.
-/

noncomputable section

namespace Vegas.ApplicationPlan.ForwardCheckpoint

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

private theorem conditional_forward_common
    {rootContext Γ : VCtx P L} {rootPending headPending pending : Finset VarId}
    {rootProg : VegasCore P L rootContext}
    {rootAccounted : CommitmentAccounting rootPending rootProg}
    {rootFresh : FreshBindings rootProg} {rootState : BuildState P L rootContext}
    {name publicName : VarId} {who : P} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool}
    {tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ)}
    (spec : ConditionalOpening guard)
    {headAccounted : CommitmentAccounting headPending
      (.commit name who guard (.reveal publicName who name .here tail))}
    {accounted : CommitmentAccounting pending tail}
    {fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail))}
    {state : BuildState P L Γ}
    {root : ApplicationPlan rootAccounted rootFresh rootState}
    {rootProfile : SourceBehavioralProfile rootProg}
    (headPlan : ApplicationPlan headAccounted fresh state)
    (nextPlan : ApplicationPlan accounted fresh.2.2
      (((state.addCommitEvent name who guard fresh.1).1).addRevealEvent
        publicName who .here fresh.2.1).1)
    (profile : SourceBehavioralProfile
      (.commit name who guard (.reveal publicName who name .here tail)))
    (continuation : ProfileContinuation root rootProfile headPlan profile)
    (nextContinuation : ProfileContinuation root rootProfile nextPlan
      profile.afterCommit.afterReveal)
    (publicGuard : ConditionalPublicationSite.PubliclyValidatable
      (ConditionalPublicationSite.atHead name publicName who guard tail spec) fresh state)
    (deadlineOf : Nat → Nat)
    (current : CoupledAt
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh state).graph state)
    (execution : (root.image deadlineOf).application.PolicyExecution)
    (checkpoint : ForwardCheckpoint root rootProfile deadlineOf headPlan profile
      current execution)
    (hinitial : ∀ ref ∈ (eventGuardOf state who guard).choiceReads,
      ∀ fieldSpec,
        (compileCore (.commit name who guard (.reveal publicName who name .here tail))
          fresh state).graph.field? ref.field = some fieldSpec →
      ∀ value, fieldSpec.source = .initial value → fieldSpec.owner = none)
    (horigins : (root.image deadlineOf).HasBindingOrigins)
    (hhead : headPlan.instructions deadlineOf =
      .conditional ((ConditionalPublicationSite.atHead name publicName who guard tail spec).code
        fresh state
        ((ConditionalPublicationSite.atHead name publicName who guard tail spec).sourceField
          fresh state)
        (deadlineOf ((ConditionalPublicationSite.atHead name publicName who guard tail spec).choice
          |>.publicationNode fresh state))) :: nextPlan.instructions deadlineOf)
    (hpolicy : ∀ history,
      (root.liftProfile deadlineOf rootProfile who) history
          (State.observe (root.image deadlineOf).application execution.native who) =
        let site := ConditionalPublicationSite.atHead name publicName who guard tail spec
        (site.imageController fresh state (site.sourceField fresh state)
          (deadlineOf (site.choice.publicationNode fresh state)) (root.image deadlineOf)
          ((root.image deadlineOf).ownerReadout? who
            (eventGuardOf state who guard).choiceReads)
          (profile who site.choice.decision) (fun _ _ => false)).policy
            (root.image deadlineOf).application history
            (State.observe (root.image deadlineOf).application execution.native who))
    (hcaches : ∀ final, final ∈ ((root.image deadlineOf).application.runPolicies
        (root.liftProfile deadlineOf rootProfile) (root.image deadlineOf).serialService
        [.player who, .environment] execution).support →
      nextPlan.RemainingCachesEmpty (root.image deadlineOf) deadlineOf final)
    {Ω : Type*} (after : (root.image deadlineOf).application.PolicyExecution → FinDist Ω)
    (sourceAfter : VEnv L
      ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ) → FinDist Ω)
    (ih : ∀ nextCurrent nextExecution,
      ForwardCheckpoint root rootProfile deadlineOf nextPlan
          profile.afterCommit.afterReveal nextCurrent nextExecution →
        after nextExecution = sourceAfter nextCurrent.current.source) :
    (((root.image deadlineOf).application.runPolicies
        (root.liftProfile deadlineOf rootProfile) (root.image deadlineOf).serialService
        [.player who, .environment] execution).bind after) =
      (profile who
        (ConditionalPublicationSite.atHead name publicName who guard tail spec).choice.decision
        ((current.current.source.toView who).eraseEnv)).bind fun chosen =>
          sourceAfter ((current.current.source.cons chosen.1).cons chosen.1) := by
  let plan := headPlan
  let image := root.image deadlineOf
  let site := ConditionalPublicationSite.atHead name publicName who guard tail spec
  let sourceSlot := site.sourceField fresh state
  let deadline := deadlineOf (site.choice.publicationNode fresh state)
  let code := site.code fresh state sourceSlot deadline
  let phase : List (@Invocation P) := [.player who, .environment]
  have hcodeMem : (ApplicationInstruction.conditional code : ApplicationInstruction P L) ∈
      root.instructions deadlineOf := by
    apply checkpoint.instruction_mem
    rw [hhead]
    exact List.mem_cons_self
  have hcode : image.lookup code.endpoint.publicationNode = some (.conditional code) :=
    root.image_lookup_of_mem deadlineOf (.conditional code) hcodeMem
  have hserviceCode : image.instructions[execution.environmentHistory.length]? =
      some (.conditional code) := checkpoint.head_lookup (.conditional code)
        (nextPlan.instructions deadlineOf) hhead
  have hsourceReady := current.current.nextReady current.completedPrefix
    (site.choice.choiceNode fresh state) (by rfl)
  obtain ⟨previous, hreached⟩ := checkpoint.reached
  obtain ⟨reads, hreadout, hreads, _hview⟩ :=
    continuation.runPolicies_ownerReadout?_of_ready_source_view deadlineOf who
      (root.liftProfile deadlineOf rootProfile) rfl image.serialService previous execution
      hreached site.choice.decision current.current.graph.1 checkpoint.refines hsourceReady
      hinitial current.current.source (BuildState.Agrees.view current.current.agrees who)
  have haccepted : execution.native.application.memory.accepted (state.fieldOf spec.binding) =
      some (who, sourceSlot) := by
    have haccepted := ApplicationImage.AcceptedBindingPrefix.conditionalHandle
      checkpoint.accepted horigins code hcodeMem (by rfl)
    exact haccepted
  have hfrozen : ∀ chosen ∈
      (profile who site.choice.decision
        ((current.current.source.toView who).eraseEnv)).support,
      ∀ value, spec.encoding chosen.1 = some value →
        (execution.native.application.frozen (state.fieldOf spec.binding)).bind
          (fun typed => typed.as? spec.secretTy) = some value := by
    intro chosen _ value hvalue
    exact ConditionalPublicationSite.legal_choice_frozen guard tail spec fresh state current image
      (execution.principalHistory who) execution.native.application checkpoint.refines
      (checkpoint.registeredBindings who) haccepted chosen.1 chosen.2 value hvalue
  have hheadCache : (ApplicationInstruction.conditional code).CacheEmpty image execution := by
    apply (List.forall_iff_forall_mem.mp checkpoint.caches)
    rw [hhead]
    exact List.mem_cons_self
  have hcache : ChoiceEncoding.cachedValue image.application
      (site.choiceEncoding fresh state sourceSlot deadline
        (ApplicationImage.conditionalTransport spec.secretTy) |>.submission image.application)
      (execution.principalHistory who) = none := by
    exact hheadCache
  have henvironment : ∀ chosen ∈
      (profile who site.choice.decision
        ((current.current.source.toView who).eraseEnv)).support,
      ∀ submitted ∈ (image.application.playerStep who execution
        (.submit ((ApplicationImage.conditionalTransport spec.secretTy).encode
          (code.endpoint.publicationNode,
            code.endpoint.requestPayload (spec.encoding chosen.1))))).support,
      image.serialService submitted.environmentHistory
          (State.environmentView image.application submitted.native) =
        FinDist.pure (.include (who, execution.native.pool.nextSerial who)) := by
    intro chosen _ submitted hsubmitted
    exact image.serialService_after_submit execution submitted (.conditional code) who _
      hserviceCode rfl (checkpoint.lookup_nextSerial_eq_none who) hsubmitted
  have hphase := ConditionalPublicationSite.conditional_phase_source_law guard tail spec fresh
    state sourceSlot deadline current image
    (profile who site.choice.decision) (root.liftProfile deadlineOf rootProfile)
    image.serialService execution checkpoint.refines publicGuard haccepted hcode reads hpolicy
    henvironment (checkpoint.lookup_nextSerial_eq_none who) hcache hreadout hreads hfrozen
  rw [hphase.1, FinDist.bind_bind]
  apply FinDist.bind_congr
  intro chosen hchosen
  rw [FinDist.bind_bind]
  refine (FinDist.bind_congr (fun submitted hsubmitted => ?_)).trans
    (FinDist.bind_const _
      (sourceAfter ((current.current.source.cons chosen.1).cons chosen.1)))
  refine (FinDist.bind_congr (fun included hincluded => ?_)).trans
    (FinDist.bind_const _
      (sourceAfter ((current.current.source.cons chosen.1).cons chosen.1)))
  obtain ⟨nextCurrent, hsource, hrefinesNext⟩ :=
    hphase.2 chosen hchosen submitted hsubmitted included hincluded
  have hincludedPhase : included ∈ (image.application.runPolicies
      (root.liftProfile deadlineOf rootProfile) image.serialService phase execution).support := by
    simp only [phase, hphase.1, FinDist.support_bind, Set.mem_iUnion]
    exact ⟨chosen, hchosen, submitted, hsubmitted, hincluded⟩
  have hprefix := ApplicationImage.AcceptedBindingPrefix.runPolicies image state.nodes.length
    (root.liftProfile deadlineOf rootProfile) image.serialService phase execution included
    checkpoint.accepted hincludedPhase
  have hacceptedNext : image.AcceptedBindingPrefix (state.nodes.length + 2)
      included.native.application := by
    apply ApplicationImage.AcceptedBindingPrefix.advance_of_coveredNonbinding root deadlineOf
      state.nodes.length (state.nodes.length + 2) included.native.application
      (.conditional code) hprefix hcodeMem
    · intro binding hbinding
      cases hbinding
    · intro node hlower hupper
      change node ∈ [state.nodes.length, state.nodes.length + 1]
      simp only [List.mem_cons]
      omega
  have hnextCheckpoint : ForwardCheckpoint root rootProfile deadlineOf nextPlan
      profile.afterCommit.afterReveal nextCurrent included := by
    refine ⟨nextContinuation, hrefinesNext,
      checkpoint.reached_after phase included hincludedPhase, ?_, hcaches included hincludedPhase,
      ?_⟩
    · exact checkpoint.aligned_after_phase (.conditional code)
        (nextPlan.instructions deadlineOf) hhead included hincludedPhase
    · simpa only [BuildState.addRevealEvent_nodes, BuildState.addCommitEvent_nodes,
        List.length_append, List.length_singleton, Nat.add_assoc] using hacceptedNext
  rw [ih nextCurrent included hnextCheckpoint, hsource]

/-- Advance an accounted conditional publication through the actual generated
policy and service, then compose with an arbitrary established tail law. -/
theorem conditional_bind
    {rootContext Γ : VCtx P L} {rootPending pending : Finset VarId}
    {rootProg : VegasCore P L rootContext}
    {rootAccounted : CommitmentAccounting rootPending rootProg}
    {rootFresh : FreshBindings rootProg} {rootState : BuildState P L rootContext}
    {name publicName : VarId} {who : P} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool}
    {tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ)}
    {spec : ConditionalOpening guard} {sourceUnresolved : spec.source ∈ pending}
    {newName : name ∉ pending}
    {accounted : CommitmentAccounting (pending.erase spec.source) tail}
    {fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail))}
    {state : BuildState P L Γ}
    {root : ApplicationPlan rootAccounted rootFresh rootState}
    {rootProfile : SourceBehavioralProfile rootProg}
    (publicGuard : ConditionalPublicationSite.PubliclyValidatable
      (ConditionalPublicationSite.atHead name publicName who guard tail spec) fresh state)
    (nextPlan : ApplicationPlan accounted fresh.2.2
      (((state.addCommitEvent name who guard fresh.1).1).addRevealEvent
        publicName who .here fresh.2.1).1)
    (profile : SourceBehavioralProfile
      (.commit name who guard (.reveal publicName who name .here tail)))
    {deadlineOf : Nat → Nat}
    (current : CoupledAt
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh state).graph state)
    (execution : (root.image deadlineOf).application.PolicyExecution)
    (checkpoint : ForwardCheckpoint root rootProfile deadlineOf
      (.conditional (unresolved := sourceUnresolved) (newName := newName)
        (fresh := fresh) publicGuard nextPlan) profile current execution)
    (hinitial : BuildResult.InitialReadsPublic (compileCore
      (.commit name who guard (.reveal publicName who name .here tail)) fresh state)
      (eventGuardOf state who guard).choiceReads)
    (horigins : (root.image deadlineOf).HasBindingOrigins)
    {Ω : Type*} (after : (root.image deadlineOf).application.PolicyExecution → FinDist Ω)
    (sourceAfter : VEnv L
      ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ) → FinDist Ω)
    (ih : ∀ nextCurrent nextExecution,
      ForwardCheckpoint root rootProfile deadlineOf nextPlan
          profile.afterCommit.afterReveal nextCurrent nextExecution →
        after nextExecution = sourceAfter nextCurrent.current.source) :
    (((root.image deadlineOf).application.runPolicies
        (root.liftProfile deadlineOf rootProfile) (root.image deadlineOf).serialService
        [.player who, .environment] execution).bind after) =
      (profile who
        (ConditionalPublicationSite.atHead name publicName who guard tail spec).choice.decision
        ((current.current.source.toView who).eraseEnv)).bind fun chosen =>
          sourceAfter ((current.current.source.cons chosen.1).cons chosen.1) := by
  let plan := ApplicationPlan.conditional (unresolved := sourceUnresolved)
    (newName := newName) (fresh := fresh) publicGuard nextPlan
  have hunresolved : execution.native.application.memory.done (state.nodes.length + 1) = false := by
    have hbound : state.nodes.length + 1 <
        (compileCore (.commit name who guard (.reveal publicName who name .here tail))
          fresh state).graph.nodeCount := by
      exact (ConditionalPublicationSite.atHead name publicName who guard tail spec).choice
        |>.publicationNode fresh state |>.isLt
    let node : Fin (compileCore
        (.commit name who guard (.reveal publicName who name .here tail)) fresh state
      ).graph.nodeCount := ⟨state.nodes.length + 1, hbound⟩
    apply Bool.eq_false_iff.mpr
    intro hdone
    have hmem := (checkpoint.refines.memory.completed node).mp hdone
    have hlt := (current.completedPrefix node).mp hmem
    change state.nodes.length + 1 < state.nodes.length at hlt
    omega
  have hdoneView : (State.observe (root.image deadlineOf).application
      execution.native who).application.done (state.nodes.length + 1) = false := hunresolved
  apply conditional_forward_common (root := root) (rootProfile := rootProfile) spec
    plan nextPlan profile
    checkpoint.continuation (.conditional checkpoint.continuation) publicGuard deadlineOf
    current execution checkpoint hinitial
    horigins (by rfl)
  · intro history
    change root.liftProfileIn (root.image deadlineOf) deadlineOf rootProfile who history
      (State.observe (root.image deadlineOf).application execution.native who) = _
    rw [checkpoint.continuation.liftProfileIn_eq_of_refines
      (root.image deadlineOf) deadlineOf current
      execution.native checkpoint.refines who history]
    simp only [ApplicationPlan.liftProfileIn, hdoneView, Bool.false_eq_true, ↓reduceIte]
    rfl
  · intro final hfinal
    have htail : nextPlan.RemainingCachesEmpty (root.image deadlineOf) deadlineOf execution :=
      (List.forall_cons _ _ _).mp checkpoint.caches |>.2
    exact checkpoint.continuation.conditional_phase_preserves_nextCaches root rootProfile
      publicGuard nextPlan profile deadlineOf (root.image deadlineOf).serialService
      current execution final
      checkpoint.refines hunresolved htail hfinal
  · exact ih

/-- The conditional-copy accounting constructor has the same generated phase
law; only its proof-side accounting continuation differs. -/
theorem conditionalCopy_bind
    {rootContext Γ : VCtx P L} {rootPending pending : Finset VarId}
    {rootProg : VegasCore P L rootContext}
    {rootAccounted : CommitmentAccounting rootPending rootProg}
    {rootFresh : FreshBindings rootProg} {rootState : BuildState P L rootContext}
    {name publicName : VarId} {who : P} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool}
    {tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ)}
    (spec : ConditionalOpening guard)
    {newName : name ∉ pending} {unresolved : name ∈ insert name pending}
    {accounted : CommitmentAccounting ((insert name pending).erase name) tail}
    {fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail))}
    {state : BuildState P L Γ}
    {root : ApplicationPlan rootAccounted rootFresh rootState}
    {rootProfile : SourceBehavioralProfile rootProg}
    (publicGuard : ConditionalPublicationSite.PubliclyValidatable
      (ConditionalPublicationSite.atHead name publicName who guard tail spec) fresh state)
    (nextPlan : ApplicationPlan accounted fresh.2.2
      (((state.addCommitEvent name who guard fresh.1).1).addRevealEvent
        publicName who .here fresh.2.1).1)
    (profile : SourceBehavioralProfile
      (.commit name who guard (.reveal publicName who name .here tail)))
    {deadlineOf : Nat → Nat}
    (current : CoupledAt
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh state).graph state)
    (execution : (root.image deadlineOf).application.PolicyExecution)
    (checkpoint : ForwardCheckpoint root rootProfile deadlineOf
      (.conditionalCopy (newName := newName) (unresolved := unresolved) (fresh := fresh)
        spec publicGuard nextPlan) profile current execution)
    (hinitial : BuildResult.InitialReadsPublic (compileCore
      (.commit name who guard (.reveal publicName who name .here tail)) fresh state)
      (eventGuardOf state who guard).choiceReads)
    (horigins : (root.image deadlineOf).HasBindingOrigins)
    {Ω : Type*} (after : (root.image deadlineOf).application.PolicyExecution → FinDist Ω)
    (sourceAfter : VEnv L
      ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ) → FinDist Ω)
    (ih : ∀ nextCurrent nextExecution,
      ForwardCheckpoint root rootProfile deadlineOf nextPlan
          profile.afterCommit.afterReveal nextCurrent nextExecution →
        after nextExecution = sourceAfter nextCurrent.current.source) :
    (((root.image deadlineOf).application.runPolicies
        (root.liftProfile deadlineOf rootProfile) (root.image deadlineOf).serialService
        [.player who, .environment] execution).bind after) =
      (profile who
        (ConditionalPublicationSite.atHead name publicName who guard tail spec).choice.decision
        ((current.current.source.toView who).eraseEnv)).bind fun chosen =>
          sourceAfter ((current.current.source.cons chosen.1).cons chosen.1) := by
  let plan := ApplicationPlan.conditionalCopy (newName := newName)
    (unresolved := unresolved) (fresh := fresh) spec publicGuard nextPlan
  have hunresolved : execution.native.application.memory.done (state.nodes.length + 1) = false := by
    have hbound : state.nodes.length + 1 <
        (compileCore (.commit name who guard (.reveal publicName who name .here tail))
          fresh state).graph.nodeCount := by
      exact (ConditionalPublicationSite.atHead name publicName who guard tail spec).choice
        |>.publicationNode fresh state |>.isLt
    let node : Fin (compileCore
        (.commit name who guard (.reveal publicName who name .here tail)) fresh state
      ).graph.nodeCount := ⟨state.nodes.length + 1, hbound⟩
    apply Bool.eq_false_iff.mpr
    intro hdone
    have hmem := (checkpoint.refines.memory.completed node).mp hdone
    have hlt := (current.completedPrefix node).mp hmem
    change state.nodes.length + 1 < state.nodes.length at hlt
    omega
  have hdoneView : (State.observe (root.image deadlineOf).application
      execution.native who).application.done (state.nodes.length + 1) = false := hunresolved
  apply conditional_forward_common (root := root) (rootProfile := rootProfile) spec
    plan nextPlan profile
    checkpoint.continuation (.conditionalCopy checkpoint.continuation) publicGuard deadlineOf
    current execution checkpoint hinitial
    horigins (by rfl)
  · intro history
    change root.liftProfileIn (root.image deadlineOf) deadlineOf rootProfile who history
      (State.observe (root.image deadlineOf).application execution.native who) = _
    rw [checkpoint.continuation.liftProfileIn_eq_of_refines
      (root.image deadlineOf) deadlineOf current
      execution.native checkpoint.refines who history]
    simp only [ApplicationPlan.liftProfileIn, hdoneView, Bool.false_eq_true, ↓reduceIte]
    rfl
  · intro final hfinal
    have htail : nextPlan.RemainingCachesEmpty (root.image deadlineOf) deadlineOf execution :=
      (List.forall_cons _ _ _).mp checkpoint.caches |>.2
    exact checkpoint.continuation.conditionalCopy_phase_preserves_nextCaches
      root rootProfile spec publicGuard
      nextPlan profile deadlineOf (root.image deadlineOf).serialService current execution final
      checkpoint.refines hunresolved htail hfinal
  · exact ih

end Vegas.ApplicationPlan.ForwardCheckpoint

/-- info: 'Vegas.ApplicationPlan.ForwardCheckpoint.conditional_bind' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.ForwardCheckpoint.conditional_bind

/-- info: 'Vegas.ApplicationPlan.ForwardCheckpoint.conditionalCopy_bind' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.ForwardCheckpoint.conditionalCopy_bind
