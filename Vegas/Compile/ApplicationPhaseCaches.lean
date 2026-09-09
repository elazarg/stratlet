/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationPolicyCache

/-! # Future-cache preservation across source-ordered phases

The local head-controller cache laws lift to the actual invocation fragments
used by the source-ordered reference execution. Player commands do not alter
the application's public memory, so a binding head remains unresolved between
its registration and submission invocations. The final environment invocation
does not alter principal histories and therefore preserves every future cache,
regardless of whether the requested application transition succeeds.

These are support-wise phase invariants for the original root lifted profile.
They do not assert that the service selects or accepts the head request.
-/

noncomputable section

namespace Vegas

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

namespace ApplicationImage

/-- Any player command leaves the public application memory unchanged.
Private registration changes only the preparation service; submissions,
replays, and waits change only message-runner state and histories. -/
theorem playerStep_memory
    (image : ApplicationImage P L) (who : P)
    (execution next : image.application.PolicyExecution)
    (command : image.application.PlayerCommand)
    (hnext : next ∈ (image.application.playerStep who execution command).support) :
    next.native.application.memory = execution.native.application.memory := by
  have hnative : next.native ∈
      ((image.application.playerStep who execution command).map
        PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  rw [image.application.playerStep_native] at hnative
  cases command with
  | privateCommand command =>
      cases command with
      | register slot value =>
          simp only [PlayerCommand.toAction, MessageApplication.step,
            ApplicationImage.application, FinDist.mem_support_pure] at hnative
          rw [hnative]
          rfl
  | submit payload | replay id | wait =>
      simp only [PlayerCommand.toAction, MessageApplication.step,
        FinDist.mem_support_pure] at hnative
      rw [hnative]

/-- A player command preserves a fixed graph refinement. This is stronger
than public-memory equality only in the private-registration branch, where it
uses the existing preparation-local refinement law. -/
theorem playerStep_refines
    (image : ApplicationImage P L) {G : Graph P L} (cfg : Config G)
    (who : P) (execution next : image.application.PolicyExecution)
    (command : image.application.PlayerCommand)
    (hrefines : execution.native.application.Refines cfg)
    (hnext : next ∈ (image.application.playerStep who execution command).support) :
    next.native.application.Refines cfg := by
  have hnative : next.native ∈
      ((image.application.playerStep who execution command).map
        PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  rw [image.application.playerStep_native] at hnative
  cases command with
  | privateCommand command =>
      cases command with
      | register slot value =>
          simp only [PlayerCommand.toAction, MessageApplication.step,
            ApplicationImage.application, FinDist.mem_support_pure] at hnative
          rw [hnative]
          exact hrefines.register who slot value
  | submit payload | replay id | wait =>
      simp only [PlayerCommand.toAction, MessageApplication.step,
        FinDist.mem_support_pure] at hnative
      rw [hnative]
      exact hrefines

end ApplicationImage

namespace ApplicationPlan

/-- One actual player invocation followed by one arbitrary environment
invocation preserves a suffix invariant once the player step establishes it. -/
private theorem player_environment_preserves_nextCaches
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ}
    (nextPlan : ApplicationPlan accounted fresh state)
    (image : ApplicationImage P L) (deadlineOf : Nat → Nat)
    (players : P → image.application.PlayerPolicy)
    (environment : image.application.EnvironmentPolicy) (player : P)
    (execution final : image.application.PolicyExecution)
    (hplayer : ∀ command middle,
      command ∈ (players player (execution.principalHistory player)
        (State.observe image.application execution.native player)).support →
      middle ∈ (image.application.playerStep player execution command).support →
      nextPlan.RemainingCachesEmpty image deadlineOf middle)
    (hfinal : final ∈ (image.application.runPolicies players environment
      [.player player, .environment] execution).support) :
    nextPlan.RemainingCachesEmpty image deadlineOf final := by
  simp only [MessageApplication.runPolicies, FinDist.support_bind,
    Set.mem_iUnion, FinDist.mem_support_pure] at hfinal
  obtain ⟨middle, hmiddle, after, hafter, rfl⟩ := hfinal
  simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle hafter
  obtain ⟨command, hcommand, hstep⟩ := hmiddle
  obtain ⟨environmentCommand, _, henvironment⟩ := hafter
  exact nextPlan.remainingCachesEmpty_environmentPolicyStep image deadlineOf middle
    environmentCommand final henvironment (hplayer command middle hcommand hstep)

/-- A single arbitrary environment invocation preserves every cache in a
remaining suffix. This is the complete cache argument for a chance head. -/
theorem environment_phase_preserves_remainingCaches
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ}
    (plan : ApplicationPlan accounted fresh state)
    (image : ApplicationImage P L) (deadlineOf : Nat → Nat)
    (players : P → image.application.PlayerPolicy)
    (environment : image.application.EnvironmentPolicy)
    (execution final : image.application.PolicyExecution)
    (hfresh : plan.RemainingCachesEmpty image deadlineOf execution)
    (hfinal : final ∈ (image.application.runPolicies players environment
      [.environment] execution).support) :
    plan.RemainingCachesEmpty image deadlineOf final := by
  simp only [MessageApplication.runPolicies, FinDist.support_bind,
    Set.mem_iUnion, FinDist.mem_support_pure] at hfinal
  obtain ⟨middle, hmiddle, rfl⟩ := hfinal
  simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
  obtain ⟨command, _, hstep⟩ := hmiddle
  exact plan.remainingCachesEmpty_environmentPolicyStep image deadlineOf execution
    command final hstep hfresh

variable {rootContext : VCtx P L} {rootPending : Finset VarId}
variable {rootProg : VegasCore P L rootContext}
variable {rootAccounted : CommitmentAccounting rootPending rootProg}
variable {rootFresh : FreshBindings rootProg}
variable {rootState : BuildState P L rootContext}
variable (root : ApplicationPlan rootAccounted rootFresh rootState)
variable (rootProfile : SourceBehavioralProfile rootProg)

/-- Convert the original root policy to an exact continuation head for one
player invocation, then preserve the supplied tail caches through the phase's
environment invocation. The command premise is local to the actual head
policy, rather than an externally supplied raw controller. -/
theorem ProfileContinuation.player_environment_phase_preserves_nextCaches
    {Γ Δ : VCtx P L} {pending nextPending : Finset VarId}
    {prog : VegasCore P L Γ} {nextProg : VegasCore P L Δ}
    {accounted : CommitmentAccounting pending prog}
    {nextAccounted : CommitmentAccounting nextPending nextProg}
    {fresh : FreshBindings prog} {nextFresh : FreshBindings nextProg}
    {state : BuildState P L Γ} {nextState : BuildState P L Δ}
    (plan : ApplicationPlan accounted fresh state)
    (profile : SourceBehavioralProfile prog)
    (continuation : ProfileContinuation root rootProfile plan profile)
    (nextPlan : ApplicationPlan nextAccounted nextFresh nextState)
    (deadlineOf : Nat → Nat)
    (environment : (root.image deadlineOf).application.EnvironmentPolicy)
    (player : P)
    (current : CoupledAt (compileCore prog fresh state).graph state)
    (execution final : (root.image deadlineOf).application.PolicyExecution)
    (hrefines : execution.native.application.Refines current.current.graph.1)
    (hplayer : ∀ command middle,
      command ∈ (plan.liftProfileIn (root.image deadlineOf) deadlineOf profile player
        (execution.principalHistory player)
        (State.observe (root.image deadlineOf).application execution.native player)).support →
      middle ∈ ((root.image deadlineOf).application.playerStep player execution
        command).support →
      nextPlan.RemainingCachesEmpty (root.image deadlineOf) deadlineOf middle)
    (hfinal : final ∈ ((root.image deadlineOf).application.runPolicies
      (root.liftProfile deadlineOf rootProfile) environment
      [.player player, .environment] execution).support) :
    nextPlan.RemainingCachesEmpty (root.image deadlineOf) deadlineOf final := by
  let image := root.image deadlineOf
  apply player_environment_preserves_nextCaches nextPlan image deadlineOf
    (root.liftProfile deadlineOf rootProfile) environment player execution final
  · intro command middle hcommand hstep
    have hhead := hcommand
    change command ∈
      (root.liftProfileIn image deadlineOf rootProfile player
        (execution.principalHistory player)
        (State.observe image.application execution.native player)).support at hhead
    rw [continuation.liftProfileIn_eq_of_refines image deadlineOf current execution.native
      hrefines player (execution.principalHistory player)] at hhead
    exact hplayer command middle hhead hstep
  · exact hfinal

/-- The chance phase contains only an environment invocation, so the original
root profile cannot populate any future player cache. -/
theorem ProfileContinuation.sample_phase_preserves_nextCaches
    {Γ : VCtx P L} {pending : Finset VarId} {name : VarId} {ty : L.Ty}
    {dist : L.DistExpr (erasePubVCtx Γ) ty}
    {tail : VegasCore P L ((name, .pub ty) :: Γ)}
    {accounted : CommitmentAccounting pending tail}
    {fresh : FreshBindings (.sample name dist tail)} {state : BuildState P L Γ}
    (nextPlan : ApplicationPlan accounted fresh.2
      (state.addSampleEvent name dist fresh.1).1)
    (profile : SourceBehavioralProfile (.sample name dist tail))
    (_continuation : ProfileContinuation root rootProfile
      (.sample (fresh := fresh) nextPlan) profile)
    (deadlineOf : Nat → Nat)
    (environment : (root.image deadlineOf).application.EnvironmentPolicy)
    (execution final : (root.image deadlineOf).application.PolicyExecution)
    (hfresh : nextPlan.RemainingCachesEmpty (root.image deadlineOf) deadlineOf execution)
    (hfinal : final ∈ ((root.image deadlineOf).application.runPolicies
      (root.liftProfile deadlineOf rootProfile) environment [.environment] execution).support) :
    nextPlan.RemainingCachesEmpty (root.image deadlineOf) deadlineOf final :=
  environment_phase_preserves_remainingCaches nextPlan (root.image deadlineOf) deadlineOf
    (root.liftProfile deadlineOf rootProfile) environment execution final hfresh hfinal

/-- Two consecutive owner invocations at an unresolved binding head, followed
by an arbitrary environment invocation, preserve every future cache. Dispatch
continues to use the original root lifted profile on both player invocations. -/
theorem ProfileContinuation.binding_phase_preserves_nextCaches
    {Γ : VCtx P L} {pending : Finset VarId} {name : VarId} {who : P}
    {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool}
    {tail : VegasCore P L ((name, .sealed who ty) :: Γ)}
    {newName : name ∉ pending}
    {accounted : CommitmentAccounting (insert name pending) tail}
    {fresh : FreshBindings (.commit name who guard tail)}
    {state : BuildState P L Γ} (unrestricted : UnrestrictedBinding guard)
    (nextPlan : ApplicationPlan accounted fresh.2
      (state.addCommitEvent name who guard fresh.1).1)
    (profile : SourceBehavioralProfile (.commit name who guard tail))
    (continuation : ProfileContinuation root rootProfile
      (.binding (newName := newName) (fresh := fresh) unrestricted nextPlan) profile)
    (deadlineOf : Nat → Nat)
    (environment : (root.image deadlineOf).application.EnvironmentPolicy)
    (current : CoupledAt
      (compileCore (.commit name who guard tail) fresh state).graph state)
    (execution final : (root.image deadlineOf).application.PolicyExecution)
    (hrefines : execution.native.application.Refines current.current.graph.1)
    (hunresolved : execution.native.application.memory.done state.nodes.length = false)
    (hfresh : nextPlan.RemainingCachesEmpty (root.image deadlineOf) deadlineOf execution)
    (hfinal : final ∈ ((root.image deadlineOf).application.runPolicies
      (root.liftProfile deadlineOf rootProfile) environment
      [.player who, .player who, .environment] execution).support) :
    nextPlan.RemainingCachesEmpty (root.image deadlineOf) deadlineOf final := by
  let image := root.image deadlineOf
  simp only [MessageApplication.runPolicies, FinDist.support_bind,
    Set.mem_iUnion, FinDist.mem_support_pure] at hfinal
  obtain ⟨first, hfirst, second, hsecond, after, hafter, rfl⟩ := hfinal
  simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at hfirst
  simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at hsecond
  simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at hafter
  obtain ⟨firstCommand, hfirstCommand, hfirstStep⟩ := hfirst
  obtain ⟨secondCommand, hsecondCommand, hsecondStep⟩ := hsecond
  obtain ⟨environmentCommand, _, henvironment⟩ := hafter
  have hfirstHead := hfirstCommand
  change firstCommand ∈
    (root.liftProfileIn image deadlineOf rootProfile who
      (execution.principalHistory who)
      (State.observe image.application execution.native who)).support at hfirstHead
  rw [continuation.liftProfileIn_eq_of_refines image deadlineOf current execution.native
    hrefines who (execution.principalHistory who)] at hfirstHead
  have hfreshFirst := binding_head_preserves_nextCaches unrestricted nextPlan deadlineOf image
    profile who execution first firstCommand hunresolved hfirstHead hfirstStep hfresh
  have hrefinesFirst := image.playerStep_refines current.current.graph.1 who execution first
    firstCommand hrefines hfirstStep
  have hmemoryFirst := image.playerStep_memory who execution first firstCommand hfirstStep
  have hunresolvedFirst :
      first.native.application.memory.done state.nodes.length = false := by
    rw [hmemoryFirst]
    exact hunresolved
  have hsecondHead := hsecondCommand
  change secondCommand ∈
    (root.liftProfileIn image deadlineOf rootProfile who
      (first.principalHistory who)
      (State.observe image.application first.native who)).support at hsecondHead
  rw [continuation.liftProfileIn_eq_of_refines image deadlineOf current first.native
    hrefinesFirst who (first.principalHistory who)] at hsecondHead
  have hfreshSecond := binding_head_preserves_nextCaches unrestricted nextPlan deadlineOf image
    profile who first second secondCommand hunresolvedFirst hsecondHead hsecondStep hfreshFirst
  exact nextPlan.remainingCachesEmpty_environmentPolicyStep image deadlineOf second
    environmentCommand final henvironment hfreshSecond

/-- An unresolved ordinary public-choice head preserves all later caches
through its owner invocation and the following environment invocation. -/
theorem ProfileContinuation.publicChoice_phase_preserves_nextCaches
    {Γ : VCtx P L} {pending : Finset VarId} {name publicName : VarId} {who : P}
    {ty : L.Ty}
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
    (continuation : ProfileContinuation root rootProfile
      (.publicChoice (newName := newName) (unresolved := unresolved)
        (fresh := fresh) publicGuard nextPlan) profile)
    (deadlineOf : Nat → Nat)
    (environment : (root.image deadlineOf).application.EnvironmentPolicy)
    (current : CoupledAt
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh state).graph state)
    (execution final : (root.image deadlineOf).application.PolicyExecution)
    (hrefines : execution.native.application.Refines current.current.graph.1)
    (hunresolved : execution.native.application.memory.done (state.nodes.length + 1) = false)
    (hfresh : nextPlan.RemainingCachesEmpty (root.image deadlineOf) deadlineOf execution)
    (hfinal : final ∈ ((root.image deadlineOf).application.runPolicies
      (root.liftProfile deadlineOf rootProfile) environment
      [.player who, .environment] execution).support) :
    nextPlan.RemainingCachesEmpty (root.image deadlineOf) deadlineOf final := by
  apply continuation.player_environment_phase_preserves_nextCaches root rootProfile
    (.publicChoice (newName := newName) (unresolved := unresolved)
      (fresh := fresh) publicGuard nextPlan) profile nextPlan deadlineOf environment who
      current execution final hrefines
  · intro command middle hcommand hstep
    exact publicChoice_head_preserves_nextCaches publicGuard nextPlan deadlineOf
      (root.image deadlineOf) profile who execution middle command hunresolved hcommand hstep
      hfresh
  · exact hfinal

/-- An unresolved accounted conditional-publication head preserves all later
caches through its owner invocation and the following environment invocation. -/
theorem ProfileContinuation.conditional_phase_preserves_nextCaches
    {Γ : VCtx P L} {pending : Finset VarId} {name publicName : VarId} {who : P}
    {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool}
    {tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ)}
    {spec : ConditionalOpening guard} {sourceUnresolved : spec.source ∈ pending}
    {newName : name ∉ pending}
    {accounted : CommitmentAccounting (pending.erase spec.source) tail}
    {fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail))}
    {state : BuildState P L Γ}
    (publicGuard : ConditionalPublicationSite.PubliclyValidatable
      (ConditionalPublicationSite.atHead name publicName who guard tail spec) fresh state)
    (nextPlan : ApplicationPlan accounted fresh.2.2
      (((state.addCommitEvent name who guard fresh.1).1).addRevealEvent
        publicName who .here fresh.2.1).1)
    (profile : SourceBehavioralProfile
      (.commit name who guard (.reveal publicName who name .here tail)))
    (continuation : ProfileContinuation root rootProfile
      (.conditional (unresolved := sourceUnresolved) (newName := newName)
        (fresh := fresh) publicGuard nextPlan) profile)
    (deadlineOf : Nat → Nat)
    (environment : (root.image deadlineOf).application.EnvironmentPolicy)
    (current : CoupledAt
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh state).graph state)
    (execution final : (root.image deadlineOf).application.PolicyExecution)
    (hrefines : execution.native.application.Refines current.current.graph.1)
    (hunresolved : execution.native.application.memory.done (state.nodes.length + 1) = false)
    (hfresh : nextPlan.RemainingCachesEmpty (root.image deadlineOf) deadlineOf execution)
    (hfinal : final ∈ ((root.image deadlineOf).application.runPolicies
      (root.liftProfile deadlineOf rootProfile) environment
      [.player who, .environment] execution).support) :
    nextPlan.RemainingCachesEmpty (root.image deadlineOf) deadlineOf final := by
  apply continuation.player_environment_phase_preserves_nextCaches root rootProfile
    (.conditional (unresolved := sourceUnresolved) (newName := newName)
      (fresh := fresh) publicGuard nextPlan) profile nextPlan deadlineOf environment who
      current execution final hrefines
  · intro command middle hcommand hstep
    exact conditional_head_preserves_nextCaches publicGuard nextPlan deadlineOf
      (root.image deadlineOf) profile who execution middle command hunresolved hcommand hstep
      hfresh
  · exact hfinal

/-- An unresolved conditional-copy head preserves all later caches through
its owner invocation and the following environment invocation. -/
theorem ProfileContinuation.conditionalCopy_phase_preserves_nextCaches
    {Γ : VCtx P L} {pending : Finset VarId} {name publicName : VarId} {who : P}
    {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool}
    {tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ)}
    (spec : ConditionalOpening guard)
    {newName : name ∉ pending} {unresolved : name ∈ insert name pending}
    {accounted : CommitmentAccounting ((insert name pending).erase name) tail}
    {fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail))}
    {state : BuildState P L Γ}
    (publicGuard : ConditionalPublicationSite.PubliclyValidatable
      (ConditionalPublicationSite.atHead name publicName who guard tail spec) fresh state)
    (nextPlan : ApplicationPlan accounted fresh.2.2
      (((state.addCommitEvent name who guard fresh.1).1).addRevealEvent
        publicName who .here fresh.2.1).1)
    (profile : SourceBehavioralProfile
      (.commit name who guard (.reveal publicName who name .here tail)))
    (continuation : ProfileContinuation root rootProfile
      (.conditionalCopy (newName := newName) (unresolved := unresolved)
        (fresh := fresh) spec publicGuard nextPlan) profile)
    (deadlineOf : Nat → Nat)
    (environment : (root.image deadlineOf).application.EnvironmentPolicy)
    (current : CoupledAt
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh state).graph state)
    (execution final : (root.image deadlineOf).application.PolicyExecution)
    (hrefines : execution.native.application.Refines current.current.graph.1)
    (hunresolved : execution.native.application.memory.done (state.nodes.length + 1) = false)
    (hfresh : nextPlan.RemainingCachesEmpty (root.image deadlineOf) deadlineOf execution)
    (hfinal : final ∈ ((root.image deadlineOf).application.runPolicies
      (root.liftProfile deadlineOf rootProfile) environment
      [.player who, .environment] execution).support) :
    nextPlan.RemainingCachesEmpty (root.image deadlineOf) deadlineOf final := by
  apply continuation.player_environment_phase_preserves_nextCaches root rootProfile
    (.conditionalCopy (newName := newName) (unresolved := unresolved)
      (fresh := fresh) spec publicGuard nextPlan) profile nextPlan deadlineOf environment who
      current execution final hrefines
  · intro command middle hcommand hstep
    exact conditionalCopy_head_preserves_nextCaches spec publicGuard nextPlan deadlineOf
      (root.image deadlineOf) profile who execution middle command hunresolved hcommand hstep
      hfresh
  · exact hfinal

end ApplicationPlan
end Vegas

/-- info: 'Vegas.ApplicationImage.playerStep_memory' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.playerStep_memory

/-- info: 'Vegas.ApplicationPlan.ProfileContinuation.binding_phase_preserves_nextCaches'
depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.ProfileContinuation.binding_phase_preserves_nextCaches

/-- info: 'Vegas.ApplicationPlan.ProfileContinuation.sample_phase_preserves_nextCaches'
depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.ProfileContinuation.sample_phase_preserves_nextCaches

/-- info: 'Vegas.ApplicationPlan.ProfileContinuation.publicChoice_phase_preserves_nextCaches'
depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.ProfileContinuation.publicChoice_phase_preserves_nextCaches

/-- info: 'Vegas.ApplicationPlan.ProfileContinuation.conditional_phase_preserves_nextCaches'
depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.ProfileContinuation.conditional_phase_preserves_nextCaches

/--
info: 'Vegas.ApplicationPlan.ProfileContinuation.conditionalCopy_phase_preserves_nextCaches'
depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.ApplicationPlan.ProfileContinuation.conditionalCopy_phase_preserves_nextCaches
