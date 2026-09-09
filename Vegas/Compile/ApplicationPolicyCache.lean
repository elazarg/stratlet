/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationCacheSeparation
import Vegas.Compile.ApplicationProfileContinuation

/-! # Future-cache preservation by lifted source policies

When the first instruction of a source-plan suffix is unresolved, the lifted
profile either runs that instruction's generated controller or waits.  Its
actual supported player step cannot populate any cache belonging to the later
suffix. This is a local forward invariant; it assumes neither service progress
nor a whole-program outcome law.
-/

noncomputable section

namespace Vegas.ApplicationPlan

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- The first emitted instruction has a different dispatch address from every
instruction in the emitted tail. -/
private theorem head_address_ne_next
    {Γ Δ : VCtx P L} {pending nextPending : Finset VarId}
    {prog : VegasCore P L Γ} {nextProg : VegasCore P L Δ}
    {accounted : CommitmentAccounting pending prog}
    {nextAccounted : CommitmentAccounting nextPending nextProg}
    {fresh : FreshBindings prog} {nextFresh : FreshBindings nextProg}
    {state : BuildState P L Γ} {nextState : BuildState P L Δ}
    (plan : ApplicationPlan accounted fresh state)
    (next : ApplicationPlan nextAccounted nextFresh nextState)
    (deadlineOf : Nat → Nat) (head later : ApplicationInstruction P L)
    (hinstructions : plan.instructions deadlineOf =
      head :: next.instructions deadlineOf)
    (hlater : later ∈ next.instructions deadlineOf) :
    head.address ≠ later.address := by
  have hnodup := plan.instructionAddresses_nodup deadlineOf
  rw [hinstructions] at hnodup
  have hnotMem := (List.nodup_cons.mp hnodup).1
  intro heq
  apply hnotMem
  exact List.mem_map.mpr ⟨later, hlater, heq.symm⟩

/-- A head command that is either a wait or recognized by the head cache is
rejected by every later generated instruction. For two bindings, distinct
registration slots are derived from the plan's actual field allocation. -/
private theorem head_command_rejects_next
    {Γ Δ : VCtx P L} {pending nextPending : Finset VarId}
    {prog : VegasCore P L Γ} {nextProg : VegasCore P L Δ}
    {accounted : CommitmentAccounting pending prog}
    {nextAccounted : CommitmentAccounting nextPending nextProg}
    {fresh : FreshBindings prog} {nextFresh : FreshBindings nextProg}
    {state : BuildState P L Γ} {nextState : BuildState P L Δ}
    (plan : ApplicationPlan accounted fresh state)
    (next : ApplicationPlan nextAccounted nextFresh nextState)
    (deadlineOf : Nat → Nat) (image : ApplicationImage P L)
    (head : ApplicationInstruction P L) (who : P)
    (command : image.application.PlayerCommand)
    (hinstructions : plan.instructions deadlineOf =
      head :: next.instructions deadlineOf)
    (hhead : command = .wait ∨ ¬ head.RejectsCommand image who command)
    (later : ApplicationInstruction P L)
    (hlater : later ∈ next.instructions deadlineOf) :
    later.RejectsCommand image who command := by
  have haddress := head_address_ne_next plan next deadlineOf head later hinstructions hlater
  cases head with
  | sample code =>
      rcases hhead with rfl | hfalse
      · cases later <;> simp [ApplicationInstruction.RejectsCommand]
      · exact False.elim (hfalse trivial)
  | publicChoice code =>
      exact ApplicationInstruction.rejectsCommand_of_publicChoice image code later who command
        haddress hhead
  | conditional code =>
      exact ApplicationInstruction.rejectsCommand_of_conditional image code later who command
        haddress hhead
  | bind code =>
      apply ApplicationInstruction.rejectsCommand_of_binding image code later who command
        haddress _ hhead
      intro second hlaterEq
      have hheadMem : ApplicationInstruction.bind code ∈ plan.instructions deadlineOf := by
        rw [hinstructions]
        simp
      have hlaterMem : ApplicationInstruction.bind second ∈ plan.instructions deadlineOf := by
        rw [hinstructions]
        exact List.mem_cons_of_mem _ (hlaterEq ▸ hlater)
      have hcodeAllocated := plan.instructions_allocated deadlineOf (.bind code) hheadMem
      have hsecondAllocated := plan.instructions_allocated deadlineOf (.bind second) hlaterMem
      have hnodup := plan.allocatedFields_nodup deadlineOf
      rw [hinstructions] at hnodup
      simp only [List.flatMap_cons, ApplicationInstruction.allocatedFields,
        List.singleton_append] at hnodup
      have hnotMem := (List.nodup_cons.mp hnodup).1
      intro hslot
      apply hnotMem
      apply List.mem_flatMap.mpr
      refine ⟨.bind second, ?_, ?_⟩
      · rw [hlaterEq] at hlater
        exact hlater
      · have hfield : code.sourceField = second.sourceField :=
          hcodeAllocated.2.symm.trans (hslot.trans hsecondAllocated.2)
        simp [ApplicationInstruction.allocatedFields, hfield]

/-- The actual supported player step for a separated head command preserves
all caches in the supplied generated tail. -/
private theorem head_command_preserves_nextCaches
    {Γ Δ : VCtx P L} {pending nextPending : Finset VarId}
    {prog : VegasCore P L Γ} {nextProg : VegasCore P L Δ}
    {accounted : CommitmentAccounting pending prog}
    {nextAccounted : CommitmentAccounting nextPending nextProg}
    {fresh : FreshBindings prog} {nextFresh : FreshBindings nextProg}
    {state : BuildState P L Γ} {nextState : BuildState P L Δ}
    (plan : ApplicationPlan accounted fresh state)
    (next : ApplicationPlan nextAccounted nextFresh nextState)
    (deadlineOf : Nat → Nat) (image : ApplicationImage P L)
    (head : ApplicationInstruction P L) (who : P)
    (execution nextExecution : image.application.PolicyExecution)
    (command : image.application.PlayerCommand)
    (hinstructions : plan.instructions deadlineOf =
      head :: next.instructions deadlineOf)
    (hhead : command = .wait ∨ ¬ head.RejectsCommand image who command)
    (hstep : nextExecution ∈
      (image.application.playerStep who execution command).support)
    (hfresh : next.RemainingCachesEmpty image deadlineOf execution) :
    next.RemainingCachesEmpty image deadlineOf nextExecution := by
  apply next.remainingCachesEmpty_playerStep image deadlineOf who execution command
    nextExecution hstep hfresh
  intro later hlater
  exact head_command_rejects_next plan next deadlineOf image head who command
    hinstructions hhead later hlater

/-- An unresolved chance head makes every player wait, so its actual player
step preserves every later source-choice cache. -/
theorem sample_head_preserves_nextCaches
    {Γ : VCtx P L} {pending : Finset VarId} {name : VarId} {ty : L.Ty}
    {dist : L.DistExpr (erasePubVCtx Γ) ty}
    {tail : VegasCore P L ((name, .pub ty) :: Γ)}
    {accounted : CommitmentAccounting pending tail}
    {fresh : FreshBindings (.sample name dist tail)} {state : BuildState P L Γ}
    (next : ApplicationPlan accounted fresh.2
      (state.addSampleEvent name dist fresh.1).1)
    (deadlineOf : Nat → Nat) (image : ApplicationImage P L)
    (profile : SourceBehavioralProfile (.sample name dist tail)) (player : P)
    (execution nextExecution : image.application.PolicyExecution)
    (command : image.application.PlayerCommand)
    (hunresolved : execution.native.application.memory.done state.nodes.length = false)
    (hcommand : command ∈
      ((ApplicationPlan.sample (fresh := fresh) next).liftProfileIn image deadlineOf
        profile player (execution.principalHistory player)
          (State.observe image.application execution.native player)).support)
    (hstep : nextExecution ∈
      (image.application.playerStep player execution command).support)
    (hfresh : next.RemainingCachesEmpty image deadlineOf execution) :
    next.RemainingCachesEmpty image deadlineOf nextExecution := by
  have hunresolvedView :
      (State.observe image.application execution.native player).application.done
          state.nodes.length = false := hunresolved
  have hwait : command = .wait := by
    simpa [liftProfileIn, hunresolvedView] using hcommand
  apply head_command_preserves_nextCaches
    (ApplicationPlan.sample (fresh := fresh) next) next deadlineOf image
    (.sample (headSampleCode fresh state)) player execution nextExecution command
    (by rfl) (Or.inl hwait) hstep hfresh

/-- At an unresolved binding head, an arbitrary player's actual lifted-policy
step preserves every later cache. The owner runs the generated two-phase
binding controller; every other player waits. -/
theorem binding_head_preserves_nextCaches
    {Γ : VCtx P L} {pending : Finset VarId} {name : VarId} {who : P}
    {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool}
    {tail : VegasCore P L ((name, .sealed who ty) :: Γ)}
    {newName : name ∉ pending}
    {accounted : CommitmentAccounting (insert name pending) tail}
    {fresh : FreshBindings (.commit name who guard tail)} {state : BuildState P L Γ}
    (unrestricted : UnrestrictedBinding guard)
    (next : ApplicationPlan accounted fresh.2
      (state.addCommitEvent name who guard fresh.1).1)
    (deadlineOf : Nat → Nat) (image : ApplicationImage P L)
    (profile : SourceBehavioralProfile (.commit name who guard tail)) (player : P)
    (execution nextExecution : image.application.PolicyExecution)
    (command : image.application.PlayerCommand)
    (hunresolved : execution.native.application.memory.done state.nodes.length = false)
    (hcommand : command ∈
      ((ApplicationPlan.binding (newName := newName) (fresh := fresh)
        unrestricted next).liftProfileIn image deadlineOf profile player
          (execution.principalHistory player)
          (State.observe image.application execution.native player)).support)
    (hstep : nextExecution ∈
      (image.application.playerStep player execution command).support)
    (hfresh : next.RemainingCachesEmpty image deadlineOf execution) :
    next.RemainingCachesEmpty image deadlineOf nextExecution := by
  have hunresolvedView (actor : P) :
      (State.observe image.application execution.native actor).application.done
          state.nodes.length = false := hunresolved
  by_cases hplayer : player = who
  · subst player
    have hcontroller : command ∈
        ((.here guard tail : SourceDecisionSite who
          (.commit name who guard tail) Γ name ty guard).bindingPolicy fresh state image
            (profile who (.here guard tail)) (execution.principalHistory who)
              (State.observe image.application execution.native who)).support := by
      rw [liftProfileIn_binding_unresolved unrestricted next deadlineOf image profile
        (execution.principalHistory who) (State.observe image.application execution.native who)
        (hunresolvedView who)] at hcommand
      exact hcommand
    exact bindingPolicy_preserves_nextCaches (newName := newName) unrestricted next deadlineOf
      image (profile who (.here guard tail)) execution nextExecution command hcontroller hstep
      hfresh
  · have hwait : command = .wait := by
      simpa [liftProfileIn, hunresolvedView player, hplayer] using hcommand
    apply head_command_preserves_nextCaches
      (ApplicationPlan.binding (newName := newName) (fresh := fresh) unrestricted next) next
      deadlineOf image
      (.bind ((.here guard tail : SourceDecisionSite who
        (.commit name who guard tail) Γ name ty guard).bindingCode fresh state state.nextField))
      player execution nextExecution command (by rfl) (Or.inl hwait) hstep hfresh

/-- At an unresolved ordinary public-choice head, an arbitrary player's actual
lifted-policy step preserves every later cache. -/
theorem publicChoice_head_preserves_nextCaches
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
    (next : ApplicationPlan accounted fresh.2.2
      (((state.addCommitEvent name who guard fresh.1).1).addRevealEvent
        publicName who .here fresh.2.1).1)
    (deadlineOf : Nat → Nat) (image : ApplicationImage P L)
    (profile : SourceBehavioralProfile
      (.commit name who guard (.reveal publicName who name .here tail)))
    (player : P) (execution nextExecution : image.application.PolicyExecution)
    (command : image.application.PlayerCommand)
    (hunresolved : execution.native.application.memory.done (state.nodes.length + 1) = false)
    (hcommand : command ∈
      ((ApplicationPlan.publicChoice (newName := newName) (unresolved := unresolved)
        (fresh := fresh) publicGuard next).liftProfileIn image deadlineOf profile player
          (execution.principalHistory player)
          (State.observe image.application execution.native player)).support)
    (hstep : nextExecution ∈
      (image.application.playerStep player execution command).support)
    (hfresh : next.RemainingCachesEmpty image deadlineOf execution) :
    next.RemainingCachesEmpty image deadlineOf nextExecution := by
  have hunresolvedView (actor : P) :
      (State.observe image.application execution.native actor).application.done
          (state.nodes.length + 1) = false := hunresolved
  let site := PublicChoiceSite.atHead name publicName who guard tail
  let readout := image.ownerReadout? who (site.compiledGuard fresh state).choiceReads
  let controller := site.imageController fresh state image readout (profile who site.decision)
    (fun _ _ => false)
  by_cases hplayer : player = who
  · subst player
    have hcontroller : command ∈
        (controller.policy image.application (execution.principalHistory who)
          (State.observe image.application execution.native who)).support := by
      simpa [liftProfileIn, hunresolvedView who, site, readout, controller] using hcommand
    have hsupported := controller.supported_wait_or_encoded image.application
      (execution.principalHistory who) (State.observe image.application execution.native who)
      command hcontroller
    have hhead : command = .wait ∨
        ¬ (ApplicationInstruction.publicChoice (site.code fresh state)).RejectsCommand
          image who command := by
      rcases hsupported with hwait | ⟨value, hvalue⟩
      · exact Or.inl hwait
      · subst command
        right
        intro hreject
        have hnone := hreject rfl
        change controller.codec.decode (controller.codec.encode value) = none at hnone
        rw [controller.codec.decode_encode] at hnone
        contradiction
    apply head_command_preserves_nextCaches
      (ApplicationPlan.publicChoice (newName := newName) (unresolved := unresolved)
        (fresh := fresh) publicGuard next) next deadlineOf image
      (.publicChoice (site.code fresh state)) who execution nextExecution command
      (by rfl) hhead hstep hfresh
  · have hwait : command = .wait := by
      simpa [liftProfileIn, hunresolvedView player, hplayer] using hcommand
    apply head_command_preserves_nextCaches
      (ApplicationPlan.publicChoice (newName := newName) (unresolved := unresolved)
        (fresh := fresh) publicGuard next) next deadlineOf image
      (.publicChoice (site.code fresh state)) player execution nextExecution command
      (by rfl) (Or.inl hwait) hstep hfresh

/-- Supported commands of one generated conditional controller are either a
wait or are recognized by that exact conditional instruction cache. -/
private theorem conditionalController_headCommand
    {Γ : VCtx P L} {prog : VegasCore P L Γ}
    (site : ConditionalPublicationSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) (sourceSlot deadline : Nat)
    (image : ApplicationImage P L)
    (readout : List image.application.PlayerEntry → image.application.View →
      Option (site.ChoiceReads fresh state))
    (sourcePolicy :
      (visible : Env L.Val
        (eraseVCtx (viewVCtx site.choice.owner site.choice.context))) →
        FinDist { value : L.Val site.choice.ty //
          evalGuard site.choice.guard value visible = true })
    (history : List image.application.PlayerEntry) (view : image.application.View)
    (command : image.application.PlayerCommand)
    (hcommand : command ∈
      ((site.imageController fresh state sourceSlot deadline image readout sourcePolicy
        (fun _ _ => false)).policy image.application history view).support) :
    command = .wait ∨
      ¬ (ApplicationInstruction.conditional
        (site.code fresh state sourceSlot deadline)).RejectsCommand
          image site.choice.owner command := by
  let controller := site.imageController fresh state sourceSlot deadline image readout sourcePolicy
    (fun _ _ => false)
  have hsupported := controller.supported_wait_or_encoded image.application history view command
    (by simpa [controller] using hcommand)
  rcases hsupported with hwait | ⟨value, hvalue⟩
  · exact Or.inl hwait
  · subst command
    right
    intro hreject
    have hnone := hreject rfl
    change controller.codec.decode (controller.codec.encode value) = none at hnone
    rw [controller.codec.decode_encode] at hnone
    contradiction

/-- At an unresolved accounted conditional-publication head, an arbitrary
player's actual lifted-policy step preserves every later cache. -/
theorem conditional_head_preserves_nextCaches
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
    (next : ApplicationPlan accounted fresh.2.2
      (((state.addCommitEvent name who guard fresh.1).1).addRevealEvent
        publicName who .here fresh.2.1).1)
    (deadlineOf : Nat → Nat) (image : ApplicationImage P L)
    (profile : SourceBehavioralProfile
      (.commit name who guard (.reveal publicName who name .here tail)))
    (player : P) (execution nextExecution : image.application.PolicyExecution)
    (command : image.application.PlayerCommand)
    (hunresolved : execution.native.application.memory.done (state.nodes.length + 1) = false)
    (hcommand : command ∈
      ((ApplicationPlan.conditional (unresolved := sourceUnresolved) (newName := newName)
        (fresh := fresh) publicGuard next).liftProfileIn image deadlineOf profile player
          (execution.principalHistory player)
          (State.observe image.application execution.native player)).support)
    (hstep : nextExecution ∈
      (image.application.playerStep player execution command).support)
    (hfresh : next.RemainingCachesEmpty image deadlineOf execution) :
    next.RemainingCachesEmpty image deadlineOf nextExecution := by
  have hunresolvedView (actor : P) :
      (State.observe image.application execution.native actor).application.done
          (state.nodes.length + 1) = false := hunresolved
  let site := ConditionalPublicationSite.atHead name publicName who guard tail spec
  let sourceSlot := site.sourceField fresh state
  let deadline := deadlineOf (site.choice.publicationNode fresh state)
  let readout := image.ownerReadout? who (site.choice.compiledGuard fresh state).choiceReads
  let sourcePolicy := profile who site.choice.decision
  by_cases hplayer : player = who
  · subst player
    have hcontroller : command ∈
        ((site.imageController fresh state sourceSlot deadline image readout sourcePolicy
          (fun _ _ => false)).policy image.application (execution.principalHistory who)
            (State.observe image.application execution.native who)).support := by
      simpa [liftProfileIn, hunresolvedView who, site, sourceSlot, deadline, readout, sourcePolicy]
        using hcommand
    have hhead := conditionalController_headCommand site fresh state sourceSlot deadline image
      readout sourcePolicy (execution.principalHistory who)
      (State.observe image.application execution.native who) command hcontroller
    apply head_command_preserves_nextCaches
      (ApplicationPlan.conditional (unresolved := sourceUnresolved) (newName := newName)
        (fresh := fresh) publicGuard next) next deadlineOf image
      (.conditional (site.code fresh state sourceSlot deadline)) who execution nextExecution
      command (by rfl) hhead hstep hfresh
  · have hwait : command = .wait := by
      simpa [liftProfileIn, hunresolvedView player, hplayer] using hcommand
    apply head_command_preserves_nextCaches
      (ApplicationPlan.conditional (unresolved := sourceUnresolved) (newName := newName)
        (fresh := fresh) publicGuard next) next deadlineOf image
      (.conditional (site.code fresh state sourceSlot deadline)) player execution nextExecution
      command (by rfl) (Or.inl hwait) hstep hfresh

/-- At an unresolved conditional copy with its own accounting discharge, an
arbitrary player's actual lifted-policy step preserves every later cache. -/
theorem conditionalCopy_head_preserves_nextCaches
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
    (next : ApplicationPlan accounted fresh.2.2
      (((state.addCommitEvent name who guard fresh.1).1).addRevealEvent
        publicName who .here fresh.2.1).1)
    (deadlineOf : Nat → Nat) (image : ApplicationImage P L)
    (profile : SourceBehavioralProfile
      (.commit name who guard (.reveal publicName who name .here tail)))
    (player : P) (execution nextExecution : image.application.PolicyExecution)
    (command : image.application.PlayerCommand)
    (hunresolved : execution.native.application.memory.done (state.nodes.length + 1) = false)
    (hcommand : command ∈
      ((ApplicationPlan.conditionalCopy (newName := newName) (unresolved := unresolved)
        (fresh := fresh) spec publicGuard next).liftProfileIn image deadlineOf profile player
          (execution.principalHistory player)
          (State.observe image.application execution.native player)).support)
    (hstep : nextExecution ∈
      (image.application.playerStep player execution command).support)
    (hfresh : next.RemainingCachesEmpty image deadlineOf execution) :
    next.RemainingCachesEmpty image deadlineOf nextExecution := by
  have hunresolvedView (actor : P) :
      (State.observe image.application execution.native actor).application.done
          (state.nodes.length + 1) = false := hunresolved
  let site := ConditionalPublicationSite.atHead name publicName who guard tail spec
  let sourceSlot := site.sourceField fresh state
  let deadline := deadlineOf (site.choice.publicationNode fresh state)
  let readout := image.ownerReadout? who (site.choice.compiledGuard fresh state).choiceReads
  let sourcePolicy := profile who site.choice.decision
  by_cases hplayer : player = who
  · subst player
    have hcontroller : command ∈
        ((site.imageController fresh state sourceSlot deadline image readout sourcePolicy
          (fun _ _ => false)).policy image.application (execution.principalHistory who)
            (State.observe image.application execution.native who)).support := by
      simpa [liftProfileIn, hunresolvedView who, site, sourceSlot, deadline, readout, sourcePolicy]
        using hcommand
    have hhead := conditionalController_headCommand site fresh state sourceSlot deadline image
      readout sourcePolicy (execution.principalHistory who)
      (State.observe image.application execution.native who) command hcontroller
    apply head_command_preserves_nextCaches
      (ApplicationPlan.conditionalCopy (newName := newName) (unresolved := unresolved)
        (fresh := fresh) spec publicGuard next) next deadlineOf image
      (.conditional (site.code fresh state sourceSlot deadline)) who execution nextExecution
      command (by rfl) hhead hstep hfresh
  · have hwait : command = .wait := by
      simpa [liftProfileIn, hunresolvedView player, hplayer] using hcommand
    apply head_command_preserves_nextCaches
      (ApplicationPlan.conditionalCopy (newName := newName) (unresolved := unresolved)
        (fresh := fresh) spec publicGuard next) next deadlineOf image
      (.conditional (site.code fresh state sourceSlot deadline)) player execution nextExecution
      command (by rfl) (Or.inl hwait) hstep hfresh

end Vegas.ApplicationPlan

/-- info: 'Vegas.ApplicationPlan.sample_head_preserves_nextCaches' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.sample_head_preserves_nextCaches

/-- info: 'Vegas.ApplicationPlan.binding_head_preserves_nextCaches' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.binding_head_preserves_nextCaches

/-- info: 'Vegas.ApplicationPlan.publicChoice_head_preserves_nextCaches' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.publicChoice_head_preserves_nextCaches

/-- info: 'Vegas.ApplicationPlan.conditional_head_preserves_nextCaches' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.conditional_head_preserves_nextCaches

/-- info: 'Vegas.ApplicationPlan.conditionalCopy_head_preserves_nextCaches' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.conditionalCopy_head_preserves_nextCaches
