/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationImageBindings
import Vegas.Compile.ApplicationImageRegistration

/-! # Accepted-binding provenance for an individual runtime policy

A policy that submits its binding handles only after private registration
retains that registration and any supplied slot/value predicate in every
accepted snapshot. Other principals and
the environment remain arbitrary, including replay, inclusion, and clocks.
The invariant includes every message carrier: an old delivered packet may
be replayed after its original pending copy has been included.

These are safety statements, with no delivery or completion premise. They
concern actual private history and native state, not a source environment.
-/

noncomputable section

namespace Vegas.ApplicationImage

open EventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Every accepted handle belonging to this owner has a recorded private
registration satisfying `valid`, and that first recorded value is exactly its
frozen snapshot. The compiler instantiates `valid` with field/type agreement.
No condition is imposed on unaccepted handles. -/
def RegisteredBindings (image : ApplicationImage P L) (owner : P)
    (valid : Nat → TypedValue L → Prop)
    (history : List image.application.PlayerEntry) (native : State P L) : Prop :=
  ∀ field handle, native.memory.accepted field = some handle → handle.1 = owner →
    ∃ value, image.registrationCache handle.2 history = some value ∧
      native.frozen field = some value ∧ valid handle.2 value

/-- Accepted-registration provenance supplies the snapshot agreement used
by the owner-local source readout, without assuming a cache value exists. -/
theorem RegisteredBindings.registrationMatches
    {image : ApplicationImage P L} {owner : P}
    {valid : Nat → TypedValue L → Prop}
    {history : List image.application.PlayerEntry} {native : State P L}
    (hbindings : image.RegisteredBindings owner valid history native) :
    image.RegistrationMatches owner history native := by
  intro field value _ haccepted hcache
  obtain ⟨stored, hstored, hfrozen, _⟩ := hbindings field (owner, field) haccepted rfl
  exact hfrozen.trans (congrArg some (Option.some.inj (hstored.symm.trans hcache)))

/-- At an accepted canonical private field, the executable owner-local
readout recovers the exact frozen snapshot using only command history.
The snapshot appears in this equation's proof, not in the loader's inputs. -/
theorem RegisteredBindings.ownerReadStore_accepted
    {image : ApplicationImage P L} {owner : P}
    {valid : Nat → TypedValue L → Prop}
    {history : List image.application.PlayerEntry} {native : State P L}
    (hbindings : image.RegisteredBindings owner valid history native)
    (field : Nat) (hprivate : native.memory.store field = none)
    (haccepted : native.memory.accepted field = some (owner, field)) :
    image.ownerReadStore owner history native.memory field = native.frozen field := by
  obtain ⟨value, hcache, hfrozen, _⟩ := hbindings field (owner, field) haccepted rfl
  simp only [ownerReadStore, hprivate, if_pos haccepted, hcache, hfrozen]

private def PreparedMessage (owner : P) (valid : Nat → TypedValue L → Prop)
    (prepared : IdealCommitments P Nat (TypedValue L))
    (message : Message P (Payload P L)) : Prop :=
  message.sender = owner → ∀ address handle, message.payload = .binding address handle →
    ∃ value, prepared.lookup handle = some value ∧ valid handle.2 value

private def PreparedSnapshots (owner : P) (valid : Nat → TypedValue L → Prop)
    (state : State P L) : Prop :=
  ∀ field handle, state.memory.accepted field = some handle → handle.1 = owner →
    ∃ value, state.prepared.lookup handle = some value ∧
      state.frozen field = some value ∧ valid handle.2 value

private structure BindingProvenance (image : ApplicationImage P L) (owner : P)
    (valid : Nat → TypedValue L → Prop)
    (state : image.application.State) : Prop where
  messages : state.pool.Satisfies (PreparedMessage owner valid state.application.prepared)
  snapshots : PreparedSnapshots owner valid state.application

private theorem provenance_register (image : ApplicationImage P L) (owner : P)
    (valid : Nat → TypedValue L → Prop)
    (state : image.application.State) (who : P) (slot : Nat) (value : TypedValue L)
    (hstate : BindingProvenance image owner valid state) :
    BindingProvenance image owner valid
      { state with application := state.application.register who slot value } := by
  constructor
  · apply hstate.messages.mono
    intro message hmessage howner address handle hbinding
    obtain ⟨stored, hstored, hvalid⟩ := hmessage howner address handle hbinding
    exact ⟨stored, IdealCommitments.lookup_sealValue_of_eq_some
      state.application.prepared who slot value handle stored hstored, hvalid⟩
  · intro field handle haccepted howner
    obtain ⟨stored, hstored, hfrozen, hvalid⟩ := hstate.snapshots field handle haccepted howner
    exact ⟨stored, IdealCommitments.lookup_sealValue_of_eq_some
      state.application.prepared who slot value handle stored hstored, hfrozen, hvalid⟩

private theorem snapshots_handle (image : ApplicationImage P L) (owner : P)
    (valid : Nat → TypedValue L → Prop)
    (state next : State P L) (message : Message P (Payload P L))
    (hsnapshots : PreparedSnapshots owner valid state)
    (hmessage : PreparedMessage owner valid state.prepared message)
    (hnext : image.handle state message = some next) :
    PreparedSnapshots owner valid next := by
  obtain ⟨hprepared, hunchanged | hbinding⟩ :=
    image.handle_binding_effect state next message hnext
  · intro field handle haccepted howner
    rw [hunchanged.1] at haccepted
    obtain ⟨value, hvalue, hfrozen, hvalid⟩ := hsnapshots field handle haccepted howner
    exact ⟨value, hprepared ▸ hvalue, hunchanged.2 ▸ hfrozen, hvalid⟩
  · obtain ⟨address, code, binding, hpayload, hsender, hbinding, rfl⟩ := hbinding
    intro field handle haccepted howner
    by_cases hfield : field = code.sourceField
    · subst field
      have heq : binding = handle := by
        apply Option.some.inj
        simpa only [State.bind, if_pos] using haccepted
      subst handle
      have hsenderOwner : message.sender = owner := by
        rw [hbinding] at howner
        exact hsender.trans howner
      obtain ⟨value, hvalue, hvalid⟩ := hmessage hsenderOwner address binding hpayload
      exact ⟨value, hvalue, by simpa only [State.bind, if_pos] using hvalue, hvalid⟩
    · have hprior : state.memory.accepted field = some handle := by
        simpa only [State.bind, if_neg hfield] using haccepted
      obtain ⟨value, hvalue, hfrozen, hvalid⟩ := hsnapshots field handle hprior howner
      exact ⟨value, hvalue, by simpa only [State.bind, if_neg hfield] using hfrozen, hvalid⟩

private theorem provenance_include (image : ApplicationImage P L) (owner : P)
    (valid : Nat → TypedValue L → Prop)
    (state : image.application.State) (id : MessageId P)
    (hstate : BindingProvenance image owner valid state) :
    BindingProvenance image owner valid (image.application.includePending state id) := by
  cases hlookup : state.pool.lookup id with
  | none =>
      rw [MessageApplication.includePending_missing _ _ _ hlookup]
      exact hstate
  | some message =>
      have hmessage := hstate.messages.1 message (List.mem_of_find?_eq_some hlookup)
      cases hhandle : image.handle state.application message with
      | none =>
          rw [image.application.includePending_reject state id message hlookup hhandle]
          exact ⟨hstate.messages.includePending id, hstate.snapshots⟩
      | some application =>
          rw [image.application.includePending_accept state id message application hlookup hhandle]
          have hprepared := (image.handle_binding_effect state.application application
            message hhandle).1
          constructor
          · simpa only [hprepared] using hstate.messages.includePending id
          · exact snapshots_handle image owner valid state.application application message
              hstate.snapshots hmessage hhandle

private theorem provenance_playerStep (image : ApplicationImage P L) (owner : P)
    (valid : Nat → TypedValue L → Prop)
    (execution next : image.application.PolicyExecution) (who : P)
    (command : image.application.PlayerCommand)
    (hstate : BindingProvenance image owner valid execution.native)
    (hsubmit : ∀ payload, command = .submit payload →
      PreparedMessage owner valid execution.native.application.prepared
        ⟨(who, execution.native.pool.nextSerial who), payload⟩)
    (hnext : next ∈ (image.application.playerStep who execution command).support) :
    BindingProvenance image owner valid next.native := by
  cases command with
  | privateCommand command =>
      cases command with
      | register slot value =>
          simp only [MessageApplication.playerStep, PlayerCommand.toAction,
            MessageApplication.advance, MessageApplication.step, ApplicationImage.application,
            FinDist.pure_bind, FinDist.mem_support_pure] at hnext
          subst next
          exact provenance_register image owner valid execution.native who slot value hstate
  | submit payload =>
      simp only [MessageApplication.playerStep, PlayerCommand.toAction,
        MessageApplication.advance, MessageApplication.step, FinDist.pure_bind,
        FinDist.mem_support_pure] at hnext
      subst next
      exact ⟨hstate.messages.submit who payload (hsubmit payload rfl), hstate.snapshots⟩
  | replay id =>
      simp only [MessageApplication.playerStep, PlayerCommand.toAction,
        MessageApplication.advance, MessageApplication.step, FinDist.pure_bind,
        FinDist.mem_support_pure] at hnext
      subst next
      exact ⟨hstate.messages.replay who id, hstate.snapshots⟩
  | wait =>
      simp only [MessageApplication.playerStep, PlayerCommand.toAction,
        MessageApplication.advance, FinDist.pure_bind, FinDist.mem_support_pure] at hnext
      subst next
      exact hstate

private theorem provenance_environmentStep (image : ApplicationImage P L) (owner : P)
    (valid : Nat → TypedValue L → Prop)
    (execution next : image.application.PolicyExecution)
    (command : image.application.EnvironmentPolicyCommand)
    (hstate : BindingProvenance image owner valid execution.native)
    (hnext : next ∈ (image.application.environmentPolicyStep execution command).support) :
    BindingProvenance image owner valid next.native := by
  have hnative : next.native ∈
      ((image.application.environmentPolicyStep execution command).map
        PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  rw [image.application.environmentStep_native] at hnative
  cases command with
  | deliver observer id =>
      simp only [EnvironmentPolicyCommand.toAction, MessageApplication.step,
        FinDist.mem_support_pure] at hnative
      rw [hnative]
      exact ⟨hstate.messages.deliver observer id, hstate.snapshots⟩
  | «include» id =>
      simp only [EnvironmentPolicyCommand.toAction, MessageApplication.step,
        FinDist.mem_support_pure] at hnative
      rw [hnative]
      exact provenance_include image owner valid execution.native id hstate
  | wait =>
      simp only [EnvironmentPolicyCommand.toAction, FinDist.mem_support_pure] at hnative
      rw [hnative]
      exact hstate
  | application command =>
      cases command with
      | advance clock =>
          simp only [EnvironmentPolicyCommand.toAction, MessageApplication.step,
            ApplicationImage.application, FinDist.map_pure, FinDist.mem_support_pure] at hnative
          rw [hnative]
          exact ⟨hstate.messages, hstate.snapshots⟩
      | sample address =>
          change next.native ∈
            ((image.sample execution.native.application address).map
              fun application => { execution.native with application }).support at hnative
          rw [FinDist.support_map] at hnative
          obtain ⟨sampled, hsampled, heq⟩ := hnative
          rw [← heq]
          rcases image.sample_support execution.native.application address sampled hsampled with
            rfl | ⟨code, reads, value, _, _, _, _, _, rfl⟩
          · exact hstate
          · exact ⟨hstate.messages, hstate.snapshots⟩

/-- A policy whose binding submissions have already been registered cannot
acquire a mismatching accepted snapshot. All other policies, schedules, and
environment commands remain arbitrary. Initial memory has no accepted handles;
private registration and pending messages start empty. -/
theorem runPolicies_registeredBindings_of_registered_submissions
    (image : ApplicationImage P L) (memory : Memory P L)
    (hempty : ∀ field, memory.accepted field = none)
    (owner : P) (valid : Nat → TypedValue L → Prop)
    (players : P → image.application.PlayerPolicy)
    (environment : image.application.EnvironmentPolicy)
    (hbinding : ∀ history view address handle,
      .submit (.binding address handle) ∈ (players owner history view).support →
        handle.1 = owner ∧ ∃ value,
          image.registrationCache handle.2 history = some value ∧ valid handle.2 value)
    (schedule : List (@Invocation P)) (next : image.application.PolicyExecution)
    (hnext : next ∈ (image.application.runPolicies players environment schedule
      (PolicyExecution.initial image.application
        (MessageApplication.State.initial image.application (State.initial memory)))).support) :
    image.RegisteredBindings owner valid (next.principalHistory owner)
      next.native.application := by
  let invariant (execution : image.application.PolicyExecution) :=
    image.RegistrationConsistent execution ∧ BindingProvenance image owner valid execution.native
  have hinvariant : invariant next := by
    apply image.application.runPolicies_execution_invariant invariant players environment
      ?_ ?_ schedule _ next ?_ hnext
    · intro execution who command final hstate hcommand hfinal
      refine ⟨image.playerStep_registrationConsistent execution final who command hstate.1 hfinal,
        provenance_playerStep image owner valid execution final who command hstate.2 ?_ hfinal⟩
      intro payload hsubmit howner address handle hpayload
      change who = owner at howner
      subst who
      subst command
      change payload = .binding address handle at hpayload
      subst payload
      obtain ⟨hhandle, value, hcache, hvalid⟩ := hbinding _ _ address handle hcommand
      refine ⟨value, ?_, hvalid⟩
      have heq : handle = (owner, handle.2) := Prod.ext hhandle rfl
      rw [heq, ← hstate.1 owner handle.2]
      exact hcache
    · intro execution command final hstate _ hfinal
      exact ⟨image.environmentStep_registrationConsistent execution final command hstate.1 hfinal,
        provenance_environmentStep image owner valid execution final command hstate.2 hfinal⟩
    · constructor
      · intro who slot
        rfl
      · constructor
        · exact MessagePool.Satisfies.empty
        · intro field handle haccepted _
          simp only [PolicyExecution.initial, MessageApplication.State.initial,
            State.initial, hempty] at haccepted
          contradiction
  intro field handle haccepted howner
  obtain ⟨value, hprepared, hfrozen, hvalid⟩ :=
    hinvariant.2.snapshots field handle haccepted howner
  refine ⟨value, ?_, hfrozen, hvalid⟩
  rw [hinvariant.1 owner handle.2]
  have heq : handle = (owner, handle.2) := Prod.ext howner rfl
  exact (congrArg (fun reference => next.native.application.prepared.lookup reference)
    heq).symm.trans hprepared

end Vegas.ApplicationImage

/-- info:
'Vegas.ApplicationImage.runPolicies_registeredBindings_of_registered_submissions' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.runPolicies_registeredBindings_of_registered_submissions
