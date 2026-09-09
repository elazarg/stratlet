/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationImageReadout
import Vegas.Compile.ApplicationImageInvariants
import Vegas.Compile.ApplicationImageSamples
import Interaction.ChoiceControllerHistory
import Interaction.MessageApplicationPolicyInvariant

/-! # Private-registration provenance for generated applications

The authenticated private-command history and the generated application's
sample-once preparation table record the same first registration at every
owner-scoped slot.  This is an unconditional execution property: public
traffic, inclusion, chance, and later registrations cannot disturb it.

The result concerns `prepared`, not `frozen`.  Once a binding has been
accepted, later registration still leaves its frozen snapshot unchanged, so a
separate acceptance-time argument is required to relate history to `frozen`.
-/

noncomputable section

namespace Vegas.ApplicationImage

open EventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Every owner-local registration cache agrees with the corresponding entry
of the application's authenticated preparation table. -/
def RegistrationConsistent (image : ApplicationImage P L)
    (execution : image.application.PolicyExecution) : Prop :=
  ∀ who slot, image.registrationCache slot (execution.principalHistory who) =
    execution.native.application.prepared.lookup (who, slot)

private theorem lookup_sealValue_other
    (prepared : IdealCommitments P Nat (TypedValue L))
    (owner : P) (slot : Nat) (value : TypedValue L)
    (handle : CommitmentHandle P Nat) (hne : handle ≠ (owner, slot)) :
    (prepared.sealValue owner slot value).state.lookup handle =
      prepared.lookup handle := by
  cases hstored : prepared.lookup (owner, slot) with
  | none =>
      apply IdealCommitments.seal_other
      · exact hstored
      · by_cases howner : handle.1 = owner
        · exact Or.inr fun hslot => hne (Prod.ext howner hslot)
        · exact Or.inl howner
  | some stored =>
      rw [IdealCommitments.seal_occupied prepared owner slot stored value hstored]

private theorem registrationCache_append_undecoded
    (image : ApplicationImage P L) (slot : Nat)
    (history : List image.application.PlayerEntry)
    (view : image.application.View) (command : image.application.PlayerCommand)
    (hdecode : ((registrationEncoding slot).privateCommand image.application).decode
      command = none) :
    image.registrationCache slot (history ++ [⟨view, command⟩]) =
      image.registrationCache slot history := by
  unfold registrationCache
  cases hcache : ((registrationEncoding slot).privateCommand image.application).cachedValue
      image.application history with
  | none =>
      rw [ChoiceEncoding.cachedValue_append_of_none _ _ _ _ hcache]
      simp [ChoiceEncoding.cachedValue, hdecode]
  | some value =>
      exact ChoiceEncoding.cachedValue_append_of_some _ _ _ _ value hcache

private theorem registration_after_register
    (image : ApplicationImage P L) (who : P)
    (history : List image.application.PlayerEntry)
    (view : image.application.View)
    (prepared : IdealCommitments P Nat (TypedValue L))
    (actual : Nat) (value : TypedValue L)
    (hconsistent : ∀ slot, image.registrationCache slot history =
      prepared.lookup (who, slot)) :
    ∀ slot,
      image.registrationCache slot
          (history ++ [⟨view, .privateCommand (.register actual value)⟩]) =
        (prepared.sealValue who actual value).state.lookup (who, slot) := by
  intro slot
  by_cases hslot : slot = actual
  · subst slot
    cases hcache : image.registrationCache actual history with
    | none =>
        have hempty : prepared.lookup (who, actual) = none :=
          (hconsistent actual).symm.trans hcache
        have hrecorded : image.registrationCache actual
            (history ++ [⟨view, .privateCommand (.register actual value)⟩]) =
              some value := by
          unfold registrationCache
          exact ChoiceEncoding.cachedValue_append_encoded_of_none _ _ history view value
            hcache
        exact hrecorded.trans
          (IdealCommitments.seal_first prepared who actual value hempty).2.symm
    | some stored =>
        have hrecorded := image.registrationCache_append actual history
          [⟨view, .privateCommand (.register actual value)⟩] stored hcache
        exact hrecorded.trans
          (IdealCommitments.lookup_sealValue_of_eq_some prepared who actual value
            (who, actual) stored ((hconsistent actual).symm.trans hcache)).symm
  · have hrecorded := registrationCache_append_undecoded image slot history view
      (.privateCommand (.register actual value)) (by
        simp only [ChoiceEncoding.privateCommand_decode_private, registrationEncoding]
        rw [if_neg (Ne.symm hslot)])
    rw [hrecorded, hconsistent slot]
    exact (lookup_sealValue_other prepared who actual value (who, slot) (by
        intro heq
        exact hslot (Prod.mk.inj heq).2)).symm

private theorem handle_prepared
    (image : ApplicationImage P L) (state next : State P L)
    (message : Message P (Payload P L))
    (hnext : image.handle state message = some next) :
    next.prepared = state.prepared := by
  cases message with
  | mk id payload =>
      cases payload with
      | malformed data => simp [ApplicationImage.handle] at hnext
      | choice address typed =>
          cases hlookup : image.lookup address with
          | none => simp [ApplicationImage.handle, hlookup] at hnext
          | some instruction =>
              cases instruction with
              | sample code => simp [ApplicationImage.handle, hlookup] at hnext
              | bind code => simp [ApplicationImage.handle, hlookup] at hnext
              | conditional code => simp [ApplicationImage.handle, hlookup] at hnext
              | publicChoice code =>
                  simp only [ApplicationImage.handle, hlookup, Option.bind_eq_bind,
                    Option.bind_some] at hnext
                  cases htyped : typed.as? code.guard.ty with
                  | none => simp [htyped] at hnext
                  | some value =>
                      simp only [htyped, Option.bind_some] at hnext
                      cases hresolved : code.endpoint.resolve? state.memory.done
                          (code.guard.validate state.memory.store) ⟨id, value⟩ with
                      | none => simp [hresolved] at hnext
                      | some accepted =>
                          simp only [hresolved, Option.bind_some] at hnext
                          cases hnext
                          rfl
      | binding address bindingHandle =>
          cases hlookup : image.lookup address with
          | none => simp [ApplicationImage.handle, hlookup] at hnext
          | some instruction =>
              cases instruction with
              | sample code => simp [ApplicationImage.handle, hlookup] at hnext
              | publicChoice code => simp [ApplicationImage.handle, hlookup] at hnext
              | conditional code => simp [ApplicationImage.handle, hlookup] at hnext
              | bind code =>
                  simp only [ApplicationImage.handle, hlookup, Option.bind_eq_bind,
                    Option.bind_some] at hnext
                  split at hnext
                  · cases hnext
                    rfl
                  · contradiction
      | conditional address payload =>
          cases hlookup : image.lookup address with
          | none => simp [ApplicationImage.handle, hlookup] at hnext
          | some instruction =>
              cases instruction with
              | sample code => simp [ApplicationImage.handle, hlookup] at hnext
              | publicChoice code => simp [ApplicationImage.handle, hlookup] at hnext
              | bind code => simp [ApplicationImage.handle, hlookup] at hnext
              | conditional code =>
                  simp only [ApplicationImage.handle, hlookup, Option.bind_eq_bind,
                    Option.bind_some] at hnext
                  cases hdecoded : code.decode payload with
                  | none => simp [hdecoded] at hnext
                  | some decoded =>
                      simp only [hdecoded, Option.bind_some] at hnext
                      cases hresolved : code.endpoint.resolve? state.memory.clock
                          (state.verify code) (state.memory.accepted code.sourceField)
                          state.memory.done (code.canOpen state.memory.store)
                          ⟨id, decoded⟩ with
                      | none => simp [hresolved] at hnext
                      | some result =>
                          simp only [hresolved, Option.bind_some] at hnext
                          cases hnext
                          rfl

omit [DecidableEq P] in
private theorem sample_prepared
    (image : ApplicationImage P L) (state next : State P L) (address : Nat)
    (hnext : next ∈ (image.sample state address).support) :
    next.prepared = state.prepared := by
  rcases image.sample_support state address next hnext with rfl | hsampled
  · rfl
  · obtain ⟨code, reads, value, hcode, hdone, hrequires, hreads, hvalue, rfl⟩ :=
      hsampled
    rfl

private theorem includePending_prepared
    (image : ApplicationImage P L) (state : image.application.State)
    (id : MessageId P) :
    (image.application.includePending state id).application.prepared =
      state.application.prepared := by
  cases hlookup : state.pool.lookup id with
  | none => simp [MessageApplication.includePending_missing _ _ _ hlookup]
  | some message =>
      cases hhandle : image.handle state.application message with
      | none =>
          rw [image.application.includePending_reject state id message hlookup hhandle]
      | some next =>
          rw [image.application.includePending_accept state id message next hlookup hhandle]
          exact handle_prepared image state.application next message hhandle

private theorem environmentStep_prepared
    (image : ApplicationImage P L)
    (execution next : image.application.PolicyExecution)
    (command : image.application.EnvironmentPolicyCommand)
    (hnext : next ∈ (image.application.environmentPolicyStep execution command).support) :
    next.native.application.prepared = execution.native.application.prepared := by
  have hnative : next.native ∈
      ((image.application.environmentPolicyStep execution command).map
        PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  rw [image.application.environmentStep_native] at hnative
  cases command with
  | deliver observer id =>
      have heq : next.native =
          { execution.native with
            pool := (execution.native.pool.deliver observer id).state } := by
        simpa [EnvironmentPolicyCommand.toAction, MessageApplication.step] using hnative
      rw [heq]
  | «include» id =>
      have heq : next.native = image.application.includePending execution.native id := by
        simpa [EnvironmentPolicyCommand.toAction, MessageApplication.step] using hnative
      rw [heq]
      exact includePending_prepared image execution.native id
  | wait =>
      have heq : next.native = execution.native := by
        simpa [EnvironmentPolicyCommand.toAction] using hnative
      rw [heq]
  | application applicationCommand =>
      cases applicationCommand with
      | advance clock =>
          have heq : next.native =
              { execution.native with
                application := execution.native.application.advance clock } := by
            simpa [EnvironmentPolicyCommand.toAction, MessageApplication.step,
              ApplicationImage.application] using hnative
          rw [heq]
          rfl
      | sample address =>
          change next.native ∈
            ((image.sample execution.native.application address).map
              fun application => { execution.native with application }).support at hnative
          rw [FinDist.support_map] at hnative
          obtain ⟨sampled, hsampled, heq⟩ := hnative
          rw [← heq]
          exact sample_prepared image execution.native.application sampled address hsampled

private theorem playerStep_registrationConsistent
    (image : ApplicationImage P L)
    (execution next : image.application.PolicyExecution) (who : P)
    (command : image.application.PlayerCommand)
    (hconsistent : image.RegistrationConsistent execution)
    (hnext : next ∈ (image.application.playerStep who execution command).support) :
    image.RegistrationConsistent next := by
  cases command with
  | privateCommand privateCommand =>
      cases privateCommand with
      | register actual value =>
          simp only [MessageApplication.playerStep, PlayerCommand.toAction,
            MessageApplication.advance, MessageApplication.step,
            ApplicationImage.application, FinDist.pure_bind,
            FinDist.mem_support_pure] at hnext
          subst next
          intro owner slot
          by_cases howner : owner = who
          · subst owner
            simp only [if_pos]
            exact registration_after_register image who _ _ _ actual value
              (hconsistent who) slot
          · simp only [if_neg howner, State.register]
            rw [hconsistent owner slot]
            exact (lookup_sealValue_other execution.native.application.prepared who actual
              value (owner, slot) (by
                intro heq
                exact howner (Prod.mk.inj heq).1)).symm
  | submit payload | replay id | wait =>
      simp only [MessageApplication.playerStep, PlayerCommand.toAction,
        MessageApplication.advance, MessageApplication.step, FinDist.pure_bind,
        FinDist.mem_support_pure] at hnext
      subst next
      intro owner slot
      by_cases howner : owner = who
      · subst owner
        simp only [if_pos]
        rw [registrationCache_append_undecoded]
        · exact hconsistent who slot
        · rfl
      · simp only [if_neg howner]
        exact hconsistent owner slot

private theorem environmentStep_registrationConsistent
    (image : ApplicationImage P L)
    (execution next : image.application.PolicyExecution)
    (command : image.application.EnvironmentPolicyCommand)
    (hconsistent : image.RegistrationConsistent execution)
    (hnext : next ∈ (image.application.environmentPolicyStep execution command).support) :
    image.RegistrationConsistent next := by
  have hhistory := image.application.environmentStep_principalHistory execution command next hnext
  intro who slot
  rw [congrFun hhistory who, hconsistent who slot]
  exact congrArg (fun prepared => prepared.lookup (who, slot))
    (environmentStep_prepared image execution next command hnext).symm

/-- Registration provenance is preserved by every supported policy run from
an execution where it already holds. -/
theorem runPolicies_registrationConsistent
    (image : ApplicationImage P L)
    (players : P → image.application.PlayerPolicy)
    (environment : image.application.EnvironmentPolicy)
    (schedule : List (@Invocation P))
    (execution next : image.application.PolicyExecution)
    (hexecution : image.RegistrationConsistent execution)
    (hnext : next ∈
      (image.application.runPolicies players environment schedule execution).support) :
    image.RegistrationConsistent next := by
  exact image.application.runPolicies_execution_invariant
    image.RegistrationConsistent players environment
    (fun execution who command next hconsistent _ hstep =>
      playerStep_registrationConsistent image execution next who command hconsistent hstep)
    (fun execution command next hconsistent _ hstep =>
      environmentStep_registrationConsistent image execution next command hconsistent hstep)
    schedule execution next hexecution hnext

/-- From canonical initialization, the first typed private registration in
each owner's local history is exactly the value retained by the authenticated
preparation table at that owner-scoped slot. -/
theorem runPolicies_registrationCache
    (image : ApplicationImage P L) (memory : Memory P L)
    (players : P → image.application.PlayerPolicy)
    (environment : image.application.EnvironmentPolicy)
    (schedule : List (@Invocation P))
    (next : image.application.PolicyExecution)
    (hnext : next ∈ (image.application.runPolicies players environment schedule
      (PolicyExecution.initial image.application
        (MessageApplication.State.initial image.application
          (State.initial memory)))).support) :
    ∀ who slot, image.registrationCache slot (next.principalHistory who) =
      next.native.application.prepared.lookup (who, slot) := by
  apply image.runPolicies_registrationConsistent players environment schedule _ next
    (hexecution := ?_) hnext
  intro who slot
  rfl

/-- If a binding update snapshots a value that is already present in the
owner's registration cache, arbitrary subsequent policy execution preserves
both that cache entry and the exact accepted frozen snapshot. This is the
registration-before-binding bridge needed by `RegistrationMatches`; it does
not let a later registration repair an empty earlier snapshot. -/
theorem runPolicies_cachedSnapshot_after_bind
    (image : ApplicationImage P L)
    (execution : image.application.PolicyExecution)
    (who : P) (slot : Nat) (value : TypedValue L)
    (code : BindingCode P) (hfield : code.sourceField = slot)
    (hconsistent : image.RegistrationConsistent execution)
    (hcache : image.registrationCache slot
      (execution.principalHistory who) = some value)
    (players : P → image.application.PlayerPolicy)
    (environment : image.application.EnvironmentPolicy)
    (schedule : List (@Invocation P))
    (next : image.application.PolicyExecution)
    (hnext : next ∈ (image.application.runPolicies players environment schedule
      { execution with
        native := { execution.native with
          application := execution.native.application.bind code (who, slot) } }).support) :
    image.registrationCache slot (next.principalHistory who) = some value ∧
      AcceptedSnapshot slot (who, slot) (some value)
        next.native.application := by
  let bound : image.application.PolicyExecution :=
    { execution with
      native := { execution.native with
        application := execution.native.application.bind code (who, slot) } }
  have hprepared : execution.native.application.prepared.lookup (who, slot) =
      some value := (hconsistent who slot).symm.trans hcache
  have hboundSnapshot : AcceptedSnapshot slot (who, slot) (some value)
      bound.native.application := by
    constructor
    · simp [bound, State.bind, hfield]
    · simp [bound, State.bind, hfield, hprepared]
  have hboundCache : image.registrationCache slot
      (bound.principalHistory who) = some value := by
    exact hcache
  have hnext' : next ∈
      (image.application.runPolicies players environment schedule bound).support := by
    exact hnext
  constructor
  · unfold registrationCache at hboundCache ⊢
    exact ChoiceEncoding.runPolicies_cachedValue_of_some
      image.application ((registrationEncoding slot).privateCommand image.application)
      who players environment schedule bound next value
      hboundCache hnext'
  · exact image.runPolicies_acceptedSnapshot slot (who, slot) (some value)
      players environment schedule bound next hboundSnapshot hnext'

end Vegas.ApplicationImage

/-- info: 'Vegas.ApplicationImage.runPolicies_registrationCache' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.runPolicies_registrationCache

/-- info: 'Vegas.ApplicationImage.runPolicies_cachedSnapshot_after_bind' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.runPolicies_cachedSnapshot_after_bind
