/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedTimeout
import Interaction.SealedProgramLaws

namespace Interaction.SealedTimeout

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Value]

theorem handle_preserves_service (timed : SealedTimeout Principal) (now : Nat)
    (application next : Application Principal Value)
    (message : Message Principal (Payload Principal Value))
    (hhandle : timed.handle now application message = some next) :
    next.service = application.service := by
  cases hpayload : message.payload with
  | protocol payload =>
      simp only [handle, hpayload] at hhandle
      split at hhandle
      · contradiction
      · cases hvalid : timed.program.validateMessage? application.service application.events
          ⟨message.id, payload⟩ <;> simp [hvalid] at hhandle
        cases hhandle
        rfl
  | expire =>
      simp only [handle, hpayload] at hhandle
      split at hhandle
      · split at hhandle
        · cases hhandle
          rfl
        · contradiction
      · contradiction

theorem includePending_preserves_service (timed : SealedTimeout Principal)
    (state : State Principal Value) (id : MessageId Principal) :
    (timed.includePending state id).application.service = state.application.service := by
  unfold includePending
  cases hlookup : state.pool.lookup id with
  | none => simp [MessagePool.includeApplication, MessagePool.includePending, hlookup,
      MessagePool.Result.invalid]
  | some message =>
      cases hhandle : timed.handle state.clock state.application message with
      | none => simp [MessagePool.includeApplication, MessagePool.includePending, hlookup, hhandle]
      | some next =>
          simp only [MessagePool.includeApplication, MessagePool.includePending, hlookup, hhandle]
          exact handle_preserves_service timed state.clock state.application next message hhandle

theorem step_lookup_of_eq_some (timed : SealedTimeout Principal)
    (state : State Principal Value) (action : Action Principal Value)
    (handle : CommitmentHandle Principal Nat) (value : Value)
    (hlookup : state.application.service.lookup handle = some value) :
    (timed.step state action).application.service.lookup handle = some value := by
  cases action with
  | register registeredOwner registeredSlot registeredValue =>
      exact IdealCommitments.lookup_sealValue_of_eq_some state.application.service
        registeredOwner registeredSlot registeredValue handle value hlookup
  | submit => simpa [step] using hlookup
  | replay => simpa [step] using hlookup
  | deliver => simpa [step] using hlookup
  | «include» id => simpa [step, includePending_preserves_service] using hlookup
  | advance clock =>
      simp only [step]
      split <;> exact hlookup

theorem run_lookup_of_eq_some (timed : SealedTimeout Principal)
    (state : State Principal Value) (actions : List (Action Principal Value))
    (handle : CommitmentHandle Principal Nat) (value : Value)
    (hlookup : state.application.service.lookup handle = some value) :
    (timed.run state actions).application.service.lookup handle = some value := by
  induction actions generalizing state with
  | nil => exact hlookup
  | cons action rest ih =>
      exact ih (timed.step state action)
        (step_lookup_of_eq_some timed state action handle value hlookup)

theorem step_advance_application_pool_receipts (timed : SealedTimeout Principal)
    (state : State Principal Value) (clock : Nat) :
    let next := timed.step state (.advance clock)
    next.application = state.application ∧ next.pool = state.pool ∧
      next.receipts = state.receipts := by
  simp only [step]
  split <;> simp

theorem handle_protocol_expired (timed : SealedTimeout Principal) (now : Nat)
    (application : Application Principal Value)
    (message : Message Principal (Payload Principal Value))
    (payload : SealedProgram.Payload Principal Value)
    (hpayload : message.payload = .protocol payload)
    (hexpired : application.resolution = .expired) :
    timed.handle now application message = none := by
  simp [handle, hpayload, hexpired]

theorem handle_expire_success_iff (timed : SealedTimeout Principal) (now : Nat)
    (application : Application Principal Value)
    (message : Message Principal (Payload Principal Value))
    (hpayload : message.payload = .expire) :
    (∃ next, timed.handle now application message = some next) ↔
      timed.ready application.events = true ∧
      application.resolution = .pending ∧ timed.deadline < now := by
  by_cases hready : timed.ready application.events = true
  · by_cases hpast : application.resolution = .pending ∧ timed.deadline < now
    · simp [handle, hpayload, hready, Deadline.expire, hpast]
    · simp [handle, hpayload, hready, Deadline.expire, hpast]
  · simp [handle, hpayload, hready]

theorem handle_expire_updates_only_resolution (timed : SealedTimeout Principal) (now : Nat)
    (application next : Application Principal Value)
    (message : Message Principal (Payload Principal Value))
    (hpayload : message.payload = .expire)
    (hhandle : timed.handle now application message = some next) :
    next.service = application.service ∧ next.events = application.events ∧
      next.resolution = .expired := by
  by_cases hready : timed.ready application.events = true
  · by_cases hpast : application.resolution = .pending ∧ timed.deadline < now
    · simp [handle, hpayload, hready, Deadline.expire, hpast] at hhandle
      cases hhandle
      simp
    · simp [handle, hpayload, hready, Deadline.expire, hpast] at hhandle
  · simp [handle, hpayload, hready] at hhandle

theorem handle_opening_completes (timed : SealedTimeout Principal) (now : Nat)
    (application : Application Principal Value)
    (message : Message Principal (Payload Principal Value))
    (payload : SealedProgram.Payload Principal Value) (value : Value)
    (hpayload : message.payload = .protocol payload)
    (hnotExpired : application.resolution ≠ .expired)
    (hvalid : SealedProgram.validateMessage? timed.program application.service
      application.events ⟨message.id, payload⟩ = some (.opened timed.openingNode value)) :
    ∃ next, timed.handle now application message = some next ∧
      next.resolution = .completed := by
  simp [handle, hpayload, hnotExpired, hvalid]

theorem handle_expire_after_opening (timed : SealedTimeout Principal) (now : Nat)
    (application opened : Application Principal Value)
    (opening expiration : Message Principal (Payload Principal Value))
    (payload : SealedProgram.Payload Principal Value) (value : Value)
    (hopening : opening.payload = .protocol payload)
    (hexpiration : expiration.payload = .expire)
    (hnotExpired : application.resolution ≠ .expired)
    (hvalid : SealedProgram.validateMessage? timed.program application.service
      application.events ⟨opening.id, payload⟩ = some (.opened timed.openingNode value))
    (hhandle : timed.handle now application opening = some opened) :
    timed.handle now opened expiration = none := by
  have hopened : opened.resolution = .completed := by
    obtain ⟨next, hnext, hresolution⟩ := handle_opening_completes timed now application
      opening payload value hopening hnotExpired hvalid
    rw [hhandle] at hnext
    cases hnext
    exact hresolution
  simp [handle, hexpiration, Deadline.expire, hopened]

/-- Rejection rolls back application effects but retains publication and its
negative receipt. -/
theorem includePending_reject (timed : SealedTimeout Principal)
    (state : State Principal Value) (id : MessageId Principal)
    (message : Message Principal (Payload Principal Value))
    (hlookup : state.pool.lookup id = some message)
    (hhandle : timed.handle state.clock state.application message = none) :
    (timed.includePending state id).application = state.application ∧
      (timed.includePending state id).pool.ledger = state.pool.ledger ++ [message] ∧
      (timed.includePending state id).receipts = state.receipts ++ [(id, false)] := by
  unfold includePending
  rw [show state.pool.includeApplication state.application id (timed.handle state.clock) =
      ⟨(state.pool.includePending id).state, state.application, some false⟩ by
    exact MessagePool.includeApplication_reject _ _ _ _ _ hlookup hhandle]
  simp [MessagePool.include_ledger_of_lookup _ _ _ hlookup]

theorem includePending_preserves_inbox (timed : SealedTimeout Principal)
    (state : State Principal Value) (id : MessageId Principal) (who : Principal) :
    (timed.includePending state id).pool.inbox who = state.pool.inbox who := by
  exact MessagePool.includeApplication_preserves_inbox _ _ _ _ _

end Interaction.SealedTimeout
