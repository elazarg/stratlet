/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageInvariant
import Interaction.SealedHiding
import Interaction.SealedTimeout

/-! # Pre-disclosure hiding for timed sealed execution

Paired states have the same retained messages, public events, clock, checkpoint
status, and receipts. Their ideal services may differ in one principal's
occupied secret values, but not slot occupancy. No retained message contains
an opening authored by that principal. Validation, including rejection, and
expiration then agree on their public effects. Generic carrier invariants
track this condition through delivery, inclusion, and replay.

The raw trace theorem fixes identical actions and excludes new commands from
the protected principal. It is not an adaptive-policy law or a theorem that
an arbitrary protected-player controller respects the disclosure discipline.
-/

namespace Interaction.SealedTimeout

open SealedProgram

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable {hiddenOwner : Principal} {left right : State Principal Value}

def MessageSafe (hiddenOwner : Principal)
    (message : Message Principal (Payload Principal Value)) : Prop :=
  match message.payload with
  | .protocol payload =>
      SealedProgram.MessageSafe hiddenOwner ⟨message.id, payload⟩
  | .expire => True

structure HidingRelated (hiddenOwner : Principal)
    (left right : State Principal Value) : Prop where
  service : ServiceAgreement hiddenOwner left.application.service right.application.service
  pool : left.pool = right.pool
  events : left.application.events = right.application.events
  resolution : left.application.resolution = right.application.resolution
  clock : left.clock = right.clock
  receipts : left.receipts = right.receipts
  safe : left.pool.Satisfies (MessageSafe hiddenOwner)

theorem HidingRelated.observe_eq (related : HidingRelated hiddenOwner left right)
    (who : Principal) : left.observe who = right.observe who := by
  cases related
  simp [State.observe, *]

private def ApplicationRelated (hiddenOwner : Principal)
    (left right : Application Principal Value) : Prop :=
  ServiceAgreement hiddenOwner left.service right.service ∧
    left.events = right.events ∧ left.resolution = right.resolution

private theorem handle_related [DecidableEq Principal] [DecidableEq Value]
    (timed : SealedTimeout Principal) (hiddenOwner : Principal) (now : Nat)
    (left right : Application Principal Value)
    (related : ApplicationRelated hiddenOwner left right)
    (message : Message Principal (Payload Principal Value))
    (safe : MessageSafe hiddenOwner message) :
    match timed.handle now left message, timed.handle now right message with
    | none, none => True
    | some nextLeft, some nextRight => ApplicationRelated hiddenOwner nextLeft nextRight
    | _, _ => False := by
  rcases related with ⟨hservice, hevents, hresolution⟩
  cases hpayload : message.payload with
  | expire =>
      simp only [handle, hpayload]
      rw [hevents, hresolution]
      by_cases hready : timed.ready right.events = true
      · rw [if_pos hready, if_pos hready]
        cases Deadline.expire now
            ⟨timed.deadline, right.resolution⟩ <;>
          simp [ApplicationRelated, hservice]
      · rw [if_neg hready, if_neg hready]
        trivial
  | protocol payload =>
      simp only [handle, hpayload]
      rw [hevents, hresolution]
      have hvalidate := SealedProgram.validateMessage?_eq_of_serviceAgreement
        timed.program left.service right.service hservice right.events
        ⟨message.id, payload⟩ (by simpa [MessageSafe, hpayload] using safe)
      rw [hvalidate]
      by_cases hexpired : right.resolution = .expired
      · simp [hexpired]
      · simp only [if_neg hexpired]
        cases hvalid : timed.program.validateMessage? right.service right.events
            ⟨message.id, payload⟩ <;>
          simp [ApplicationRelated, hservice]

theorem HidingRelated.includePending [DecidableEq Principal] [DecidableEq Value]
    (related : HidingRelated hiddenOwner left right)
    (timed : SealedTimeout Principal) (id : MessageId Principal) :
    HidingRelated hiddenOwner (timed.includePending left id)
      (timed.includePending right id) := by
  have hlookup : left.pool.lookup id = right.pool.lookup id := by rw [related.pool]
  cases hl : left.pool.lookup id with
  | none =>
      have hr : right.pool.lookup id = none := hlookup ▸ hl
      unfold SealedTimeout.includePending
      rw [MessagePool.includeApplication_missing _ _ _ _ hl,
        MessagePool.includeApplication_missing _ _ _ _ hr]
      constructor
      · exact related.service
      · exact related.pool
      · exact related.events
      · exact related.resolution
      · exact related.clock
      · exact related.receipts
      · exact related.safe
  | some message =>
      have hr : right.pool.lookup id = some message := hlookup ▸ hl
      have hsafe : MessageSafe hiddenOwner message :=
        related.safe.1 message (List.mem_of_find?_eq_some hl)
      have happ : ApplicationRelated hiddenOwner left.application right.application :=
        ⟨related.service, related.events, related.resolution⟩
      have hh := handle_related timed hiddenOwner left.clock left.application
        right.application happ message hsafe
      rw [related.clock] at hh
      cases hlh : timed.handle right.clock left.application message with
      | none =>
        cases hrh : timed.handle right.clock right.application message with
        | none =>
          simp [hlh, hrh] at hh
          unfold SealedTimeout.includePending
          rw [related.clock]
          rw [MessagePool.includeApplication_reject _ _ _ _ _ hl hlh,
            MessagePool.includeApplication_reject _ _ _ _ _ hr hrh]
          exact ⟨related.service, by rw [related.pool], related.events,
            related.resolution, rfl, by rw [related.receipts],
            related.safe.includePending id⟩
        | some next => simp [hlh, hrh] at hh
      | some nextLeft =>
        cases hrh : timed.handle right.clock right.application message with
        | none => simp [hlh, hrh] at hh
        | some nextRight =>
          simp [hlh, hrh] at hh
          rcases hh with ⟨hs, he, hres⟩
          unfold SealedTimeout.includePending
          rw [related.clock]
          rw [MessagePool.includeApplication_accept _ _ _ _ _ _ hl hlh,
            MessagePool.includeApplication_accept _ _ _ _ _ _ hr hrh]
          exact ⟨hs, by rw [related.pool], he, hres, rfl,
            by rw [related.receipts], related.safe.includePending id⟩

/-- While the protected principal does not issue commands, other principals
may register and submit arbitrary values. Wire operations and clock advances
remain unrestricted. The paired executions use the same raw action. -/
def AllowedBeforeDisclosure (hiddenOwner : Principal) : Action Principal Value → Prop
  | .register owner _ _ => owner ≠ hiddenOwner
  | .submit sender _ => sender ≠ hiddenOwner
  | .replay _ _ => True
  | .deliver _ _ => True
  | .include _ => True
  | .advance _ => True

theorem HidingRelated.step [DecidableEq Principal] [DecidableEq Value]
    (related : HidingRelated hiddenOwner left right) (timed : SealedTimeout Principal)
    (action : Action Principal Value) (allowed : AllowedBeforeDisclosure hiddenOwner action) :
    HidingRelated hiddenOwner (timed.step left action) (timed.step right action) := by
  cases action with
  | register owner slot value =>
      exact ⟨ServiceAgreement.seal_other _ _ related.service owner slot value allowed,
        related.pool, related.events, related.resolution, related.clock,
        related.receipts, related.safe⟩
  | submit sender payload =>
      exact ⟨related.service, by simp only [SealedTimeout.step]; rw [related.pool],
        related.events, related.resolution, related.clock, related.receipts,
        related.safe.submit sender payload (by
          cases payload with
          | protocol payload =>
              cases payload <;> simp [MessageSafe, SealedProgram.MessageSafe,
                Message.sender, AllowedBeforeDisclosure] at allowed ⊢ <;> exact allowed
          | expire => trivial)⟩
  | replay broadcaster id =>
      exact ⟨related.service, by simp only [SealedTimeout.step]; rw [related.pool],
        related.events, related.resolution, related.clock, related.receipts,
        related.safe.replay broadcaster id⟩
  | deliver observer id =>
      exact ⟨related.service, by simp only [SealedTimeout.step]; rw [related.pool],
        related.events, related.resolution, related.clock, related.receipts,
        related.safe.deliver observer id⟩
  | «include» id => exact related.includePending timed id
  | advance clock =>
      by_cases htime : left.clock ≤ clock
      · have hright : right.clock ≤ clock := related.clock ▸ htime
        simp only [SealedTimeout.step, if_pos htime, if_pos hright]
        exact ⟨related.service, related.pool, related.events, related.resolution,
          rfl, related.receipts, related.safe⟩
      · have hright : ¬right.clock ≤ clock := related.clock ▸ htime
        simp only [SealedTimeout.step, if_neg htime, if_neg hright]
        exact related

/-- Lockstep allowed native traces preserve all declared public/local views,
including expiration status and acceptance/rejection receipts. This is a raw
execution relation, not an adaptive-policy law or a cryptographic theorem. -/
theorem HidingRelated.run [DecidableEq Principal] [DecidableEq Value]
    (related : HidingRelated hiddenOwner left right) (timed : SealedTimeout Principal)
    (actions : List (Action Principal Value))
    (allowed : ∀ action ∈ actions, AllowedBeforeDisclosure hiddenOwner action) :
    HidingRelated hiddenOwner (timed.run left actions) (timed.run right actions) := by
  induction actions generalizing left right with
  | nil => exact related
  | cons action rest ih =>
      exact ih (related.step timed action (allowed action (by simp)))
        (fun next hnext => allowed next (by simp [hnext]))

end Interaction.SealedTimeout
