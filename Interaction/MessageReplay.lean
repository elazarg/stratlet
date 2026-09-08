/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessagePool

/-! # Replay laws for the native message pool -/

namespace Interaction.MessagePool

universe uPrincipal uPayload

variable {Principal : Type uPrincipal} {Payload : Type uPayload}
variable [DecidableEq Principal]

theorem View.known?_mem (view : View Principal Payload) (id : MessageId Principal)
    (message : Message Principal Payload) (hknown : view.known? id = some message) :
    message ∈ view.sent ++ view.inbox ++ view.ledger := by
  exact List.mem_of_find?_eq_some hknown

theorem replay_of_known (state : MessagePool Principal Payload) (broadcaster : Principal)
    (id : MessageId Principal) (message : Message Principal Payload)
    (hknown : (state.observe broadcaster).known? id = some message) :
    replay state broadcaster id = ⟨some message, {
      state with
      pending := state.pending ++ [message]
      sent := fun who =>
        if who = broadcaster then state.sent broadcaster ++ [message] else state.sent who }⟩ := by
  simp [replay, hknown]

@[simp] theorem replay_invalid (state : MessagePool Principal Payload)
    (broadcaster : Principal) (id : MessageId Principal)
    (hunknown : (state.observe broadcaster).known? id = none) :
    replay state broadcaster id = Result.invalid state := by
  simp [replay, hunknown]

theorem replay_message_eq_of_known (state : MessagePool Principal Payload)
    (broadcaster : Principal) (id : MessageId Principal)
    (message : Message Principal Payload)
    (hknown : (state.observe broadcaster).known? id = some message) :
    (replay state broadcaster id).message = some message := by
  simp [replay, hknown]

theorem replay_preserves_ledger (state : MessagePool Principal Payload)
    (broadcaster : Principal) (id : MessageId Principal) :
    (replay state broadcaster id).state.ledger = state.ledger := by
  unfold replay
  split <;> rfl

theorem replay_preserves_inbox (state : MessagePool Principal Payload)
    (broadcaster : Principal) (id : MessageId Principal) (who : Principal) :
    (replay state broadcaster id).state.inbox who = state.inbox who := by
  unfold replay
  split <;> rfl

theorem replay_preserves_nextSerial (state : MessagePool Principal Payload)
    (broadcaster : Principal) (id : MessageId Principal) (who : Principal) :
    (replay state broadcaster id).state.nextSerial who = state.nextSerial who := by
  unfold replay
  split <;> rfl

theorem replay_other_observe (state : MessagePool Principal Payload)
    (broadcaster observer : Principal) (id : MessageId Principal)
    (hne : observer ≠ broadcaster) :
    observe (replay state broadcaster id).state observer = observe state observer := by
  unfold replay
  split <;> simp [observe, Result.invalid, hne]

theorem replay_view_determined (left right : MessagePool Principal Payload)
    (broadcaster : Principal) (id : MessageId Principal)
    (hview : left.observe broadcaster = right.observe broadcaster) :
    (replay left broadcaster id).message = (replay right broadcaster id).message ∧
      observe (replay left broadcaster id).state broadcaster =
        observe (replay right broadcaster id).state broadcaster := by
  have hinbox : left.inbox broadcaster = right.inbox broadcaster :=
    congrArg View.inbox hview
  have hledger : left.ledger = right.ledger :=
    congrArg View.ledger hview
  have hsent : left.sent broadcaster = right.sent broadcaster :=
    congrArg View.sent hview
  have hknown : (left.observe broadcaster).known? id =
      (right.observe broadcaster).known? id := congrArg (fun view => view.known? id) hview
  unfold replay
  rw [hknown]
  split
  · constructor
    · rfl
    · simp [observe, hinbox, hledger, hsent]
  · exact ⟨rfl, hview⟩

end Interaction.MessagePool
