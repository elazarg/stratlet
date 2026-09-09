/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

/-! # A minimal native message pool

Messages carry sender-local identifiers. Submission records a pending message;
delivery copies an existing pending message into a selected observer's local
inbox; inclusion removes an existing pending message and appends it to the
public ledger. Replay copies an unchanged message known to a broadcaster back
into pending. Neither delivery nor inclusion invokes a sender callback.

Any observer may receive any pending message. The published ledger is a shared
observation in this model; pending delivery is recipient-local. Sender fields
are raw labels and provide no authentication. Sent lists record both newly
authored submissions and rebroadcast messages, and the ledger may contain
repeated copies of the same envelope. The carrier adds no clocks or service
guarantees.
-/

namespace Interaction

universe uPrincipal uPayload

abbrev MessageId (Principal : Type uPrincipal) := Principal × Nat

structure Message (Principal : Type uPrincipal) (Payload : Type uPayload) where
  id : MessageId Principal
  payload : Payload

def Message.sender {Principal : Type uPrincipal} {Payload : Type uPayload}
    (message : Message Principal Payload) : Principal :=
  message.id.1

structure MessagePool (Principal : Type uPrincipal) (Payload : Type uPayload) where
  pending : List (Message Principal Payload)
  ledger : List (Message Principal Payload)
  inbox : Principal → List (Message Principal Payload)
  sent : Principal → List (Message Principal Payload)
  nextSerial : Principal → Nat

namespace MessagePool

def empty (Principal : Type uPrincipal) (Payload : Type uPayload) :
    MessagePool Principal Payload where
  pending := []
  ledger := []
  inbox := fun _ => []
  sent := fun _ => []
  nextSerial := fun _ => 0

structure Result (Principal : Type uPrincipal) (Payload : Type uPayload) where
  message : Option (Message Principal Payload)
  state : MessagePool Principal Payload

def Result.invalid {Principal : Type uPrincipal} {Payload : Type uPayload}
    (state : MessagePool Principal Payload) : Result Principal Payload :=
  ⟨none, state⟩

variable {Principal : Type uPrincipal} {Payload : Type uPayload}
variable [DecidableEq Principal]

def submit (state : MessagePool Principal Payload) (sender : Principal)
    (payload : Payload) : MessageId Principal × MessagePool Principal Payload :=
  let id := (sender, state.nextSerial sender)
  let message : Message Principal Payload := ⟨id, payload⟩
  (id, {
    state with
    pending := state.pending ++ [message]
    sent := fun who => if who = sender then state.sent sender ++ [message] else state.sent who
    nextSerial := fun who =>
      if who = sender then state.nextSerial sender + 1 else state.nextSerial who })

def lookup (state : MessagePool Principal Payload) (id : MessageId Principal) :
    Option (Message Principal Payload) :=
  state.pending.find? fun message => message.id = id

def removeFirst (id : MessageId Principal) :
    List (Message Principal Payload) → List (Message Principal Payload)
  | [] => []
  | message :: rest =>
      if message.id = id then rest else message :: removeFirst id rest

def deliver (state : MessagePool Principal Payload) (observer : Principal)
    (id : MessageId Principal) : Result Principal Payload :=
  match state.lookup id with
  | some message =>
      ⟨some message, {
        state with
        inbox := fun who =>
          if who = observer then state.inbox observer ++ [message] else state.inbox who }⟩
  | none => Result.invalid state

def includePending (state : MessagePool Principal Payload) (id : MessageId Principal) :
    Result Principal Payload :=
  match state.lookup id with
  | some message =>
      ⟨some message, {
        state with
        pending := removeFirst id state.pending
        ledger := state.ledger ++ [message] }⟩
  | none => Result.invalid state

structure View (Principal : Type uPrincipal) (Payload : Type uPayload) where
  inbox : List (Message Principal Payload)
  ledger : List (Message Principal Payload)
  sent : List (Message Principal Payload)

def View.known? (view : View Principal Payload) (id : MessageId Principal) :
    Option (Message Principal Payload) :=
  (view.sent ++ view.inbox ++ view.ledger).find? fun message => message.id = id

def observe (state : MessagePool Principal Payload) (who : Principal) :
    View Principal Payload :=
  ⟨state.inbox who, state.ledger, state.sent who⟩

def replay (state : MessagePool Principal Payload) (broadcaster : Principal)
    (id : MessageId Principal) : Result Principal Payload :=
  match (state.observe broadcaster).known? id with
  | some message =>
      ⟨some message, {
        state with
        pending := state.pending ++ [message]
        sent := fun who =>
          if who = broadcaster then state.sent broadcaster ++ [message] else state.sent who }⟩
  | none => Result.invalid state

theorem replay_pending_length_le (state : MessagePool Principal Payload)
    (broadcaster : Principal) (id : MessageId Principal) :
    (state.replay broadcaster id).state.pending.length ≤ state.pending.length + 1 := by
  unfold replay
  split <;> simp [Result.invalid]

@[simp] theorem deliver_invalid (state : MessagePool Principal Payload) (observer : Principal)
    (id : MessageId Principal) (hmissing : state.lookup id = none) :
    deliver state observer id = Result.invalid state := by
  simp [deliver, hmissing]

@[simp] theorem include_invalid (state : MessagePool Principal Payload)
    (id : MessageId Principal) (hmissing : state.lookup id = none) :
    includePending state id = Result.invalid state := by
  simp [includePending, hmissing]

theorem deliver_other_observe (state : MessagePool Principal Payload)
    (recipient observer : Principal) (id : MessageId Principal)
    (message : Message Principal Payload) (hlookup : state.lookup id = some message)
    (hne : observer ≠ recipient) :
    observe (deliver state recipient id).state observer = observe state observer := by
  simp [deliver, hlookup, observe, hne]

theorem include_of_lookup (state : MessagePool Principal Payload) (id : MessageId Principal)
    (message : Message Principal Payload) (hlookup : state.lookup id = some message) :
    includePending state id = ⟨some message, {
      state with
      pending := removeFirst id state.pending
      ledger := state.ledger ++ [message] }⟩ := by
  simp [includePending, hlookup]

theorem deliver_then_include_inbox (state : MessagePool Principal Payload)
    (observer : Principal) (id : MessageId Principal)
    (message : Message Principal Payload) (hlookup : state.lookup id = some message) :
    (includePending (deliver state observer id).state id).state.inbox observer =
      state.inbox observer ++ [message] := by
  change state.pending.find? (fun candidate => candidate.id = id) = some message at hlookup
  simp [deliver, includePending, lookup, hlookup]

theorem include_ledger_of_lookup (state : MessagePool Principal Payload)
    (id : MessageId Principal) (message : Message Principal Payload)
    (hlookup : state.lookup id = some message) :
    (includePending state id).state.ledger = state.ledger ++ [message] := by
  simp [includePending, hlookup]

theorem include_pending_of_lookup (state : MessagePool Principal Payload)
    (id : MessageId Principal) (message : Message Principal Payload)
    (hlookup : state.lookup id = some message) :
    (includePending state id).state.pending =
      removeFirst id state.pending := by
  simp [includePending, hlookup]

theorem removeFirst_length_of_find (id : MessageId Principal)
    (messages : List (Message Principal Payload)) (message : Message Principal Payload)
    (hfind : messages.find? (fun candidate => candidate.id = id) = some message) :
    (removeFirst id messages).length + 1 = messages.length := by
  induction messages with
  | nil => simp at hfind
  | cons first rest ih =>
      by_cases hfirst : first.id = id
      · simp [removeFirst, hfirst]
      · have hrest : rest.find? (fun candidate => candidate.id = id) = some message := by
          simpa [List.find?, hfirst] using hfind
        simpa [removeFirst, hfirst, Nat.add_assoc] using congrArg Nat.succ (ih hrest)

/-- Inclusion consumes one pending copy even when the application rejects it,
and even when other copies carry the same identifier. -/
theorem include_pending_length (state : MessagePool Principal Payload)
    (id : MessageId Principal) (message : Message Principal Payload)
    (hlookup : state.lookup id = some message) :
    (includePending state id).state.pending.length + 1 = state.pending.length := by
  rw [include_pending_of_lookup state id message hlookup]
  exact removeFirst_length_of_find id state.pending message hlookup

theorem include_preserves_inbox (state : MessagePool Principal Payload)
    (id : MessageId Principal) (who : Principal) :
    (includePending state id).state.inbox who = state.inbox who := by
  unfold includePending
  split <;> rfl

theorem deliver_preserves_pending (state : MessagePool Principal Payload)
    (observer : Principal) (id : MessageId Principal) :
    (deliver state observer id).state.pending = state.pending := by
  unfold deliver
  split <;> rfl

theorem deliver_preserves_ledger (state : MessagePool Principal Payload)
    (observer : Principal) (id : MessageId Principal) :
    (deliver state observer id).state.ledger = state.ledger := by
  unfold deliver
  split <;> rfl

theorem include_preserves_sent (state : MessagePool Principal Payload)
    (id : MessageId Principal) (who : Principal) :
    (includePending state id).state.sent who = state.sent who := by
  unfold includePending
  split <;> rfl

theorem include_preserves_nextSerial (state : MessagePool Principal Payload)
    (id : MessageId Principal) (who : Principal) :
    (includePending state id).state.nextSerial who = state.nextSerial who := by
  unfold includePending
  split <;> rfl

end MessagePool

end Interaction
