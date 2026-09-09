/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationImage

/-! # Opaque binding and conditional inclusion laws

Binding admission has the same public effect for every private preparation
table. The accepted snapshot, including a missing value, survives later private
registration. Conditional inclusion consumes this snapshot; invalid raw traffic
remains in the shared runtime's ledger and local message histories.
-/

namespace Vegas

open EventGraph Interaction

variable {P : Type} [DecidableEq P] {L : IExpr}

namespace ConditionalCode

/-- The generated voluntary packet carries a typed opening or an explicit
decline. Expiry and malformed traffic are not compiled voluntary choices. -/
def requestPayload (code : ConditionalCode P L) :
    Option (L.Val code.secretTy) → ConditionalPublication.Payload P (TypedValue L)
  | none => .decline
  | some value => .opening (code.endpoint.owner, code.endpoint.sourceSlot)
      ⟨code.secretTy, value⟩

omit [DecidableEq P] in
theorem decode_requestPayload (code : ConditionalCode P L)
    (result : Option (L.Val code.secretTy)) :
    code.decode (code.requestPayload result) = some (code.endpoint.requestPayload result) := by
  cases result <;> simp [decode, requestPayload, ConditionalPublication.requestPayload,
    TypedValue.as?]

end ConditionalCode

namespace ApplicationImage

theorem State.register_memory (state : State P L) (who : P) (slot : Nat)
    (value : TypedValue L) : (state.register who slot value).memory = state.memory := rfl

theorem State.register_frozen (state : State P L) (who : P) (slot : Nat)
    (value : TypedValue L) : (state.register who slot value).frozen = state.frozen := rfl

omit [DecidableEq P] in
theorem State.advance_clock (state : State P L) (clock : Nat) :
    state.memory.clock ≤ (state.advance clock).memory.clock := Nat.le_max_left _ _

omit [DecidableEq P] in
/-- An accepted handle captures exactly its registration at that instant,
whether it is a well-typed value, nonsense, or absent altogether. -/
theorem State.bind_frozen (state : State P L) (code : BindingCode P)
    (handle : CommitmentHandle P Nat) :
    (state.bind code handle).frozen code.sourceField = state.prepared.lookup handle := by
  simp [State.bind]

/-- Later private registration cannot repair a missing or invalid frozen
opening. This is an equation of the verifier on every proposed opening. -/
theorem State.verify_register (state : State P L) (code : ConditionalCode P L)
    (who : P) (slot : Nat) (value : TypedValue L)
    (opening : IdealCommitments.Opening
      (Principal := P) (Slot := Nat) (Value := L.Val code.secretTy)) :
    (state.register who slot value).verify code opening = state.verify code opening := rfl

theorem handle_binding (image : ApplicationImage P L) (state : State P L)
    (address : Nat) (code : BindingCode P)
    (hcode : image.lookup address = some (.bind code))
    (id : MessageId P) (handle : CommitmentHandle P Nat) :
    image.handle state ⟨id, .binding address handle⟩ =
      if id.1 = code.owner ∧ handle = (code.owner, code.sourceSlot) ∧
          state.memory.accepted code.sourceField = none ∧
          state.memory.done code.node = false ∧ code.requires.all state.memory.done then
        some (state.bind code handle)
      else none := by
  simp [ApplicationImage.handle, hcode, Message.sender]

/-- Public binding admission and the resulting public memory reveal nothing
about preparation or frozen values. This local equation does not erase later
owner-chosen opening traffic or claim full-run strategic correspondence. -/
theorem binding_public_effect_eq (image : ApplicationImage P L)
    (first second : State P L) (hpublic : first.memory = second.memory)
    (address : Nat) (code : BindingCode P)
    (hcode : image.lookup address = some (.bind code))
    (id : MessageId P) (handle : CommitmentHandle P Nat) :
    (image.handle first ⟨id, .binding address handle⟩).map State.memory =
      (image.handle second ⟨id, .binding address handle⟩).map State.memory := by
  rw [image.handle_binding first address code hcode id handle,
    image.handle_binding second address code hcode id handle]
  simp only [hpublic]
  split <;> simp [State.bind, hpublic]

/-- Neither replay nor a newly authored binding packet can overwrite the
accepted snapshot at the same source field. -/
theorem handle_binding_after_acceptance (image : ApplicationImage P L)
    (state : State P L) (address : Nat) (code : BindingCode P)
    (hcode : image.lookup address = some (.bind code))
    (prior handle : CommitmentHandle P Nat) (id : MessageId P) :
    image.handle (state.bind code prior) ⟨id, .binding address handle⟩ = none := by
  rw [image.handle_binding _ address code hcode id handle]
  simp [State.bind]

/-- Successful dynamic decoding exposes exactly the existing conditional
classifier, using the public clock and the frozen verifier. -/
theorem handle_conditional (image : ApplicationImage P L) (state : State P L)
    (address : Nat) (code : ConditionalCode P L)
    (hcode : image.lookup address = some (.conditional code))
    (id : MessageId P) (payload : ConditionalPublication.Payload P (TypedValue L))
    (decoded : ConditionalPublication.Payload P (L.Val code.secretTy))
    (hdecode : code.decode payload = some decoded) :
    image.handle state ⟨id, .conditional address payload⟩ =
      (code.endpoint.resolve? state.memory.clock (state.verify code)
        (state.memory.accepted code.sourceField) state.memory.done
        (code.canOpen state.memory.store) ⟨id, decoded⟩).map
          (state.publishConditional code) := by
  simp only [handle, hcode, Option.bind_eq_bind, Option.bind_some, hdecode]
  cases code.endpoint.resolve? state.memory.clock (state.verify code)
    (state.memory.accepted code.sourceField) state.memory.done
    (code.canOpen state.memory.store) ⟨id, decoded⟩ <;> rfl

/-- An opponent cannot probe a site's private verifier by submitting guessed
openings under its own authenticated identity. -/
theorem handle_opening_other_owner (image : ApplicationImage P L) (state : State P L)
    (address : Nat) (code : ConditionalCode P L)
    (hcode : image.lookup address = some (.conditional code))
    (id : MessageId P) (howner : id.1 ≠ code.endpoint.owner)
    (reference : CommitmentHandle P Nat) (typed : TypedValue L) :
    image.handle state ⟨id, .conditional address (.opening reference typed)⟩ = none := by
  cases htyped : typed.as? code.secretTy <;>
    simp [handle, hcode, ConditionalCode.decode, htyped,
      ConditionalPublication.resolve?, Message.sender, howner]

/-- Once a conditional pair is complete, no subsequent packet can resolve it
again, regardless of author, proposed value, or elapsed public time. -/
theorem handle_conditional_after_publication (image : ApplicationImage P L)
    (state : State P L) (address : Nat) (code : ConditionalCode P L)
    (hcode : image.lookup address = some (.conditional code))
    (id : MessageId P) (payload : ConditionalPublication.Payload P (TypedValue L))
    (prior : Option (L.Val code.secretTy)) :
    image.handle (state.publishConditional code prior)
      ⟨id, .conditional address payload⟩ = none := by
  cases hdecode : code.decode payload <;>
    simp [handle, hcode, hdecode, ConditionalPublication.resolve?,
      ConditionalPublication.ready, State.publishConditional]

/-- The actual pending conditional packet is recorded, together with its
acceptance receipt; resolution changes only the application portion of state. -/
theorem include_conditional (image : ApplicationImage P L)
    (state : image.application.State) (address : Nat) (code : ConditionalCode P L)
    (hcode : image.lookup address = some (.conditional code)) (id : MessageId P)
    (payload : ConditionalPublication.Payload P (TypedValue L))
    (decoded : ConditionalPublication.Payload P (L.Val code.secretTy))
    (hdecode : code.decode payload = some decoded)
    (result : Option (L.Val code.secretTy))
    (hlookup : state.pool.lookup id = some ⟨id, .conditional address payload⟩)
    (hresolve : code.endpoint.resolve? state.application.memory.clock
      (state.application.verify code) (state.application.memory.accepted code.sourceField)
      state.application.memory.done (code.canOpen state.application.memory.store)
      ⟨id, decoded⟩ = some result) :
    let next := image.application.includePending state id
    next.application = state.application.publishConditional code result ∧
      next.receipts = state.receipts ++ [(id, true)] ∧
      next.pool.ledger = state.pool.ledger ++ [⟨id, .conditional address payload⟩] ∧
      next.pool.sent = state.pool.sent ∧ next.pool.inbox = state.pool.inbox := by
  have hhandle := image.handle_conditional state.application address code hcode
    id payload decoded hdecode
  rw [hresolve, Option.map_some] at hhandle
  exact image.include_accepted state id ⟨id, .conditional address payload⟩
    (state.application.publishConditional code result) hlookup hhandle

end ApplicationImage

end Vegas

/-- info: 'Vegas.ApplicationImage.binding_public_effect_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.binding_public_effect_eq

/-- info: 'Vegas.ApplicationImage.include_conditional' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.include_conditional
