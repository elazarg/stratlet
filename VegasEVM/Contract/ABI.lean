/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasEVM.Contract.Layout

/-!
# Logical contract request boundary

The logical ABI erases a proof-carrying machine command to a stable node id,
logical authority, and optional typed payload.  Its reference decoder accepts
exactly requests represented by a currently valid machine command.

The decoder is a semantic specification, not generated target code: it uses
classical choice over command validity.  A backend validator must implement
the same accepted-request relation and separately model authentication,
reverts, gas, transaction ordering, and who may trigger internal actions.
-/

noncomputable section

namespace Vegas.Machine.Contract

open EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- Untyped-at-the-envelope request payload. The embedded `TypedValue` retains
the language type tag for semantic validation. -/
inductive Payload (L : IExpr) where
  | none
  | value (value : TypedValue L)

/-- Stable logical request before state-dependent validation. -/
structure Request (Player : Type) (L : IExpr) where
  node : Nat
  authority : Authority Player
  payload : Payload L

namespace Request

variable {program : Program Player L}

/-- Erase a currently valid proof-carrying machine command to its logical ABI
request. Internal samples and reveals carry no caller-supplied value; commit
commands retain their proposed typed value. -/
def encode {state : program.State}
    (command : program.Command state) : Request Player L :=
  match command with
  | .commit who action _ =>
      { node := action.node
        authority := .player who
        payload := .value action.value }
  | .internal event _ =>
      { node := event.node
        authority := .internal
        payload := .none }

/-- A raw request represents a valid command exactly when some proof-carrying
command in the current machine state erases to it. -/
def Represents (state : program.State) (request : Request Player L) : Prop :=
  ∃ command : program.Command state, encode command = request

/-- Reference validation of a logical request.  Executable backends refine
this specification with concrete checks and a proof of the same acceptance
relation. -/
noncomputable def decode (state : program.State)
    (request : Request Player L) : Option (program.Command state) := by
  classical
  exact
    if valid : Represents state request then
      some (Classical.choose valid)
    else
      none

theorem decode_eq_some_of_represents
    {state : program.State} {request : Request Player L}
    (valid : Represents state request) :
    decode state request = some (Classical.choose valid) := by
  classical
  simp [decode, valid]

/-- Every decoded command represents exactly the submitted request. -/
theorem encode_of_decode_eq_some
    {state : program.State} {request : Request Player L}
    {command : program.Command state}
    (hdecode : decode state request = some command) :
    encode command = request := by
  classical
  unfold decode at hdecode
  split at hdecode
  · rename_i valid
    have hcommand : Classical.choose valid = command :=
      Option.some.inj hdecode
    rw [← hcommand]
    exact Classical.choose_spec valid
  · simp at hdecode

/-- The reference decoder accepts exactly the requests represented by valid
machine commands. -/
theorem decode_isSome_iff
    (state : program.State) (request : Request Player L) :
    (decode state request).isSome ↔ Represents state request := by
  constructor
  · intro hsome
    rcases Option.isSome_iff_exists.mp hsome with ⟨command, hcommand⟩
    exact ⟨command, encode_of_decode_eq_some hcommand⟩
  · intro valid
    rw [decode_eq_some_of_represents valid]
    rfl

/-- Erasing a valid command always yields an accepted request. -/
theorem decode_encode_isSome
    {state : program.State} (command : program.Command state) :
    (decode state (encode command)).isSome := by
  exact (decode_isSome_iff state (encode command)).2 ⟨command, rfl⟩

/-- Decoding an encoded command may choose proof-irrelevant evidence afresh,
but the resulting command erases to the same logical request. -/
theorem decode_encode
    {state : program.State} (command : program.Command state) :
    ∃ decoded : program.Command state,
      decode state (encode command) = some decoded ∧
        encode decoded = encode command := by
  have hsome := decode_encode_isSome command
  rcases Option.isSome_iff_exists.mp hsome with ⟨decoded, hdecoded⟩
  exact
    ⟨decoded, hdecoded,
      encode_of_decode_eq_some hdecoded⟩

end Request

end Vegas.Machine.Contract
