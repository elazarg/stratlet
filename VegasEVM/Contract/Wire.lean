/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasEVM.Contract.Configured

/-!
# Transaction wire encoding

This pass adds one representation decision to a configured contract: a
lossless encoding of its typed transaction sum into a target wire carrier.
Malformed wire values reject before typed validation. Valid encoded calls
retain the configured contract's exact execution laws.

`WireCodec` does not prescribe selectors, byte order, address encoding, or a
chain ABI. A concrete backend supplies those choices and the round-trip proof.
-/

noncomputable section

namespace Vegas.Machine.Contract

open EventGraph

variable {Player Address Wire : Type}
variable [DecidableEq Player] [DecidableEq Address]
variable {L : IExpr} {program : Program Player L}

/-- A lossless target-wire encoding for typed values of `α`. The decoder may
reject malformed wire inputs. -/
structure WireCodec (α Wire : Type) where
  encode : α → Wire
  decode : Wire → Option α
  decode_encode : ∀ value, decode (encode value) = some value

namespace WireCodec

variable {α : Type}

/-- Proof-facing codec with no representation change. -/
def identity (α : Type) : WireCodec α α where
  encode := id
  decode := some
  decode_encode _ := rfl

/-- A lossless wire encoder is injective. -/
theorem encode_injective (codec : WireCodec α Wire) :
    Function.Injective codec.encode := by
  intro left right heq
  have hdecode := congrArg codec.decode heq
  simpa [codec.decode_encode] using hdecode

/-- A decoder is canonical when every accepted wire value is exactly the
encoder output of the value it decodes to. This excludes accepted aliases. -/
structure Canonical (codec : WireCodec α Wire) : Prop where
  encode_decode : ∀ wire value,
    codec.decode wire = some value → codec.encode value = wire

namespace Canonical

variable {codec : WireCodec α Wire}

theorem decode_eq_some_iff (canonical : Canonical codec)
    (wire : Wire) (value : α) :
    codec.decode wire = some value ↔ wire = codec.encode value := by
  constructor
  · intro hdecode
    exact (canonical.encode_decode wire value hdecode).symm
  · intro hencode
    subst wire
    exact codec.decode_encode value

end Canonical

/-- Identity representation accepts only its unique canonical value. -/
theorem identity_canonical (α : Type) : Canonical (identity α) where
  encode_decode wire value hdecode := by
    simpa [identity] using (Option.some.inj hdecode).symm

end WireCodec

namespace ConfiguredContract

variable (contract : ConfiguredContract program Address)

/-- A wire codec specialized to this configured contract's typed transaction
surface. -/
abbrev TransactionWireCodec (Wire : Type) :=
  WireCodec contract.Calldata Wire

/-- Decode and validate one wire transaction. -/
def acceptsWire (wireCodec : contract.TransactionWireCodec Wire)
    (store : contract.Store) (wire : Wire) : Bool :=
  match wireCodec.decode wire with
  | none => false
  | some calldata => contract.accepts store calldata

/-- Decode and execute one wire transaction. -/
def executeWire? (wireCodec : contract.TransactionWireCodec Wire)
    (store : contract.Store) (wire : Wire) :
    Option (GameTheory.Math.Probability.FinDist contract.Store) :=
  match wireCodec.decode wire with
  | none => none
  | some calldata => contract.execute? store calldata

/-- Wire execution succeeds exactly when wire validation accepts. -/
theorem executeWire?_isSome
    (wireCodec : contract.TransactionWireCodec Wire)
    (store : contract.Store) (wire : Wire) :
    (contract.executeWire? wireCodec store wire).isSome =
      contract.acceptsWire wireCodec store wire := by
  unfold executeWire? acceptsWire
  cases wireCodec.decode wire with
  | none => rfl
  | some calldata => exact contract.execute?_isSome store calldata

/-- Encoding any typed configured-contract transaction is behaviorally
transparent at the wire boundary. -/
@[simp] theorem executeWire?_encode
    (wireCodec : contract.TransactionWireCodec Wire)
    (store : contract.Store) (calldata : contract.Calldata) :
    contract.executeWire? wireCodec store (wireCodec.encode calldata) =
      contract.execute? store calldata := by
  simp [executeWire?, wireCodec.decode_encode]

/-- A valid player commit retains its exact stored machine-step law after wire
encoding and decoding. -/
theorem executeWire?_encodeState_playerCommit
    (wireCodec : contract.TransactionWireCodec Wire)
    {state : program.State} {who : Player}
    (action : CommitAction program.graph who)
    (step : CommitStep program.graph state.1 who action) :
    contract.executeWire? wireCodec
        (RawStore.encodeState contract.codec state)
        (wireCodec.encode
          (.player
            (PlayerCalldata.encodeCommit contract.players contract.codec
              action step))) =
      some ((program.step state (.commit who action step)).map
        (RawStore.encodeState contract.codec)) := by
  rw [executeWire?_encode]
  exact contract.execute?_encodeState_playerCommit action step

/-- An authorized valid internal event retains its exact stored machine-step
law after wire encoding and decoding. -/
theorem executeWire?_encodeState_internal
    (wireCodec : contract.TransactionWireCodec Wire)
    (caller : Address) {state : program.State}
    (event : InternalEvent program.graph)
    (step : InternalStep program.graph state.1 event)
    (hauthorized : contract.triggers.allows caller event.node = true) :
    contract.executeWire? wireCodec
        (RawStore.encodeState contract.codec state)
        (wireCodec.encode
          (.internal (InternalCalldata.encode caller event))) =
      some ((program.step state (.internal event step)).map
        (RawStore.encodeState contract.codec)) := by
  rw [executeWire?_encode]
  exact contract.execute?_encodeState_internal
    caller event step hauthorized

/-- Every accepted external wire value over encoded reachable storage executes
as some valid semantic command and preserves the canonical reachable-state
image. -/
theorem executeWire?_encodeState_of_accepts
    (wireCodec : contract.TransactionWireCodec Wire)
    (state : program.State) (wire : Wire)
    (haccept :
      contract.acceptsWire wireCodec
        (RawStore.encodeState contract.codec state) wire = true) :
    ∃ command : program.Command state,
      contract.executeWire? wireCodec
          (RawStore.encodeState contract.codec state) wire =
        some ((program.step state command).map
          (RawStore.encodeState contract.codec)) := by
  unfold acceptsWire at haccept
  cases hdecode : wireCodec.decode wire with
  | none => simp [hdecode] at haccept
  | some calldata =>
      simp only [hdecode] at haccept
      rcases contract.execute?_encodeState_of_accepts
          state calldata haccept with
        ⟨command, hexecute⟩
      refine ⟨command, ?_⟩
      unfold executeWire?
      rw [hdecode]
      exact hexecute

end ConfiguredContract

end Vegas.Machine.Contract
