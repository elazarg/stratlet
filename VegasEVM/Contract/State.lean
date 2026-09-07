/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.FiniteState
import VegasEVM.Contract.Storage

/-!
# Contract storage state bridge

The canonical layout stores a finite graph snapshot as optional typed field
words followed by explicit completion bits.  Encoding and decoding are
executable, round-trip exactly, and the induced raw-storage encoding is
injective on reachable machine states.

Decoding arbitrary raw storage yields a structural `StateSnapshot`, not a
proof that the snapshot is reachable.  A concrete runtime must maintain that
separate state invariant across its lowered transitions.
-/

namespace Vegas.Machine.Contract

open EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {program : Program Player L}

namespace RawStore

/-- Encode every logical component of a graph snapshot into the canonical
dense layout. Optional graph values remain uninitialized when absent;
completion bits are always written explicitly. -/
def encodeSnapshot (codec : StorageCodec program)
    (snapshot : StateSnapshot program.graph) : RawStore codec :=
  fun key =>
    if hfield : key < program.graph.fieldCount then
      let field : Fin program.graph.fieldCount := ⟨key, hfield⟩
      match snapshot.fieldValue? field with
      | none => none
      | some value =>
          some (codec.encodeValue (program.graph.fieldRow field).ty value)
    else
      let rawNode := key - program.graph.fieldCount
      if hnode : rawNode < program.graph.nodeCount then
        let node : Fin program.graph.nodeCount := ⟨rawNode, hnode⟩
        some (codec.encodeCompleted (decide (node ∈ snapshot.done)))
      else
        none

@[simp] theorem readValue_encodeSnapshot
    (codec : StorageCodec program) (snapshot : StateSnapshot program.graph)
    (field : Fin program.graph.fieldCount) :
    readValue (Layout.canonical program) codec
        (encodeSnapshot codec snapshot) field =
      snapshot.fieldValue? field := by
  cases hvalue : snapshot.fieldValue? field with
  | none =>
      simp [readValue, encodeSnapshot, Layout.canonical,
        Layout.canonicalAddress, field.isLt, hvalue]
  | some value =>
      simp [readValue, encodeSnapshot, Layout.canonical,
        Layout.canonicalAddress, field.isLt, hvalue,
        codec.decode_encode_value _ (codec.field_supported field)]

@[simp] theorem readCompleted_encodeSnapshot
    (codec : StorageCodec program) (snapshot : StateSnapshot program.graph)
    (node : Fin program.graph.nodeCount) :
    readCompleted (Layout.canonical program) codec
        (encodeSnapshot codec snapshot) node =
      some (decide (node ∈ snapshot.done)) := by
  have hnotField :
      ¬program.graph.fieldCount + (node : Nat) <
        program.graph.fieldCount := by
    omega
  simp [readCompleted, encodeSnapshot, Layout.canonical,
    Layout.canonicalAddress, hnotField, node.isLt,
    codec.decode_encode_completed]

/-- Decode the typed values and explicit completion bits in canonical storage.
Malformed or absent completion words reject the whole snapshot; absent value
words remain absent graph fields. -/
def decodeSnapshot (codec : StorageCodec program) (store : RawStore codec) :
    Option (StateSnapshot program.graph) :=
  let layout := Layout.canonical program
  if available :
      ∀ node : Fin program.graph.nodeCount,
        (readCompleted layout codec store node).isSome then
    some
      { done :=
          Finset.univ.filter fun node =>
            (readCompleted layout codec store node).get (available node) = true
        fieldValue? := fun field => readValue layout codec store field }
  else
    none

/-- Canonical storage decoding is a left inverse of snapshot encoding. -/
@[simp] theorem decodeSnapshot_encodeSnapshot
    (codec : StorageCodec program) (snapshot : StateSnapshot program.graph) :
    decodeSnapshot codec (encodeSnapshot codec snapshot) = some snapshot := by
  have available :
      ∀ node : Fin program.graph.nodeCount,
        (readCompleted (Layout.canonical program) codec
          (encodeSnapshot codec snapshot) node).isSome := by
    intro node
    rw [readCompleted_encodeSnapshot]
    rfl
  unfold decodeSnapshot
  rw [dif_pos available]
  congr 1
  apply StateSnapshot.ext
  · ext node
    simp
  · intro field
    exact readValue_encodeSnapshot codec snapshot field

/-- Encode a reachable semantic machine state through its finite graph
snapshot. -/
def encodeState (codec : StorageCodec program) (state : program.State) :
    RawStore codec :=
  encodeSnapshot codec (StateSnapshot.ofConfig state.1)

@[simp] theorem decodeSnapshot_encodeState
    (codec : StorageCodec program) (state : program.State) :
    decodeSnapshot codec (encodeState codec state) =
      some (StateSnapshot.ofConfig state.1) := by
  exact decodeSnapshot_encodeSnapshot codec (StateSnapshot.ofConfig state.1)

/-- Canonical raw storage is a lossless representation of reachable machine
states. -/
theorem encodeState_injective (codec : StorageCodec program) :
    Function.Injective (encodeState (program := program) codec) := by
  intro left right hstore
  apply StateSnapshot.ofConfig_injective_on_reachable program.graphWF
  have hdecode := congrArg (decodeSnapshot (program := program) codec) hstore
  rw [decodeSnapshot_encodeState, decodeSnapshot_encodeState] at hdecode
  exact Option.some.inj hdecode

end RawStore

end Vegas.Machine.Contract
