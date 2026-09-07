/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasEVM.Contract.Layout

/-!
# Contract storage words

A storage codec relates language values and action-completion bits to one
target word type.  Together with a certified `Layout`, it induces typed reads
and writes on raw target storage.  The round-trip laws and layout injectivity
are sufficient to prove same-slot correctness and cross-slot noninterference.

This layer deliberately does not require the target word type to be finite or
serializable. A codec is indexed by one program and only promises exactness for
types that occur in that program. An exact codec into EVM words still cannot be
supplied for a program that uses unbounded integers without first choosing a
bounded source type, a range invariant, or explicit modular/checked-overflow
semantics.
-/

namespace Vegas.Machine.Contract

open EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- A program-indexed target-neutral value encoding and administrative
completion-bit encoding into one raw storage-word type. Encoding and decoding
are total operations for convenient execution; the inverse law is required
only for `Supported` types, while every field and node type in `program` must
be supported. Decoders may reject words that do not encode a value of the
requested language type. -/
structure StorageCodec {Player : Type} [DecidableEq Player] {L : IExpr}
    (program : Program Player L) where
  Word : Type
  Supported : L.Ty → Prop
  encodeValue : (ty : L.Ty) → L.Val ty → Word
  decodeValue : (ty : L.Ty) → Word → Option (L.Val ty)
  decode_encode_value :
    ∀ (ty : L.Ty) (_ : Supported ty) (value : L.Val ty),
      decodeValue ty (encodeValue ty value) = some value
  field_supported :
    ∀ field : Fin program.graph.fieldCount,
      Supported (program.graph.fieldRow field).ty
  node_supported :
    ∀ node : Fin program.graph.nodeCount,
      Supported (program.graph.nodeRow node).ty
  encodeCompleted : Bool → Word
  decodeCompleted : Word → Option Bool
  decode_encode_completed :
    ∀ completed, decodeCompleted (encodeCompleted completed) = some completed

namespace StorageCodec

variable {program : Program Player L}

/-- A semantic reference word that retains its dynamic language type.  This is
useful for specifications and tests, but is not a finite target serialization.
-/
inductive ReferenceWord (L : IExpr) where
  | value (value : TypedValue L)
  | completed (value : Bool)

/-- The lossless semantic reference codec.  A concrete backend codec refines
this interface with a finite representation and target arithmetic semantics.
-/
noncomputable def reference (program : Program Player L) :
    StorageCodec program where
  Word := ReferenceWord L
  Supported _ := True
  encodeValue ty value := .value ⟨ty, value⟩
  decodeValue ty
    | .value value => value.as? ty
    | .completed _ => none
  decode_encode_value ty _ value := by
    simp [TypedValue.as?]
  field_supported _ := trivial
  node_supported _ := trivial
  encodeCompleted value := .completed value
  decodeCompleted
    | .value _ => none
    | .completed value => some value
  decode_encode_completed completed := rfl

end StorageCodec

variable {program : Program Player L}

/-- Sparse raw target storage.  `none` denotes an uninitialized physical key;
a backend may refine it to the target's concrete default-word convention. -/
abbrev RawStore (codec : StorageCodec program) := Nat → Option codec.Word

namespace RawStore

variable {program : Program Player L}
variable (layout : Layout program) (codec : StorageCodec program)

/-- Read and dynamically validate one typed graph value. -/
def readValue (store : RawStore codec)
    (field : Fin program.graph.fieldCount) :
    Option (L.Val (program.graph.fieldRow field).ty) :=
  match store (layout.address (.value field)) with
  | none => none
  | some word =>
      codec.decodeValue (program.graph.fieldRow field).ty word

/-- Encode and write one typed graph value. -/
def writeValue (store : RawStore codec)
    (field : Fin program.graph.fieldCount)
    (value : L.Val (program.graph.fieldRow field).ty) : RawStore codec :=
  Function.update store (layout.address (.value field))
    (some (codec.encodeValue (program.graph.fieldRow field).ty value))

/-- Read an action-completion bit. -/
def readCompleted (store : RawStore codec)
    (node : Fin program.graph.nodeCount) : Option Bool :=
  match store (layout.address (.completed node)) with
  | none => none
  | some word => codec.decodeCompleted word

/-- Encode and write an action-completion bit. -/
def writeCompleted (store : RawStore codec)
    (node : Fin program.graph.nodeCount) (completed : Bool) :
    RawStore codec :=
  Function.update store (layout.address (.completed node))
    (some (codec.encodeCompleted completed))

@[simp] theorem readValue_writeValue
    (store : RawStore codec)
    (field : Fin program.graph.fieldCount)
    (value : L.Val (program.graph.fieldRow field).ty) :
    readValue layout codec (writeValue layout codec store field value) field =
      some value := by
  simp [readValue, writeValue,
    codec.decode_encode_value _ (codec.field_supported field)]

@[simp] theorem readCompleted_writeCompleted
    (store : RawStore codec)
    (node : Fin program.graph.nodeCount) (completed : Bool) :
    readCompleted layout codec
        (writeCompleted layout codec store node completed) node =
      some completed := by
  simp [readCompleted, writeCompleted, codec.decode_encode_completed]

/-- Completion bookkeeping cannot change a language-value read. -/
@[simp] theorem readValue_writeCompleted
    (store : RawStore codec)
    (field : Fin program.graph.fieldCount)
    (node : Fin program.graph.nodeCount) (completed : Bool) :
    readValue layout codec
        (writeCompleted layout codec store node completed) field =
      readValue layout codec store field := by
  have hne :
      layout.address (.value field) ≠
        layout.address (.completed node) := by
    intro heq
    have hslots := layout.injective heq
    cases hslots
  simp [readValue, writeCompleted, hne]

/-- A language-value write cannot change a completion-bit read. -/
@[simp] theorem readCompleted_writeValue
    (store : RawStore codec)
    (field : Fin program.graph.fieldCount)
    (value : L.Val (program.graph.fieldRow field).ty)
    (node : Fin program.graph.nodeCount) :
    readCompleted layout codec
        (writeValue layout codec store field value) node =
      readCompleted layout codec store node := by
  have hne :
      layout.address (.completed node) ≠
        layout.address (.value field) := by
    intro heq
    have hslots := layout.injective heq
    cases hslots
  simp [readCompleted, writeValue, hne]

/-- A write to a distinct value field cannot change this field's read. -/
@[simp] theorem readValue_writeValue_of_ne
    (store : RawStore codec)
    (readField writeField : Fin program.graph.fieldCount)
    (value : L.Val (program.graph.fieldRow writeField).ty)
    (hne : readField ≠ writeField) :
    readValue layout codec
        (writeValue layout codec store writeField value) readField =
      readValue layout codec store readField := by
  have haddress :
      layout.address (.value readField) ≠
        layout.address (.value writeField) := by
    intro heq
    have hslots := layout.injective heq
    cases hslots
    exact hne rfl
  simp [readValue, writeValue, haddress]

/-- A write to a distinct completion slot cannot change this node's bit. -/
@[simp] theorem readCompleted_writeCompleted_of_ne
    (store : RawStore codec)
    (readNode writeNode : Fin program.graph.nodeCount)
    (completed : Bool) (hne : readNode ≠ writeNode) :
    readCompleted layout codec
        (writeCompleted layout codec store writeNode completed) readNode =
      readCompleted layout codec store readNode := by
  have haddress :
      layout.address (.completed readNode) ≠
        layout.address (.completed writeNode) := by
    intro heq
    have hslots := layout.injective heq
    cases hslots
    exact hne rfl
  simp [readCompleted, writeCompleted, haddress]

end RawStore

end Vegas.Machine.Contract
