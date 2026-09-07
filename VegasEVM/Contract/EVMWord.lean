/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Core.ExprSimple
import VegasEVM.Contract.Storage
import VegasEVM.Contract.Wire

/-!
# EVM-sized storage words

This module supplies the first concrete finite storage representation. It does
not claim to be an EVM backend: there is no byte-level ABI, instruction IR,
gas, revert, or transaction semantics here. It only represents Boolean graph
values and completion flags by canonical 256-bit words.

The codec is available to a `simpleExpr` program exactly when all of its graph
fields and nodes have Boolean type. Other `simpleExpr` types still have total
placeholder encoding functions because `StorageCodec` is an executable
interface, but they are unsupported and no inverse law is claimed for them.
-/

namespace Vegas.Machine.Contract.EVM

open EventGraph

variable {Player : Type} [DecidableEq Player]

/-- One EVM-sized word. This is a representation type, not yet an EVM value
semantics or byte encoding. -/
abbrev Word := BitVec 256

/-- Canonical Boolean encoding: false is zero and true is one. -/
def encodeBool : Bool → Word
  | false => 0
  | true => 1

/-- Decode only the two canonical Boolean words. -/
def decodeBool (word : Word) : Option Bool :=
  if word = 0 then some false
  else if word = 1 then some true
  else none

@[simp] theorem decodeBool_encodeBool (value : Bool) :
    decodeBool (encodeBool value) = some value := by
  cases value <;> simp [decodeBool, encodeBool]

/-- Total implementation used beneath the supported-type boundary. A `word`
is already a machine word, so it encodes by the identity; the unbounded `int`
and the remaining types receive a dummy word that carries no round-trip
promise. -/
def encodeSimpleValue : (ty : BaseTy) → Val ty → Word
  | .int, _ => 0
  | .bool, value => encodeBool value
  | .word, value => value
  | .range _ _, _ => 0
  | .option _, _ => 0

/-- Booleans and machine words have concrete decoders. Every 256-bit word is a
valid `word` value, so that decoder is total. -/
def decodeSimpleValue : (ty : BaseTy) → Word → Option (Val ty)
  | .int, _ => none
  | .bool, word => decodeBool word
  | .word, word => some word
  | .range _ _, _ => none
  | .option _, _ => none

/-- Machine words round-trip through storage exactly, with no side condition:
this is the representation law the unbounded `int` cannot satisfy. -/
@[simp] theorem decodeSimpleValue_encodeSimpleValue_word (value : Val .word) :
    decodeSimpleValue .word (encodeSimpleValue .word value) = some value := rfl

/-- Storage types carried losslessly by a single 256-bit word. -/
def WordEncodable : BaseTy → Prop
  | .bool => True
  | .word => True
  | _ => False

instance : DecidablePred WordEncodable
  | .int => inferInstanceAs (Decidable False)
  | .bool => inferInstanceAs (Decidable True)
  | .word => inferInstanceAs (Decidable True)
  | .range _ _ => inferInstanceAs (Decidable False)
  | .option _ => inferInstanceAs (Decidable False)

/-- Every word-encodable storage type round-trips. -/
theorem decodeSimpleValue_encodeSimpleValue
    (ty : BaseTy) (supported : WordEncodable ty) (value : Val ty) :
    decodeSimpleValue ty (encodeSimpleValue ty value) = some value := by
  cases ty with
  | bool => exact decodeBool_encodeBool value
  | word => rfl
  | int => exact absurd supported not_false
  | range _ _ => exact absurd supported not_false
  | option _ => exact absurd supported not_false

/-- Evidence that the storage-bearing portion of a compiled program uses only
Boolean values. Payoff expressions are deliberately irrelevant here because
they are evaluated after decoding the terminal graph store. -/
structure UsesOnlyBoolStorage (program : Program Player simpleExpr) : Prop where
  field_type :
    ∀ field : Fin program.graph.fieldCount,
      (program.graph.fieldRow field).ty = .bool
  node_type :
    ∀ node : Fin program.graph.nodeCount,
      (program.graph.nodeRow node).ty = .bool

/-- Evidence that the storage-bearing portion of a compiled program uses only
values with a lossless single-word representation. This is the general
condition `boolStorageCodec` was a special case of: it admits `word`-typed
fields and nodes, which carry real EVM data rather than a single bit. -/
structure UsesWordStorage (program : Program Player simpleExpr) : Prop where
  field_type :
    ∀ field : Fin program.graph.fieldCount,
      WordEncodable (program.graph.fieldRow field).ty
  node_type :
    ∀ node : Fin program.graph.nodeCount,
      WordEncodable (program.graph.nodeRow node).ty

/-- Boolean storage is word storage. -/
theorem UsesOnlyBoolStorage.usesWordStorage
    {program : Program Player simpleExpr}
    (usesBool : UsesOnlyBoolStorage program) : UsesWordStorage program where
  field_type field := by rw [usesBool.field_type field]; trivial
  node_type node := by rw [usesBool.node_type node]; trivial

/-- A finite 256-bit storage codec for any word-encodable program. -/
def wordStorageCodec (program : Program Player simpleExpr)
    (usesWord : UsesWordStorage program) : StorageCodec program where
  Word := Word
  Supported := WordEncodable
  encodeValue := encodeSimpleValue
  decodeValue := decodeSimpleValue
  decode_encode_value := decodeSimpleValue_encodeSimpleValue
  field_supported := usesWord.field_type
  node_supported := usesWord.node_type
  encodeCompleted := encodeBool
  decodeCompleted := decodeBool
  decode_encode_completed := decodeBool_encodeBool

/-- A finite 256-bit storage codec for a Boolean-storage program. Retained
alongside `wordStorageCodec` because the Boolean instruction generator needs
`Supported` to pin the type to `.bool`, so that it may emit canonical zero/one
selection circuits. -/
def boolStorageCodec (program : Program Player simpleExpr)
    (usesBool : UsesOnlyBoolStorage program) : StorageCodec program where
  Word := Word
  Supported ty := ty = .bool
  encodeValue := encodeSimpleValue
  decodeValue := decodeSimpleValue
  decode_encode_value ty supported value := by
    subst ty
    exact decodeBool_encodeBool value
  field_supported := usesBool.field_type
  node_supported := usesBool.node_type
  encodeCompleted := encodeBool
  decodeCompleted := decodeBool
  decode_encode_completed := decodeBool_encodeBool

/-- The representation law required by instruction generation: the backend's
storage word and outer EVM wire codecs agree with the canonical single-word
encoding at every word-encodable type.

Generalizes the Boolean-only form this replaced. At `.bool` it is exactly the
literal zero/one law that branchless selection circuits depend on; at `.word` it
says the outer wire codec is transparent, since `encodeSimpleValue .word` is the
identity. -/
structure CanonicalRepresentation (program : Program Player simpleExpr)
    (codec : StorageCodec program)
    (words : WireCodec codec.Word Word) : Prop where
  encode_value :
    ∀ (ty : BaseTy), WordEncodable ty → ∀ value : Val ty,
      words.encode (codec.encodeValue ty value) = encodeSimpleValue ty value
  decode_value :
    ∀ (ty : BaseTy), WordEncodable ty → ∀ word : Word,
      (words.decode word).bind (codec.decodeValue ty) =
        decodeSimpleValue ty word

/-- Transporting a value through a proof about its storage type does not change
its canonical single-word representation. -/
theorem CanonicalRepresentation.encode_type_eq
    {program : Program Player simpleExpr} {codec : StorageCodec program}
    {words : WireCodec codec.Word Word}
    (canonical : CanonicalRepresentation program codec words)
    {ty ty' : simpleExpr.Ty} (hty : ty = ty')
    (hword : WordEncodable ty') (value : Val ty') :
    words.encode (codec.encodeValue ty (hty.symm ▸ value)) =
      encodeSimpleValue ty' value := by
  subst ty
  exact canonical.encode_value ty' hword value

/-- The Boolean instance of `encode_type_eq`, which is what the zero/one
selection circuits consume. -/
theorem CanonicalRepresentation.encode_type_eq_bool
    {program : Program Player simpleExpr} {codec : StorageCodec program}
    {words : WireCodec codec.Word Word}
    (canonical : CanonicalRepresentation program codec words)
    {ty : simpleExpr.Ty} (hty : ty = .bool) (value : Bool) :
    words.encode
        (codec.encodeValue ty (hty.symm ▸ value)) =
      encodeBool value :=
  canonical.encode_type_eq hty trivial value

/-- The word storage codec with the identity outer wire encoding satisfies the
representation law at every supported type: both codecs are `encodeSimpleValue`
by construction. -/
theorem identityRepresentation (program : Program Player simpleExpr)
    (usesWord : UsesWordStorage program) :
    CanonicalRepresentation program (wordStorageCodec program usesWord)
      (WireCodec.identity Word) where
  encode_value _ty _hword _value := rfl
  decode_value _ty _hword _word := rfl

/-- The native Boolean storage codec with the identity outer wire encoding
has the exact representation expected by generated instructions. -/
theorem boolIdentityRepresentation (program : Program Player simpleExpr)
    (usesBool : UsesOnlyBoolStorage program) :
    CanonicalRepresentation program (boolStorageCodec program usesBool)
      (WireCodec.identity Word) where
  encode_value _ty _hword _value := rfl
  decode_value _ty _hword _word := rfl

end Vegas.Machine.Contract.EVM
