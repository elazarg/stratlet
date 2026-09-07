/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasEVM.Contract.ClassicalEVMCalldata
import VegasEVM.Contract.EVMAddress

/-!
# EVM instruction encoding and four-way runtime linking

This module introduces actual EVM runtime bytes, one deliberately small layer
at a time. `Instruction` covers the stack, calldata, caller, storage, control,
log, and termination operations needed by a deterministic Vegas contract.
Every instruction has its Yellow-Paper opcode byte and `emit` concatenates
instruction encodings with a proved byte-length equation.

`RuntimeImage` links four independently compiled handler fragments behind the
classical Vegas selectors. The dispatcher extracts the high 32 bits of the
first calldata word, compares them in stable entry-point order, jumps to the
matching fragment, and reverts for every unknown selector. Handler offsets are
32-bit byte offsets; `LinkableHandlers` carries the corresponding code-size
bound instead of silently truncating an address.

This is runtime-byte generation, not yet a compiler-correctness result. In
particular, the handler fragments still need to be produced by certified
expression, storage, authentication, and oracle-state lowerings, and execution
of the emitted bytes must be related to an EVM semantics.
-/

namespace Vegas.Machine.Contract.EVM

/-- One byte of EVM code. -/
abbrev Byte := BitVec 8

/-- Maximum stack height admitted by the EVM. -/
def stackLimit : Nat := 1024

/-- Construct an EVM byte from its numeric opcode. -/
def byte (value : Nat) : Byte := BitVec.ofNat 8 value

/-- A valid immediate payload for `PUSH1` through `PUSH32`. The semantic value
must fit the selected payload width; emitted bytes are derived in EVM
big-endian order, so callers cannot supply bytes inconsistent with the value.
-/
structure PushData where
  value : Word
  byteLength : Nat
  positive : 0 < byteLength
  length_le : byteLength ≤ 32
  value_fits : value.toNat < 2 ^ (8 * byteLength)

namespace PushData

/-- Canonical big-endian payload bytes of a bounded push value. -/
def bytes (data : PushData) : List Byte :=
  List.ofFn fun index : Fin data.byteLength =>
    data.value.extractLsb'
      (8 * (data.byteLength - 1 - (index : Nat))) 8

@[simp] theorem bytes_length (data : PushData) :
    data.bytes.length = data.byteLength := by
  simp [bytes]

/-- One-byte immediate. -/
def one (value : Byte) : PushData where
  value := BitVec.ofNat 256 value.toNat
  byteLength := 1
  positive := by simp
  length_le := by simp
  value_fits := by
    have hsmall : value.toNat < 2 ^ 8 := value.isLt
    rw [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (hsmall.trans (by norm_num))]
    simpa using hsmall

/-- Four-byte immediate. -/
def four (a b c d : Byte) : PushData where
  value := BitVec.ofNat 256
    (((a.toNat * 256 + b.toNat) * 256 + c.toNat) * 256 + d.toNat)
  byteLength := 4
  positive := by simp
  length_le := by simp
  value_fits := by
    have ha : a.toNat < 256 := by simpa using a.isLt
    have hb : b.toNat < 256 := by simpa using b.isLt
    have hc : c.toNat < 256 := by simpa using c.isLt
    have hd : d.toNat < 256 := by simpa using d.isLt
    have hvalue :
        ((a.toNat * 256 + b.toNat) * 256 + c.toNat) * 256 + d.toNat <
          2 ^ 32 := by
      norm_num
      omega
    rw [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (hvalue.trans (by norm_num))]
    simpa using hvalue

/-- Big-endian bytes of a 32-bit EVM selector. -/
def selector (value : Selector) : PushData :=
  { value := BitVec.ofNat 256 value.toNat
    byteLength := 4
    positive := by simp
    length_le := by simp
    value_fits := by
      have hsmall : value.toNat < 2 ^ 32 := value.isLt
      rw [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (hsmall.trans (by norm_num))]
      simpa using hsmall }

/-- A natural number encoded as one 32-bit big-endian immediate. Values at or
above `2^32` wrap; linkable runtime images prove that jump destinations never
do so. -/
def nat32 (value : Nat) : PushData :=
  { value := BitVec.ofNat 256 (value % 2 ^ 32)
    byteLength := 4
    positive := by simp
    length_le := by simp
    value_fits := by
      have hsmall : value % 2 ^ 32 < 2 ^ 32 :=
        Nat.mod_lt _ (by norm_num)
      rw [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (hsmall.trans (by norm_num))]
      simpa using hsmall }

/-- Big-endian bytes of one full EVM word. -/
def word (value : Word) : PushData where
  value := value
  byteLength := 32
  positive := by simp
  length_le := by simp
  value_fits := by simpa using value.isLt

/-- Natural number encoded as a full 256-bit immediate. Values at or above
`2^256` wrap; storage-layout backends carry the bound that excludes this. -/
def nat256 (value : Nat) : PushData :=
  word (BitVec.ofNat 256 value)

/-- Big-endian bytes of one native 160-bit EVM account address. -/
def address (value : AddressWord) : PushData where
  value := BitVec.ofNat 256 value.toNat
  byteLength := 20
  positive := by simp
  length_le := by simp
  value_fits := by
    have hsmall : value.toNat < 2 ^ 160 := value.isLt
    rw [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (hsmall.trans (by norm_num))]
    simpa using hsmall

@[simp] theorem one_length (value : Byte) :
    (one value).bytes.length = 1 := by
  simp [one]

@[simp] theorem selector_length (value : Selector) :
    (selector value).bytes.length = 4 := by
  simp [selector]

@[simp] theorem nat32_length (value : Nat) :
    (nat32 value).bytes.length = 4 := by
  simp [nat32]

@[simp] theorem word_length (value : Word) :
    (word value).bytes.length = 32 := by
  simp [word]

@[simp] theorem nat256_length (value : Nat) :
    (nat256 value).bytes.length = 32 := by
  simp [nat256, word]

@[simp] theorem address_length (value : AddressWord) :
    (address value).bytes.length = 20 := by
  simp [address]

@[simp] theorem one_byteLength (value : Byte) :
    (one value).byteLength = 1 := by rfl

@[simp] theorem selector_byteLength (value : Selector) :
    (selector value).byteLength = 4 := by rfl

@[simp] theorem nat32_byteLength (value : Nat) :
    (nat32 value).byteLength = 4 := by rfl

@[simp] theorem word_byteLength (value : Word) :
    (word value).byteLength = 32 := by rfl

@[simp] theorem nat256_byteLength (value : Nat) :
    (nat256 value).byteLength = 32 := by rfl

@[simp] theorem address_byteLength (value : AddressWord) :
    (address value).byteLength = 20 := by rfl

@[simp] theorem one_value (value : Byte) :
    (one value).value = BitVec.ofNat 256 value.toNat := by rfl

@[simp] theorem one_byte_one_value :
    (one (byte 1)).value = (1 : Word) := by rfl

@[simp] theorem byte_one_setWidth :
    BitVec.setWidth 256 (byte 1) = (1 : Word) := by rfl

@[simp] theorem byte_zero_setWidth :
    BitVec.setWidth 256 (byte 0) = (0 : Word) := by rfl

@[simp] theorem one_bool_value (value : Bool) :
    (one (byte (if value then 1 else 0))).value = encodeBool value := by
  cases value <;> rfl

@[simp] theorem selector_value (value : Selector) :
    (selector value).value = BitVec.ofNat 256 value.toNat := by rfl

@[simp] theorem nat32_value (value : Nat) :
    (nat32 value).value = BitVec.ofNat 256 (value % 2 ^ 32) := by rfl

theorem nat32_value_of_lt {value : Nat} (hvalue : value < 2 ^ 32) :
    (nat32 value).value = BitVec.ofNat 256 value := by
  have hmod : value % 2 ^ 32 = value := Nat.mod_eq_of_lt hvalue
  change BitVec.ofNat 256 (value % 2 ^ 32) = _
  rw [hmod]

theorem nat32_value_toNat_of_lt {value : Nat} (hvalue : value < 2 ^ 32) :
    (nat32 value).value.toNat = value := by
  rw [nat32_value_of_lt hvalue, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  exact hvalue.trans (by norm_num)

@[simp] theorem word_value (value : Word) :
    (word value).value = value := by rfl

@[simp] theorem nat256_value (value : Nat) :
    (nat256 value).value = BitVec.ofNat 256 value := by rfl

theorem nat256_value_toNat_of_lt {value : Nat} (hvalue : value < 2 ^ 256) :
    (nat256 value).value.toNat = value := by
  change (BitVec.ofNat 256 value).toNat = value
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  norm_num at hvalue ⊢
  exact hvalue

@[simp] theorem address_value (value : AddressWord) :
    (address value).value = BitVec.ofNat 256 value.toNat := by rfl

end PushData

/-- Reified EVM operations used by the classical backend. `dup` and `swap`
use zero-based indices: `dup 0` emits `DUP1`, and `swap 0` emits `SWAP1`. -/
inductive Instruction where
  | stop
  | add
  | mul
  | sub
  | div
  | mod
  | lt
  | gt
  | eq
  | iszero
  | and
  | or
  | xor
  | not
  | shl
  | shr
  | keccak256
  | address
  | caller
  | callvalue
  | calldataload
  | calldatasize
  | codecopy
  | pop
  | mload
  | mstore
  | sload
  | sstore
  | jump
  | jumpi
  | pc
  | jumpdest
  | push (data : PushData)
  | dup (index : Fin 16)
  | swap (index : Fin 16)
  | log0
  | return
  | revert
  | invalid

namespace Instruction

/-- Numeric opcode byte of an instruction. Immediate bytes are emitted
separately by `encode`. -/
def opcode : Instruction → Byte
  | .stop => byte 0x00
  | .add => byte 0x01
  | .mul => byte 0x02
  | .sub => byte 0x03
  | .div => byte 0x04
  | .mod => byte 0x06
  | .lt => byte 0x10
  | .gt => byte 0x11
  | .eq => byte 0x14
  | .iszero => byte 0x15
  | .and => byte 0x16
  | .or => byte 0x17
  | .xor => byte 0x18
  | .not => byte 0x19
  | .shl => byte 0x1b
  | .shr => byte 0x1c
  | .keccak256 => byte 0x20
  | .address => byte 0x30
  | .caller => byte 0x33
  | .callvalue => byte 0x34
  | .calldataload => byte 0x35
  | .calldatasize => byte 0x36
  | .codecopy => byte 0x39
  | .pop => byte 0x50
  | .mload => byte 0x51
  | .mstore => byte 0x52
  | .sload => byte 0x54
  | .sstore => byte 0x55
  | .jump => byte 0x56
  | .jumpi => byte 0x57
  | .pc => byte 0x58
  | .jumpdest => byte 0x5b
  | .push data => byte (0x5f + data.byteLength)
  | .dup index => byte (0x80 + index)
  | .swap index => byte (0x90 + index)
  | .log0 => byte 0xa0
  | .return => byte 0xf3
  | .revert => byte 0xfd
  | .invalid => byte 0xfe

/-- Exact byte encoding of one instruction. -/
def encode : Instruction → List Byte
  | instruction@(.push data) => instruction.opcode :: data.bytes
  | instruction => [instruction.opcode]

/-- Encoded byte length of one instruction. -/
def byteLength : Instruction → Nat
  | .push data => 1 + data.byteLength
  | _ => 1

@[simp] theorem encode_length (instruction : Instruction) :
    instruction.encode.length = instruction.byteLength := by
  cases instruction <;> simp [encode, byteLength, Nat.add_comm]

@[simp] theorem opcode_push_one (value : Byte) :
    opcode (.push (.one value)) = byte 0x60 := by
  rfl

@[simp] theorem opcode_push_selector (value : Selector) :
    opcode (.push (.selector value)) = byte 0x63 := by
  rfl

@[simp] theorem opcode_push_word (value : Word) :
    opcode (.push (.word value)) = byte 0x7f := by
  simp [opcode]

@[simp] theorem opcode_push_address (value : AddressWord) :
    opcode (.push (.address value)) = byte 0x73 := by
  simp [opcode]

end Instruction

/-- A symbolic EVM instruction program. -/
abbrev Assembly := List Instruction

namespace Assembly

/-- Number of bytes occupied by an instruction program. -/
def byteLength (program : Assembly) : Nat :=
  (program.map Instruction.byteLength).sum

/-- Emit actual EVM bytes. -/
def emit (program : Assembly) : List Byte :=
  program.flatMap Instruction.encode

/-- Emission occupies exactly the statically computed byte length. -/
@[simp] theorem emit_length (program : Assembly) :
    program.emit.length = program.byteLength := by
  induction program with
  | nil => rfl
  | cons instruction rest ih =>
      simp [emit, byteLength]

@[simp] theorem byteLength_append (left right : Assembly) :
    (left ++ right).byteLength = left.byteLength + right.byteLength := by
  simp [byteLength]

@[simp] theorem emit_append (left right : Assembly) :
    (left ++ right).emit = left.emit ++ right.emit := by
  simp [emit]

end Assembly

/-- Four entry points of the deterministic classical contract ABI. -/
inductive ClassicalEntry where
  | player
  | reveal
  | sampleRequest
  | oracleCallback
deriving DecidableEq

namespace ClassicalEntry

/-- Stable zero-based position of an entry in the public dispatcher. -/
@[simp] def dispatchIndex : ClassicalEntry → Nat
  | .player => 0
  | .reveal => 1
  | .sampleRequest => 2
  | .oracleCallback => 3

end ClassicalEntry

namespace ClassicalSelectors

/-- Selector assigned to one classical entry point. -/
@[simp] def get (selectors : ClassicalSelectors) : ClassicalEntry → Selector
  | .player => selectors.player
  | .reveal => selectors.reveal
  | .sampleRequest => selectors.sampleRequest
  | .oracleCallback => selectors.oracleCallback

end ClassicalSelectors

/-- Independently compiled runtime fragments for the classical ABI. A handler
is entered with an otherwise empty stack after selector dispatch. -/
structure ClassicalHandlers where
  player : Assembly
  reveal : Assembly
  sampleRequest : Assembly
  oracleCallback : Assembly

namespace ClassicalHandlers

/-- Select one handler fragment. -/
def get (handlers : ClassicalHandlers) : ClassicalEntry → Assembly
  | .player => handlers.player
  | .reveal => handlers.reveal
  | .sampleRequest => handlers.sampleRequest
  | .oracleCallback => handlers.oracleCallback

/-- Each handler begins with `JUMPDEST` and discards the selector retained by
the dispatcher. -/
def block (handlers : ClassicalHandlers) (entry : ClassicalEntry) : Assembly :=
  [.jumpdest, .pop] ++ handlers.get entry

/-- Encoded size of one linked handler block. -/
def blockSize (handlers : ClassicalHandlers) (entry : ClassicalEntry) : Nat :=
  2 + (handlers.get entry).byteLength

@[simp] theorem block_byteLength (handlers : ClassicalHandlers)
    (entry : ClassicalEntry) :
    (handlers.block entry).byteLength = handlers.blockSize entry := by
  simp [block, blockSize, Assembly.byteLength, Instruction.byteLength]
  omega

end ClassicalHandlers

/-- The selector dispatcher is always 64 bytes: 6 bytes to extract the
selector, four 13-byte comparisons with `PUSH4` destinations, and a 6-byte
fallback revert. -/
def classicalDispatcherSize : Nat := 64

/-- Byte offset of a handler's `JUMPDEST` in the linked runtime image. -/
def classicalEntryOffset (handlers : ClassicalHandlers) :
    ClassicalEntry → Nat
  | .player => classicalDispatcherSize
  | .reveal =>
      classicalDispatcherSize + handlers.blockSize .player
  | .sampleRequest =>
      classicalDispatcherSize + handlers.blockSize .player +
        handlers.blockSize .reveal
  | .oracleCallback =>
      classicalDispatcherSize + handlers.blockSize .player +
        handlers.blockSize .reveal + handlers.blockSize .sampleRequest

/-- One selector comparison and conditional jump. -/
def classicalDispatchBranch (selector : Selector) (destination : Nat) :
    Assembly :=
  [ .dup ⟨0, by decide⟩,
    .push (.selector selector),
    .eq,
    .push (.nat32 destination),
    .jumpi ]

@[simp] theorem classicalDispatchBranch_byteLength
    (selector : Selector) (destination : Nat) :
    (classicalDispatchBranch selector destination).byteLength = 13 := by
  simp [classicalDispatchBranch, Assembly.byteLength,
    Instruction.byteLength]

/-- Load and isolate the high four calldata bytes used as the selector. -/
def classicalDispatchPrelude : Assembly :=
  [ .push (.one (byte 0)), .calldataload,
    .push (.one (byte 224)), .shr ]

@[simp] theorem classicalDispatchPrelude_byteLength :
    classicalDispatchPrelude.byteLength = 6 := by
  simp [classicalDispatchPrelude, Assembly.byteLength,
    Instruction.byteLength]

/-- Unknown-selector fallback with empty revert data. -/
def classicalDispatchFallback : Assembly :=
  [ .pop, .push (.one (byte 0)), .push (.one (byte 0)), .revert ]

@[simp] theorem classicalDispatchFallback_byteLength :
    classicalDispatchFallback.byteLength = 6 := by
  simp [classicalDispatchFallback, Assembly.byteLength,
    Instruction.byteLength]

/-- The fixed four-way selector dispatcher. -/
def classicalDispatcher (selectors : ClassicalSelectors)
    (handlers : ClassicalHandlers) : Assembly :=
  classicalDispatchPrelude ++
  classicalDispatchBranch selectors.player
    (classicalEntryOffset handlers .player) ++
  classicalDispatchBranch selectors.reveal
    (classicalEntryOffset handlers .reveal) ++
  classicalDispatchBranch selectors.sampleRequest
    (classicalEntryOffset handlers .sampleRequest) ++
  classicalDispatchBranch selectors.oracleCallback
    (classicalEntryOffset handlers .oracleCallback) ++
  classicalDispatchFallback

@[simp] theorem classicalDispatcher_byteLength
    (selectors : ClassicalSelectors) (handlers : ClassicalHandlers) :
    (classicalDispatcher selectors handlers).byteLength =
      classicalDispatcherSize := by
  simp only [classicalDispatcher, Assembly.byteLength_append,
    classicalDispatchPrelude_byteLength, classicalDispatchBranch_byteLength,
    classicalDispatchFallback_byteLength]
  norm_num [Assembly.byteLength, Instruction.byteLength,
    classicalDispatcherSize]

/-- Complete linked EVM runtime assembly. -/
def classicalRuntimeAssembly (selectors : ClassicalSelectors)
    (handlers : ClassicalHandlers) : Assembly :=
  classicalDispatcher selectors handlers ++
    handlers.block .player ++
    handlers.block .reveal ++
    handlers.block .sampleRequest ++
    handlers.block .oracleCallback

/-- Total linked runtime byte length. -/
def classicalRuntimeSize (handlers : ClassicalHandlers) : Nat :=
  classicalDispatcherSize +
    handlers.blockSize .player +
    handlers.blockSize .reveal +
    handlers.blockSize .sampleRequest +
    handlers.blockSize .oracleCallback

/-- Every handler destination names a byte inside the linked runtime image. -/
theorem classicalEntryOffset_lt_runtimeSize (handlers : ClassicalHandlers)
    (entry : ClassicalEntry) :
    classicalEntryOffset handlers entry < classicalRuntimeSize handlers := by
  cases entry <;>
    simp [classicalEntryOffset, classicalRuntimeSize,
      ClassicalHandlers.blockSize]
  all_goals omega

@[simp] theorem classicalRuntimeAssembly_byteLength
    (selectors : ClassicalSelectors) (handlers : ClassicalHandlers) :
    (classicalRuntimeAssembly selectors handlers).byteLength =
      classicalRuntimeSize handlers := by
  simp [classicalRuntimeAssembly, classicalRuntimeSize]
  omega

/-- Handler code that can be linked without truncating a 32-bit destination.
The condition is intentionally stated on the complete runtime image. -/
structure LinkableHandlers where
  handlers : ClassicalHandlers
  size_fits : classicalRuntimeSize handlers < 2 ^ 32

namespace LinkableHandlers

/-- No linked jump destination is truncated by its `PUSH4` encoding. -/
theorem entryOffset_fits (handlers : LinkableHandlers)
    (entry : ClassicalEntry) :
    classicalEntryOffset handlers.handlers entry < 2 ^ 32 :=
  (classicalEntryOffset_lt_runtimeSize handlers.handlers entry).trans
    handlers.size_fits

end LinkableHandlers

/-- A linked EVM runtime image with actual bytecode and the proof that every
statically computed handler destination is represented exactly by `PUSH4`. -/
structure RuntimeImage (selectors : ClassicalSelectors) where
  handlers : LinkableHandlers

namespace RuntimeImage

variable {selectors : ClassicalSelectors}

/-- The assembly determined by a linked image's selectors and handlers. -/
def assembly (image : RuntimeImage selectors) : Assembly :=
  classicalRuntimeAssembly selectors image.handlers.handlers

/-- The exact bytes emitted by a linked image. -/
def bytecode (image : RuntimeImage selectors) : List Byte :=
  image.assembly.emit

/-- Emission has the exact size certified by the handler linker. -/
@[simp] theorem bytecode_length (image : RuntimeImage selectors) :
    image.bytecode.length =
      classicalRuntimeSize image.handlers.handlers := by
  simp [RuntimeImage.bytecode, RuntimeImage.assembly]

/-- The deployed runtime length is represented exactly by `PUSH4`. -/
theorem bytecode_length_fits (image : RuntimeImage selectors) :
    image.bytecode.length < 2 ^ 32 := by
  rw [bytecode_length]
  exact image.handlers.size_fits

/-- Link independently compiled handlers behind one classical ABI. -/
def link (selectors : ClassicalSelectors) (handlers : LinkableHandlers) :
    RuntimeImage selectors where
  handlers := handlers

@[simp] theorem link_assembly (selectors : ClassicalSelectors)
    (handlers : LinkableHandlers) :
    (link selectors handlers).assembly =
      classicalRuntimeAssembly selectors handlers.handlers := by
  rfl

@[simp] theorem link_bytecode (selectors : ClassicalSelectors)
    (handlers : LinkableHandlers) :
    (link selectors handlers).bytecode =
      (classicalRuntimeAssembly selectors handlers.handlers).emit := by
  rfl

@[simp] theorem link_bytecode_length (selectors : ClassicalSelectors)
    (handlers : LinkableHandlers) :
    (link selectors handlers).bytecode.length =
      classicalRuntimeSize handlers.handlers := by
  simp [link]

end RuntimeImage

end Vegas.Machine.Contract.EVM
