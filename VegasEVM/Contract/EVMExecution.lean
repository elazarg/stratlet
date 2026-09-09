/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasEVM.Contract.EVMDeployment
import VegasEVM.Contract.ClassicalEVMBytes

/-!
# Executable semantics for the emitted EVM subset

This module gives the reified EVM instructions an explicit gas-free execution
semantics. Program counters and jump destinations are byte offsets, pushes use
their emitted big-endian payload, calldata is zero-padded as on EVM, storage is
total, and memory/log/return/revert effects are concrete byte sequences.

The semantics deliberately faults on operations the current Vegas backend does
not emit (`KECCAK256` is the only such nontrivial operation). Gas accounting,
call frames, and chain transaction scheduling are later refinements. This is a
classical target semantics, not yet the theorem that generated handlers refine
the typed classical contract.

**This semantics is not validated against the Ethereum conformance suite.**
Every theorem proved against it — the code-generation results included — holds
relative to *this* model of the EVM rather than to the EVM. That is a trust
assumption of a different kind from a missing theorem, and it is the largest one
in the backend: a discrepancy here would not show up as an unproved goal.

Two mature alternatives are conformance-tested and would discharge it rather
than restate it: `EVMYulLean`, a Cancun-aligned executable EVM/Yul model in
Lean 4 reported to pass 99.99% of the official Ethereum tests, and the HOL4 EVM
model underlying `vyper-hol`, validated against the Ethereum Execution Spec
Tests. Retargeting code generation at the former is the natural move, and is
the architecture `sir-lean` independently recommends for the same problem.
-/

namespace Vegas.Machine.Contract.EVM

/-- Interpret a big-endian byte string as one 256-bit EVM word. -/
def bytesToWord (bytes : List Byte) : Word :=
  BitVec.setWidth 256 (BitVec.flattenList bytes)

/-- Read a fixed number of bytes, padding beyond the input with zero. -/
def readBytes (bytes : List Byte) (offset count : Nat) : List Byte :=
  List.ofFn fun index : Fin count => bytes[offset + index]?.getD 0

@[simp] theorem readBytes_length (bytes : List Byte) (offset count : Nat) :
    (readBytes bytes offset count).length = count := by
  simp [readBytes]

/-- Reading exactly the available suffix does not introduce zero padding. -/
theorem readBytes_drop_length (bytes : List Byte) (offset : Nat) :
    readBytes bytes offset (bytes.drop offset).length = bytes.drop offset := by
  apply List.ext_getElem
  · simp
  · intro index hleft hright
    have hinBounds : offset + index < bytes.length := by
      simp at hright
      omega
    simp [readBytes, List.getElem_drop, hinBounds]

/-- One EVM `CALLDATALOAD`. -/
def calldataLoad (calldata : List Byte) (offset : Nat) : Word :=
  bytesToWord (readBytes calldata offset 32)

/-- Big-endian byte sequence represented by dependent byte calldata. -/
def ByteCalldata.bytes (calldata : ByteCalldata) : List Byte :=
  List.ofFn fun index : Fin calldata.byteLength =>
    calldata.bits.extractLsb'
      (8 * (calldata.byteLength - 1 - (index : Nat))) 8

@[simp] theorem ByteCalldata.bytes_length (calldata : ByteCalldata) :
    calldata.bytes.length = calldata.byteLength := by
  simp [ByteCalldata.bytes]

/-- Byte serialization followed by bitvector concatenation recovers the
dependent calldata bitstring exactly. -/
theorem ByteCalldata.flatten_bytes (calldata : ByteCalldata) :
    BitVec.cast (by simp) (BitVec.flattenList calldata.bytes) =
      calldata.bits := by
  apply BitVec.eq_of_getMsbD_eq
  intro index hindex
  have hbyte : index / 8 < calldata.byteLength := by omega
  have hmod : index % 8 < 8 := Nat.mod_lt _ (by omega)
  have hdecomp : 8 * (index / 8) + index % 8 = index :=
    Nat.div_add_mod index 8
  have hwithin :
      8 * (calldata.byteLength - 1 - index / 8) + 8 - index % 8 ≤
        8 * calldata.byteLength := by omega
  simp only [BitVec.getMsbD_cast]
  simp only [BitVec.getMsbD_flattenList, ByteCalldata.bytes,
    List.getElem?_ofFn, hbyte]
  rw [dif_pos (by trivial)]
  simp only [Option.getD_some,
    BitVec.getMsbD_extractLsb', hmod, hwithin, decide_true, Bool.true_and]
  apply congrArg calldata.bits.getMsbD
  omega

/-- An in-bounds EVM word load from serialized calldata is the corresponding
256-bit slice of its dependent bitstring. -/
theorem ByteCalldata.calldataLoad_eq_extract (calldata : ByteCalldata)
    (offset : Nat) (hbound : offset + 32 ≤ calldata.byteLength) :
    calldataLoad calldata.bytes offset =
      calldata.bits.extractLsb'
        (8 * (calldata.byteLength - (offset + 32))) 256 := by
  apply BitVec.eq_of_getMsbD_eq
  intro index hindex
  have hwordByte : index / 8 < 32 := by omega
  have hsourceByte : offset + index / 8 < calldata.byteLength := by omega
  have hmod : index % 8 < 8 := Nat.mod_lt _ (by omega)
  have hdecomp : 8 * (index / 8) + index % 8 = index :=
    Nat.div_add_mod index 8
  have hleftWithin :
      8 * (calldata.byteLength - 1 - (offset + index / 8)) + 8 -
          index % 8 ≤
        8 * calldata.byteLength := by omega
  have hrightWithin :
      8 * (calldata.byteLength - (offset + 32)) + 256 - index ≤
        8 * calldata.byteLength := by omega
  simp only [calldataLoad, bytesToWord, BitVec.getMsbD_setWidth,
    readBytes_length, Nat.reduceMul, Nat.sub_self, Nat.zero_le,
    decide_true, Bool.true_and, Nat.add_sub_cancel,
    BitVec.getMsbD_flattenList]
  simp only [readBytes, List.getElem?_ofFn, hwordByte,
    ByteCalldata.bytes, hsourceByte]
  rw [dif_pos (by trivial), dif_pos (by trivial)]
  simp only [Option.getD_some, BitVec.getMsbD_extractLsb', hmod,
    hleftWithin, hindex, hrightWithin, decide_true, Bool.true_and]
  apply congrArg calldata.bits.getMsbD
  omega

namespace ClassicalABI

open EventGraph

variable {Player ValueWord : Type}
variable [DecidableEq Player]
variable {L : IExpr} {program : Program Player L}

/-- Linked dispatch compares selectors as zero-extended EVM words. -/
def selectorWord (selector : Selector) : Word :=
  BitVec.ofNat 256 selector.toNat

/-- Taking the leading 32 bytes and applying the dispatcher shift recovers
the zero-extended selector independently of following calldata. -/
theorem selectorWord_extract_append (selector : Selector)
    {tailWidth : Nat} (tail : BitVec tailWidth)
    (htail : 224 ≤ tailWidth) :
    (selector ++ tail).extractLsb' (tailWidth - 224) 256 >>> 224 =
      selectorWord selector := by
  apply BitVec.eq_of_getLsbD_eq
  intro index hindex
  have hposition : tailWidth - 224 + (224 + index) =
      tailWidth + index := by omega
  by_cases hbit : selector.getLsbD index = true
  · have hselector := BitVec.lt_of_getLsbD hbit
    simp [BitVec.getLsbD_extractLsb', selectorWord,
      BitVec.getLsbD_append, hindex, hposition, hbit]
    omega
  · simp [BitVec.getLsbD_extractLsb', selectorWord,
      BitVec.getLsbD_append, hindex, hposition, hbit]

@[simp] theorem calldataSelector_encodeBytes_player
    (abi : ClassicalABI program ValueWord)
    (message : Blockchain.PlayerMessage program ValueWord) :
    calldataLoad (abi.encodeBytes (.player message)).bytes 0 >>> 224 =
      selectorWord abi.selectors.player := by
  rw [ByteCalldata.calldataLoad_eq_extract _ 0 (by simp [encodeBytes])]
  change
    (BitVec.extractLsb' 544 256
      (((abi.selectors.player ++ abi.players.encode message.player) ++
        abi.nodes.encode message.node) ++ abi.values.encode message.value) >>>
          224) = _
  rw [BitVec.append_assoc, BitVec.append_assoc]
  simp only [BitVec.extractLsb'_cast]
  exact selectorWord_extract_append abi.selectors.player
    (abi.players.encode message.player ++
      (abi.nodes.encode message.node ++ abi.values.encode message.value))
    (by norm_num)

@[simp] theorem calldataSelector_encodeBytes_reveal
    (abi : ClassicalABI program ValueWord)
    (message : ClassicalNodeMessage program) :
    calldataLoad (abi.encodeBytes (.reveal message)).bytes 0 >>> 224 =
      selectorWord abi.selectors.reveal := by
  rw [ByteCalldata.calldataLoad_eq_extract _ 0 (by simp [encodeBytes])]
  change (BitVec.extractLsb' 32 256
    (abi.selectors.reveal ++ abi.nodes.encode message.node) >>> 224) = _
  exact selectorWord_extract_append abi.selectors.reveal
    (abi.nodes.encode message.node) (by norm_num)

@[simp] theorem calldataSelector_encodeBytes_sampleRequest
    (abi : ClassicalABI program ValueWord)
    (message : ClassicalNodeMessage program) :
    calldataLoad (abi.encodeBytes (.sampleRequest message)).bytes 0 >>> 224 =
      selectorWord abi.selectors.sampleRequest := by
  rw [ByteCalldata.calldataLoad_eq_extract _ 0 (by simp [encodeBytes])]
  change (BitVec.extractLsb' 32 256
    (abi.selectors.sampleRequest ++ abi.nodes.encode message.node) >>> 224) = _
  exact selectorWord_extract_append abi.selectors.sampleRequest
    (abi.nodes.encode message.node) (by norm_num)

@[simp] theorem calldataSelector_encodeBytes_oracleCallback
    (abi : ClassicalABI program ValueWord)
    (message : ClassicalOracleMessage program) :
    calldataLoad (abi.encodeBytes (.oracleCallback message)).bytes 0 >>> 224 =
      selectorWord abi.selectors.oracleCallback := by
  rw [ByteCalldata.calldataLoad_eq_extract _ 0 (by simp [encodeBytes])]
  change (((abi.selectors.oracleCallback ++ abi.nodes.encode message.node) ++
    message.choice).extractLsb' 288 256 >>> 224) = _
  rw [BitVec.append_assoc]
  simp only [BitVec.extractLsb'_cast]
  exact selectorWord_extract_append abi.selectors.oracleCallback
    (abi.nodes.encode message.node ++ message.choice) (by norm_num)

/-- The three player-call arguments occupy their standard EVM word offsets. -/
@[simp] theorem calldataLoad_encodeBytes_player_player
    (abi : ClassicalABI program ValueWord)
    (message : Blockchain.PlayerMessage program ValueWord) :
    calldataLoad (abi.encodeBytes (.player message)).bytes 4 =
      abi.players.encode message.player := by
  rw [ByteCalldata.calldataLoad_eq_extract _ 4 (by simp [encodeBytes])]
  simp [encodeBytes]

@[simp] theorem calldataLoad_encodeBytes_player_node
    (abi : ClassicalABI program ValueWord)
    (message : Blockchain.PlayerMessage program ValueWord) :
    calldataLoad (abi.encodeBytes (.player message)).bytes 36 =
      abi.nodes.encode message.node := by
  rw [ByteCalldata.calldataLoad_eq_extract _ 36 (by simp [encodeBytes])]
  simp [encodeBytes]

@[simp] theorem calldataLoad_encodeBytes_player_value
    (abi : ClassicalABI program ValueWord)
    (message : Blockchain.PlayerMessage program ValueWord) :
    calldataLoad (abi.encodeBytes (.player message)).bytes 68 =
      abi.values.encode message.value := by
  rw [ByteCalldata.calldataLoad_eq_extract _ 68 (by simp [encodeBytes])]
  simp [encodeBytes]

/-- The one-word internal entry points place their node at byte offset four. -/
@[simp] theorem calldataLoad_encodeBytes_reveal_node
    (abi : ClassicalABI program ValueWord)
    (message : ClassicalNodeMessage program) :
    calldataLoad (abi.encodeBytes (.reveal message)).bytes 4 =
      abi.nodes.encode message.node := by
  rw [ByteCalldata.calldataLoad_eq_extract _ 4 (by simp [encodeBytes])]
  simp [encodeBytes]

@[simp] theorem calldataLoad_encodeBytes_sampleRequest_node
    (abi : ClassicalABI program ValueWord)
    (message : ClassicalNodeMessage program) :
    calldataLoad (abi.encodeBytes (.sampleRequest message)).bytes 4 =
      abi.nodes.encode message.node := by
  rw [ByteCalldata.calldataLoad_eq_extract _ 4 (by simp [encodeBytes])]
  simp [encodeBytes]

/-- Callback node and table index occupy the two standard argument words. -/
@[simp] theorem calldataLoad_encodeBytes_oracleCallback_node
    (abi : ClassicalABI program ValueWord)
    (message : ClassicalOracleMessage program) :
    calldataLoad (abi.encodeBytes (.oracleCallback message)).bytes 4 =
      abi.nodes.encode message.node := by
  rw [ByteCalldata.calldataLoad_eq_extract _ 4 (by simp [encodeBytes])]
  simp [encodeBytes]

@[simp] theorem calldataLoad_encodeBytes_oracleCallback_choice
    (abi : ClassicalABI program ValueWord)
    (message : ClassicalOracleMessage program) :
    calldataLoad (abi.encodeBytes (.oracleCallback message)).bytes 36 =
      message.choice := by
  rw [ByteCalldata.calldataLoad_eq_extract _ 36 (by simp [encodeBytes])]
  simp [encodeBytes]

end ClassicalABI

/-- Byte-addressed volatile EVM memory. -/
abbrev Memory := Nat → Byte

/-- Initially zero EVM memory. -/
def emptyMemory : Memory := fun _ => 0

/-- Write a byte string to consecutive memory addresses. -/
def writeBytes (memory : Memory) (offset : Nat) : List Byte → Memory
  | [] => memory
  | value :: rest =>
      writeBytes (Function.update memory offset value) (offset + 1) rest

/-- Read consecutive bytes from memory. -/
def readMemory (memory : Memory) (offset count : Nat) : List Byte :=
  List.ofFn fun index : Fin count => memory (offset + index)

@[simp] theorem readMemory_length (memory : Memory) (offset count : Nat) :
    (readMemory memory offset count).length = count := by
  simp [readMemory]

/-- Writes beginning strictly after an address leave that address unchanged. -/
theorem writeBytes_eq_of_lt (memory : Memory) (offset : Nat)
    (bytes : List Byte) (address : Nat) (haddress : address < offset) :
    writeBytes memory offset bytes address = memory address := by
  induction bytes generalizing offset memory with
  | nil => rfl
  | cons value rest ih =>
      rw [writeBytes]
      rw [ih (offset := offset + 1) (memory := Function.update memory offset value)
        (by omega)]
      simp [Function.update, Nat.ne_of_lt haddress]

/-- A byte written at an in-range displacement can be read back exactly. -/
theorem writeBytes_getElem (memory : Memory) (offset : Nat)
    (bytes : List Byte) (index : Nat) (hindex : index < bytes.length) :
    writeBytes memory offset bytes (offset + index) = bytes[index] := by
  induction bytes generalizing offset memory index with
  | nil => simp at hindex
  | cons value rest ih =>
      cases index with
      | zero =>
          rw [writeBytes]
          rw [writeBytes_eq_of_lt]
          · simp [Function.update]
          · omega
      | succ index =>
          rw [writeBytes]
          have hrest : index < rest.length := by simpa using hindex
          have hread := ih (offset := offset + 1)
            (memory := Function.update memory offset value) index hrest
          simpa only [List.getElem_cons_succ, Nat.add_assoc,
            Nat.add_comm 1 index] using hread

/-- Reading the interval just written returns the complete byte string. -/
theorem readMemory_writeBytes (memory : Memory) (offset : Nat)
    (bytes : List Byte) :
    readMemory (writeBytes memory offset bytes) offset bytes.length = bytes := by
  apply List.ext_getElem
  · simp
  · intro index hleft hright
    simpa [readMemory] using
      writeBytes_getElem memory offset bytes index hright

/-- Environment fixed for one EVM call or creation execution. -/
structure ExecutionEnv where
  codeBytes : List Byte
  calldata : List Byte
  caller : AddressWord
  contractAddress : AddressWord
  callValue : Word

/-- Terminal reason of one execution. `fault` covers stack underflow, invalid
jumps, unsupported opcodes, and running past the code. -/
inductive Exit where
  | stopped
  | returned (data : List Byte)
  | reverted (data : List Byte)
  | fault
deriving DecidableEq

/-- Gas-free state of one execution. Stack head is the EVM top of stack. -/
structure ExecutionState where
  pc : Nat
  stack : List Word
  memory : Memory
  storage : TotalStorage
  logs : List (List Byte)
  exit : Option Exit

/-- Initial state of one call over supplied account storage. -/
def ExecutionState.initial (storage : TotalStorage) : ExecutionState where
  pc := 0
  stack := []
  memory := emptyMemory
  storage := storage
  logs := []
  exit := none

/-- Fetch an instruction only at an instruction boundary denoted by its byte
offset. Landing inside a push payload returns `none`. -/
def Assembly.fetch? : Assembly → Nat → Option Instruction
  | [], _ => none
  | instruction :: rest, offset =>
      if offset = 0 then some instruction
      else if offset < instruction.byteLength then none
      else Assembly.fetch? rest (offset - instruction.byteLength)

@[simp] theorem Assembly.fetch?_zero (instruction : Instruction)
    (rest : Assembly) :
    Assembly.fetch? (instruction :: rest) 0 = some instruction :=
  by simp [Assembly.fetch?]

/-- Skipping one leading instruction by its encoded byte length lands at the
same offset in the remaining assembly. -/
theorem Assembly.fetch?_add_byteLength (instruction : Instruction)
    (rest : Assembly) (offset : Nat) :
    Assembly.fetch? (instruction :: rest)
        (instruction.byteLength + offset) =
      Assembly.fetch? rest offset := by
  cases instruction <;>
    simp [Assembly.fetch?, Instruction.byteLength]

/-- Fetching after an arbitrary emitted prefix is exactly fetching from the
following suffix at offset zero. -/
theorem Assembly.fetch?_append_byteLength (pre suffix : Assembly) :
    Assembly.fetch? (pre ++ suffix) pre.byteLength =
      Assembly.fetch? suffix 0 := by
  induction pre with
  | nil => rfl
  | cons instruction rest ih =>
      change
        Assembly.fetch? (instruction :: (rest ++ suffix))
            (instruction.byteLength + Assembly.byteLength rest) = _
      calc
        _ = Assembly.fetch? (rest ++ suffix) (Assembly.byteLength rest) :=
          Assembly.fetch?_add_byteLength instruction (rest ++ suffix)
            (Assembly.byteLength rest)
        _ = Assembly.fetch? suffix 0 := ih

/-- A fragment begins at one byte offset inside a whole assembly program. -/
def Assembly.CodeAt (whole fragment : Assembly) (offset : Nat) : Prop :=
  ∃ pre suffix,
    whole = pre ++ fragment ++ suffix ∧ pre.byteLength = offset

/-- Every complete assembly is its own fragment at byte offset zero. -/
theorem Assembly.codeAt_self (program : Assembly) :
    program.CodeAt program 0 := by
  exact ⟨[], [], by simp, rfl⟩

/-- Successful symbolic resolution places an embedded straight-line fragment
at the byte offset of its symbolic prefix. -/
theorem LocalAssembly.resolveAt_codeAt
    {base : Nat} {program pre suffix : LocalAssembly}
    {fragment resolved : Assembly}
    (hprogram : program = pre ++ LocalAssembly.ofAssembly fragment ++ suffix)
    (hresolve : program.resolveAt base = some resolved) :
    Assembly.CodeAt resolved fragment pre.byteLength := by
  rcases LocalAssembly.resolveAt_decomposition hprogram hresolve with
    ⟨preCode, suffixCode, hresolved, hlength⟩
  exact ⟨preCode, suffixCode, hresolved, hlength⟩

/-- `CodeAt` makes fetching the fragment's first instruction exact. -/
theorem Assembly.fetch?_of_codeAt {whole rest : Assembly} {offset : Nat}
    {instruction : Instruction}
    (hcode : Assembly.CodeAt whole (instruction :: rest) offset) :
    whole.fetch? offset = some instruction := by
  rcases hcode with ⟨pre, suffix, rfl, hoffset⟩
  rw [← hoffset]
  rw [List.append_assoc]
  rw [Assembly.fetch?_append_byteLength]
  rfl

/-- Advancing by the first instruction's byte length preserves `CodeAt` for
the remaining fragment. -/
theorem Assembly.CodeAt.tail {whole rest : Assembly} {offset : Nat}
    {instruction : Instruction}
    (hcode : Assembly.CodeAt whole (instruction :: rest) offset) :
    Assembly.CodeAt whole rest (offset + instruction.byteLength) := by
  rcases hcode with ⟨pre, suffix, hwhole, hoffset⟩
  refine ⟨pre ++ [instruction], suffix, ?_, ?_⟩
  · simpa [List.append_assoc] using hwhole
  · rw [Assembly.byteLength_append, hoffset]
    simp [Assembly.byteLength, Instruction.byteLength]

/-- A leading subfragment starts at the same certified offset. -/
theorem Assembly.CodeAt.left {whole left right : Assembly} {offset : Nat}
    (hcode : Assembly.CodeAt whole (left ++ right) offset) :
    Assembly.CodeAt whole left offset := by
  rcases hcode with ⟨pre, suffix, hwhole, hoffset⟩
  refine ⟨pre, right ++ suffix, ?_, hoffset⟩
  simpa [List.append_assoc] using hwhole

/-- The trailing subfragment starts after the leading fragment's emitted byte
length. -/
theorem Assembly.CodeAt.right {whole left right : Assembly} {offset : Nat}
    (hcode : Assembly.CodeAt whole (left ++ right) offset) :
    Assembly.CodeAt whole right (offset + left.byteLength) := by
  rcases hcode with ⟨pre, suffix, hwhole, hoffset⟩
  refine ⟨pre ++ left, suffix, ?_, ?_⟩
  · simpa [List.append_assoc] using hwhole
  · rw [Assembly.byteLength_append, hoffset]

/-- Select a certified middle fragment and advance by the exact byte length
of its prefix. -/
theorem Assembly.CodeAt.middle {whole pre fragment suffix : Assembly}
    {offset : Nat}
    (hcode : Assembly.CodeAt whole (pre ++ fragment ++ suffix) offset) :
    Assembly.CodeAt whole fragment (offset + pre.byteLength) := by
  have htail : Assembly.CodeAt whole (fragment ++ suffix)
      (offset + pre.byteLength) := by
    apply Assembly.CodeAt.right
    simpa [List.append_assoc] using hcode
  exact htail.left

/-- The complete selector dispatcher is the leading fragment of a linked
classical runtime. -/
theorem classicalRuntime_dispatcher_codeAt (selectors : ClassicalSelectors)
    (handlers : ClassicalHandlers) :
    Assembly.CodeAt (classicalRuntimeAssembly selectors handlers)
      (classicalDispatcher selectors handlers) 0 := by
  refine ⟨[], handlers.block .player ++ handlers.block .reveal ++
    handlers.block .sampleRequest ++ handlers.block .oracleCallback, ?_, rfl⟩
  simp [classicalRuntimeAssembly, List.append_assoc]

/-- Each linked handler block begins at its statically computed public jump
destination. -/
theorem classicalRuntime_block_codeAt (selectors : ClassicalSelectors)
    (handlers : ClassicalHandlers) (entry : ClassicalEntry) :
    Assembly.CodeAt (classicalRuntimeAssembly selectors handlers)
      (handlers.block entry) (classicalEntryOffset handlers entry) := by
  cases entry with
  | player =>
      refine ⟨classicalDispatcher selectors handlers,
        handlers.block .reveal ++ handlers.block .sampleRequest ++
          handlers.block .oracleCallback, ?_, ?_⟩
      · simp [classicalRuntimeAssembly, List.append_assoc]
      · simp [classicalEntryOffset]
  | reveal =>
      refine ⟨classicalDispatcher selectors handlers ++ handlers.block .player,
        handlers.block .sampleRequest ++ handlers.block .oracleCallback,
        ?_, ?_⟩
      · simp [classicalRuntimeAssembly, List.append_assoc]
      · simp [Assembly.byteLength_append, classicalEntryOffset]
  | sampleRequest =>
      refine ⟨classicalDispatcher selectors handlers ++ handlers.block .player ++
          handlers.block .reveal,
        handlers.block .oracleCallback, ?_, ?_⟩
      · simp [classicalRuntimeAssembly, List.append_assoc]
      · simp [Assembly.byteLength_append, classicalEntryOffset]
        omega
  | oracleCallback =>
      refine ⟨classicalDispatcher selectors handlers ++ handlers.block .player ++
          handlers.block .reveal ++ handlers.block .sampleRequest,
        [], ?_, ?_⟩
      · simp [classicalRuntimeAssembly, List.append_assoc]
      · simp [Assembly.byteLength_append, classicalEntryOffset]
        omega

/-- The fixed dispatcher fragments occur at offsets 0, 6, 19, 32, and 45 in
every linked classical runtime. -/
theorem classicalRuntime_dispatchPrelude_codeAt
    (selectors : ClassicalSelectors) (handlers : ClassicalHandlers) :
    Assembly.CodeAt (classicalRuntimeAssembly selectors handlers)
      classicalDispatchPrelude 0 := by
  have h := classicalRuntime_dispatcher_codeAt selectors handlers
  have hdecomp : classicalDispatcher selectors handlers =
      classicalDispatchPrelude ++
        (classicalDispatchBranch selectors.player
          (classicalEntryOffset handlers .player) ++
        (classicalDispatchBranch selectors.reveal
          (classicalEntryOffset handlers .reveal) ++
        (classicalDispatchBranch selectors.sampleRequest
          (classicalEntryOffset handlers .sampleRequest) ++
        (classicalDispatchBranch selectors.oracleCallback
          (classicalEntryOffset handlers .oracleCallback) ++
          classicalDispatchFallback)))) := by
    simp [classicalDispatcher, List.append_assoc]
  rw [hdecomp] at h
  exact h.left

theorem classicalRuntime_dispatchBranch_codeAt
    (selectors : ClassicalSelectors) (handlers : ClassicalHandlers)
    (entry : ClassicalEntry) :
    Assembly.CodeAt (classicalRuntimeAssembly selectors handlers)
      (classicalDispatchBranch
        (selectors.get entry)
        (classicalEntryOffset handlers entry))
      (6 + 13 * entry.dispatchIndex) := by
  have h := classicalRuntime_dispatcher_codeAt selectors handlers
  have hdecomp : classicalDispatcher selectors handlers =
      classicalDispatchPrelude ++
        (classicalDispatchBranch selectors.player
          (classicalEntryOffset handlers .player) ++
        (classicalDispatchBranch selectors.reveal
          (classicalEntryOffset handlers .reveal) ++
        (classicalDispatchBranch selectors.sampleRequest
          (classicalEntryOffset handlers .sampleRequest) ++
        (classicalDispatchBranch selectors.oracleCallback
          (classicalEntryOffset handlers .oracleCallback) ++
          classicalDispatchFallback)))) := by
    simp [classicalDispatcher, List.append_assoc]
  rw [hdecomp] at h
  cases entry with
  | player => simpa using h.right.left
  | reveal => simpa using h.right.right.left
  | sampleRequest => simpa using h.right.right.right.left
  | oracleCallback => simpa using h.right.right.right.right.left

/-- Whether a byte destination is a valid `JUMPDEST`. -/
def Assembly.validJumpDest (program : Assembly) (destination : Nat) : Bool :=
  match program.fetch? destination with
  | some .jumpdest => true
  | _ => false

/-- Advance to the byte following an instruction. -/
def advance (state : ExecutionState) (instruction : Instruction)
    (stack : List Word := state.stack) : ExecutionState :=
  { state with
    pc := state.pc + instruction.byteLength
    stack := stack }

/-- Fault the current execution. -/
def fault (state : ExecutionState) : ExecutionState :=
  { state with exit := some .fault }

/-- Canonical Boolean EVM result word. -/
def boolWord (condition : Bool) : Word :=
  if condition then 1 else 0

/-- Execute one instruction at the current byte program counter. -/
def stepInstruction (program : Assembly) (env : ExecutionEnv)
    (instruction : Instruction) (state : ExecutionState) : ExecutionState :=
  match instruction with
  | .stop => { state with exit := some .stopped }
  | .push data => advance state instruction (data.value :: state.stack)
  | .pop =>
      match state.stack with
      | _ :: rest => advance state instruction rest
      | [] => fault state
  | .dup index =>
      match state.stack[index]? with
      | some value => advance state instruction (value :: state.stack)
      | none => fault state
  | .swap index =>
      let target := (index : Nat) + 1
      match state.stack, state.stack[target]? with
      | top :: _, some value =>
          let swapped := (state.stack.set target top).set 0 value
          advance state instruction swapped
      | _, _ => fault state
  | .add | .mul | .sub | .div | .mod | .lt | .gt | .eq | .and | .or |
      .xor | .shl | .shr =>
      match state.stack with
      | top :: next :: rest =>
          let result :=
            match instruction with
            | .add => next + top
            | .mul => next * top
            | .sub => top - next
            | .div => if next = 0 then 0 else top / next
            | .mod => if next = 0 then 0 else top % next
            | .lt => boolWord (top.toNat < next.toNat)
            | .gt => boolWord (top.toNat > next.toNat)
            | .eq => boolWord (next = top)
            | .and => next &&& top
            | .or => next ||| top
            | .xor => next ^^^ top
            | .shl => next <<< top.toNat
            | .shr => next >>> top.toNat
            | _ => 0
          advance state instruction (result :: rest)
      | _ => fault state
  | .iszero =>
      match state.stack with
      | value :: rest =>
          advance state instruction (boolWord (value = 0) :: rest)
      | [] => fault state
  | .not =>
      match state.stack with
      | value :: rest => advance state instruction (~~~value :: rest)
      | [] => fault state
  | .caller =>
      advance state instruction
        (BitVec.ofNat 256 env.caller.toNat :: state.stack)
  | .address =>
      advance state instruction
        (BitVec.ofNat 256 env.contractAddress.toNat :: state.stack)
  | .callvalue => advance state instruction (env.callValue :: state.stack)
  | .calldatasize =>
      advance state instruction
        (BitVec.ofNat 256 env.calldata.length :: state.stack)
  | .calldataload =>
      match state.stack with
      | offset :: rest =>
          advance state instruction
            (calldataLoad env.calldata offset.toNat :: rest)
      | [] => fault state
  | .mload =>
      match state.stack with
      | offset :: rest =>
          advance state instruction
            (bytesToWord (readMemory state.memory offset.toNat 32) :: rest)
      | [] => fault state
  | .mstore =>
      match state.stack with
      | offset :: value :: rest =>
          { advance state instruction rest with
            memory := writeBytes state.memory offset.toNat
              (PushData.word value).bytes }
      | _ => fault state
  | .sload =>
      match state.stack with
      | key :: rest =>
          advance state instruction (state.storage key.toNat :: rest)
      | [] => fault state
  | .sstore =>
      match state.stack with
      | key :: value :: rest =>
          { advance state instruction rest with
            storage := Function.update state.storage key.toNat value }
      | _ => fault state
  | .jump =>
      match state.stack with
      | destination :: rest =>
          if program.validJumpDest destination.toNat then
            { state with pc := destination.toNat, stack := rest }
          else
            fault state
      | [] => fault state
  | .jumpi =>
      match state.stack with
      | destination :: condition :: rest =>
          if condition = 0 then advance state instruction rest
          else if program.validJumpDest destination.toNat then
            { state with pc := destination.toNat, stack := rest }
          else
            fault state
      | _ => fault state
  | .pc =>
      advance state instruction (BitVec.ofNat 256 state.pc :: state.stack)
  | .jumpdest => advance state instruction
  | .log0 =>
      match state.stack with
      | offset :: size :: rest =>
          { advance state instruction rest with
            logs := state.logs ++
              [readMemory state.memory offset.toNat size.toNat] }
      | _ => fault state
  | .return =>
      match state.stack with
      | offset :: size :: rest =>
          { state with
            stack := rest
            exit := some (.returned
              (readMemory state.memory offset.toNat size.toNat)) }
      | _ => fault state
  | .revert =>
      match state.stack with
      | offset :: size :: rest =>
          { state with
            stack := rest
            exit := some (.reverted
              (readMemory state.memory offset.toNat size.toNat)) }
      | _ => fault state
  | .codecopy =>
      match state.stack with
      | destination :: source :: size :: rest =>
          { advance state instruction rest with
            memory := writeBytes state.memory destination.toNat
              (readBytes env.codeBytes source.toNat size.toNat) }
      | _ => fault state
  | .keccak256 | .invalid => fault state

/-- `SWAPn` exchanges the stack top with the item at natural depth `n`.
The instruction index is zero-based, so its target depth is one greater. -/
theorem stepInstruction_swap_exact (program : Assembly) (env : ExecutionEnv)
    (state : ExecutionState) (index : Fin 16) (top value : Word)
    (rest : List Word)
    (hvalue : (top :: rest)[(index : Nat) + 1]? = some value) :
    stepInstruction program env (.swap index)
        { state with stack := top :: rest } =
      advance { state with stack := top :: rest } (.swap index)
        (((top :: rest).set ((index : Nat) + 1) top).set 0 value) := by
  simp [stepInstruction, hvalue]

/-- `SWAP16` reaches the seventeenth stack item rather than wrapping its
`Fin 16` instruction index back to the top. -/
theorem stepInstruction_swap16_boundary (program : Assembly)
    (env : ExecutionEnv) (state : ExecutionState) :
    let stack := (List.range 17).map fun value => BitVec.ofNat 256 value
    let result := stepInstruction program env (.swap ⟨15, by decide⟩)
      { state with stack := stack }
    result.stack[0]? = some (BitVec.ofNat 256 16) ∧
      result.stack[16]? = some (BitVec.ofNat 256 0) := by
  constructor <;> rfl

/-- A `SWAP16` with only sixteen stack items faults at the exact underflow
boundary. -/
theorem stepInstruction_swap16_underflow (program : Assembly)
    (env : ExecutionEnv) (state : ExecutionState) :
    stepInstruction program env (.swap ⟨15, by decide⟩)
        { state with
          stack := (List.range 16).map fun value => BitVec.ofNat 256 value } =
      fault { state with
        stack := (List.range 16).map fun value => BitVec.ofNat 256 value } := by
  rfl

/-- Execute one fetched EVM instruction. Terminal states are stable. -/
def step (program : Assembly) (env : ExecutionEnv)
    (state : ExecutionState) : ExecutionState :=
  match state.exit with
  | some _ => state
  | none =>
      match program.fetch? state.pc with
      | none => fault state
      | some instruction => stepInstruction program env instruction state

/-- A running state at a certified code fragment executes that fragment's
first instruction. -/
theorem step_of_codeAt {program rest : Assembly} {env : ExecutionEnv}
    {state : ExecutionState} {instruction : Instruction}
    (hrunning : state.exit = none)
    (hcode : Assembly.CodeAt program (instruction :: rest) state.pc) :
    step program env state = stepInstruction program env instruction state := by
  simp [step, hrunning, Assembly.fetch?_of_codeAt hcode]

@[simp] theorem step_of_exit (program : Assembly) (env : ExecutionEnv)
    (state : ExecutionState) (exit : Exit) (hexit : state.exit = some exit) :
    step program env state = state := by
  simp [step, hexit]

/-- Fuel-bounded execution. Generated acyclic handlers have a structural
fuel bound; fuel is explicit here so arbitrary reified assembly remains total.
-/
def run : Nat → Assembly → ExecutionEnv → ExecutionState → ExecutionState
  | 0, _, _, state => state
  | fuel + 1, program, env, state =>
      match state.exit with
      | some _ => state
      | none => run fuel program env (step program env state)

@[simp] theorem run_of_exit (fuel : Nat) (program : Assembly)
    (env : ExecutionEnv) (state : ExecutionState) (exit : Exit)
    (hexit : state.exit = some exit) :
    run fuel program env state = state := by
  cases fuel <;> simp [run, hexit]

/-- Fuel composition: running two step budgets successively is the same as
running their sum. Terminal-state stability makes the law exact. -/
theorem run_add (first second : Nat) (program : Assembly)
    (env : ExecutionEnv) (state : ExecutionState) :
    run (first + second) program env state =
      run second program env (run first program env state) := by
  induction first generalizing state with
  | zero => simp [run]
  | succ first ih =>
      cases hexit : state.exit with
      | none =>
          rw [show Nat.succ first + second = (first + second) + 1 by omega]
          simp only [run, hexit]
          exact ih (step program env state)
      | some exit => simp [run, hexit, run_of_exit]

/-- Peel one certified instruction from a fuel-bounded execution. -/
theorem run_succ_of_codeAt {program rest : Assembly} {env : ExecutionEnv}
    {state : ExecutionState} {instruction : Instruction} (fuel : Nat)
    (hrunning : state.exit = none)
    (hcode : Assembly.CodeAt program (instruction :: rest) state.pc) :
    run (fuel + 1) program env state =
      run fuel program env
        (stepInstruction program env instruction state) := by
  simp [run, hrunning, step_of_codeAt hrunning hcode]

/-- A conditional jump with a true condition reaches a certified destination,
consuming the destination and condition words from the stack. -/
theorem run_guardedJump {program : Assembly} {env : ExecutionEnv}
    {state : ExecutionState} (destination : Nat) (restStack : List Word)
    (hrunning : state.exit = none)
    (hdestination : destination < 2 ^ 32)
    (hstack : state.stack =
      (PushData.nat32 destination).value :: 1 :: restStack)
    (hcode : Assembly.CodeAt program [.jumpi] state.pc)
    (htarget : Assembly.CodeAt program [.jumpdest] destination) :
    run 1 program env state =
      { state with pc := destination, stack := restStack } := by
  have hvalid : program.validJumpDest destination = true := by
    simp [Assembly.validJumpDest, Assembly.fetch?_of_codeAt htarget]
  have hdestinationValue :
      (PushData.nat32 destination).value.toNat = destination :=
    PushData.nat32_value_toNat_of_lt hdestination
  rw [run_succ_of_codeAt 0 hrunning hcode]
  simp only [run, stepInstruction, hstack]
  change
    (if program.validJumpDest
        (PushData.nat32 destination).value.toNat then
      { state with
        pc := (PushData.nat32 destination).value.toNat
        stack := restStack }
     else fault state) =
      { state with pc := destination, stack := restStack }
  simp only [hdestinationValue, hvalid, ite_true]

/-- A reified fragment executes sequentially without exiting or changing its
next byte address unexpectedly. This deliberately excludes taken jumps. -/
def StraightRun (program : Assembly) (env : ExecutionEnv) :
    Assembly → ExecutionState → ExecutionState → Prop
  | [], state, result => result = state
  | instruction :: rest, state, result =>
      state.exit = none ∧
      (stepInstruction program env instruction state).pc =
        state.pc + instruction.byteLength ∧
      StraightRun program env rest
        (stepInstruction program env instruction state) result

/-- A certified sequential fragment agrees with fuel-bounded execution for
exactly one step per instruction. -/
theorem StraightRun.run_eq {program fragment : Assembly} {env : ExecutionEnv}
    {state result : ExecutionState}
    (hstraight : StraightRun program env fragment state result)
    (hcode : Assembly.CodeAt program fragment state.pc) :
    run fragment.length program env state = result := by
  induction fragment generalizing state result with
  | nil =>
      change result = state at hstraight
      change state = result
      exact hstraight.symm
  | cons instruction rest ih =>
      rcases hstraight with ⟨hrunning, hpc, hrest⟩
      rw [List.length_cons, run_succ_of_codeAt rest.length hrunning hcode]
      apply ih hrest
      have htail := hcode.tail
      rw [← hpc] at htail
      exact htail

/-- A certified straight-line setup followed by a taken conditional jump runs
as one composed fragment. -/
theorem StraightRun.run_guardedJump {program setup : Assembly}
    {env : ExecutionEnv} {state beforeJump : ExecutionState}
    (hstraight : StraightRun program env setup state beforeJump)
    (destination : Nat) (restStack : List Word)
    (hsetup : Assembly.CodeAt program setup state.pc)
    (hrunning : beforeJump.exit = none)
    (hdestination : destination < 2 ^ 32)
    (hstack : beforeJump.stack =
      (PushData.nat32 destination).value :: 1 :: restStack)
    (hjump : Assembly.CodeAt program [.jumpi] beforeJump.pc)
    (htarget : Assembly.CodeAt program [.jumpdest] destination) :
    run (setup.length + 1) program env state =
      { beforeJump with pc := destination, stack := restStack } := by
  rw [run_add, hstraight.run_eq hsetup]
  exact Vegas.Machine.Contract.EVM.run_guardedJump destination restStack
    hrunning hdestination hstack hjump htarget

/-- The fixed dispatcher prefix extracts the high four calldata bytes and
retains their zero-extended selector word on the stack. -/
theorem run_classicalDispatchPrelude (whole : Assembly) (env : ExecutionEnv)
    (state : ExecutionState) (selector : Selector)
    (hrunning : state.exit = none)
    (hload : calldataLoad env.calldata 0 >>> 224 =
      ClassicalABI.selectorWord selector)
    (hcode : Assembly.CodeAt whole classicalDispatchPrelude state.pc) :
    run 4 whole env state =
      { state with
        pc := state.pc + 6
        stack := ClassicalABI.selectorWord selector :: state.stack } := by
  have hload' : calldataLoad env.calldata 0 >>> 224 =
      BitVec.setWidth 256 selector := by
    simpa [ClassicalABI.selectorWord] using hload
  have hbyte224 : (byte 224).toNat = 224 := by
    norm_num [byte]
  apply StraightRun.run_eq ?_ hcode
  simp [classicalDispatchPrelude, StraightRun, stepInstruction, advance,
    hrunning, hload', hbyte224, ClassicalABI.selectorWord,
    Instruction.byteLength]

/-- A nonmatching selector branch falls through while retaining the original
selector word for subsequent comparisons. -/
theorem run_classicalDispatchBranch_miss (whole : Assembly)
    (env : ExecutionEnv) (state : ExecutionState)
    (actual expected : Selector) (destination : Nat)
    (hrunning : state.exit = none) (hstack : state.stack =
      ClassicalABI.selectorWord actual :: [])
    (hne : actual ≠ expected)
    (hcode : Assembly.CodeAt whole
      (classicalDispatchBranch expected destination) state.pc) :
    run 5 whole env state =
      { state with pc := state.pc + 13 } := by
  have hword : ClassicalABI.selectorWord actual ≠
      ClassicalABI.selectorWord expected := by
    intro heq
    apply hne
    have heq' := congrArg (BitVec.setWidth 32) heq
    simpa [ClassicalABI.selectorWord] using heq'
  have hsetWidth : BitVec.setWidth 256 actual ≠
      BitVec.setWidth 256 expected := by
    simpa [ClassicalABI.selectorWord] using hword
  apply StraightRun.run_eq ?_ hcode
  simp [StraightRun, classicalDispatchBranch, stepInstruction, advance,
    hrunning, hstack, hsetWidth, boolWord, ClassicalABI.selectorWord,
    Instruction.byteLength]

/-- A matching selector branch jumps to its certified handler destination and
retains the selector word for the handler block prefix. -/
theorem run_classicalDispatchBranch_hit (whole : Assembly)
    (env : ExecutionEnv) (state : ExecutionState)
    (selector : Selector) (destination : Nat)
    (hrunning : state.exit = none) (hstack : state.stack =
      ClassicalABI.selectorWord selector :: [])
    (hdestination : destination < 2 ^ 32)
    (hcode : Assembly.CodeAt whole
      (classicalDispatchBranch selector destination) state.pc)
    (htarget : Assembly.CodeAt whole [.jumpdest] destination) :
    run 5 whole env state =
      { state with pc := destination } := by
  let setup : Assembly :=
    [ .dup ⟨0, by decide⟩,
      .push (.selector selector),
      .eq,
      .push (.nat32 destination) ]
  let beforeJump : ExecutionState :=
    { state with
      pc := state.pc + setup.byteLength
      stack := (PushData.nat32 destination).value :: 1 ::
        ClassicalABI.selectorWord selector :: [] }
  have hdecomp : classicalDispatchBranch selector destination =
      setup ++ [.jumpi] := by rfl
  rw [hdecomp] at hcode
  have hsetup : Assembly.CodeAt whole setup state.pc := hcode.left
  have hjump : Assembly.CodeAt whole [.jumpi]
      (state.pc + setup.byteLength) := hcode.right
  have hstraight : StraightRun whole env setup state beforeJump := by
    simp [StraightRun, setup, beforeJump, stepInstruction, advance,
      hrunning, hstack, boolWord, ClassicalABI.selectorWord,
      Assembly.byteLength, Instruction.byteLength]
  have hbeforeRunning : beforeJump.exit = none := by
    simp [beforeJump, hrunning]
  have hjump' : Assembly.CodeAt whole [.jumpi] beforeJump.pc := by
    simpa [beforeJump] using hjump
  rw [show 5 = setup.length + 1 by simp [setup]]
  simpa [beforeJump, hstack] using
    hstraight.run_guardedJump destination
      [ClassicalABI.selectorWord selector] hsetup hbeforeRunning hdestination
      (by simp [beforeJump]) hjump' htarget

/-- The linked `JUMPDEST; POP` block prefix restores the empty handler stack
and enters the handler body two bytes after its public destination. -/
theorem run_classicalHandlerPrefix (whole : Assembly) (env : ExecutionEnv)
    (state : ExecutionState) (selector : Selector)
    (handler : Assembly) (hrunning : state.exit = none)
    (hstack : state.stack = ClassicalABI.selectorWord selector :: [])
    (hcode : Assembly.CodeAt whole
      ([.jumpdest, .pop] ++ handler) state.pc) :
    run 2 whole env state =
      { state with pc := state.pc + 2, stack := [] } := by
  apply StraightRun.run_eq ?_ hcode.left
  simp [StraightRun, stepInstruction, advance, hrunning, hstack,
    Instruction.byteLength]

namespace RuntimeImage

variable {selectors : ClassicalSelectors}

/-- Any straight-line fragment embedded in a local handler remains at the
statically computed byte offset in the final checked-and-linked runtime. -/
theorem linkLocalChecked?_fragment_codeAt
    (sourceHandlers : LocalClassicalHandlers) (image : RuntimeImage selectors)
    (hlink : linkLocalChecked? selectors sourceHandlers = some image)
    (entry : ClassicalEntry) (pre suffix : LocalAssembly)
    (fragment : Assembly)
    (hsource : sourceHandlers.get entry =
      pre ++ LocalAssembly.ofAssembly fragment ++ suffix) :
    Assembly.CodeAt image.assembly fragment
      (sourceHandlers.entryOffset entry + 2 + pre.byteLength) := by
  let resolved := image.handlers.handlers
  have hresolve : sourceHandlers.resolve? = some resolved :=
    linkLocalChecked?_handlers_resolve hlink
  have hget : (sourceHandlers.get entry).resolveAt
      (sourceHandlers.entryOffset entry + 2) = some (resolved.get entry) :=
    LocalClassicalHandlers.resolve?_get hresolve entry
  rcases LocalAssembly.resolveAt_decomposition hsource hget with
    ⟨preCode, suffixCode, hresolved, hlength⟩
  have hblock : Assembly.CodeAt image.assembly (resolved.block entry)
      (classicalEntryOffset resolved entry) := by
    simpa [RuntimeImage.assembly, resolved] using
      classicalRuntime_block_codeAt selectors resolved entry
  have hblock' : Assembly.CodeAt image.assembly
      ([.jumpdest, .pop] ++ resolved.get entry)
      (classicalEntryOffset resolved entry) := by
    simpa [ClassicalHandlers.block] using hblock
  have hhandler : Assembly.CodeAt image.assembly (resolved.get entry)
      (classicalEntryOffset resolved entry + 2) := by
    have := hblock'.right
    simpa [Assembly.byteLength, Instruction.byteLength] using this
  rw [hresolved] at hhandler
  have hfragment := hhandler.middle
  have hentry := LocalClassicalHandlers.resolve?_entryOffset hresolve entry
  simpa [hentry, hlength, Nat.add_assoc] using hfragment

/-- The same linked-code bridge for a symbolic fragment containing local
labels or jumps, given its independently resolved instruction sequence. -/
theorem linkLocalChecked?_resolvedFragment_codeAt
    (sourceHandlers : LocalClassicalHandlers) (image : RuntimeImage selectors)
    (hlink : linkLocalChecked? selectors sourceHandlers = some image)
    (entry : ClassicalEntry) (pre fragment suffix : LocalAssembly)
    (fragmentCode : Assembly)
    (hsource : sourceHandlers.get entry = pre ++ fragment ++ suffix)
    (hfragment : LocalAssembly.resolveFrom?
      (sourceHandlers.get entry) (sourceHandlers.entryOffset entry + 2)
      fragment = some fragmentCode) :
    Assembly.CodeAt image.assembly fragmentCode
      (sourceHandlers.entryOffset entry + 2 + pre.byteLength) := by
  let resolved := image.handlers.handlers
  have hresolve : sourceHandlers.resolve? = some resolved :=
    linkLocalChecked?_handlers_resolve hlink
  have hget : (sourceHandlers.get entry).resolveAt
      (sourceHandlers.entryOffset entry + 2) = some (resolved.get entry) :=
    LocalClassicalHandlers.resolve?_get hresolve entry
  rcases LocalAssembly.resolveAt_resolved_decomposition hsource hfragment
      hget with ⟨preCode, suffixCode, hresolved, hlength⟩
  have hblock : Assembly.CodeAt image.assembly (resolved.block entry)
      (classicalEntryOffset resolved entry) := by
    simpa [RuntimeImage.assembly, resolved] using
      classicalRuntime_block_codeAt selectors resolved entry
  have hblock' : Assembly.CodeAt image.assembly
      ([.jumpdest, .pop] ++ resolved.get entry)
      (classicalEntryOffset resolved entry) := by
    simpa [ClassicalHandlers.block] using hblock
  have hhandler : Assembly.CodeAt image.assembly (resolved.get entry)
      (classicalEntryOffset resolved entry + 2) := by
    have := hblock'.right
    simpa [Assembly.byteLength, Instruction.byteLength] using this
  rw [hresolved] at hhandler
  have hselected := hhandler.middle
  have hentry := LocalClassicalHandlers.resolve?_entryOffset hresolve entry
  simpa [hentry, hlength, Nat.add_assoc] using hselected

/-- Every resolved local label is an actual `JUMPDEST` at the absolute address
used by jumps targeting that label. -/
theorem linkLocalChecked?_label_codeAt
    (sourceHandlers : LocalClassicalHandlers) (image : RuntimeImage selectors)
    (hlink : linkLocalChecked? selectors sourceHandlers = some image)
    (entry : ClassicalEntry) (target offset : Nat)
    (hlabel : (sourceHandlers.get entry).labelOffset? target = some offset) :
    Assembly.CodeAt image.assembly [.jumpdest]
      (sourceHandlers.entryOffset entry + 2 + offset) := by
  rcases LocalAssembly.labelOffset?_eq_some
      (sourceHandlers.get entry) target offset hlabel with
    ⟨pre, suffix, hsource, hlength⟩
  have hfragment : LocalAssembly.resolveFrom?
      (sourceHandlers.get entry) (sourceHandlers.entryOffset entry + 2)
      [LocalItem.label target] = some [.jumpdest] := by
    rfl
  have hcode := linkLocalChecked?_resolvedFragment_codeAt sourceHandlers image
    hlink entry pre [LocalItem.label target] suffix [.jumpdest]
    hsource hfragment
  simpa [hlength] using hcode

/-- From the selected comparison branch, a matching selector enters that
handler body after the taken jump and `JUMPDEST; POP` prefix. -/
theorem run_enter_from_branch (image : RuntimeImage selectors)
    (entry : ClassicalEntry) (env : ExecutionEnv) (state : ExecutionState)
    (hrunning : state.exit = none)
    (hpc : state.pc = 6 + 13 * entry.dispatchIndex)
    (hstack : state.stack =
      ClassicalABI.selectorWord (selectors.get entry) :: []) :
    run 7 image.assembly env state =
      { state with
        pc := classicalEntryOffset image.handlers.handlers entry + 2
        stack := [] } := by
  let handlers := image.handlers.handlers
  let destination := classicalEntryOffset handlers entry
  let afterBranch : ExecutionState :=
    { state with
      pc := destination
      stack := ClassicalABI.selectorWord (selectors.get entry) :: [] }
  have hbranchCode : Assembly.CodeAt image.assembly
      (classicalDispatchBranch (selectors.get entry) destination) state.pc := by
    have hcode := classicalRuntime_dispatchBranch_codeAt selectors handlers entry
    simpa [RuntimeImage.assembly, hpc, destination] using hcode
  have hblock : Assembly.CodeAt image.assembly
      (handlers.block entry) destination := by
    simpa [RuntimeImage.assembly, destination] using
      classicalRuntime_block_codeAt selectors handlers entry
  have hblock' : Assembly.CodeAt image.assembly
      ([.jumpdest] ++ ([.pop] ++ handlers.get entry)) destination := by
    simpa [ClassicalHandlers.block, List.append_assoc] using hblock
  have htarget : Assembly.CodeAt image.assembly [.jumpdest] destination :=
    hblock'.left
  have hrunBranch : run 5 image.assembly env state = afterBranch := by
    have hrun := run_classicalDispatchBranch_hit image.assembly env state
      (selectors.get entry) destination hrunning hstack
      (image.handlers.entryOffset_fits entry) hbranchCode htarget
    simpa [afterBranch, hstack] using hrun
  have hprefixCode : Assembly.CodeAt image.assembly
      ([.jumpdest, .pop] ++ handlers.get entry) afterBranch.pc := by
    simpa [afterBranch, List.append_assoc] using hblock'
  have hrunPrefix : run 2 image.assembly env afterBranch =
      { afterBranch with pc := afterBranch.pc + 2, stack := [] } := by
    apply run_classicalHandlerPrefix image.assembly env afterBranch
      (selectors.get entry) (handlers.get entry)
    · simp [afterBranch, hrunning]
    · simp [afterBranch]
    · exact hprefixCode
  rw [show 7 = 5 + 2 by omega, run_add, hrunBranch, hrunPrefix]

/-- A player selector enters the linked player-handler body with an empty
stack after exactly the dispatcher path and block prefix. -/
theorem run_enter_player (image : RuntimeImage selectors)
    (env : ExecutionEnv) (state : ExecutionState)
    (hrunning : state.exit = none) (hpc : state.pc = 0)
    (hstack : state.stack = [])
    (hselector : calldataLoad env.calldata 0 >>> 224 =
      ClassicalABI.selectorWord selectors.player) :
    run 11 image.assembly env state =
      { state with
        pc := classicalEntryOffset image.handlers.handlers .player + 2
        stack := [] } := by
  let handlers := image.handlers.handlers
  let destination := classicalEntryOffset handlers .player
  let afterPrelude : ExecutionState :=
    { state with
      pc := 6
      stack := ClassicalABI.selectorWord selectors.player :: [] }
  let afterBranch : ExecutionState :=
    { state with
      pc := destination
      stack := ClassicalABI.selectorWord selectors.player :: [] }
  have hpreludeCode : Assembly.CodeAt image.assembly
      classicalDispatchPrelude state.pc := by
    simpa [RuntimeImage.assembly, hpc] using
      classicalRuntime_dispatchPrelude_codeAt selectors handlers
  have hrunPrelude : run 4 image.assembly env state = afterPrelude := by
    have hrun := run_classicalDispatchPrelude image.assembly env state
      selectors.player hrunning hselector hpreludeCode
    simpa [afterPrelude, hpc, hstack] using hrun
  have hbranchCode : Assembly.CodeAt image.assembly
      (classicalDispatchBranch selectors.player destination)
      afterPrelude.pc := by
    have hcode := classicalRuntime_dispatchBranch_codeAt selectors handlers
      .player
    simpa [RuntimeImage.assembly, afterPrelude, destination] using hcode
  have hblock : Assembly.CodeAt image.assembly
      (handlers.block .player) destination := by
    simpa [RuntimeImage.assembly, destination] using
      classicalRuntime_block_codeAt selectors handlers .player
  have htarget : Assembly.CodeAt image.assembly [.jumpdest] destination := by
    have hblock' : Assembly.CodeAt image.assembly
        ([.jumpdest] ++ ([.pop] ++ handlers.player)) destination := by
      simpa [ClassicalHandlers.block, ClassicalHandlers.get,
        List.append_assoc] using hblock
    exact hblock'.left
  have hrunBranch : run 5 image.assembly env afterPrelude = afterBranch := by
    have hrun := run_classicalDispatchBranch_hit image.assembly env
      afterPrelude selectors.player destination (by
        simp [afterPrelude, hrunning]) (by simp [afterPrelude])
      (image.handlers.entryOffset_fits .player) hbranchCode htarget
    simpa [afterBranch] using hrun
  have hprefixCode : Assembly.CodeAt image.assembly
      ([.jumpdest, .pop] ++ handlers.player) afterBranch.pc := by
    simpa [ClassicalHandlers.block, ClassicalHandlers.get, afterBranch] using
      hblock
  have hrunPrefix : run 2 image.assembly env afterBranch =
      { afterBranch with pc := afterBranch.pc + 2, stack := [] } := by
    apply run_classicalHandlerPrefix image.assembly env afterBranch
      selectors.player handlers.player
    · simp [afterBranch, hrunning]
    · simp [afterBranch]
    · exact hprefixCode
  rw [show 11 = 4 + (5 + 2) by omega, run_add, hrunPrelude,
    run_add, hrunBranch, hrunPrefix]

/-- A reveal selector passes the player comparison and enters the linked
reveal-handler body with an empty stack. -/
theorem run_enter_reveal (image : RuntimeImage selectors)
    (env : ExecutionEnv) (state : ExecutionState)
    (hrunning : state.exit = none) (hpc : state.pc = 0)
    (hstack : state.stack = [])
    (hselector : calldataLoad env.calldata 0 >>> 224 =
      ClassicalABI.selectorWord selectors.reveal) :
    run 16 image.assembly env state =
      { state with
        pc := classicalEntryOffset image.handlers.handlers .reveal + 2
        stack := [] } := by
  let handlers := image.handlers.handlers
  let afterPrelude : ExecutionState :=
    { state with
      pc := 6
      stack := ClassicalABI.selectorWord selectors.reveal :: [] }
  let afterPlayer : ExecutionState :=
    { state with
      pc := 19
      stack := ClassicalABI.selectorWord selectors.reveal :: [] }
  have hpreludeCode : Assembly.CodeAt image.assembly
      classicalDispatchPrelude state.pc := by
    simpa [RuntimeImage.assembly, hpc] using
      classicalRuntime_dispatchPrelude_codeAt selectors handlers
  have hrunPrelude : run 4 image.assembly env state = afterPrelude := by
    have hrun := run_classicalDispatchPrelude image.assembly env state
      selectors.reveal hrunning hselector hpreludeCode
    simpa [afterPrelude, hpc, hstack] using hrun
  have hplayerCode : Assembly.CodeAt image.assembly
      (classicalDispatchBranch selectors.player
        (classicalEntryOffset handlers .player)) afterPrelude.pc := by
    have hcode := classicalRuntime_dispatchBranch_codeAt selectors handlers
      .player
    simpa [RuntimeImage.assembly, afterPrelude] using hcode
  have hrunPlayer : run 5 image.assembly env afterPrelude = afterPlayer := by
    have hrun := run_classicalDispatchBranch_miss image.assembly env
      afterPrelude selectors.reveal selectors.player
      (classicalEntryOffset handlers .player)
      (by simp [afterPrelude, hrunning]) (by simp [afterPrelude])
      (Ne.symm selectors.player_ne_reveal) hplayerCode
    simpa [afterPlayer] using hrun
  have hrunSelected : run 7 image.assembly env afterPlayer =
      { afterPlayer with
        pc := classicalEntryOffset handlers .reveal + 2
        stack := [] } := by
    apply run_enter_from_branch image .reveal env afterPlayer
    · simp [afterPlayer, hrunning]
    · simp [afterPlayer]
    · simp [afterPlayer]
  rw [show 16 = 4 + (5 + 7) by omega, run_add, hrunPrelude,
    run_add, hrunPlayer, hrunSelected]

/-- A sample-request selector passes both preceding comparisons and enters
the linked request-handler body with an empty stack. -/
theorem run_enter_sampleRequest (image : RuntimeImage selectors)
    (env : ExecutionEnv) (state : ExecutionState)
    (hrunning : state.exit = none) (hpc : state.pc = 0)
    (hstack : state.stack = [])
    (hselector : calldataLoad env.calldata 0 >>> 224 =
      ClassicalABI.selectorWord selectors.sampleRequest) :
    run 21 image.assembly env state =
      { state with
        pc := classicalEntryOffset image.handlers.handlers .sampleRequest + 2
        stack := [] } := by
  let handlers := image.handlers.handlers
  let afterPrelude : ExecutionState :=
    { state with
      pc := 6
      stack := ClassicalABI.selectorWord selectors.sampleRequest :: [] }
  let afterPlayer : ExecutionState :=
    { state with
      pc := 19
      stack := ClassicalABI.selectorWord selectors.sampleRequest :: [] }
  let afterReveal : ExecutionState :=
    { state with
      pc := 32
      stack := ClassicalABI.selectorWord selectors.sampleRequest :: [] }
  have hpreludeCode : Assembly.CodeAt image.assembly
      classicalDispatchPrelude state.pc := by
    simpa [RuntimeImage.assembly, hpc] using
      classicalRuntime_dispatchPrelude_codeAt selectors handlers
  have hrunPrelude : run 4 image.assembly env state = afterPrelude := by
    have hrun := run_classicalDispatchPrelude image.assembly env state
      selectors.sampleRequest hrunning hselector hpreludeCode
    simpa [afterPrelude, hpc, hstack] using hrun
  have hplayerCode : Assembly.CodeAt image.assembly
      (classicalDispatchBranch selectors.player
        (classicalEntryOffset handlers .player)) afterPrelude.pc := by
    have hcode := classicalRuntime_dispatchBranch_codeAt selectors handlers
      .player
    simpa [RuntimeImage.assembly, afterPrelude] using hcode
  have hrunPlayer : run 5 image.assembly env afterPrelude = afterPlayer := by
    have hrun := run_classicalDispatchBranch_miss image.assembly env
      afterPrelude selectors.sampleRequest selectors.player
      (classicalEntryOffset handlers .player)
      (by simp [afterPrelude, hrunning]) (by simp [afterPrelude])
      (Ne.symm selectors.player_ne_sampleRequest) hplayerCode
    simpa [afterPlayer] using hrun
  have hrevealCode : Assembly.CodeAt image.assembly
      (classicalDispatchBranch selectors.reveal
        (classicalEntryOffset handlers .reveal)) afterPlayer.pc := by
    have hcode := classicalRuntime_dispatchBranch_codeAt selectors handlers
      .reveal
    simpa [RuntimeImage.assembly, afterPlayer] using hcode
  have hrunReveal : run 5 image.assembly env afterPlayer = afterReveal := by
    have hrun := run_classicalDispatchBranch_miss image.assembly env
      afterPlayer selectors.sampleRequest selectors.reveal
      (classicalEntryOffset handlers .reveal)
      (by simp [afterPlayer, hrunning]) (by simp [afterPlayer])
      (Ne.symm selectors.reveal_ne_sampleRequest) hrevealCode
    simpa [afterReveal] using hrun
  have hrunSelected : run 7 image.assembly env afterReveal =
      { afterReveal with
        pc := classicalEntryOffset handlers .sampleRequest + 2
        stack := [] } := by
    apply run_enter_from_branch image .sampleRequest env afterReveal
    · simp [afterReveal, hrunning]
    · simp [afterReveal]
    · simp [afterReveal]
  rw [show 21 = 4 + (5 + (5 + 7)) by omega, run_add, hrunPrelude,
    run_add, hrunPlayer, run_add, hrunReveal, hrunSelected]

/-- An oracle-callback selector passes all preceding comparisons and enters
the linked callback-handler body with an empty stack. -/
theorem run_enter_oracleCallback (image : RuntimeImage selectors)
    (env : ExecutionEnv) (state : ExecutionState)
    (hrunning : state.exit = none) (hpc : state.pc = 0)
    (hstack : state.stack = [])
    (hselector : calldataLoad env.calldata 0 >>> 224 =
      ClassicalABI.selectorWord selectors.oracleCallback) :
    run 26 image.assembly env state =
      { state with
        pc := classicalEntryOffset image.handlers.handlers .oracleCallback + 2
        stack := [] } := by
  let handlers := image.handlers.handlers
  let afterPrelude : ExecutionState :=
    { state with
      pc := 6
      stack := ClassicalABI.selectorWord selectors.oracleCallback :: [] }
  let afterPlayer : ExecutionState :=
    { state with
      pc := 19
      stack := ClassicalABI.selectorWord selectors.oracleCallback :: [] }
  let afterReveal : ExecutionState :=
    { state with
      pc := 32
      stack := ClassicalABI.selectorWord selectors.oracleCallback :: [] }
  let afterSampleRequest : ExecutionState :=
    { state with
      pc := 45
      stack := ClassicalABI.selectorWord selectors.oracleCallback :: [] }
  have hpreludeCode : Assembly.CodeAt image.assembly
      classicalDispatchPrelude state.pc := by
    simpa [RuntimeImage.assembly, hpc] using
      classicalRuntime_dispatchPrelude_codeAt selectors handlers
  have hrunPrelude : run 4 image.assembly env state = afterPrelude := by
    have hrun := run_classicalDispatchPrelude image.assembly env state
      selectors.oracleCallback hrunning hselector hpreludeCode
    simpa [afterPrelude, hpc, hstack] using hrun
  have hplayerCode : Assembly.CodeAt image.assembly
      (classicalDispatchBranch selectors.player
        (classicalEntryOffset handlers .player)) afterPrelude.pc := by
    have hcode := classicalRuntime_dispatchBranch_codeAt selectors handlers
      .player
    simpa [RuntimeImage.assembly, afterPrelude] using hcode
  have hrunPlayer : run 5 image.assembly env afterPrelude = afterPlayer := by
    have hrun := run_classicalDispatchBranch_miss image.assembly env
      afterPrelude selectors.oracleCallback selectors.player
      (classicalEntryOffset handlers .player)
      (by simp [afterPrelude, hrunning]) (by simp [afterPrelude])
      (Ne.symm selectors.player_ne_oracleCallback) hplayerCode
    simpa [afterPlayer] using hrun
  have hrevealCode : Assembly.CodeAt image.assembly
      (classicalDispatchBranch selectors.reveal
        (classicalEntryOffset handlers .reveal)) afterPlayer.pc := by
    have hcode := classicalRuntime_dispatchBranch_codeAt selectors handlers
      .reveal
    simpa [RuntimeImage.assembly, afterPlayer] using hcode
  have hrunReveal : run 5 image.assembly env afterPlayer = afterReveal := by
    have hrun := run_classicalDispatchBranch_miss image.assembly env
      afterPlayer selectors.oracleCallback selectors.reveal
      (classicalEntryOffset handlers .reveal)
      (by simp [afterPlayer, hrunning]) (by simp [afterPlayer])
      (Ne.symm selectors.reveal_ne_oracleCallback) hrevealCode
    simpa [afterReveal] using hrun
  have hsampleCode : Assembly.CodeAt image.assembly
      (classicalDispatchBranch selectors.sampleRequest
        (classicalEntryOffset handlers .sampleRequest)) afterReveal.pc := by
    have hcode := classicalRuntime_dispatchBranch_codeAt selectors handlers
      .sampleRequest
    simpa [RuntimeImage.assembly, afterReveal] using hcode
  have hrunSample : run 5 image.assembly env afterReveal =
      afterSampleRequest := by
    have hrun := run_classicalDispatchBranch_miss image.assembly env
      afterReveal selectors.oracleCallback selectors.sampleRequest
      (classicalEntryOffset handlers .sampleRequest)
      (by simp [afterReveal, hrunning]) (by simp [afterReveal])
      (Ne.symm selectors.sampleRequest_ne_oracleCallback) hsampleCode
    simpa [afterSampleRequest] using hrun
  have hrunSelected : run 7 image.assembly env afterSampleRequest =
      { afterSampleRequest with
        pc := classicalEntryOffset handlers .oracleCallback + 2
        stack := [] } := by
    apply run_enter_from_branch image .oracleCallback env afterSampleRequest
    · simp [afterSampleRequest, hrunning]
    · simp [afterSampleRequest]
    · simp [afterSampleRequest]
  rw [show 26 = 4 + (5 + (5 + (5 + 7))) by omega,
    run_add, hrunPrelude, run_add, hrunPlayer, run_add, hrunReveal,
    run_add, hrunSample, hrunSelected]

end RuntimeImage

/-- The two-instruction pattern used for an event's result write stores the
existing stack top at the pushed key and otherwise falls through. -/
theorem run_push_sstore (program : Assembly) (env : ExecutionEnv)
    (state : ExecutionState) (key : PushData) (value : Word)
    (rest : List Word)
    (hrunning : state.exit = none)
    (hstack : state.stack = value :: rest)
    (hcode : Assembly.CodeAt program [.push key, .sstore] state.pc) :
    run 2 program env state =
      { state with
        pc := state.pc + (.push key : Instruction).byteLength + 1
        stack := rest
        storage := Function.update state.storage key.value.toNat value } := by
  let pushed : ExecutionState :=
    advance state (.push key) (key.value :: value :: rest)
  have hpush : step program env state = pushed := by
    rw [step_of_codeAt hrunning hcode]
    simp [stepInstruction, pushed, hstack]
  have htail := hcode.tail
  have htail' :
      Assembly.CodeAt program [.sstore] pushed.pc := by
    simpa [pushed, advance] using htail
  let stored : ExecutionState :=
    { pushed with
      pc := pushed.pc + 1
      stack := rest
      storage := Function.update state.storage key.value.toNat value }
  have hpushedRunning : pushed.exit = none := by
    simp [pushed, advance, hrunning]
  have hstore : step program env pushed = stored := by
    rw [step_of_codeAt hpushedRunning htail']
    simp [stepInstruction, stored, pushed, advance,
      Instruction.byteLength]
  have hrunPush : run 1 program env state = pushed := by
    simp [run, hrunning, hpush]
  have hrunStore : run 1 program env pushed = stored := by
    simp [run, hpushedRunning, hstore]
  rw [show 2 = 1 + 1 by omega, run_add]
  rw [hrunPush, hrunStore]
  simp [stored, pushed, advance, Instruction.byteLength]

/-- The three-instruction constant-write pattern used for administrative bits
stores the pushed value and preserves the prior stack. -/
theorem run_push_push_sstore (program : Assembly) (env : ExecutionEnv)
    (state : ExecutionState) (value key : PushData)
    (hrunning : state.exit = none)
    (hcode : Assembly.CodeAt program
      [.push value, .push key, .sstore] state.pc) :
    run 3 program env state =
      { state with
        pc := state.pc + (.push value : Instruction).byteLength +
          (.push key : Instruction).byteLength + 1
        storage := Function.update state.storage key.value.toNat value.value } := by
  let pushed : ExecutionState :=
    advance state (.push value) (value.value :: state.stack)
  have hpush : step program env state = pushed := by
    rw [step_of_codeAt hrunning hcode]
    simp [stepInstruction, pushed]
  have htail := hcode.tail
  have htail' :
      Assembly.CodeAt program [.push key, .sstore] pushed.pc := by
    simpa [pushed, advance] using htail
  have hpushedRunning : pushed.exit = none := by
    simp [pushed, advance, hrunning]
  have hrunPush : run 1 program env state = pushed := by
    simp [run, hrunning, hpush]
  have hrunStore :=
    run_push_sstore program env pushed key value.value state.stack
      hpushedRunning rfl htail'
  rw [show 3 = 1 + 2 by omega, run_add, hrunPush, hrunStore]
  simp [pushed, advance, Instruction.byteLength]

/-- Constructor storage-write generation executes its ordered finite storage
transformer exactly. -/
theorem run_compileStorageWrites (slots : List Nat) (target : TotalStorage)
    (program : Assembly) (env : ExecutionEnv) (state : ExecutionState)
    (hrunning : state.exit = none)
    (hslots : ∀ slot ∈ slots, slot < 2 ^ 256)
    (hcode : Assembly.CodeAt program
      (compileStorageWrites slots target) state.pc) :
    run (compileStorageWrites slots target).length program env state =
      { state with
        pc := state.pc + (compileStorageWrites slots target).byteLength
        storage := applyStorageWrites slots target state.storage } := by
  induction slots generalizing state with
  | nil =>
      cases state
      simp [compileStorageWrites, applyStorageWrites, run,
        Assembly.byteLength]
  | cons slot rest ih =>
      by_cases hzero : target slot = 0
      · have hcompileZero :
            compileStorageWrites (slot :: rest) target =
              compileStorageWrites rest target := by
          simp only [compileStorageWrites, List.flatMap_cons]
          rw [if_pos hzero]
          rfl
        have happlyZero :
            applyStorageWrites (slot :: rest) target state.storage =
              applyStorageWrites rest target state.storage := by
          simp only [applyStorageWrites]
          rw [if_pos hzero]
        rw [hcompileZero, happlyZero]
        apply ih state hrunning
        · intro key hkey
          exact hslots key (by simp [hkey])
        · simpa [hcompileZero] using hcode
      · let head : Assembly :=
          [ .push (.word (target slot)), .push (.nat256 slot), .sstore ]
        let tail := compileStorageWrites rest target
        have hdecomp : compileStorageWrites (slot :: rest) target =
            head ++ tail := by
          simp only [compileStorageWrites, List.flatMap_cons]
          rw [if_neg hzero]
          rfl
        have happly :
            applyStorageWrites (slot :: rest) target state.storage =
              applyStorageWrites rest target
                (Function.update state.storage slot (target slot)) := by
          simp only [applyStorageWrites]
          rw [if_neg hzero]
        rw [hdecomp] at hcode ⊢
        have hhead : Assembly.CodeAt program head state.pc := hcode.left
        have htail : Assembly.CodeAt program tail
            (state.pc + head.byteLength) := hcode.right
        let after : ExecutionState :=
          { state with
            pc := state.pc + head.byteLength
            storage := Function.update state.storage slot (target slot) }
        have hslot : slot < 2 ^ 256 := hslots slot (by simp)
        have hrunHead : run 3 program env state = after := by
          have hrun := run_push_push_sstore program env state
            (.word (target slot)) (.nat256 slot) hrunning
          rw [show head =
            [.push (.word (target slot)), .push (.nat256 slot), .sstore]
              by rfl] at hhead
          specialize hrun hhead
          rw [PushData.nat256_value_toNat_of_lt hslot] at hrun
          simpa [after, head, Assembly.byteLength,
            Instruction.byteLength] using hrun
        have hafterRunning : after.exit = none := by
          simp [after, hrunning]
        have htail' : Assembly.CodeAt program tail after.pc := by
          simpa [after] using htail
        have hrunTail : run tail.length program env after =
            { after with
              pc := after.pc + tail.byteLength
              storage := applyStorageWrites rest target after.storage } := by
          apply ih after hafterRunning
          · intro key hkey
            exact hslots key (by simp [hkey])
          · simpa [tail] using htail'
        have hlength : (head ++ tail).length = 3 + tail.length := by
          simp [head]
          omega
        rw [hlength, run_add, hrunHead, hrunTail]
        rw [happly]
        simp [after, Assembly.byteLength_append]
        omega

/-- From zero account storage, the certified constructor initialization prefix
installs its finitely supported target exactly. -/
theorem run_compileStorageInitialization (slotCount : Nat)
    (target : TotalStorage) (program : Assembly) (env : ExecutionEnv)
    (state : ExecutionState)
    (hslotCount : slotCount ≤ 2 ^ 256)
    (hzeroOutside : ∀ key, slotCount ≤ key → target key = 0)
    (hrunning : state.exit = none)
    (hstorage : state.storage = fun _ => 0)
    (hcode : Assembly.CodeAt program
      (compileStorageInitialization slotCount target) state.pc) :
    run (compileStorageInitialization slotCount target).length program env
        state =
      { state with
        pc := state.pc +
          (compileStorageInitialization slotCount target).byteLength
        storage := target } := by
  have hrun := run_compileStorageWrites (List.range slotCount) target program
    env state hrunning (by
      intro slot hslot
      have hlt : slot < slotCount := List.mem_range.mp hslot
      exact hlt.trans_le hslotCount) (by
        simpa [compileStorageInitialization] using hcode)
  have happly :
      applyStorageWrites (List.range slotCount) target state.storage = target := by
    rw [hstorage]
    exact applyStorageWrites_range_eq_target slotCount target hzeroOutside
  simp only [compileStorageInitialization]
  rw [hrun]
  rw [happly]

/-- The fixed constructor suffix copies the selected code interval into memory
and returns those exact bytes. -/
theorem run_deploymentCopyReturn (runtimeOffset runtimeSize : Nat)
    (program : Assembly) (env : ExecutionEnv) (state : ExecutionState)
    (hoffset : runtimeOffset < 2 ^ 32)
    (hsize : runtimeSize < 2 ^ 32)
    (hrunning : state.exit = none)
    (hcode : Assembly.CodeAt program
      (deploymentCopyReturn runtimeOffset runtimeSize) state.pc) :
    run (deploymentCopyReturn runtimeOffset runtimeSize).length program env
        state =
      { state with
        pc := state.pc + 20
        stack := state.stack
        memory := writeBytes state.memory 0
          (readBytes env.codeBytes runtimeOffset runtimeSize)
        exit := some (.returned
          (readBytes env.codeBytes runtimeOffset runtimeSize)) } := by
  let encodedOffset := (PushData.nat32 runtimeOffset).value.toNat
  let encodedSize := (PushData.nat32 runtimeSize).value.toNat
  let copied := readBytes env.codeBytes encodedOffset encodedSize
  let setup : Assembly :=
    [ .push (.nat32 runtimeSize),
      .push (.nat32 runtimeOffset),
      .push (.one (byte 0)),
      .codecopy,
      .push (.nat32 runtimeSize),
      .push (.one (byte 0)) ]
  let beforeReturn : ExecutionState :=
    { state with
      pc := state.pc + setup.byteLength
      stack := 0 :: (PushData.nat32 runtimeSize).value :: state.stack
      memory := writeBytes state.memory 0 copied }
  have hdecomp : deploymentCopyReturn runtimeOffset runtimeSize =
      setup ++ [.return] := by
    rfl
  rw [hdecomp] at hcode ⊢
  have hsetup : Assembly.CodeAt program setup state.pc := hcode.left
  have hreturn : Assembly.CodeAt program [.return]
      (state.pc + setup.byteLength) := hcode.right
  have hstraight : StraightRun program env setup state beforeReturn := by
    simp [StraightRun, setup, beforeReturn, stepInstruction, advance,
      hrunning, copied, encodedOffset, encodedSize,
      Assembly.byteLength, Instruction.byteLength]
  have hrunSetup : run setup.length program env state = beforeReturn :=
    hstraight.run_eq hsetup
  have hreturn' : Assembly.CodeAt program [.return] beforeReturn.pc := by
    simpa [beforeReturn] using hreturn
  have hbeforeRunning : beforeReturn.exit = none := by
    simp [beforeReturn, hrunning]
  have hcopiedLength : copied.length = encodedSize := by
    simp [copied]
  have hreadCopied :
      readMemory (writeBytes state.memory 0 copied) 0 encodedSize = copied := by
    rw [← hcopiedLength]
    exact readMemory_writeBytes state.memory 0 copied
  have hrunReturn : run 1 program env beforeReturn =
      { state with
        pc := state.pc + 20
        stack := state.stack
        memory := writeBytes state.memory 0 copied
        exit := some (.returned copied) } := by
    rw [run_succ_of_codeAt 0 hbeforeRunning hreturn']
    simp only [run]
    change
      ExecutionState.mk (state.pc + setup.byteLength) state.stack
        (writeBytes state.memory 0 copied) state.storage state.logs
        (some (.returned
          (readMemory (writeBytes state.memory 0 copied) 0 encodedSize))) =
      ExecutionState.mk (state.pc + 20) state.stack
        (writeBytes state.memory 0 copied) state.storage state.logs
        (some (.returned copied))
    rw [hreadCopied]
    simp [setup, Assembly.byteLength, Instruction.byteLength]
  have hencodedOffset : encodedOffset = runtimeOffset :=
    PushData.nat32_value_toNat_of_lt hoffset
  have hencodedSize : encodedSize = runtimeSize :=
    PushData.nat32_value_toNat_of_lt hsize
  have hcopied : copied =
      readBytes env.codeBytes runtimeOffset runtimeSize := by
    unfold copied
    rw [hencodedOffset, hencodedSize]
  rw [List.length_append]
  simp only [List.length_singleton]
  rw [run_add, hrunSetup, hrunReturn]
  rw [hcopied]

/-- Execute from the standard empty-stack/memory state. -/
def execute (fuel : Nat) (program : Assembly) (env : ExecutionEnv)
    (storage : TotalStorage) : ExecutionState :=
  run fuel program env (ExecutionState.initial storage)

/-- Transaction-level projection. Revert and fault carry no successor storage,
so rollback is structural rather than an additional theorem premise. -/
inductive TransactionResult where
  | success (storage : TotalStorage) (logs : List (List Byte))
      (returnData : List Byte)
  | revert (data : List Byte)
  | fault
  | outOfFuel

/-- Commit state only after normal `STOP`/`RETURN`; every revert discards all
intermediate writes. -/
def ExecutionState.transactionResult
    (state : ExecutionState) : TransactionResult :=
  match state.exit with
  | some .stopped => .success state.storage state.logs []
  | some (.returned data) => .success state.storage state.logs data
  | some (.reverted data) => .revert data
  | some .fault => .fault
  | none => .outOfFuel

/-- Run one transaction and apply the rollback-aware result projection. -/
def executeTransaction (fuel : Nat) (program : Assembly)
    (env : ExecutionEnv) (storage : TotalStorage) : TransactionResult :=
  (execute fuel program env storage).transactionResult

/-- Fresh EVM account storage before constructor execution. -/
def freshStorage : TotalStorage := fun _ => 0

namespace DeploymentImage

variable {selectors : ClassicalSelectors}

/-- Execute creation assembly against its actual appended creation bytes.
The program is acyclic, so one step per assembly instruction is sufficient. -/
def execute (image : DeploymentImage selectors) : ExecutionState :=
  EVM.execute (image.creationAssembly.length + 1) image.creationAssembly
    { codeBytes := image.bytecode
      calldata := []
      caller := 0
      contractAddress := 0
      callValue := 0 }
    freshStorage

/-- Every certified deployment image installs its exact finite storage and
returns its exact linked runtime bytecode. -/
theorem execute_transactionResult (image : DeploymentImage selectors) :
    image.execute.transactionResult =
      .success image.initialStorage [] image.runtime.bytecode := by
  let env : ExecutionEnv :=
    { codeBytes := image.bytecode
      calldata := []
      caller := 0
      contractAddress := 0
      callValue := 0 }
  let initial := ExecutionState.initial freshStorage
  let afterInitialization : ExecutionState :=
    { initial with
      pc := image.initialization.byteLength
      storage := image.initialStorage }
  let suffix := deploymentCopyReturn image.runtimeOffset
    image.runtime.bytecode.length
  have hcode : Assembly.CodeAt image.creationAssembly
      (image.initialization ++ suffix) 0 := by
    refine ⟨[], [], ?_, rfl⟩
    simp [DeploymentImage.creationAssembly, suffix]
  have hinitialization : Assembly.CodeAt image.creationAssembly
      image.initialization initial.pc := by
    change Assembly.CodeAt image.creationAssembly image.initialization 0
    exact hcode.left
  have hsuffix : Assembly.CodeAt image.creationAssembly suffix
      afterInitialization.pc := by
    have hright := hcode.right
    simpa [initial, afterInitialization] using hright
  have hrunInitialization :
      run image.initialization.length image.creationAssembly env initial =
        afterInitialization := by
    have hrun := run_compileStorageInitialization image.slotCount
      image.initialStorage image.creationAssembly env initial
      image.slotCount_fits image.storage_zero_outside
      (by simp [initial, ExecutionState.initial])
      (by rfl) (by
        simpa [DeploymentImage.initialization] using hinitialization)
    simpa [DeploymentImage.initialization, afterInitialization, initial,
      ExecutionState.initial] using hrun
  have hrunSuffix :
      run suffix.length image.creationAssembly env afterInitialization =
        { afterInitialization with
          pc := afterInitialization.pc + 20
          stack := afterInitialization.stack
          memory := writeBytes afterInitialization.memory 0
            (readBytes image.bytecode image.runtimeOffset
              image.runtime.bytecode.length)
          exit := some (.returned
            (readBytes image.bytecode image.runtimeOffset
              image.runtime.bytecode.length)) } := by
    apply run_deploymentCopyReturn image.runtimeOffset
      image.runtime.bytecode.length image.creationAssembly env
      afterInitialization image.runtimeOffset_fits
      image.runtime.bytecode_length_fits
    · simp [afterInitialization, initial, ExecutionState.initial]
    · simpa [suffix] using hsuffix
  have hcopy :
      readBytes image.bytecode image.runtimeOffset
          image.runtime.bytecode.length = image.runtime.bytecode := by
    simpa using readBytes_drop_length image.bytecode image.runtimeOffset
  have hfuel : image.creationAssembly.length + 1 =
      image.initialization.length + (suffix.length + 1) := by
    simp [DeploymentImage.creationAssembly, suffix, Nat.add_assoc]
  rw [hcopy] at hrunSuffix
  unfold DeploymentImage.execute EVM.execute
  change
    (run (image.creationAssembly.length + 1) image.creationAssembly env
      initial).transactionResult = _
  rw [hfuel, run_add, hrunInitialization, run_add, hrunSuffix]
  simp [afterInitialization, initial, ExecutionState.initial,
    ExecutionState.transactionResult]

end DeploymentImage

end Vegas.Machine.Contract.EVM
