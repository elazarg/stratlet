/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasEVM.Contract.EVMCalldata

/-!
# Byte-aligned EVM calldata

This pass serializes the two fixed Vegas entry-point shapes as byte-aligned
bitstrings. Internal calls occupy 4 selector bytes plus one 32-byte word;
player calls occupy 4 selector bytes plus three 32-byte words. Concatenation is
big-endian, matching Ethereum's selector-and-word layout.

The representation records its byte length dependently, so non-byte-aligned
inputs cannot be constructed. Decoding rejects every length other than 36 or
100 bytes before extracting the selector and argument words. Selector values
are still supplied by `MessageABI`; deriving them from Keccak signatures is a
separate pass.
-/

namespace Vegas.Machine.Contract.EVM

open EventGraph Blockchain

variable {Player Address : Type}
variable [DecidableEq Player] [DecidableEq Address]
variable {L : IExpr} {program : Program Player L}

/-- Raw byte-aligned calldata represented as a bitstring with its byte length.
-/
structure ByteCalldata where
  byteLength : Nat
  bits : BitVec (8 * byteLength)

namespace ByteCalldata

/-- Calldata whose byte length is represented exactly by the EVM's 256-bit
`CALLDATASIZE` result. Every concrete blockchain transaction satisfies this;
the predicate excludes only mathematical lists too large to exist on-chain.
-/
def FitsWord (calldata : ByteCalldata) : Prop :=
  calldata.byteLength < 2 ^ 256

end ByteCalldata

@[simp] theorem extractInternalSelector (selector : Selector) (node : Word) :
    (selector ++ node).extractLsb' 256 32 = selector :=
  BitVec.extractLsb'_append_eq_left

@[simp] theorem extractInternalNode (selector : Selector) (node : Word) :
    (selector ++ node).extractLsb' 0 256 = node :=
  BitVec.extractLsb'_append_eq_right

@[simp] theorem extractPlayerSelector (selector : Selector)
    (player node value : Word) :
    (((selector ++ player) ++ node) ++ value).extractLsb' 768 32 =
      selector := by
  rw [BitVec.extractLsb'_append_eq_of_le (by omega)]
  rw [BitVec.extractLsb'_append_eq_of_le (by omega)]
  exact BitVec.extractLsb'_append_eq_left

@[simp] theorem extractPlayerWord0 (selector : Selector)
    (player node value : Word) :
    (((selector ++ player) ++ node) ++ value).extractLsb' 512 256 =
      player := by
  rw [BitVec.extractLsb'_append_eq_of_le (by omega)]
  rw [BitVec.extractLsb'_append_eq_of_le (by omega)]
  exact BitVec.extractLsb'_append_eq_right

@[simp] theorem extractPlayerWord1 (selector : Selector)
    (player node value : Word) :
    (((selector ++ player) ++ node) ++ value).extractLsb' 256 256 = node := by
  rw [BitVec.extractLsb'_append_eq_of_le (by omega)]
  exact BitVec.extractLsb'_append_eq_right

@[simp] theorem extractPlayerWord2 (selector : Selector)
    (player node value : Word) :
    (((selector ++ player) ++ node) ++ value).extractLsb' 0 256 = value :=
  BitVec.extractLsb'_append_eq_right

namespace MessageABI

variable {Argument : Type}

/-- Serialize a decoded Vegas message directly to its fixed EVM calldata
shape. -/
def encodeBytes (abi : MessageABI program Argument)
    (words : WireCodec Argument Word) :
    Blockchain.Message program Argument → ByteCalldata
  | .player message =>
      { byteLength := 100
        bits :=
          ((abi.selectors.player ++
              words.encode (abi.players.encode message.player)) ++
            words.encode (abi.nodes.encode message.node)) ++
              words.encode message.value }
  | .internal message =>
      { byteLength := 36
        bits := abi.selectors.internal ++
          words.encode (abi.nodes.encode message.node) }

/-- Parse byte-aligned calldata and then apply the certified word-level message
decoder. -/
def decodeBytes (abi : MessageABI program Argument)
    (words : WireCodec Argument Word)
    (calldata : ByteCalldata) :
    Option (Blockchain.Message program Argument) :=
  if hinternal : calldata.byteLength = 36 then
    let bits : BitVec 288 := calldata.bits.cast (by omega)
    match words.decode (bits.extractLsb' 0 256) with
    | none => none
    | some nodeWord =>
        abi.decode
          { selector := bits.extractLsb' 256 32
            arguments := [nodeWord] }
  else if hplayer : calldata.byteLength = 100 then
    let bits : BitVec 800 := calldata.bits.cast (by omega)
    match words.decode (bits.extractLsb' 512 256),
        words.decode (bits.extractLsb' 256 256),
        words.decode (bits.extractLsb' 0 256) with
    | some playerWord, some nodeWord, some value =>
        abi.decode
          { selector := bits.extractLsb' 768 32
            arguments := [playerWord, nodeWord, value] }
    | _, _, _ => none
  else
    none

/-- Fixed byte serialization is lossless for every configured Vegas message.
-/
@[simp] theorem decodeBytes_encodeBytes
    (abi : MessageABI program Argument) (words : WireCodec Argument Word)
    (message : Blockchain.Message program Argument) :
    abi.decodeBytes words (abi.encodeBytes words message) = some message := by
  cases message with
  | player message =>
      have hlen :
          (abi.encodeBytes words (Blockchain.Message.player message)).byteLength
            = 100 := rfl
      have hne36 :
          ¬ (abi.encodeBytes words
              (Blockchain.Message.player message)).byteLength = 36 := by
        rw [hlen]
        decide
      unfold decodeBytes
      rw [dif_neg hne36, dif_pos hlen]
      simp only [BitVec.extractLsb'_cast]
      simp [encodeBytes, decode, words.decode_encode,
        abi.players.decode_encode, abi.nodes.decode_encode]
  | internal message =>
      have hne : abi.selectors.internal ≠ abi.selectors.player :=
        Ne.symm abi.selectors.player_ne_internal
      have hlen :
          (abi.encodeBytes words
            (Blockchain.Message.internal message)).byteLength = 36 := rfl
      unfold decodeBytes
      rw [dif_pos hlen]
      simp only [BitVec.extractLsb'_cast]
      simp [encodeBytes, decode, hne, words.decode_encode,
        abi.nodes.decode_encode]

/-- Byte-aligned message framing as a standard lossless wire codec. -/
def byteWireCodec (abi : MessageABI program Argument)
    (words : WireCodec Argument Word) :
    WireCodec (Blockchain.Message program Argument) ByteCalldata where
  encode := abi.encodeBytes words
  decode := abi.decodeBytes words
  decode_encode := abi.decodeBytes_encodeBytes words

end MessageABI

end Vegas.Machine.Contract.EVM

noncomputable section

namespace Vegas.Machine.Contract.ConfiguredContract

open EventGraph Blockchain

variable {Player Address : Type}
variable [DecidableEq Player] [DecidableEq Address]
variable {L : IExpr} {program : Program Player L}
variable (contract : ConfiguredContract program Address)

/-- Validate byte-aligned EVM calldata. -/
def acceptsEVMBytes
    (abi : EVM.MessageABI program contract.codec.Word)
    (words : WireCodec contract.codec.Word EVM.Word)
    (context : CallContext Address) (store : contract.Store)
    (calldata : EVM.ByteCalldata) : Bool :=
  match abi.decodeBytes words calldata with
  | none => false
  | some message => contract.acceptsMessage context store message

/-- Decode and execute byte-aligned EVM calldata. Framing failures remain
distinguishable from decoded semantic rejection. -/
def receiveEVMBytes (chain : ChainView)
    (abi : EVM.MessageABI program contract.codec.Word)
    (words : WireCodec contract.codec.Word EVM.Word)
    (context : CallContext Address) (store : contract.Store)
    (calldata : EVM.ByteCalldata) :
    ReceiveResult contract.Store Empty :=
  match abi.decodeBytes words calldata with
  | none => .revert .malformed
  | some message => contract.receive chain context store message

/-- Byte serialization is behaviorally transparent for encoded messages. -/
@[simp] theorem receiveEVMBytes_encode
    (chain : ChainView)
    (abi : EVM.MessageABI program contract.codec.Word)
    (words : WireCodec contract.codec.Word EVM.Word)
    (context : CallContext Address) (store : contract.Store)
    (message : contract.Message) :
    contract.receiveEVMBytes chain abi words context store
        (abi.encodeBytes words message) =
      contract.receive chain context store message := by
  simp [receiveEVMBytes, abi.decodeBytes_encodeBytes]

/-- Every accepted byte string over reachable encoded storage still executes
as a valid semantic command. -/
theorem receiveEVMBytes_encodeState_of_accepts
    (chain : ChainView)
    (abi : EVM.MessageABI program contract.codec.Word)
    (words : WireCodec contract.codec.Word EVM.Word)
    (context : CallContext Address) (state : program.State)
    (calldata : EVM.ByteCalldata)
    (haccept :
      contract.acceptsEVMBytes abi words context
        (RawStore.encodeState contract.codec state) calldata = true) :
    ∃ command : program.Command state,
      contract.receiveEVMBytes chain abi words context
          (RawStore.encodeState contract.codec state) calldata =
        .success (CallSuccess.silentLaw Empty
          ((program.step state command).map
            (RawStore.encodeState contract.codec))) := by
  unfold acceptsEVMBytes at haccept
  cases hdecode : abi.decodeBytes words calldata with
  | none => simp [hdecode] at haccept
  | some message =>
      simp only [hdecode] at haccept
      rcases contract.receive_encodeState_of_accepts
          chain context state message haccept with
        ⟨command, hexecute⟩
      refine ⟨command, ?_⟩
      simp [receiveEVMBytes, hdecode, hexecute]

end Vegas.Machine.Contract.ConfiguredContract
