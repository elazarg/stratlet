/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasEVM.Contract.ClassicalEVMCalldata
import VegasEVM.Contract.EVMBytes

/-!
# Byte calldata for the classical contract

This pass serializes all four deterministic entry points using Ethereum's
four-byte-selector followed by 32-byte-word convention. Reveal and sample
requests occupy 36 bytes, oracle callbacks occupy 68 bytes, and player commits
occupy 100 bytes. Decoding rejects every other length before selector and word
decoding.

Function selectors remain certified configuration values. Deriving them from
Keccak signatures and emitting executable EVM instructions are later backend
passes.
-/

noncomputable section

namespace Vegas.Machine.Contract.EVM

open Blockchain

variable {Player Address ValueWord : Type}
variable [DecidableEq Player] [DecidableEq Address]
variable {L : IExpr} {program : Program Player L}

@[simp] theorem extractTwoWordSelector (selector : Selector)
    (first second : Word) :
    ((selector ++ first) ++ second).extractLsb' 512 32 = selector := by
  rw [BitVec.extractLsb'_append_eq_of_le (by omega)]
  exact BitVec.extractLsb'_append_eq_left

@[simp] theorem extractTwoWord0 (selector : Selector)
    (first second : Word) :
    ((selector ++ first) ++ second).extractLsb' 256 256 = first := by
  rw [BitVec.extractLsb'_append_eq_of_le (by omega)]
  exact BitVec.extractLsb'_append_eq_right

@[simp] theorem extractTwoWord1 (selector : Selector)
    (first second : Word) :
    ((selector ++ first) ++ second).extractLsb' 0 256 = second :=
  BitVec.extractLsb'_append_eq_right

namespace ClassicalABI

/-- Serialize a decoded classical message to its fixed byte calldata shape. -/
def encodeBytes (abi : ClassicalABI program ValueWord) :
    ClassicalMessage program ValueWord → ByteCalldata
  | .player message =>
      { byteLength := 100
        bits :=
          ((abi.selectors.player ++ abi.players.encode message.player) ++
            abi.nodes.encode message.node) ++
              abi.values.encode message.value }
  | .reveal message =>
      { byteLength := 36
        bits := abi.selectors.reveal ++ abi.nodes.encode message.node }
  | .sampleRequest message =>
      { byteLength := 36
        bits := abi.selectors.sampleRequest ++ abi.nodes.encode message.node }
  | .oracleCallback message =>
      { byteLength := 68
        bits :=
          (abi.selectors.oracleCallback ++ abi.nodes.encode message.node) ++
            message.choice }

/-- Parse byte-aligned calldata and apply the certified four-selector word
decoder. -/
def decodeBytes (abi : ClassicalABI program ValueWord)
    (calldata : ByteCalldata) :
    Option (ClassicalMessage program ValueWord) :=
  if hone : calldata.byteLength = 36 then
    let bits : BitVec 288 := calldata.bits.cast (by omega)
    abi.decode
      { selector := bits.extractLsb' 256 32
        arguments := [bits.extractLsb' 0 256] }
  else if htwo : calldata.byteLength = 68 then
    let bits : BitVec 544 := calldata.bits.cast (by omega)
    abi.decode
      { selector := bits.extractLsb' 512 32
        arguments :=
          [bits.extractLsb' 256 256, bits.extractLsb' 0 256] }
  else if hthree : calldata.byteLength = 100 then
    let bits : BitVec 800 := calldata.bits.cast (by omega)
    abi.decode
      { selector := bits.extractLsb' 768 32
        arguments :=
          [bits.extractLsb' 512 256, bits.extractLsb' 256 256,
            bits.extractLsb' 0 256] }
  else
    none

/-- Fixed byte serialization is lossless for all four classical messages. -/
@[simp] theorem decodeBytes_encodeBytes
    (abi : ClassicalABI program ValueWord)
    (message : ClassicalMessage program ValueWord) :
    abi.decodeBytes (abi.encodeBytes message) = some message := by
  cases message with
  | player message =>
      have hlen :
          (abi.encodeBytes (ClassicalMessage.player message)).byteLength
            = 100 := rfl
      have h36 :
          ¬ (abi.encodeBytes
              (ClassicalMessage.player message)).byteLength = 36 := by
        rw [hlen]
        decide
      have h68 :
          ¬ (abi.encodeBytes
              (ClassicalMessage.player message)).byteLength = 68 := by
        rw [hlen]
        decide
      unfold decodeBytes
      rw [dif_neg h36, dif_neg h68, dif_pos hlen]
      simp only [BitVec.extractLsb'_cast]
      simp [encodeBytes, ClassicalABI.decode,
        abi.players.decode_encode, abi.nodes.decode_encode,
        abi.values.decode_encode]
  | reveal message =>
      have hne : abi.selectors.reveal ≠ abi.selectors.player :=
        Ne.symm abi.selectors.player_ne_reveal
      have hlen :
          (abi.encodeBytes (ClassicalMessage.reveal message)).byteLength
            = 36 := rfl
      unfold decodeBytes
      rw [dif_pos hlen]
      simp only [BitVec.extractLsb'_cast]
      simp [encodeBytes, ClassicalABI.decode, hne, abi.nodes.decode_encode]
  | sampleRequest message =>
      have hp : abi.selectors.sampleRequest ≠ abi.selectors.player :=
        Ne.symm abi.selectors.player_ne_sampleRequest
      have hr : abi.selectors.sampleRequest ≠ abi.selectors.reveal :=
        Ne.symm abi.selectors.reveal_ne_sampleRequest
      have hlen :
          (abi.encodeBytes
            (ClassicalMessage.sampleRequest message)).byteLength = 36 := rfl
      unfold decodeBytes
      rw [dif_pos hlen]
      simp only [BitVec.extractLsb'_cast]
      simp [encodeBytes, ClassicalABI.decode, hp, hr,
        abi.nodes.decode_encode]
  | oracleCallback message =>
      have hp : abi.selectors.oracleCallback ≠ abi.selectors.player :=
        Ne.symm abi.selectors.player_ne_oracleCallback
      have hr : abi.selectors.oracleCallback ≠ abi.selectors.reveal :=
        Ne.symm abi.selectors.reveal_ne_oracleCallback
      have hs :
          abi.selectors.oracleCallback ≠ abi.selectors.sampleRequest :=
        Ne.symm abi.selectors.sampleRequest_ne_oracleCallback
      have hlen :
          (abi.encodeBytes
            (ClassicalMessage.oracleCallback message)).byteLength = 68 := rfl
      have h36 :
          ¬ (abi.encodeBytes
              (ClassicalMessage.oracleCallback message)).byteLength = 36 := by
        rw [hlen]
        decide
      unfold decodeBytes
      rw [dif_neg h36, dif_pos hlen]
      simp only [BitVec.extractLsb'_cast]
      simp [encodeBytes, ClassicalABI.decode, hp, hr, hs,
        abi.nodes.decode_encode]

/-- Byte framing of the complete classical message surface as a standard
lossless wire codec. -/
def byteWireCodec (abi : ClassicalABI program ValueWord) :
    WireCodec (ClassicalMessage program ValueWord) ByteCalldata where
  encode := abi.encodeBytes
  decode := abi.decodeBytes
  decode_encode := abi.decodeBytes_encodeBytes

end ClassicalABI

end Vegas.Machine.Contract.EVM

namespace Vegas.Machine.Contract.ClassicalContract

open Blockchain

variable {Player Address : Type}
variable [DecidableEq Player] [DecidableEq Address]
variable {L : IExpr} {program : Program Player L}
variable (contract : ClassicalContract program Address)

/-- Decode and execute byte-aligned EVM calldata for the deterministic
classical contract. -/
def receiveEVMBytes (abi : EVM.ClassicalABI program contract.codec.Word)
    (context : CallContext Address) (state : contract.State)
    (calldata : EVM.ByteCalldata) :
    DeterministicResult contract.State OracleProtocol.Request :=
  match abi.decodeBytes calldata with
  | none => .revert .malformed
  | some message => contract.receive state (message.contextualize context)

/-- Byte framing is behaviorally transparent for every encoded classical
message. -/
@[simp] theorem receiveEVMBytes_encode
    (abi : EVM.ClassicalABI program contract.codec.Word)
    (context : CallContext Address) (state : contract.State)
    (message : EVM.ClassicalMessage program contract.codec.Word) :
    contract.receiveEVMBytes abi context state (abi.encodeBytes message) =
      contract.receive state (message.contextualize context) := by
  simp [receiveEVMBytes, abi.decodeBytes_encodeBytes]

/-- Every unrecognized byte shape is rejected before typed validation. -/
theorem receiveEVMBytes_revert_malformed
    (abi : EVM.ClassicalABI program contract.codec.Word)
    (context : CallContext Address) (state : contract.State)
    (calldata : EVM.ByteCalldata)
    (hdecode : abi.decodeBytes calldata = none) :
    contract.receiveEVMBytes abi context state calldata =
      .revert .malformed := by
  simp [receiveEVMBytes, hdecode]

end Vegas.Machine.Contract.ClassicalContract
