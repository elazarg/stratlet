/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasEVM.Contract.Blockchain
import VegasEVM.Contract.EVMWord
import VegasEVM.Contract.Wire

/-!
# EVM word-calldata framing

This pass introduces exactly two ABI-like details: a 32-bit entry-point
selector and an ordered list of argument words. Player messages have arguments
`[player, node, value]`; internal messages have `[node]`. Wrong selectors,
wrong arities, unknown players, and out-of-range nodes reject during decoding.

The representation is not byte-level Ethereum ABI encoding and selector values
are supplied explicitly rather than derived from Keccak function signatures.
Those are later refinements. The node codec records the real 256-bit capacity
obligation instead of pretending arbitrary `Nat` values fit in one word.
-/

namespace Vegas.Machine.Contract.EVM

open EventGraph Blockchain

variable {Player Address : Type}
variable [DecidableEq Player] [DecidableEq Address]
variable {L : IExpr} {program : Program Player L}

/-- Four-byte function selector before byte serialization. -/
abbrev Selector := BitVec 32

/-- Selector plus statically ordered whole-word arguments. -/
structure Calldata (Word : Type) where
  selector : Selector
  arguments : List Word

/-- Distinct selectors for the two configured Vegas entry points. -/
structure Selectors where
  player : Selector
  internal : Selector
  player_ne_internal : player ≠ internal

/-- A complete framing configuration for caller-free messages. Player and
bounded-node codecs share the contract's argument-word type. -/
structure MessageABI (program : Program Player L) (Word : Type) where
  selectors : Selectors
  players : WireCodec Player Word
  nodes : WireCodec (Fin program.graph.nodeCount) Word

namespace MessageABI

variable {Word : Type}

/-- Encode a decoded message to selector-framed words. -/
def encode (abi : MessageABI program Word) :
    Blockchain.Message program Word → Calldata Word
  | .player message =>
      { selector := abi.selectors.player
        arguments :=
          [abi.players.encode message.player,
            abi.nodes.encode message.node, message.value] }
  | .internal message =>
      { selector := abi.selectors.internal
        arguments := [abi.nodes.encode message.node] }

/-- Decode selector-framed words, rejecting every unrecognized shape. -/
def decode (abi : MessageABI program Word) (calldata : Calldata Word) :
    Option (Blockchain.Message program Word) :=
  if calldata.selector = abi.selectors.player then
    match calldata.arguments with
    | [playerWord, nodeWord, value] =>
        match abi.players.decode playerWord, abi.nodes.decode nodeWord with
        | some player, some node =>
            some (.player { player := player, node := node, value := value })
        | _, _ => none
    | _ => none
  else if calldata.selector = abi.selectors.internal then
    match calldata.arguments with
    | [nodeWord] =>
        match abi.nodes.decode nodeWord with
        | some node => some (.internal { node := node })
        | none => none
    | _ => none
  else
    none

@[simp] theorem decode_encode (abi : MessageABI program Word)
    (message : Blockchain.Message program Word) :
    abi.decode (abi.encode message) = some message := by
  cases message with
  | player message =>
      simp [decode, encode, abi.players.decode_encode,
        abi.nodes.decode_encode]
  | internal message =>
      have hne : abi.selectors.internal ≠ abi.selectors.player :=
        Ne.symm abi.selectors.player_ne_internal
      simp [decode, encode, hne, abi.nodes.decode_encode]

/-- The selector-framed encoding is a standard lossless wire codec. -/
def wireCodec (abi : MessageABI program Word) :
    WireCodec (Blockchain.Message program Word) (Calldata Word) where
  encode := abi.encode
  decode := abi.decode
  decode_encode := abi.decode_encode

end MessageABI

/-- A finite index family fits in one 256-bit unsigned word. -/
def IndexFitsWord (count : Nat) : Prop := count ≤ 2 ^ 256

/-- Encode a bounded index as an unsigned 256-bit word. -/
def encodeIndex {count : Nat} (index : Fin count) : Word :=
  BitVec.ofNat 256 index

/-- Decode an unsigned word only when it names an index below `count`. -/
def decodeIndex (count : Nat) (word : Word) : Option (Fin count) :=
  if h : word.toNat < count then
    some ⟨word.toNat, h⟩
  else
    none

@[simp] theorem decodeIndex_encodeIndex
    {count : Nat} (fits : IndexFitsWord count) (index : Fin count) :
    decodeIndex count (encodeIndex index) = some index := by
  have hword : (index : Nat) < 2 ^ 256 :=
    lt_of_lt_of_le index.isLt fits
  have hnat : (encodeIndex index).toNat = index := by
    rw [encodeIndex, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hword]
  simp [decodeIndex, hnat, index.isLt]

/-- Lossless one-word codec for any finite index family satisfying the explicit
256-bit capacity bound. -/
def indexWordCodec (count : Nat) (fits : IndexFitsWord count) :
    WireCodec (Fin count) Word where
  encode := encodeIndex
  decode := decodeIndex count
  decode_encode := decodeIndex_encodeIndex fits

/-- The bounded-index decoder accepts no noncanonical word aliases. -/
theorem indexWordCodec_canonical (count : Nat) (fits : IndexFitsWord count) :
    WireCodec.Canonical (indexWordCodec count fits) where
  encode_decode word index hdecode := by
    change decodeIndex count word = some index at hdecode
    change encodeIndex index = word
    unfold decodeIndex at hdecode
    split at hdecode
    · cases hdecode
      apply BitVec.eq_of_toNat_eq
      simp [encodeIndex]
    · contradiction

/-- The program has few enough nodes for every valid node index to fit in one
256-bit unsigned word. -/
abbrev NodesFitWord (program : Program Player L) : Prop :=
  IndexFitsWord program.graph.nodeCount

/-- Lossless one-word codec for the finite node index of a program satisfying
the explicit 256-bit capacity bound. -/
def nodeWordCodec (program : Program Player L) (fits : NodesFitWord program) :
    WireCodec (Fin program.graph.nodeCount) Word :=
  indexWordCodec program.graph.nodeCount fits

theorem nodeWordCodec_canonical
    (program : Program Player L) (fits : NodesFitWord program) :
    WireCodec.Canonical (nodeWordCodec program fits) :=
  indexWordCodec_canonical program.graph.nodeCount fits

end Vegas.Machine.Contract.EVM

noncomputable section

namespace Vegas.Machine.Contract.ConfiguredContract

open EventGraph Blockchain

variable {Player Address : Type}
variable [DecidableEq Player] [DecidableEq Address]
variable {L : IExpr} {program : Program Player L}
variable (contract : ConfiguredContract program Address)

/-- Decode and validate selector-framed, caller-free calldata. -/
def acceptsEVMCalldata
    (abi : EVM.MessageABI program contract.codec.Word)
    (context : CallContext Address) (store : contract.Store)
    (calldata : EVM.Calldata contract.codec.Word) : Bool :=
  match abi.decode calldata with
  | none => false
  | some message => contract.acceptsMessage context store message

/-- Decode and execute selector-framed, caller-free calldata. Malformed framing
and semantic rejection remain distinct. -/
def receiveEVMCalldata (chain : ChainView)
    (abi : EVM.MessageABI program contract.codec.Word)
    (context : CallContext Address) (store : contract.Store)
    (calldata : EVM.Calldata contract.codec.Word) :
    ReceiveResult contract.Store Empty :=
  match abi.decode calldata with
  | none => .revert .malformed
  | some message => contract.receive chain context store message

/-- A framing failure is reported as a malformed-call revert before semantic
validation runs. -/
theorem receiveEVMCalldata_revert_malformed
    (chain : ChainView)
    (abi : EVM.MessageABI program contract.codec.Word)
    (context : CallContext Address) (store : contract.Store)
    (calldata : EVM.Calldata contract.codec.Word)
    (hdecode : abi.decode calldata = none) :
    contract.receiveEVMCalldata chain abi context store calldata =
      .revert .malformed := by
  simp [receiveEVMCalldata, hdecode]

/-- Framed execution succeeds exactly when framed validation accepts. -/
theorem receiveEVMCalldata_succeeded
    (chain : ChainView)
    (abi : EVM.MessageABI program contract.codec.Word)
    (context : CallContext Address) (store : contract.Store)
    (calldata : EVM.Calldata contract.codec.Word) :
    (contract.receiveEVMCalldata chain abi context store calldata).succeeded =
      contract.acceptsEVMCalldata abi context store calldata := by
  unfold receiveEVMCalldata acceptsEVMCalldata
  cases abi.decode calldata with
  | none => rfl
  | some message => exact contract.receive_succeeded chain context store message

/-- Encoding a contextual message is behaviorally transparent at the framed
calldata boundary. -/
@[simp] theorem receiveEVMCalldata_encode
    (chain : ChainView)
    (abi : EVM.MessageABI program contract.codec.Word)
    (context : CallContext Address) (store : contract.Store)
    (message : contract.Message) :
    contract.receiveEVMCalldata chain abi context store
        (abi.encode message) =
      contract.receive chain context store message := by
  simp [receiveEVMCalldata, abi.decode_encode]

/-- Every accepted selector-framed input over reachable encoded storage still
executes as a valid semantic command. -/
theorem receiveEVMCalldata_encodeState_of_accepts
    (chain : ChainView)
    (abi : EVM.MessageABI program contract.codec.Word)
    (context : CallContext Address) (state : program.State)
    (calldata : EVM.Calldata contract.codec.Word)
    (haccept :
      contract.acceptsEVMCalldata abi context
        (RawStore.encodeState contract.codec state) calldata = true) :
    ∃ command : program.Command state,
      contract.receiveEVMCalldata chain abi context
          (RawStore.encodeState contract.codec state) calldata =
        .success (CallSuccess.silentLaw Empty
          ((program.step state command).map
            (RawStore.encodeState contract.codec))) := by
  unfold acceptsEVMCalldata at haccept
  cases hdecode : abi.decode calldata with
  | none => simp [hdecode] at haccept
  | some message =>
      simp only [hdecode] at haccept
      rcases contract.receive_encodeState_of_accepts
          chain context state message haccept with
        ⟨command, hexecute⟩
      refine ⟨command, ?_⟩
      simp [receiveEVMCalldata, hdecode, hexecute]

end Vegas.Machine.Contract.ConfiguredContract
