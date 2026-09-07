/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasEVM.Contract.Classical
import VegasEVM.Contract.EVMCalldata

/-!
# EVM word framing for the classical contract

The complete deterministic classical surface has four caller-free entry points:
player commit, reveal, sample request, and oracle callback.  This pass assigns
distinct 32-bit selectors and the fixed word shapes `[player,node,value]`,
`[node]`, `[node]`, and `[node,choice]`.  The blockchain call context supplies
the authenticated sender.

This is concrete EVM-sized calldata framing, not instruction generation.  The
callback choice is an unsigned 256-bit word and becomes a natural table index
at the typed contract boundary.  Producing a word from an arbitrary source
table index therefore carries an explicit `< 2^256` obligation.
-/

noncomputable section

namespace Vegas.Machine.Contract.EVM

open EventGraph Blockchain

variable {Player Address ValueWord : Type}
variable [DecidableEq Player] [DecidableEq Address]
variable {L : IExpr} {program : Program Player L}

/-- One-node caller-free message used by reveal and sample-request entry
points. -/
structure ClassicalNodeMessage (program : Program Player L) where
  node : Fin program.graph.nodeCount

/-- Caller-free authenticated-oracle callback arguments. -/
structure ClassicalOracleMessage (program : Program Player L) where
  node : Fin program.graph.nodeCount
  choice : Word

/-- Complete caller-free deterministic classical message surface. -/
inductive ClassicalMessage (program : Program Player L) (ValueWord : Type)
    where
  | player (message : PlayerMessage program ValueWord)
  | reveal (message : ClassicalNodeMessage program)
  | sampleRequest (message : ClassicalNodeMessage program)
  | oracleCallback (message : ClassicalOracleMessage program)

namespace ClassicalMessage

/-- Attach the blockchain sender to a decoded caller-free message. -/
def contextualize (context : CallContext Address) :
    ClassicalMessage program ValueWord →
      ClassicalCalldata Player Address ValueWord
  | .player message =>
      .player
        { caller := context.sender
          player := message.player
          node := message.node
          value := message.value }
  | .reveal message =>
      .reveal { caller := context.sender, node := message.node }
  | .sampleRequest message =>
      .sampleRequest { caller := context.sender, node := message.node }
  | .oracleCallback message =>
      .oracleCallback
        { caller := context.sender
          node := message.node
          choice := message.choice.toNat }

/-- Encode a valid semantic commitment without serializing its physical
caller. -/
def encodeCommit (codec : StorageCodec program)
    {state : program.State} {who : Player}
    (action : CommitAction program.graph who)
    (step : CommitStep program.graph state.1 who action) :
    ClassicalMessage program codec.Word :=
  .player (PlayerMessage.encodeCommit codec action step)

/-- Encode one reveal node for the caller-free reveal entry point. -/
def encodeReveal (event : InternalEvent program.graph) :
    ClassicalMessage program ValueWord :=
  .reveal { node := event.node }

/-- Encode one sample node for the caller-free request entry point. -/
def encodeSampleRequest (event : InternalEvent program.graph) :
    ClassicalMessage program ValueWord :=
  .sampleRequest { node := event.node }

/-- Encode a fixed-policy callback choice into one unsigned EVM word. -/
def encodeOracleCallback (event : InternalEvent program.graph)
    {dist : EventDist L} {env : ReadEnv L dist.reads}
    (choice : OraclePolicy.Choice dist env) :
    ClassicalMessage program ValueWord :=
  .oracleCallback
    { node := event.node
      choice := BitVec.ofNat 256 choice }

omit [DecidableEq Address] in
theorem contextualize_encodeCommit
    (codec : StorageCodec program) (context : CallContext Address)
    {state : program.State} {who : Player} {whoAddress : Address}
    (action : CommitAction program.graph who)
    (step : CommitStep program.graph state.1 who action)
    (hsender : context.sender = whoAddress) :
    contextualize context (encodeCommit codec action step) =
      .player
        { caller := whoAddress
          player := who
          node := action.node
          value := codec.encodeValue step.guard.ty step.value } := by
  simp [contextualize, encodeCommit, PlayerMessage.encodeCommit, hsender]

omit [DecidableEq Address] in
/-- A valid fixed-policy callback is represented exactly when its retained
table index fits in one unsigned EVM word. -/
theorem contextualize_encodeOracleCallback
    (context : CallContext Address) (oracle : OracleRegistry Address)
    (event : InternalEvent program.graph)
    {dist : EventDist L} {env : ReadEnv L dist.reads}
    (choice : OraclePolicy.Choice dist env)
    (hsender : context.sender = oracle.address)
    (hfits : (choice : Nat) < 2 ^ 256) :
    contextualize context
        (encodeOracleCallback (ValueWord := ValueWord) event choice) =
      .oracleCallback (OracleCalldata.encode oracle event choice) := by
  have hnat : (BitVec.ofNat 256 (choice : Nat)).toNat = choice := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfits]
  simp [contextualize, encodeOracleCallback, OracleCalldata.encode,
    hsender, hnat]

end ClassicalMessage

/-- Four pairwise-distinct selectors for the deterministic classical entry
points. -/
structure ClassicalSelectors where
  player : Selector
  reveal : Selector
  sampleRequest : Selector
  oracleCallback : Selector
  player_ne_reveal : player ≠ reveal
  player_ne_sampleRequest : player ≠ sampleRequest
  player_ne_oracleCallback : player ≠ oracleCallback
  reveal_ne_sampleRequest : reveal ≠ sampleRequest
  reveal_ne_oracleCallback : reveal ≠ oracleCallback
  sampleRequest_ne_oracleCallback : sampleRequest ≠ oracleCallback

/-- Complete word-framing configuration for the classical contract. -/
structure ClassicalABI (program : Program Player L) (ValueWord : Type) where
  selectors : ClassicalSelectors
  players : WireCodec Player Word
  nodes : WireCodec (Fin program.graph.nodeCount) Word
  values : WireCodec ValueWord Word

namespace ClassicalABI

/-- Encode a decoded classical message to selector-framed EVM words. -/
def encode (abi : ClassicalABI program ValueWord) :
    ClassicalMessage program ValueWord → Calldata Word
  | .player message =>
      { selector := abi.selectors.player
        arguments :=
          [abi.players.encode message.player,
            abi.nodes.encode message.node,
            abi.values.encode message.value] }
  | .reveal message =>
      { selector := abi.selectors.reveal
        arguments := [abi.nodes.encode message.node] }
  | .sampleRequest message =>
      { selector := abi.selectors.sampleRequest
        arguments := [abi.nodes.encode message.node] }
  | .oracleCallback message =>
      { selector := abi.selectors.oracleCallback
        arguments := [abi.nodes.encode message.node, message.choice] }

/-- Decode only the four recognized selectors with their exact arities and
certified player/node/value word codecs. -/
def decode (abi : ClassicalABI program ValueWord) (calldata : Calldata Word) :
    Option (ClassicalMessage program ValueWord) :=
  if calldata.selector = abi.selectors.player then
    match calldata.arguments with
    | [playerWord, nodeWord, valueWord] =>
        match abi.players.decode playerWord, abi.nodes.decode nodeWord,
            abi.values.decode valueWord with
        | some player, some node, some value =>
            some (.player { player := player, node := node, value := value })
        | _, _, _ => none
    | _ => none
  else if calldata.selector = abi.selectors.reveal then
    match calldata.arguments with
    | [nodeWord] =>
        (abi.nodes.decode nodeWord).map fun node => .reveal { node := node }
    | _ => none
  else if calldata.selector = abi.selectors.sampleRequest then
    match calldata.arguments with
    | [nodeWord] =>
        (abi.nodes.decode nodeWord).map fun node =>
          .sampleRequest { node := node }
    | _ => none
  else if calldata.selector = abi.selectors.oracleCallback then
    match calldata.arguments with
    | [nodeWord, choice] =>
        (abi.nodes.decode nodeWord).map fun node =>
          .oracleCallback { node := node, choice := choice }
    | _ => none
  else
    none

@[simp] theorem decode_encode (abi : ClassicalABI program ValueWord)
    (message : ClassicalMessage program ValueWord) :
    abi.decode (abi.encode message) = some message := by
  cases message with
  | player message =>
      simp [decode, encode, abi.players.decode_encode,
        abi.nodes.decode_encode, abi.values.decode_encode]
  | reveal message =>
      have hne : abi.selectors.reveal ≠ abi.selectors.player :=
        Ne.symm abi.selectors.player_ne_reveal
      simp [decode, encode, hne, abi.nodes.decode_encode]
  | sampleRequest message =>
      have hp : abi.selectors.sampleRequest ≠ abi.selectors.player :=
        Ne.symm abi.selectors.player_ne_sampleRequest
      have hr : abi.selectors.sampleRequest ≠ abi.selectors.reveal :=
        Ne.symm abi.selectors.reveal_ne_sampleRequest
      simp [decode, encode, hp, hr, abi.nodes.decode_encode]
  | oracleCallback message =>
      have hp : abi.selectors.oracleCallback ≠ abi.selectors.player :=
        Ne.symm abi.selectors.player_ne_oracleCallback
      have hr : abi.selectors.oracleCallback ≠ abi.selectors.reveal :=
        Ne.symm abi.selectors.reveal_ne_oracleCallback
      have hs :
          abi.selectors.oracleCallback ≠ abi.selectors.sampleRequest :=
        Ne.symm abi.selectors.sampleRequest_ne_oracleCallback
      simp [decode, encode, hp, hr, hs, abi.nodes.decode_encode]

/-- The four-entry-point word framing is a lossless wire codec. -/
def wireCodec (abi : ClassicalABI program ValueWord) :
    WireCodec (ClassicalMessage program ValueWord) (Calldata Word) where
  encode := abi.encode
  decode := abi.decode
  decode_encode := abi.decode_encode

end ClassicalABI

end Vegas.Machine.Contract.EVM

namespace Vegas.Machine.Contract.ClassicalContract

open Blockchain

variable {Player Address : Type}
variable [DecidableEq Player] [DecidableEq Address]
variable {L : IExpr} {program : Program Player L}
variable (contract : ClassicalContract program Address)

/-- Decode and execute selector-framed classical calldata. Framing failure is
distinguished from a well-framed call rejected by the typed contract. -/
def receiveEVMCalldata (abi : EVM.ClassicalABI program contract.codec.Word)
    (context : CallContext Address) (state : contract.State)
    (calldata : EVM.Calldata EVM.Word) :
    DeterministicResult contract.State OracleProtocol.Request :=
  match abi.decode calldata with
  | none => .revert .malformed
  | some message => contract.receive state (message.contextualize context)

/-- Selector/word framing is behaviorally transparent for every decoded
classical message. -/
@[simp] theorem receiveEVMCalldata_encode
    (abi : EVM.ClassicalABI program contract.codec.Word)
    (context : CallContext Address) (state : contract.State)
    (message : EVM.ClassicalMessage program contract.codec.Word) :
    contract.receiveEVMCalldata abi context state (abi.encode message) =
      contract.receive state (message.contextualize context) := by
  simp [receiveEVMCalldata, abi.decode_encode]

/-- Unknown selectors, arities, or undecodable words revert as malformed
before typed contract validation. -/
theorem receiveEVMCalldata_revert_malformed
    (abi : EVM.ClassicalABI program contract.codec.Word)
    (context : CallContext Address) (state : contract.State)
    (calldata : EVM.Calldata EVM.Word)
    (hdecode : abi.decode calldata = none) :
    contract.receiveEVMCalldata abi context state calldata =
      .revert .malformed := by
  simp [receiveEVMCalldata, hdecode]

end Vegas.Machine.Contract.ClassicalContract
