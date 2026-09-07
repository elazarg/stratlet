/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasEVM.Contract.DeterministicExecutor
import VegasEVM.Contract.OracleProtocol
import VegasEVM.Contract.Transaction

/-!
# Complete deterministic classical contract

`ClassicalContract` composes authenticated player commitments, deterministic
reveals, asynchronous oracle requests, and authenticated oracle callbacks into
one rollback-ready contract.  Every invocation is deterministic.  Source
chance reappears only after fixing the trusted oracle's known behavioral
policy over callback indices.

This is the endpoint of the ordinary classical compiler.  It assumes a fair
trusted oracle and request scheduler, and it treats player commitment values
as typed inputs whose information exposure is controlled by a later ideal
commitment/batching layer.  It is not the secure compiler and is not yet an EVM
artifact.
-/

noncomputable section

namespace Vegas.Machine.Contract

open EventGraph
open Blockchain
open GameTheory.Math.Probability

variable {Player Address : Type}
variable [DecidableEq Player] [DecidableEq Address]
variable {L : IExpr} {program : Program Player L}

/-- All trusted deployment choices for the deterministic classical contract. -/
structure ClassicalContract (program : Program Player L) (Address : Type)
    [DecidableEq Address] where
  codec : StorageCodec program
  players : PlayerRegistry Player Address
  reveals : TriggerPolicy Address
  sampleRequests : TriggerPolicy Address
  oracle : OracleRegistry Address

/-- The complete typed transaction surface of the classical contract. -/
inductive ClassicalCalldata
    (Player Address Word : Type) where
  | player (call : PlayerCalldata Player Address Word)
  | reveal (call : InternalCalldata Address)
  | sampleRequest (call : OracleProtocol.RequestCalldata Address)
  | oracleCallback (call : OracleCalldata Address)

/-- Caller-free trusted-oracle callback arguments at the generic blockchain
boundary. -/
structure ClassicalOracleMessage
    (program : Program Player L) where
  node : Fin program.graph.nodeCount
  choice : Nat

/-- Complete caller-free typed surface of the classical contract. Physical
identity is attached exclusively from the blockchain call context. -/
inductive ClassicalMessage
    (program : Program Player L) (Word : Type) where
  | player (message : Blockchain.PlayerMessage program Word)
  | reveal (message : Blockchain.InternalMessage program)
  | sampleRequest (message : Blockchain.InternalMessage program)
  | oracleCallback (message : ClassicalOracleMessage program)

namespace ClassicalMessage

/-- Attach the authenticated blockchain sender to typed message arguments. -/
def contextualize {Word : Type} (context : CallContext Address) :
    ClassicalMessage program Word → ClassicalCalldata Player Address Word
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
          choice := message.choice }

end ClassicalMessage

namespace ClassicalContract

variable (contract : ClassicalContract program Address)

abbrev State := OracleProtocol.State contract.codec
abbrev Calldata :=
  ClassicalCalldata Player Address contract.codec.Word
abbrev Message := ClassicalMessage program contract.codec.Word
abbrev Action := OracleProtocol.Request

/-- Canonical deployment state with no pending oracle interaction. -/
def initial : contract.State :=
  OracleProtocol.idleState contract.codec program.init

/-- Canonical idle representation of one reachable semantic machine state. -/
def encodeState (state : program.State) : contract.State :=
  OracleProtocol.idleState contract.codec state

/-- Deterministically dispatch one typed invocation.  While an oracle request
is pending, only its matching callback can succeed. -/
def receive (state : contract.State) :
    contract.Calldata →
      DeterministicResult contract.State OracleProtocol.Request
  | .player call =>
      if state.pending.isSome then
        .revert .rejected
      else
        match PlayerCalldata.executeDeterministicStore?
            contract.players contract.codec state.store call with
        | none => .revert .rejected
        | some nextStore =>
            .success (CallSuccess.silent
              { store := nextStore, pending := none })
  | .reveal call =>
      if state.pending.isSome then
        .revert .rejected
      else
        match InternalCalldata.executeDeterministicStore?
            (program := program) contract.reveals contract.codec
            state.store call with
        | none => .revert .rejected
        | some nextStore =>
            .success (CallSuccess.silent
              { store := nextStore, pending := none })
  | .sampleRequest call =>
      if state.pending.isSome then
        .revert .rejected
      else
        match OracleProtocol.request? (program := program)
            contract.sampleRequests contract.codec state call with
        | none => .revert .rejected
        | some result => .success result
  | .oracleCallback call =>
      match OracleProtocol.callback? (program := program)
          contract.oracle contract.codec state call with
      | none => .revert .rejected
      | some next => .success (CallSuccess.silent next)

/-- Package the classical compiler endpoint as a deterministic blockchain
contract. The physical caller is taken only from `context.sender`; it cannot
be forged in the message body. -/
def toDeterministicContract :
    DeterministicContract Address contract.Message contract.State
      OracleProtocol.Request Unit where
  initial := contract.initial
  receive := fun _chain context state message _unit =>
    contract.receive state (message.contextualize context)

/-- Generic artifact execution obtains every authenticated identity from the
blockchain context. -/
@[simp] theorem toDeterministicContract_receive
    (chain : ChainView) (context : CallContext Address)
    (state : contract.State) (message : contract.Message) :
    contract.toDeterministicContract.receive chain context state message () =
      contract.receive state (message.contextualize context) :=
  rfl

/-- A valid semantic commitment executes to its unique canonical stored
successor with no outbound action. -/
theorem receive_encodeState_playerCommit
    (state : program.State) (who : Player)
    (action : CommitAction program.graph who)
    (step : CommitStep program.graph state.1 who action) :
    contract.receive (contract.encodeState state)
        (.player
          (PlayerCalldata.encodeCommit contract.players contract.codec
            action step)) =
      .success (CallSuccess.silent
        { store := RawStore.encodeSnapshot contract.codec
            (StateSnapshot.ofConfig
              (state.1.completeNode action.node
                { ty := step.guard.ty, value := step.value }))
          pending := none }) := by
  unfold receive encodeState OracleProtocol.idleState
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  rw [PlayerCalldata.executeDeterministicStore?_encodeCommit]

/-- A valid authorized reveal executes to its unique canonical stored
successor with no outbound action. -/
theorem receive_encodeState_reveal
    (caller : Address) (state : program.State)
    (event : InternalEvent program.graph)
    (row : EventNode Player L) (source : Nat)
    (rowGet : program.graph.nodes[event.node]? = some row)
    (semEq : row.sem = .reveal source)
    (ready : Ready program.graph state.1 event.node)
    (value : L.Val row.ty)
    (valueOk : Store.getAs state.1.store source row.ty = some value)
    (authorized : contract.reveals.allows caller event.node = true) :
    contract.receive (contract.encodeState state)
        (.reveal (InternalCalldata.encode caller event)) =
      .success (CallSuccess.silent
        { store := RawStore.encodeSnapshot contract.codec
            (StateSnapshot.ofConfig
              (state.1.completeNode event.node
                { ty := row.ty, value := value }))
          pending := none }) := by
  unfold receive encodeState OracleProtocol.idleState
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  rw [InternalCalldata.executeDeterministicStore?_encodeReveal
    contract.reveals contract.codec caller state event row source rowGet semEq
    ready value valueOk authorized]

/-- A valid authorized sample request is an administrative state change that
emits exactly one ordered oracle request. -/
theorem receive_encodeState_sampleRequest
    (caller : Address) (state : program.State)
    (event : InternalEvent program.graph)
    (row : EventNode Player L) (dist : EventDist L)
    (rowGet : program.graph.nodes[event.node]? = some row)
    (semEq : row.sem = .sample dist)
    (ready : Ready program.graph state.1 event.node)
    (env : ReadEnv L dist.reads)
    (envOk : ReadEnv.ofStore? state.1.store dist.reads = some env)
    (authorized :
      contract.sampleRequests.allows caller event.node = true) :
    contract.receive (contract.encodeState state)
        (.sampleRequest { caller := caller, node := event.node }) =
      .success
        { state := OracleProtocol.waitingState contract.codec state event
          actions := [{ node := event.node }] } := by
  have hrequest :=
    OracleProtocol.request?_encodeState_sample contract.sampleRequests
      contract.codec caller state event row dist rowGet semEq ready env envOk
      authorized
  simp only [OracleProtocol.idleState] at hrequest
  unfold receive encodeState
  simp only [OracleProtocol.idleState, Option.isSome_none, Bool.false_eq_true,
    ↓reduceIte]
  rw [hrequest]

/-- Every callback selected by the fixed oracle policy succeeds from its
waiting state. -/
theorem receive_waitingState_oracleCallback
    (state : program.State)
    (event : InternalEvent program.graph)
    (row : EventNode Player L) (dist : EventDist L)
    (rowGet : program.graph.nodes[event.node]? = some row)
    (semEq : row.sem = .sample dist)
    (ready : Ready program.graph state.1 event.node)
    (env : ReadEnv L dist.reads)
    (envOk : ReadEnv.ofStore? state.1.store dist.reads = some env)
    (choice : OraclePolicy.Choice dist env) :
    contract.receive (OracleProtocol.waitingState contract.codec state event)
        (.oracleCallback
          (OracleCalldata.encode contract.oracle event choice)) =
      .success (CallSuccess.silent
        { store := RawStore.encodeSnapshot contract.codec
            (StateSnapshot.ofConfig
              (OraclePolicy.realizeChoice state.1 event dist env choice))
          pending := none }) := by
  have hcallback :=
    OracleProtocol.callback?_waitingState_encode contract.oracle
      contract.codec state event row dist rowGet semEq ready env envOk choice
  simp only [receive]
  rw [hcallback]

/-- The complete deterministic callback entry point, under the trusted
oracle's fixed strategy, induces exactly the source machine sample law. -/
theorem map_receive_oracle_fixedPolicy
    (state : program.State)
    (event : InternalEvent program.graph)
    (row : EventNode Player L) (dist : EventDist L)
    (rowGet : program.graph.nodes[event.node]? = some row)
    (semEq : row.sem = .sample dist)
    (ready : Ready program.graph state.1 event.node)
    (env : ReadEnv L dist.reads)
    (envOk : ReadEnv.ofStore? state.1.store dist.reads = some env) :
    (OraclePolicy.choiceLaw dist env).map
        (fun choice =>
          contract.receive
            (OracleProtocol.waitingState contract.codec state event)
            (.oracleCallback
              (OracleCalldata.encode contract.oracle event choice))) =
      (program.step state
        (.internal event
          (.sample row dist rowGet semEq ready env envOk))).map
            (fun next =>
              DeterministicResult.success
                (CallSuccess.silent (contract.encodeState next))) := by
  calc
    (OraclePolicy.choiceLaw dist env).map
        (fun choice =>
          contract.receive
            (OracleProtocol.waitingState contract.codec state event)
            (.oracleCallback
              (OracleCalldata.encode contract.oracle event choice))) =
      (OraclePolicy.choiceLaw dist env).map
        (fun choice =>
          DeterministicResult.success (CallSuccess.silent
            ((OracleProtocol.callback? (program := program)
              contract.oracle contract.codec
              (OracleProtocol.waitingState contract.codec state event)
              (OracleCalldata.encode contract.oracle event choice)).getD
                (OracleProtocol.waitingState contract.codec state event)))) := by
        apply FinDist.map_congr_of_eq_on_support
        intro choice _supported
        rw [receive_waitingState_oracleCallback contract state event row dist
          rowGet semEq ready env envOk choice]
        rw [OracleProtocol.callback?_waitingState_encode contract.oracle
          contract.codec state event row dist rowGet semEq ready env envOk
          choice]
        simp
    _ = ((OraclePolicy.choiceLaw dist env).map
          (fun choice =>
            (OracleProtocol.callback? (program := program)
              contract.oracle contract.codec
              (OracleProtocol.waitingState contract.codec state event)
              (OracleCalldata.encode contract.oracle event choice)).getD
                (OracleProtocol.waitingState contract.codec state event))).map
          (fun next =>
            DeterministicResult.success (CallSuccess.silent next)) := by
        rw [FinDist.map_comp]
        rfl
    _ = ((program.step state
          (.internal event
            (.sample row dist rowGet semEq ready env envOk))).map
              (fun next => contract.encodeState next)).map
          (fun next =>
            DeterministicResult.success (CallSuccess.silent next)) := by
        rw [OracleProtocol.map_callback?_fixedPolicy contract.oracle
          contract.codec state event row dist rowGet semEq ready env envOk]
        rfl
    _ = (program.step state
          (.internal event
            (.sample row dist rowGet semEq ready env envOk))).map
            (fun next =>
              DeterministicResult.success
                (CallSuccess.silent (contract.encodeState next))) := by
        unfold encodeState
        rw [FinDist.map_comp]
        rfl

/-- Terminal readout is available only when no oracle callback is pending. -/
def terminalPayout? (state : contract.State) : Option (Payout Player) :=
  if state.pending.isSome then
    none
  else
    Contract.terminalPayout? program contract.codec state.store

/-- Terminal reachable machine state has exactly the retained payoff at the
classical compiler endpoint. -/
theorem terminalPayout?_encodeState_of_terminal
    (state : program.State) (terminal : program.terminal state) :
    contract.terminalPayout? (contract.encodeState state) =
      evalPayoffs? program.payoffs state.1.store := by
  unfold terminalPayout? encodeState OracleProtocol.idleState
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  exact Contract.terminalPayout?_encodeState_of_terminal
    program contract.codec state terminal

end ClassicalContract

end Vegas.Machine.Contract
