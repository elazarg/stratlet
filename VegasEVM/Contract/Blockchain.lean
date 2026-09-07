/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasEVM.Contract.Configured

/-!
# Stochastic blockchain contract boundary

This pass separates transaction context from caller-supplied message data and
adds a minimal blockchain view. Its shape is suitable for later connection to
contract execution frameworks: a contract receives a chain view, call context,
current state, and message.

Vegas chance transitions are still exact `FinDist` laws, so this interface is
intentionally stochastic. A deterministic blockchain contract cannot implement
it until a later pass replaces each internal probability law with a concrete
entropy protocol and states the associated adversarial assumptions.

Height, slot, origin, contract address, balances, and transferred amount are
introduced but ignored by the configured Vegas transition. This makes their
semantic inertness explicit before later passes use them for timing, payments,
or entropy.
-/

noncomputable section

namespace Vegas.Machine.Contract.Blockchain

open EventGraph

variable {Player Address : Type}
variable [DecidableEq Player] [DecidableEq Address]
variable {L : IExpr} {program : Program Player L}

/-- Read-only chain data supplied to one contract invocation. -/
structure ChainView where
  height : Nat
  slot : Nat
  finalizedHeight : Nat

/-- Invocation metadata supplied by the blockchain rather than serialized in
the message body. Amounts remain mathematical integers at this layer. -/
structure CallContext (Address : Type) where
  origin : Address
  sender : Address
  contractAddress : Address
  contractBalance : Int
  transferredAmount : Int

/-- Player entry-point arguments after bounded-node decoding and excluding the
physical caller. -/
structure PlayerMessage {Player : Type} [DecidableEq Player] {L : IExpr}
    (program : Program Player L) (Word : Type) where
  player : Player
  node : Fin program.graph.nodeCount
  value : Word

/-- Internal entry-point arguments after bounded-node decoding and excluding
the physical caller. -/
structure InternalMessage {Player : Type} [DecidableEq Player] {L : IExpr}
    (program : Program Player L) where
  node : Fin program.graph.nodeCount

/-- Caller-free configured-contract messages. -/
inductive Message {Player : Type} [DecidableEq Player] {L : IExpr}
    (program : Program Player L) (Word : Type) where
  | player (message : PlayerMessage program Word)
  | internal (message : InternalMessage program)

/-- Why a blockchain-facing invocation reverted at the current boundary. -/
inductive RevertReason where
  | malformed
  | rejected
deriving DecidableEq

/-- State and ordered outbound actions produced by one successful call. This
matches the shape used by contract frameworks while leaving the action type
runtime-specific. -/
structure CallSuccess (State Action : Type) where
  state : State
  actions : List Action

namespace CallSuccess

/-- A successful state transition that emits no outbound actions. -/
def silent {State Action : Type} (state : State) : CallSuccess State Action where
  state := state
  actions := []

/-- Lift a state law to a call-success law with an empty action trace. -/
def silentLaw {State : Type} (Action : Type)
    (law : GameTheory.Math.Probability.FinDist State) :
    GameTheory.Math.Probability.FinDist (CallSuccess State Action) :=
  law.map silent

end CallSuccess

/-- Explicit blockchain-facing result with a stochastic law over state and
outbound actions. -/
inductive ReceiveResult (State Action : Type) where
  | success (law :
      GameTheory.Math.Probability.FinDist (CallSuccess State Action))
  | revert (reason : RevertReason)

namespace ReceiveResult

/-- Executable success projection used to relate results to validators. -/
def succeeded {State Action : Type} : ReceiveResult State Action → Bool
  | .success _ => true
  | .revert _ => false

end ReceiveResult

/-- A contract interface whose successful receive function may have a finite
stochastic law over successor state and outbound actions. -/
structure StochasticContract (Address Message State Action : Type) where
  initial : State
  receive :
    ChainView → CallContext Address → State → Message →
      ReceiveResult State Action

namespace PlayerMessage

/-- Encode a valid semantic commit without duplicating the authenticated
physical sender in the message body. -/
def encodeCommit (codec : StorageCodec program)
    {state : program.State} {who : Player}
    (action : CommitAction program.graph who)
    (step : CommitStep program.graph state.1 who action) :
    PlayerMessage program codec.Word where
  player := who
  node := action.node
  value := codec.encodeValue step.guard.ty step.value

end PlayerMessage

namespace InternalMessage

/-- Encode a valid graph-directed internal event. -/
def encode (event : InternalEvent program.graph) : InternalMessage program where
  node := event.node

end InternalMessage

namespace Message

/-- Attach the authenticated blockchain sender to caller-free message data. -/
def contextualize {Word : Type} (context : CallContext Address) :
    Message program Word → ContractCalldata Player Address Word
  | .player message =>
      .player
        { caller := context.sender
          player := message.player
          node := message.node
          value := message.value }
  | .internal message =>
      .internal
        { caller := context.sender
          node := message.node }

end Message

end Vegas.Machine.Contract.Blockchain

namespace Vegas.Machine.Contract.ConfiguredContract

open EventGraph Blockchain

variable {Player Address : Type}
variable [DecidableEq Player] [DecidableEq Address]
variable {L : IExpr} {program : Program Player L}

variable (contract : ConfiguredContract program Address)

/-- Caller-free message type for this configured contract. -/
abbrev Message := Blockchain.Message program contract.codec.Word

/-- Contextual validation. Only `context.sender` is operational at this pass. -/
def acceptsMessage (context : CallContext Address) (store : contract.Store)
    (message : contract.Message) : Bool :=
  contract.accepts store (message.contextualize context)

/-- Contextual execution with explicit semantic rejection. Chain metadata is
deliberately inert at this pass. -/
def receive (_chain : ChainView) (context : CallContext Address)
    (store : contract.Store) (message : contract.Message) :
    ReceiveResult contract.Store Empty :=
  match contract.execute? store (message.contextualize context) with
  | none => .revert .rejected
  | some law => .success (CallSuccess.silentLaw Empty law)

/-- Package the configured contract at the stochastic blockchain boundary. -/
def toStochasticContract :
  StochasticContract Address contract.Message contract.Store Empty where
  initial := contract.initialStore
  receive := contract.receive

/-- Contextual receive succeeds exactly when contextual validation accepts. -/
theorem receive_succeeded (chain : ChainView) (context : CallContext Address)
    (store : contract.Store) (message : contract.Message) :
    (contract.receive chain context store message).succeeded =
      contract.acceptsMessage context store message := by
  unfold receive
  cases h : contract.execute? store (message.contextualize context) with
  | none =>
      simpa [ReceiveResult.succeeded, acceptsMessage, h] using
        contract.execute?_isSome store (message.contextualize context)
  | some law =>
      simpa [ReceiveResult.succeeded, acceptsMessage, h] using
        contract.execute?_isSome store (message.contextualize context)

/-- A semantic player commit submitted by its registered sender retains the
exact stored machine-step law in every otherwise arbitrary chain context. -/
theorem receive_encodeState_playerCommit
    (chain : ChainView) (context : CallContext Address)
    {state : program.State} {who : Player}
    (action : CommitAction program.graph who)
    (step : CommitStep program.graph state.1 who action)
    (hsender : context.sender = contract.players.address who) :
    contract.receive chain context
        (RawStore.encodeState contract.codec state)
        (.player (PlayerMessage.encodeCommit contract.codec action step)) =
      .success (CallSuccess.silentLaw Empty
        ((program.step state (.commit who action step)).map
          (RawStore.encodeState contract.codec))) := by
  unfold receive Message.contextualize PlayerMessage.encodeCommit
  rw [hsender]
  have hexecute := contract.execute?_encodeState_playerCommit action step
  simp only [PlayerCalldata.encodeCommit] at hexecute
  rw [hexecute]

/-- An authorized internal event retains its exact stored machine-step law in
every otherwise arbitrary chain context. -/
theorem receive_encodeState_internal
    (chain : ChainView) (context : CallContext Address)
    {state : program.State}
    (event : InternalEvent program.graph)
    (step : InternalStep program.graph state.1 event)
    (hauthorized :
      contract.triggers.allows context.sender event.node = true) :
    contract.receive chain context
        (RawStore.encodeState contract.codec state)
        (.internal (InternalMessage.encode event)) =
      .success (CallSuccess.silentLaw Empty
        ((program.step state (.internal event step)).map
          (RawStore.encodeState contract.codec))) := by
  unfold receive Message.contextualize InternalMessage.encode
  have hexecute := contract.execute?_encodeState_internal
    context.sender event step hauthorized
  simp only [InternalCalldata.encode] at hexecute
  rw [hexecute]

/-- Every context/message pair accepted over encoded reachable storage
executes as a valid semantic command. Chain metadata and non-sender context
fields cannot create extra transitions at this pass. -/
theorem receive_encodeState_of_accepts
    (chain : ChainView) (context : CallContext Address)
    (state : program.State) (message : contract.Message)
    (haccept :
      contract.acceptsMessage context
        (RawStore.encodeState contract.codec state) message = true) :
    ∃ command : program.Command state,
      contract.receive chain context
          (RawStore.encodeState contract.codec state) message =
        .success (CallSuccess.silentLaw Empty
          ((program.step state command).map
            (RawStore.encodeState contract.codec))) := by
  rcases contract.execute?_encodeState_of_accepts
      state (message.contextualize context) haccept with
    ⟨command, hexecute⟩
  refine ⟨command, ?_⟩
  simp [receive, hexecute]

end Vegas.Machine.Contract.ConfiguredContract
