/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Machine.Contract.Calldata
import Vegas.Machine.Contract.InternalCalldata
import Vegas.Machine.Contract.Lifecycle

/-!
# Configured target-neutral contracts

`ConfiguredContract` is the first whole-contract compiler target. It packages
one machine program with its word representation, player-address registry, and
internal-trigger authorization policy. Its transaction type is a typed sum of
the separately certified player and internal entry points.

This object remains target-neutral. A backend must still assign byte selectors,
serialize addresses and words, lower expressions, realize entropy, model
reverts and gas, and prove the corresponding trace and strategic properties.
-/

noncomputable section

namespace Vegas.Machine.Contract

open EventGraph

variable {Player Address : Type}
variable [DecidableEq Player] [DecidableEq Address]
variable {L : IExpr} {program : Program Player L}

/-- Deployment choices that configure the target-neutral contract boundary. -/
structure ConfiguredContract (program : Program Player L) (Address : Type)
    [DecidableEq Address] where
  codec : StorageCodec program
  players : PlayerRegistry Player Address
  triggers : TriggerPolicy Address

/-- The complete typed transaction surface before byte-level ABI lowering. -/
inductive ContractCalldata (Player Address Word : Type) where
  | player (call : PlayerCalldata Player Address Word)
  | internal (call : InternalCalldata Address)

namespace ConfiguredContract

variable (contract : ConfiguredContract program Address)

/-- Canonical finite logical inventory exposed to an emitter. -/
def manifest : Manifest program := Contract.compile program

/-- Canonical certified storage layout used by the configured contract. -/
def layout : Layout program := Layout.canonical program

/-- Raw configured-contract storage. -/
abbrev Store := RawStore contract.codec

/-- Typed word-level transactions accepted by the configured contract. -/
abbrev Calldata := ContractCalldata Player Address contract.codec.Word

/-- Canonical constructor storage for the configured contract. -/
def initialStore : contract.Store :=
  Contract.initialStore program contract.codec

/-- Validate one typed word-level transaction against raw storage. -/
def accepts (store : contract.Store) : contract.Calldata → Bool
  | .player call =>
      PlayerCalldata.acceptsStore (program := program)
        contract.players contract.codec store call
  | .internal call =>
      InternalCalldata.acceptsStore (program := program)
        contract.triggers contract.codec store call

/-- Execute one typed word-level transaction against raw storage. -/
def execute? (store : contract.Store) :
    contract.Calldata →
      Option (GameTheory.Math.Probability.FinDist contract.Store)
  | .player call =>
      PlayerCalldata.executeStore? (program := program)
        contract.players contract.codec store call
  | .internal call =>
      InternalCalldata.executeStore? (program := program)
        contract.triggers contract.codec store call

/-- Configured transaction execution succeeds exactly when validation
accepts. -/
theorem execute?_isSome (store : contract.Store)
    (calldata : contract.Calldata) :
    (contract.execute? store calldata).isSome =
      contract.accepts store calldata := by
  cases calldata with
  | player call =>
      exact PlayerCalldata.executeStore?_isSome
        contract.players contract.codec store call
  | internal call =>
      exact InternalCalldata.executeStore?_isSome
        contract.triggers contract.codec store call

/-- A valid semantic player commit survives whole-contract dispatch exactly:
the successor law is `Machine.step` transported through canonical raw
storage. -/
theorem execute?_encodeState_playerCommit
    {state : program.State} {who : Player}
    (action : CommitAction program.graph who)
    (step : CommitStep program.graph state.1 who action) :
    contract.execute? (RawStore.encodeState contract.codec state)
        (.player
          (PlayerCalldata.encodeCommit contract.players contract.codec
            action step)) =
      some ((program.step state (.commit who action step)).map
        (RawStore.encodeState contract.codec)) := by
  exact PlayerCalldata.executeStore?_encodeState_encodeCommit
    contract.players contract.codec action step

/-- A valid semantic internal event submitted by an authorized caller also
survives whole-contract dispatch exactly. -/
theorem execute?_encodeState_internal
    (caller : Address) {state : program.State}
    (event : InternalEvent program.graph)
    (step : InternalStep program.graph state.1 event)
    (hauthorized : contract.triggers.allows caller event.node = true) :
    contract.execute? (RawStore.encodeState contract.codec state)
        (.internal (InternalCalldata.encode caller event)) =
      some ((program.step state (.internal event step)).map
        (RawStore.encodeState contract.codec)) := by
  exact InternalCalldata.executeStore?_encodeState_encode
    contract.triggers contract.codec caller event step hauthorized

/-- Every configured transaction accepted against encoded reachable storage
executes as some valid semantic machine command. -/
theorem execute?_encodeState_of_accepts
    (state : program.State) (calldata : contract.Calldata)
    (haccept :
      contract.accepts (RawStore.encodeState contract.codec state)
        calldata = true) :
    ∃ command : program.Command state,
      contract.execute? (RawStore.encodeState contract.codec state) calldata =
        some ((program.step state command).map
          (RawStore.encodeState contract.codec)) := by
  cases calldata with
  | player call =>
      exact PlayerCalldata.executeStore?_encodeState_of_accepts
        contract.players contract.codec state call haccept
  | internal call =>
      exact InternalCalldata.executeStore?_encodeState_of_accepts
        contract.triggers contract.codec state call haccept

/-- Read terminal settlement data through the configured contract. -/
def terminalPayout? (store : contract.Store) : Option (Payout Player) :=
  Contract.terminalPayout? program contract.codec store

/-- Constructor storage decodes to the initial finite graph state. -/
@[simp] theorem decodeSnapshot_initialStore :
    RawStore.decodeSnapshot (program := program) contract.codec
        contract.initialStore =
      some (StateSnapshot.ofConfig program.init.1) := by
  exact Contract.decodeSnapshot_initialStore program contract.codec

/-- Terminal reachable storage exposes exactly the retained machine payoff
through the configured contract. -/
theorem terminalPayout?_encodeState_of_terminal
    (state : program.State) (hterminal : program.terminal state) :
    contract.terminalPayout? (RawStore.encodeState contract.codec state) =
      evalPayoffs? program.payoffs state.1.store := by
  exact Contract.terminalPayout?_encodeState_of_terminal
    program contract.codec state hterminal

end ConfiguredContract

end Vegas.Machine.Contract
