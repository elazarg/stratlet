/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasEVM.Contract.Blockchain
import VegasEVM.Contract.InternalCalldata
import VegasEVM.Contract.OracleCalldata

/-!
# Asynchronous trusted-oracle protocol

This pass splits one source chance transition into two deterministic contract
transactions.  A request transaction records a pending sample and emits an
ordered oracle request without changing semantic game storage.  While a
request is pending no second request is accepted.  An authenticated callback
supplies a retained probability-table index, clears the pending marker, and
performs the semantic sample update.

The request is administrative under projection to machine storage.  The
callback is not a command-by-command `Machine.Refinement`: one fixed callback
chooses one realization of a stochastic source command.  Instead, the fixed
oracle policy over all callbacks is proved to recover the exact source law.
Scheduler fairness, response timing, and the visibility of the pending marker
remain explicit assumptions for the classical compiler and later obligations
for a secure compiler.
-/

noncomputable section

namespace Vegas.Machine.Contract

open EventGraph
open Blockchain
open GameTheory.Math.Probability

variable {Player Address : Type}
variable [DecidableEq Player] [DecidableEq Address]
variable {L : IExpr} {program : Program Player L}

namespace OracleProtocol

/-- Contract state after introducing an asynchronous oracle phase. -/
structure State (codec : StorageCodec program) where
  store : RawStore codec
  pending : Option Nat

/-- Outbound request emitted to the trusted oracle. -/
structure Request where
  node : Nat
deriving DecidableEq

/-- Caller-bearing request to begin one available source sample. -/
structure RequestCalldata (Address : Type) where
  caller : Address
  node : Nat

/-- No oracle interaction is currently pending. -/
def idleState (codec : StorageCodec program) (state : program.State) :
    State codec where
  store := RawStore.encodeState codec state
  pending := none

/-- The protocol state waiting for the named semantic sample callback. -/
def waitingState (codec : StorageCodec program) (state : program.State)
    (event : InternalEvent program.graph) : State codec where
  store := RawStore.encodeState codec state
  pending := some event.node

/-- Begin an asynchronous sample.  Only sample rows can emit oracle requests;
commit and reveal rows retain their separate transaction paths. -/
def request? (policy : TriggerPolicy Address) (codec : StorageCodec program)
    (state : State codec) (calldata : RequestCalldata Address) :
    Option (CallSuccess (State codec) Request) :=
  if state.pending.isNone then
    if policy.allows calldata.caller calldata.node then
      if hnode : calldata.node < program.graph.nodeCount then
        let node : Fin program.graph.nodeCount := ⟨calldata.node, hnode⟩
        match (program.graph.nodeRow node).sem with
        | .sample _ =>
            let request : Contract.Request Player L :=
              { node := calldata.node
                authority := .internal
                payload := .none }
            if Contract.Request.acceptsStore
                (program := program) codec state.store request then
              some
                { state := { state with pending := some calldata.node }
                  actions := [{ node := calldata.node }] }
            else
              none
        | .commit _ _ | .reveal _ => none
      else
        none
    else
      none
  else
    none

omit [DecidableEq Address] in
/-- A valid available sample request changes only pending metadata and emits
exactly one request naming the sample node. -/
theorem request?_encodeState_sample
    (policy : TriggerPolicy Address) (codec : StorageCodec program)
    (caller : Address) (state : program.State)
    (event : InternalEvent program.graph)
    (row : EventNode Player L) (dist : EventDist L)
    (rowGet : program.graph.nodes[event.node]? = some row)
    (semEq : row.sem = .sample dist)
    (ready : Ready program.graph state.1 event.node)
    (env : ReadEnv L dist.reads)
    (envOk : ReadEnv.ofStore? state.1.store dist.reads = some env)
    (authorized : policy.allows caller event.node = true) :
    request? (program := program) policy codec (idleState codec state)
        { caller := caller, node := event.node } =
      some
        { state := waitingState codec state event
          actions := [{ node := event.node }] } := by
  have hrow : program.graph.nodeRow event.node = row := by
    have hget :
        program.graph.nodes[(event.node : Nat)]? = some row := rowGet
    rw [program.graph.nodes_get?_nodeRow event.node] at hget
    exact Option.some.inj hget
  have hsem :
      (program.graph.nodeRow event.node).sem = .sample dist := by
    rw [hrow]
    exact semEq
  have haccept :
      Contract.Request.acceptsStore (program := program) codec
          (RawStore.encodeState codec state)
          { node := event.node
            authority := .internal
            payload := .none } = true := by
    rw [Contract.Request.acceptsStore_encodeState]
    exact Contract.Request.accepts_encode
      (.internal event (.sample row dist rowGet semEq ready env envOk))
  simp [request?, idleState, waitingState, authorized, event.node.isLt, hsem,
    haccept]

/-- Consume one authenticated callback only when it names the unique pending
sample.  All other calls leave rollback to the surrounding transaction layer. -/
def callback? (oracle : OracleRegistry Address) (codec : StorageCodec program)
    (state : State codec) (calldata : OracleCalldata Address) :
    Option (State codec) :=
  match state.pending with
  | none => none
  | some pendingNode =>
      if calldata.node = pendingNode then
        (OracleCalldata.executeStore? (program := program) oracle codec
          state.store calldata).map fun nextStore =>
            { store := nextStore, pending := none }
      else
        none

/-- A matching fixed-policy callback consumes the pending request and stores
exactly the deterministic sample successor. -/
theorem callback?_waitingState_encode
    (oracle : OracleRegistry Address) (codec : StorageCodec program)
    (state : program.State)
    (event : InternalEvent program.graph)
    (row : EventNode Player L) (dist : EventDist L)
    (rowGet : program.graph.nodes[event.node]? = some row)
    (semEq : row.sem = .sample dist)
    (ready : Ready program.graph state.1 event.node)
    (env : ReadEnv L dist.reads)
    (envOk : ReadEnv.ofStore? state.1.store dist.reads = some env)
    (choice : OraclePolicy.Choice dist env) :
    callback? (program := program) oracle codec (waitingState codec state event)
        (OracleCalldata.encode oracle event choice) =
      some
        { store := RawStore.encodeSnapshot codec
            (StateSnapshot.ofConfig
              (OraclePolicy.realizeChoice state.1 event dist env choice))
          pending := none } := by
  have hexecute :=
    OracleCalldata.executeStore?_encodeState_encode oracle codec state event
      row dist rowGet semEq ready env envOk choice
  simp only [OracleCalldata.encode] at hexecute
  simp only [callback?, waitingState, OracleCalldata.encode, if_true]
  rw [hexecute]
  rfl

/-- Under the fixed trusted-oracle policy, consuming the pending callback has
exactly the encoded semantic machine-step law and always returns to idle. -/
theorem map_callback?_fixedPolicy
    (oracle : OracleRegistry Address) (codec : StorageCodec program)
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
          (callback? (program := program) oracle codec
            (waitingState codec state event)
            (OracleCalldata.encode oracle event choice)).getD
              (waitingState codec state event)) =
      (program.step state
        (.internal event
          (.sample row dist rowGet semEq ready env envOk))).map
            (fun next => idleState codec next) := by
  calc
    (OraclePolicy.choiceLaw dist env).map
        (fun choice =>
          (callback? (program := program) oracle codec
            (waitingState codec state event)
            (OracleCalldata.encode oracle event choice)).getD
              (waitingState codec state event)) =
      (OraclePolicy.choiceLaw dist env).map
        (fun choice =>
          { store := RawStore.encodeSnapshot codec
              (StateSnapshot.ofConfig
                (OraclePolicy.realizeChoice state.1 event dist env choice))
            pending := none }) := by
        apply FinDist.map_congr_of_eq_on_support
        intro choice _supported
        rw [callback?_waitingState_encode oracle codec state event row dist
          rowGet semEq ready env envOk choice]
        simp
    _ = ((OraclePolicy.choiceLaw dist env).map
          (OraclePolicy.realizeChoice state.1 event dist env)).map
            (fun cfg =>
              { store := RawStore.encodeSnapshot codec
                  (StateSnapshot.ofConfig cfg)
                pending := none }) := by
        rw [FinDist.map_comp]
        rfl
    _ = ((program.step state
          (.internal event
            (.sample row dist rowGet semEq ready env envOk))).map
              Subtype.val).map
            (fun cfg =>
              { store := RawStore.encodeSnapshot codec
                  (StateSnapshot.ofConfig cfg)
                pending := none }) := by
        rw [OraclePolicy.map_realizeChoice_choiceLaw_eq_machine state event row
          dist rowGet semEq ready env envOk]
    _ = (program.step state
          (.internal event
            (.sample row dist rowGet semEq ready env envOk))).map
              (fun next => idleState codec next) := by
        rw [FinDist.map_comp]
        rfl

end OracleProtocol

end Vegas.Machine.Contract
