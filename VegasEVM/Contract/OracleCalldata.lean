/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasEVM.Contract.OraclePolicy
import VegasEVM.Contract.State

/-!
# Deterministic trusted-oracle callbacks

Sample nodes are lowered to authenticated callbacks carrying an index into the
exact probability table evaluated at the current public state.  Execution is
fully deterministic once the callback is fixed.  The trusted oracle's fixed
policy over those indices is proved in `OraclePolicy` to recover the original
stochastic machine step.

The callback accepts every in-range table index from the configured oracle,
including an index whose retained weight is zero.  Such an index is never
selected by the fixed policy.  Rejecting or punishing a deviating oracle is a
separate secure-runtime concern and is intentionally not part of this
classical trusted-role compiler boundary.
-/

noncomputable section

namespace Vegas.Machine.Contract

open EventGraph

variable {Player Address : Type}
variable [DecidableEq Player] [DecidableEq Address]
variable {L : IExpr} {program : Program Player L}

/-- The physical identity trusted to realize source chance nodes. -/
structure OracleRegistry (Address : Type) where
  address : Address

/-- One authenticated deterministic sample callback.  `choice` is an index
into the exact table obtained by evaluating the named sample node. -/
structure OracleCalldata (Address : Type) where
  caller : Address
  node : Nat
  choice : Nat

namespace OracleCalldata

/-- Encode one fixed-policy oracle choice. -/
def encode (oracle : OracleRegistry Address)
    (event : InternalEvent program.graph)
    {dist : EventDist L} {env : ReadEnv L dist.reads}
    (choice : OraclePolicy.Choice dist env) : OracleCalldata Address where
  caller := oracle.address
  node := event.node
  choice := choice

/-- Authenticate, validate, and deterministically execute a sample callback on
a raw graph configuration.  Commit and reveal nodes are excluded. -/
def executeConfig? (oracle : OracleRegistry Address)
    (cfg : Config program.graph) (calldata : OracleCalldata Address) :
    Option (Config program.graph) :=
  if calldata.caller = oracle.address then
    if hnode : calldata.node < program.graph.nodeCount then
      let node : Fin program.graph.nodeCount := ⟨calldata.node, hnode⟩
      let row := program.graph.nodeRow node
      match row.sem with
      | .sample dist =>
          match ReadEnv.ofStoreExec? cfg.store dist.reads with
          | none => none
          | some env =>
              if Ready program.graph cfg node then
                let law := dist.evalLaw env
                if hchoice : calldata.choice < law.entries.length then
                  let choice : Fin law.entries.length :=
                    ⟨calldata.choice, hchoice⟩
                  some <| cfg.completeNode node
                    { ty := dist.ty, value := law.entryValue choice }
                else
                  none
              else
                none
      | .commit _ _ | .reveal _ => none
    else
      none
  else
    none

/-- A fixed-policy response for an available sample node executes to exactly
the deterministic realization selected by that table index. -/
theorem executeConfig?_encode
    (oracle : OracleRegistry Address)
    (state : program.State)
    (event : InternalEvent program.graph)
    (row : EventNode Player L) (dist : EventDist L)
    (rowGet : program.graph.nodes[event.node]? = some row)
    (semEq : row.sem = .sample dist)
    (ready : Ready program.graph state.1 event.node)
    (env : ReadEnv L dist.reads)
    (envOk : ReadEnv.ofStore? state.1.store dist.reads = some env)
    (choice : OraclePolicy.Choice dist env) :
    executeConfig? (program := program) oracle state.1
        (encode oracle event choice) =
      some (OraclePolicy.realizeChoice state.1 event dist env choice) := by
  have hrow : program.graph.nodeRow event.node = row := by
    have hget :
        program.graph.nodes[(event.node : Nat)]? = some row := rowGet
    rw [program.graph.nodes_get?_nodeRow event.node] at hget
    exact Option.some.inj hget
  have hsem :
      (program.graph.nodeRow event.node).sem = .sample dist := by
    rw [hrow]
    exact semEq
  have hexecSome :=
    ReadEnv.ofStoreExec?_isSome_of_ofStore?_eq_some envOk
  rcases Option.isSome_iff_exists.mp hexecSome with ⟨execEnv, hexecEnv⟩
  have hproofEnv :=
    ReadEnv.ofStore?_eq_some_of_ofStoreExec?_eq_some hexecEnv
  have henv : execEnv = env := by
    rw [envOk] at hproofEnv
    exact (Option.some.inj hproofEnv).symm
  subst execEnv
  simp [executeConfig?, encode, event.node.isLt, hsem, hexecEnv, ready,
    choice.isLt, OraclePolicy.realizeChoice]

/-- Running deterministic callbacks under the fixed oracle policy recovers
the exact raw machine sample law. -/
theorem map_executeConfig?_fixedPolicy
    (oracle : OracleRegistry Address)
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
          (executeConfig? (program := program) oracle state.1
            (encode oracle event choice)).getD state.1) =
      (program.step state
        (.internal event
          (.sample row dist rowGet semEq ready env envOk))).map Subtype.val := by
  apply Eq.trans _
    (OraclePolicy.map_realizeChoice_choiceLaw_eq_machine
      state event row dist rowGet semEq ready env envOk)
  apply GameTheory.Math.Probability.FinDist.map_congr_of_eq_on_support
  intro choice _supported
  rw [executeConfig?_encode oracle state event row dist rowGet semEq ready env
    envOk choice]
  simp

/-- Execute a deterministic callback against canonical raw contract storage. -/
def executeStore? (oracle : OracleRegistry Address)
    (codec : StorageCodec program) (store : RawStore codec)
    (calldata : OracleCalldata Address) : Option (RawStore codec) :=
  match RawStore.decodeSnapshot (program := program) codec store with
  | none => none
  | some snapshot =>
      (executeConfig? (program := program) oracle snapshot.toConfig calldata).map
        fun next => RawStore.encodeSnapshot codec (StateSnapshot.ofConfig next)

/-- A fixed-policy callback over encoded reachable state executes to the
canonical encoding of its deterministic graph successor. -/
theorem executeStore?_encodeState_encode
    (oracle : OracleRegistry Address)
    (codec : StorageCodec program)
    (state : program.State)
    (event : InternalEvent program.graph)
    (row : EventNode Player L) (dist : EventDist L)
    (rowGet : program.graph.nodes[event.node]? = some row)
    (semEq : row.sem = .sample dist)
    (ready : Ready program.graph state.1 event.node)
    (env : ReadEnv L dist.reads)
    (envOk : ReadEnv.ofStore? state.1.store dist.reads = some env)
    (choice : OraclePolicy.Choice dist env) :
    executeStore? (program := program) oracle codec
        (RawStore.encodeState codec state) (encode oracle event choice) =
      some (RawStore.encodeSnapshot codec
        (StateSnapshot.ofConfig
          (OraclePolicy.realizeChoice state.1 event dist env choice))) := by
  have hcanonical :=
    StateSnapshot.canonical_reachable program.graphWF state.2
  unfold executeStore?
  rw [RawStore.decodeSnapshot_encodeState]
  change
    (executeConfig? (program := program) oracle
      (StateSnapshot.ofConfig state.1).toConfig
      (encode oracle event choice)).map _ = _
  rw [hcanonical]
  rw [executeConfig?_encode oracle state event row dist rowGet semEq ready env
    envOk choice]
  rfl

/-- The deterministic stored callback under the fixed oracle policy has
exactly the stored semantic machine-step law. -/
theorem map_executeStore?_fixedPolicy
    (oracle : OracleRegistry Address)
    (codec : StorageCodec program)
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
          (executeStore? (program := program) oracle codec
            (RawStore.encodeState codec state)
            (encode oracle event choice)).getD
              (RawStore.encodeState codec state)) =
      (program.step state
        (.internal event
          (.sample row dist rowGet semEq ready env envOk))).map
            (RawStore.encodeState codec) := by
  let command : program.Command state :=
    .internal event (.sample row dist rowGet semEq ready env envOk)
  calc
    (OraclePolicy.choiceLaw dist env).map
        (fun choice =>
          (executeStore? (program := program) oracle codec
            (RawStore.encodeState codec state)
            (encode oracle event choice)).getD
              (RawStore.encodeState codec state)) =
      (OraclePolicy.choiceLaw dist env).map
        (fun choice =>
          RawStore.encodeSnapshot codec
            (StateSnapshot.ofConfig
              (OraclePolicy.realizeChoice state.1 event dist env choice))) := by
        apply GameTheory.Math.Probability.FinDist.map_congr_of_eq_on_support
        intro choice _supported
        rw [executeStore?_encodeState_encode oracle codec state event row dist
          rowGet semEq ready env envOk choice]
        simp
    _ = ((OraclePolicy.choiceLaw dist env).map
          (OraclePolicy.realizeChoice state.1 event dist env)).map
            (fun cfg =>
              RawStore.encodeSnapshot codec (StateSnapshot.ofConfig cfg)) := by
        rw [GameTheory.Math.Probability.FinDist.map_comp]
        rfl
    _ = ((program.step state command).map Subtype.val).map
            (fun cfg =>
              RawStore.encodeSnapshot codec (StateSnapshot.ofConfig cfg)) := by
        rw [OraclePolicy.map_realizeChoice_choiceLaw_eq_machine state event row
          dist rowGet semEq ready env envOk]
    _ = (program.step state command).map (RawStore.encodeState codec) := by
        rw [GameTheory.Math.Probability.FinDist.map_comp]
        rfl

end OracleCalldata

end Vegas.Machine.Contract
