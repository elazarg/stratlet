/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasEVM.Contract.SimpleEVMAction
import VegasEVM.Contract.SimpleEVMDist

/-!
# Trusted-oracle sample request and callback code

This module lowers the asynchronous oracle phase to EVM storage and logs. A
request checks the idle marker, stores the pending node, and emits a 32-byte
anonymous log containing that node. A callback authenticates the oracle,
checks the unique pending node, validates/realizes the retained exact-table
index, clears the marker, and can then use the common action writes.

The log is the concrete image of `OracleProtocol.Request`; liveness and the
oracle's adherence to its known exact strategy remain explicit trusted-runtime
assumptions.
-/

namespace Vegas.Machine.Contract.EVM

open EventGraph

noncomputable section

variable {Player Address : Type}
variable [DecidableEq Player] [DecidableEq Address]
variable {program : Program Player simpleExpr}

def pendingFlagSlot (program : Program Player simpleExpr) : Nat :=
  (ClassicalStorageLayout.canonical program).address .pendingFlag

def pendingNodeSlot (program : Program Player simpleExpr) : Nat :=
  (ClassicalStorageLayout.canonical program).address .pendingNode

/-- Canonical pending-flag assertion. -/
def compilePendingFlagEq (expected : Bool) (reject : LocalLabel) :
    LocalAssembly :=
  compileClassicalStorageCheck reject
    { slot := pendingFlagSlot program, expected := expected }

/-- Reject unless the stored pending node equals this action node. -/
def compilePendingNodeEq (node : Nat) (reject : LocalLabel) :
    LocalAssembly :=
  LocalAssembly.ofAssembly (loadStorageWord (pendingNodeSlot program)) ++
    [ .op (.push (.nat256 node)),
      .op .eq,
      .op .iszero,
      .jumpi reject ]

/-- Store the unique pending sample node. -/
def compileSetPending (node : Nat) : LocalAssembly :=
  [ .op (.push (.one (byte 1))),
    .op (.push (.nat256 (pendingFlagSlot program))),
    .op .sstore,
    .op (.push (.nat256 node)),
    .op (.push (.nat256 (pendingNodeSlot program))),
    .op .sstore ]

/-- Clear the asynchronous lock. The stale node word is zeroed as well even
though the false flag makes it semantically inert. -/
def compileClearPending (program : Program Player simpleExpr) : LocalAssembly :=
  [ .op (.push (.one (byte 0))),
    .op (.push (.nat256 (pendingFlagSlot program))),
    .op .sstore,
    .op (.push (.one (byte 0))),
    .op (.push (.nat256 (pendingNodeSlot program))),
    .op .sstore ]

/-- Emit the pending node as one 32-byte anonymous EVM log. -/
def compileOracleRequestLog (node : Nat) : LocalAssembly :=
  [ .op (.push (.nat256 node)),
    .op (.push (.one (byte 0))),
    .op .mstore,
    .op (.push (.one (byte 32))),
    .op (.push (.one (byte 0))),
    .op .log0 ]

/-- Request effect after readiness and authorization have succeeded. -/
def compileSimpleSampleRequestEffect
    (action : ClassicalActionIR program) : LocalAssembly :=
  compileSetPending (program := program) action.node ++
    compileOracleRequestLog action.node ++ [.op .stop]

/-- Graph well-formedness and Boolean node storage force a sample result type
to be Boolean. -/
theorem sampleDist_type_bool
    (usesBool : UsesOnlyBoolStorage program)
    (node : Fin program.graph.nodeCount) (dist : EventDist simpleExpr)
    (hsem : (program.graph.nodeRow node).sem = .sample dist) :
    dist.ty = .bool := by
  have hwf :=
    program.graphWF (node : Nat) (program.graph.nodeRow node)
      (program.graph.nodes_get?_nodeRow node)
  unfold Graph.nodeWFAt at hwf
  rw [hsem] at hwf
  exact hwf.2.1.symm.trans (usesBool.node_type node)

/-- Compile authenticated Boolean callback realization. The returned code
leaves the selected Boolean result word on stack. -/
def compileSimpleSampleCallback?
    (usesBool : UsesOnlyBoolStorage program)
    (oracle : OracleRegistry Address)
    (addresses : AddressCodec Address)
    (action : ClassicalActionIR program)
    (reject : LocalLabel) (next : Nat) : Option GeneratedLocalCode :=
  match hsem : (program.graph.nodeRow action.node).sem with
  | .sample dist =>
      let distType := sampleDist_type_bool usesBool action.node dist hsem
      let boolCode : DistCode simpleExpr .bool := distType ▸ dist.code
      match compileSimpleDistCode? boolCode reject next with
      | none => none
      | some realized =>
          some
            { code :=
                compileCallerEq (addresses.encode oracle.address) reject ++
                compilePendingFlagEq (program := program) true reject ++
                compilePendingNodeEq (program := program) action.node reject ++
                realized.code
              nextLabel := realized.nextLabel }
  | .commit _ _ | .reveal _ => none

end

end Vegas.Machine.Contract.EVM
