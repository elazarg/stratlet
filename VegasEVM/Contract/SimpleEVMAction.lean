/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasEVM.Contract.ClassicalEVMCodegen
import VegasEVM.Contract.SimpleEVMExpr
import VegasEVM.Contract.Authentication

/-!
# Boolean commit and reveal realization on EVM

This module lowers the expression-specific part of Boolean commit and reveal
actions. A player commit validates the claimed player word, authenticates
`CALLER`, rejects noncanonical Boolean action words, evaluates the retained
guard, and leaves the accepted action word on the stack. A reveal loads its
already-present sealed source word. The common structural frame then performs
the ordered output writes.
-/

namespace Vegas.Machine.Contract.EVM

open EventGraph

noncomputable section

variable {Player Address : Type}
variable [DecidableEq Player] [DecidableEq Address]
variable {program : Program Player simpleExpr}

/-- Graph well-formedness and Boolean node storage force every commit action
type to be Boolean. -/
theorem commitGuard_type_bool
    (usesBool : UsesOnlyBoolStorage program)
    (node : Fin program.graph.nodeCount) (who : Player)
    (guard : EventGuard simpleExpr)
    (hsem : (program.graph.nodeRow node).sem = .commit who guard) :
    guard.ty = .bool := by
  have hwf :=
    program.graphWF (node : Nat) (program.graph.nodeRow node)
      (program.graph.nodes_get?_nodeRow node)
  unfold Graph.nodeWFAt at hwf
  rw [hsem] at hwf
  exact hwf.2.1.symm.trans (usesBool.node_type node)

/-- Reject unless one calldata word equals the supplied 256-bit constant. -/
def compileCalldataWordEq (offset : Nat) (expected : Word)
    (reject : LocalLabel) : LocalAssembly :=
  LocalAssembly.ofAssembly (loadCalldataWord offset) ++
    [ .op (.push (.word expected)),
      .op .eq,
      .op .iszero,
      .jumpi reject ]

/-- Reject unless `CALLER` equals the supplied native EVM address. -/
def compileCallerEq (expected : AddressWord)
    (reject : LocalLabel) : LocalAssembly :=
  [ .op .caller,
    .op (.push (.address expected)),
    .op .eq,
    .op .iszero,
    .jumpi reject ]

/-- Load the player action word, prove at runtime that it is canonical zero or
one, and retain the original word on the stack. -/
def compileCanonicalBoolAction (reject : LocalLabel) : LocalAssembly :=
  LocalAssembly.ofAssembly playerActionWord ++
    [ .op (.dup ⟨0, by decide⟩),
      .op (.push (.one (byte 0))),
      .op .eq,
      .op (.dup ⟨1, by decide⟩),
      .op (.push (.one (byte 1))),
      .op .eq,
      .op .or,
      .op .iszero,
      .jumpi reject ]

/-- Compile one Boolean player-commit realization. The returned code leaves
the accepted action value on the stack for `compileClassicalActionWrites`. -/
def compileSimplePlayerCommit?
    (usesBool : UsesOnlyBoolStorage program)
    (registry : PlayerRegistry Player Address)
    (players : WireCodec Player Word)
    (addresses : AddressCodec Address)
    (action : ClassicalActionIR program)
    (reject : LocalLabel) (next : Nat) : Option GeneratedLocalCode :=
  match hsem : (program.graph.nodeRow action.node).sem with
  | .commit who guard =>
      let guardType := commitGuard_type_bool usesBool action.node who guard hsem
      let boolGuard : GuardCode simpleExpr .bool := guardType ▸ guard.code
      match compileSimpleGuardCode? boolGuard with
      | none => none
      | some guardCode =>
          some
            { code :=
                compileCalldataWordEq 4 (players.encode who) reject ++
                compileCallerEq
                  (addresses.encode (registry.address who)) reject ++
                compileCanonicalBoolAction reject ++
                LocalAssembly.ofAssembly guardCode ++
                  [.op .iszero, .jumpi reject]
              nextLabel := next }
  | .sample _ | .reveal _ => none

/-- Compile one Boolean reveal realization by loading its sealed source field.
-/
def compileSimpleReveal? (action : ClassicalActionIR program)
    (next : Nat) : Option GeneratedLocalCode :=
  match (program.graph.nodeRow action.node).sem with
  | .reveal source =>
      some
        { code := LocalAssembly.ofAssembly (loadStorageWord source)
          nextLabel := next }
  | .commit _ _ | .sample _ => none

end

end Vegas.Machine.Contract.EVM
