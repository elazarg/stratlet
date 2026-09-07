/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasEVM.Contract.ClassicalEVMIR
import VegasEVM.Contract.EVMLocalAssembly

/-!
# Structural EVM handler code generation

This pass emits the source-independent parts of every classical handler.
Readiness assertions become `SLOAD`, canonical Boolean comparison, and a local
conditional jump to rejection. A successful event value already left on the
stack is written before its presence and completion bits, preserving the
imperative effect order.

Storage keys use full `PUSH32` immediates. `ClassicalStorageFitsWord` is the
separate deployment certificate that makes those natural-number addresses
exact rather than modular.
-/

namespace Vegas.Machine.Contract.EVM

open EventGraph

noncomputable section

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} {program : Program Player L}

/-- Compile one concrete readiness assertion. Failure is the negation of
canonical equality, so non-Boolean storage also fails before this code is
entered under the decoded-state invariant. -/
def compileClassicalStorageCheck (reject : LocalLabel)
    (check : ClassicalStorageCheck) : LocalAssembly :=
  [ .op (.push (.nat256 check.slot)),
    .op .sload,
    .op (.push (.one (byte (if check.expected then 1 else 0)))),
    .op .eq,
    .op .iszero,
    .jumpi reject ]

/-- Resolved form of one storage check for a supplied absolute rejection
destination. -/
def classicalStorageCheckAssembly (rejectDestination : Nat)
    (check : ClassicalStorageCheck) : Assembly :=
  [ .push (.nat256 check.slot),
    .sload,
    .push (.one (byte (if check.expected then 1 else 0))),
    .eq,
    .iszero,
    .push (.nat32 rejectDestination),
    .jumpi ]

/-- Resolved form of an ordered list of storage checks. -/
def classicalStorageChecksAssembly (rejectDestination : Nat)
    (checks : List ClassicalStorageCheck) : Assembly :=
  checks.flatMap (classicalStorageCheckAssembly rejectDestination)

@[simp] theorem classicalStorageCheckAssembly_byteLength
    (rejectDestination : Nat) (check : ClassicalStorageCheck) :
    (classicalStorageCheckAssembly rejectDestination check).byteLength = 44 := by
  simp [classicalStorageCheckAssembly, Assembly.byteLength,
    Instruction.byteLength]

@[simp] theorem classicalStorageChecksAssembly_byteLength
    (rejectDestination : Nat) (checks : List ClassicalStorageCheck) :
    (classicalStorageChecksAssembly rejectDestination checks).byteLength =
      44 * checks.length := by
  induction checks with
  | nil => rfl
  | cons check rest ih =>
      change
        (classicalStorageCheckAssembly rejectDestination check ++
          classicalStorageChecksAssembly rejectDestination rest).byteLength = _
      rw [Assembly.byteLength_append,
        classicalStorageCheckAssembly_byteLength, ih]
      simp
      omega

@[simp] theorem compileClassicalStorageCheck_byteLength
    (reject : LocalLabel) (check : ClassicalStorageCheck) :
    (compileClassicalStorageCheck reject check).byteLength = 44 := by
  simp [compileClassicalStorageCheck, LocalAssembly.byteLength,
    LocalItem.byteLength, Instruction.byteLength]

/-- Compile ordered readiness assertions without changing their order. -/
def compileClassicalStorageChecks (reject : LocalLabel)
    (checks : List ClassicalStorageCheck) : LocalAssembly :=
  checks.flatMap (compileClassicalStorageCheck reject)

@[simp] theorem compileClassicalStorageChecks_byteLength
    (reject : LocalLabel) (checks : List ClassicalStorageCheck) :
    (compileClassicalStorageChecks reject checks).byteLength =
      44 * checks.length := by
  induction checks with
  | nil => rfl
  | cons check rest ih =>
      change
        (compileClassicalStorageCheck reject check ++
          compileClassicalStorageChecks reject rest).byteLength = _
      rw [LocalAssembly.byteLength_append,
        compileClassicalStorageCheck_byteLength, ih]
      simp only [List.length_cons]
      omega

/-- Standard rejection block with empty revert data. -/
def classicalRejectBlock (reject : LocalLabel) : LocalAssembly :=
  [ .label reject,
    .op (.push (.one (byte 0))),
    .op (.push (.one (byte 0))),
    .op .revert ]

@[simp] theorem classicalRejectBlock_byteLength (reject : LocalLabel) :
    (classicalRejectBlock reject).byteLength = 6 := by
  simp [classicalRejectBlock, LocalAssembly.byteLength,
    LocalItem.byteLength, Instruction.byteLength]

/-- Store an event result that is already on top of the EVM stack, then set
its presence and completion cells to canonical true. -/
def compileClassicalActionWrites
    (action : ClassicalActionIR program) : LocalAssembly :=
  [ .op (.push (.nat256 action.valueSlot)),
    .op .sstore,
    .op (.push (.one (byte 1))),
    .op (.push (.nat256 action.presenceSlot)),
    .op .sstore,
    .op (.push (.one (byte 1))),
    .op (.push (.nat256 action.completionSlot)),
    .op .sstore ]

/-- Resolved instruction sequence of the ordered action writes. -/
def classicalActionWritesAssembly
    (action : ClassicalActionIR program) : Assembly :=
  [ .push (.nat256 action.valueSlot),
    .sstore,
    .push (.one (byte 1)),
    .push (.nat256 action.presenceSlot),
    .sstore,
    .push (.one (byte 1)),
    .push (.nat256 action.completionSlot),
    .sstore ]

@[simp] theorem resolveAt_compileClassicalActionWrites
    (base : Nat) (action : ClassicalActionIR program) :
    (compileClassicalActionWrites action).resolveAt base =
      some (classicalActionWritesAssembly action) := by
  rfl

@[simp] theorem compileClassicalActionWrites_byteLength
    (action : ClassicalActionIR program) :
    (compileClassicalActionWrites action).byteLength = 106 := by
  simp [compileClassicalActionWrites, LocalAssembly.byteLength,
    LocalItem.byteLength, Instruction.byteLength]

/-- Structural wrapper around expression-specific event realization. The
body must leave exactly one encoded event value on top of the stack. On
fallthrough, the wrapper commits the three ordered storage writes and stops;
every failed readiness assertion reaches the local revert block. -/
def compileClassicalActionFrame (reject : LocalLabel)
    (action : ClassicalActionIR program) (realize : LocalAssembly) :
    LocalAssembly :=
  compileClassicalStorageChecks reject action.checks ++
    realize ++ compileClassicalActionWrites action ++
    [.op .stop] ++ classicalRejectBlock reject

@[simp] theorem compileClassicalActionFrame_byteLength
    (reject : LocalLabel) (action : ClassicalActionIR program)
    (realize : LocalAssembly) :
    (compileClassicalActionFrame reject action realize).byteLength =
      44 * action.checks.length + realize.byteLength + 113 := by
  simp only [compileClassicalActionFrame, LocalAssembly.byteLength_append,
    compileClassicalStorageChecks_byteLength,
    compileClassicalActionWrites_byteLength,
    classicalRejectBlock_byteLength]
  norm_num [LocalAssembly.byteLength, LocalItem.byteLength,
    Instruction.byteLength]

end

end Vegas.Machine.Contract.EVM
