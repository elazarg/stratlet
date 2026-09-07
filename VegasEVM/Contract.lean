/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Machine.Program

/-!
# Target-neutral contract manifest

The contract manifest is the first emitter-facing view of `Machine.Program`.
It makes logical value storage, per-action completion storage, stable actions,
direct dependency gates, authority, input types, and retained node code
explicit and finitely enumerable.

It does not yet choose a physical storage encoding, role-address registry,
transaction scheduler, entropy source, commitment scheme, timeout behavior,
settlement mechanism, or target integer semantics.  Those choices change the
operational or strategic model and belong in later certified passes.
-/

namespace Vegas.Machine

open EventGraph

namespace Contract

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- Who supplies or realizes one logical graph action.  Internal authority is
still abstract: a backend must decide who may trigger it and how chance is
implemented. -/
inductive Authority (Player : Type) where
  | internal
  | player (who : Player)
deriving DecidableEq

/-- Logical storage requested by the manifest.  Value slots retain their typed
graph specification; completion slots distinguish an unexecuted action from an
action that wrote a language-level default value. -/
inductive StorageSlot (program : Program Player L) where
  | value (field : Fin program.graph.fieldCount)
  | completed (node : Fin program.graph.nodeCount)

namespace StorageSlot

variable (program : Program Player L)

/-- Stable numeric id within each slot family.  A later layout pass chooses
physical offsets or keys and proves its encoding injective. -/
def logicalId : StorageSlot program → Nat
  | .value field => field
  | .completed node => node

/-- The typed graph specification of a logical value slot. -/
def valueSpec : StorageSlot program → Option (FieldSpec Player L)
  | .value field => some (program.graph.fieldRow field)
  | .completed _ => none

end StorageSlot

/-- One stable logical action in a contract manifest. -/
structure Action (program : Program Player L) where
  node : Fin program.graph.nodeCount

namespace Action

variable (program : Program Player L)

def logicalId (action : Action program) : Nat :=
  action.node

/-- Reified executable row retained from the machine program. -/
def row (action : Action program) : EventNode Player L :=
  program.graph.nodeRow action.node

/-- Exact direct dependency gates for this action. -/
def dependencies (action : Action program) :
    Finset (Fin program.graph.nodeCount) :=
  program.graph.prereqs action.node

/-- Logical authority derived from the node semantics. -/
def authority (action : Action program) : Authority Player :=
  match (action.row program).sem with
  | .commit who _ => .player who
  | .sample _ | .reveal _ => .internal

/-- The language-level value expected from a player call, if any. -/
def inputType (action : Action program) : Option L.Ty :=
  match (action.row program).sem with
  | .commit _ guard => some guard.ty
  | .sample _ | .reveal _ => none

/-- Logical output field written by the action. -/
def outputField (action : Action program) : Nat :=
  program.graph.nodeTarget action.node

end Action

/-- Finite emitter-facing inventory derived without changing machine
semantics. -/
structure Manifest (program : Program Player L) where
  storage : List (StorageSlot program)
  actions : List (Action program)

/-- Enumerate value storage, completion storage, and logical actions in their
canonical numeric orders. -/
def compile (program : Program Player L) : Manifest program where
  storage :=
    (List.finRange program.graph.fieldCount).map StorageSlot.value ++
      program.graph.nodeOrder.map StorageSlot.completed
  actions := program.graph.nodeOrder.map fun node => ⟨node⟩

namespace Manifest

variable (program : Program Player L)

@[simp] theorem compile_storage_length :
    (compile program).storage.length =
      program.graph.fieldCount + program.graph.nodeCount := by
  simp [compile, Graph.nodeOrder]

@[simp] theorem compile_actions_length :
    (compile program).actions.length = program.graph.nodeCount := by
  simp [compile, Graph.nodeOrder]

/-- Every logical value field occurs in the manifest. -/
theorem value_mem (field : Fin program.graph.fieldCount) :
    StorageSlot.value field ∈ (compile program).storage := by
  simp [compile]

/-- Every completion bit occurs in the manifest. -/
theorem completed_mem (node : Fin program.graph.nodeCount) :
    StorageSlot.completed node ∈ (compile program).storage := by
  simp [compile, Graph.mem_nodeOrder]

/-- Every machine node occurs as exactly its stable logical action. -/
theorem action_mem (node : Fin program.graph.nodeCount) :
    (⟨node⟩ : Action program) ∈ (compile program).actions := by
  simp [compile, Graph.mem_nodeOrder]

/-- The manifest never changes an action's direct dependency set. -/
@[simp] theorem action_dependencies (node : Fin program.graph.nodeCount) :
    Action.dependencies program (⟨node⟩ : Action program) =
      program.graph.prereqs node := rfl

/-- The manifest never changes an action's executable node code. -/
@[simp] theorem action_row (node : Fin program.graph.nodeCount) :
    Action.row program (⟨node⟩ : Action program) =
      program.graph.nodeRow node := rfl

end Manifest

end Contract

end Vegas.Machine
