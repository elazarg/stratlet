/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasEVM.Contract.State
import VegasEVM.Contract.Validator

/-!
# Logical ABI validation over stored state

These entry points run the executable logical request validator directly over
a finite snapshot or canonical raw storage.  On storage produced from a
reachable machine state, validation agrees exactly with semantic command
availability.  Arbitrary decoded storage is checked structurally but receives
no fabricated reachability proof.
-/

namespace Vegas.Machine.Contract

open EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {program : Program Player L}

namespace Request

/-- Validate a request against a finite graph snapshot. -/
def acceptsSnapshot (snapshot : StateSnapshot program.graph)
    (request : Request Player L) : Bool :=
  acceptsConfig snapshot.toConfig request

/-- Decode canonical raw storage and validate a logical request. Missing or
malformed completion words reject before request validation. -/
def acceptsStore (codec : StorageCodec program) (store : RawStore codec)
    (request : Request Player L) : Bool :=
  match RawStore.decodeSnapshot (program := program) codec store with
  | none => false
  | some snapshot => acceptsSnapshot snapshot request

/-- Snapshot validation reconstructed from a reachable configuration is
exactly semantic-state validation. -/
theorem acceptsSnapshot_ofConfig
    (state : program.State) (request : Request Player L) :
    acceptsSnapshot (StateSnapshot.ofConfig state.1) request =
      accepts state request := by
  unfold acceptsSnapshot accepts
  have hcanonical :=
    StateSnapshot.canonical_reachable program.graphWF state.2
  rw [hcanonical]

/-- Validation over the raw encoding of a reachable state agrees exactly with
semantic request validation. -/
@[simp] theorem acceptsStore_encodeState
    (codec : StorageCodec program) (state : program.State)
    (request : Request Player L) :
    acceptsStore (program := program) codec
        (RawStore.encodeState (program := program) codec state) request =
      accepts state request := by
  unfold acceptsStore
  rw [RawStore.decodeSnapshot_encodeState]
  exact acceptsSnapshot_ofConfig state request

/-- The stored-state validator accepts exactly valid semantic commands when
the storage was produced from a reachable machine state. -/
theorem acceptsStore_encodeState_eq_true_iff
    (codec : StorageCodec program) (state : program.State)
    (request : Request Player L) :
    acceptsStore (program := program) codec
        (RawStore.encodeState (program := program) codec state) request = true ↔
      Represents state request := by
  rw [acceptsStore_encodeState, accepts_eq_true_iff]

end Request

end Vegas.Machine.Contract
