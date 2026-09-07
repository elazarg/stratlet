/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasEVM.Contract.Executor
import VegasEVM.Contract.StoredABI

/-!
# Logical execution over contract storage

This pass composes canonical storage decoding, logical request execution, and
successor re-encoding.  On storage encoded from a reachable state and a request
encoded from a valid command, its raw-store law is exactly `Machine.step`
mapped through the certified state encoding.

As in `Executor`, the resulting `FinDist` is a semantic law rather than an
extracted sampler.
-/

noncomputable section

namespace Vegas.Machine.Contract

open EventGraph
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {program : Program Player L}

namespace Request

/-- Execute over a structural graph snapshot and retain structural successor
snapshots. -/
def executeSnapshot? (snapshot : StateSnapshot program.graph)
    (request : Request Player L) :
    Option (FinDist (StateSnapshot program.graph)) :=
  (executeConfig? snapshot.toConfig request).map fun law =>
    law.map StateSnapshot.ofConfig

/-- Execute over canonical raw storage, returning canonically encoded raw
successor stores. -/
def executeStore? (codec : StorageCodec program) (store : RawStore codec)
    (request : Request Player L) : Option (FinDist (RawStore codec)) :=
  match RawStore.decodeSnapshot (program := program) codec store with
  | none => none
  | some snapshot =>
      (executeSnapshot? snapshot request).map fun law =>
        law.map (RawStore.encodeSnapshot codec)

/-- Snapshot execution succeeds exactly when snapshot validation accepts. -/
theorem executeSnapshot?_isSome
    (snapshot : StateSnapshot program.graph) (request : Request Player L) :
    (executeSnapshot? snapshot request).isSome =
      acceptsSnapshot snapshot request := by
  simp [executeSnapshot?, acceptsSnapshot, executeConfig?_isSome]

/-- Stored execution succeeds exactly when stored validation accepts. -/
theorem executeStore?_isSome
    (codec : StorageCodec program) (store : RawStore codec)
    (request : Request Player L) :
    (executeStore? (program := program) codec store request).isSome =
      acceptsStore (program := program) codec store request := by
  unfold executeStore? acceptsStore
  cases RawStore.decodeSnapshot (program := program) codec store with
  | none => rfl
  | some snapshot =>
      simp [executeSnapshot?_isSome]

/-- Executing a valid command from its reachable-state snapshot yields the
raw semantic successor law mapped to finite snapshots. -/
theorem executeSnapshot?_ofConfig_encode
    (state : program.State) (command : program.Command state) :
    executeSnapshot? (StateSnapshot.ofConfig state.1) (encode command) =
      some ((stepAvailableEvent program.graph state.1 command).map
        StateSnapshot.ofConfig) := by
  unfold executeSnapshot?
  have hcanonical :=
    StateSnapshot.canonical_reachable program.graphWF state.2
  rw [hcanonical, executeConfig?_encode]
  rfl

/-- End-to-end storage-state law for one valid logical command: decode,
execute, and re-encode is exactly the machine law mapped through
`encodeState`. -/
theorem executeStore?_encodeState_encode
    (codec : StorageCodec program) (state : program.State)
    (command : program.Command state) :
    executeStore? (program := program) codec
        (RawStore.encodeState codec state) (encode command) =
      some ((program.step state command).map
        (RawStore.encodeState codec)) := by
  unfold executeStore?
  rw [RawStore.decodeSnapshot_encodeState]
  change
    (executeSnapshot? (StateSnapshot.ofConfig state.1) (encode command)).map
        (fun law => law.map (RawStore.encodeSnapshot codec)) =
      some ((program.step state command).map
        (RawStore.encodeState codec))
  rw [executeSnapshot?_ofConfig_encode]
  simp only [Option.map]
  congr 1
  rw [FinDist.map_comp]
  rw [← EventGraph.map_val_stepAvailable program.graph state command]
  rw [FinDist.map_comp]
  rfl

/-- Every request accepted against encoded reachable storage is the envelope
of some valid semantic command, and its entire successor law is therefore the
canonical raw-store image of that machine step. This is the transition
invariant needed for hostile external requests, not only compiler-emitted
ones. -/
theorem executeStore?_encodeState_of_accepts
    (codec : StorageCodec program) (state : program.State)
    (request : Request Player L)
    (haccept :
      acceptsStore (program := program) codec
        (RawStore.encodeState codec state) request = true) :
    ∃ command : program.Command state,
      encode command = request ∧
        executeStore? (program := program) codec
            (RawStore.encodeState codec state) request =
          some ((program.step state command).map
            (RawStore.encodeState codec)) := by
  have hrepresents :=
    (acceptsStore_encodeState_eq_true_iff codec state request).1 haccept
  rcases hrepresents with ⟨command, hencode⟩
  refine ⟨command, hencode, ?_⟩
  rw [← hencode]
  exact executeStore?_encodeState_encode codec state command

end Request

end Vegas.Machine.Contract
