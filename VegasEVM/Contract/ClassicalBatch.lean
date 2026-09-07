/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasEVM.Contract.IdealVisibility

/-!
# Atomic classical frontier batches

The source game presents every ready strategic frontier as one simultaneous
joint action.  This module is the corresponding ideal classical batching
functionality: a trusted mediator accepts one legal frontier packet, applies
its independent commitments in canonical graph-node order, and exposes only
the packet's final state.

Canonical serialization is functionally ordinary and proved equal to the
source protocol step.  Hiding packet contents and intermediate writes on a
public runtime is a later secure-compilation obligation; this module does not
claim that a sequence of public transactions is atomic or secret.
-/

noncomputable section

namespace Vegas.Machine.Contract

open EventGraph
open GameTheory.Math.Probability

variable {Player Address : Type}
variable [DecidableEq Player] [Fintype Player] [DecidableEq Address]
variable {L : IExpr} {program : Program Player L}

/-- One legal simultaneous source-game packet at a strategic checkpoint. -/
structure FrontierBatch (program : Program Player L)
    (state : program.State) where
  joint : ∀ who, Option (FrontierAction program.graph who)
  legal : program.execution.Legal state joint
  noInternal : readyInternalNodes program.graph state.1 = ∅

namespace FrontierBatch

variable {state : program.State}
variable (batch : FrontierBatch program state)

/-- Package the batch as the proof-carrying joint action consumed by the
source execution protocol. -/
def command :
    { joint : ∀ who, Option (FrontierAction program.graph who) //
      program.execution.Legal state joint } :=
  ⟨batch.joint, batch.legal⟩

/-- Deterministic canonical serialization of the simultaneous packet. -/
def result : program.State :=
  applyFrontier program.graph program.graphWF state batch.joint

/-- The source execution law for a strategic packet is exactly the point mass
at its canonical serialization. -/
theorem source_step :
    program.execution.step state batch.command = FinDist.pure batch.result := by
  exact toExecutionProtocol_step_eq_pure_applyFrontier
    program.graph program.graphWF program.guardLive state batch.command
      batch.noInternal

end FrontierBatch

namespace ClassicalContract

variable (contract : ClassicalContract program Address)

/-- Ideal atomic execution of a simultaneous frontier packet.  The returned
state is already in the ordinary classical contract's canonical encoding. -/
def executeBatch {state : program.State}
    (batch : FrontierBatch program state) : contract.State :=
  contract.encodeState batch.result

/-- Compiling a strategic source round through ideal batching preserves its
entire successor law exactly. -/
theorem map_source_step_encodeState {state : program.State}
    (batch : FrontierBatch program state) :
    (program.execution.step state batch.command).map contract.encodeState =
      FinDist.pure (contract.executeBatch batch) := by
  rw [batch.source_step, FinDist.map_pure]
  rfl

/-- Atomic batch execution exposes exactly the source public observation of
the completed packet under the ideal visibility boundary. -/
@[simp] theorem publicView?_executeBatch {state : program.State}
    (batch : FrontierBatch program state) :
    IdealVisibility.publicView? contract.codec
        (contract.executeBatch batch) =
      some (program.publicView batch.result) := by
  simp [executeBatch, ClassicalContract.encodeState]

/-- Every player's ideal private observation after a batch is exactly the
source private observation after the same joint round. -/
@[simp] theorem privateView?_executeBatch {state : program.State}
    (batch : FrontierBatch program state) (who : Player) :
    IdealVisibility.privateView? contract.codec who
        (contract.executeBatch batch) =
      some (program.view who batch.result) := by
  simp [executeBatch, ClassicalContract.encodeState]

end ClassicalContract

end Vegas.Machine.Contract
