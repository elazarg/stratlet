/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasEVM.Contract.Classical

/-!
# Ideal contract visibility

This module states the observation boundary assumed by the classical compiler.
The ideal observer decodes the semantic graph snapshot and exposes only the
source event graph's public observation and the acting player's private view.
Raw storage words, sealed fields, and the asynchronous oracle pending marker
are outside this observation.

This is an ideal functionality, not a claim about public blockchain storage.
A secure compiler must implement or refine this boundary with commitments,
encryption, private execution, or another concrete mechanism.  Keeping the
boundary explicit lets the classical game-preservation layer be proved without
conflating functional correctness with target-level secrecy.
-/

noncomputable section

namespace Vegas.Machine.Contract

open EventGraph

variable {Player Address : Type}
variable [DecidableEq Player] [DecidableEq Address]
variable {L : IExpr} {program : Program Player L}

namespace IdealVisibility

/-- Decode the finite semantic configuration carried by classical contract
storage.  Arbitrary malformed storage has no semantic observation. -/
def config? (codec : StorageCodec program)
    (state : OracleProtocol.State codec) : Option (Config program.graph) :=
  (RawStore.decodeSnapshot codec state.store).map StateSnapshot.toConfig

/-- Ideal public contract observation.  The pending oracle marker and all
sealed graph fields are intentionally absent. -/
def publicView? (codec : StorageCodec program)
    (state : OracleProtocol.State codec) :
    Option (PublicObservation program.graph) :=
  (config? codec state).map (publicObserve program.graph)

/-- Ideal observation available to one source player.  This is exactly the
machine player's graph-local view, not arbitrary contract storage. -/
def privateView? (codec : StorageCodec program) (who : Player)
    (state : OracleProtocol.State codec) :
    Option (Observation program.graph who) :=
  (config? codec state).map fun cfg => observe program.graph cfg who

/-- The administrative marker is retained as a separately named signal.  It
is useful for concrete scheduler reasoning but is not part of the ideal game
observation above. -/
def administrativeView (codec : StorageCodec program)
    (state : OracleProtocol.State codec) : Option Nat :=
  state.pending

@[simp] theorem config?_idleState
    (codec : StorageCodec program) (state : program.State) :
    config? codec (OracleProtocol.idleState codec state) = some state.1 := by
  unfold config? OracleProtocol.idleState
  rw [RawStore.decodeSnapshot_encodeState]
  simp only [Option.map_some]
  exact congrArg some (StateSnapshot.canonical_reachable
    program.graphWF state.2)

@[simp] theorem config?_waitingState
    (codec : StorageCodec program) (state : program.State)
    (event : InternalEvent program.graph) :
    config? codec (OracleProtocol.waitingState codec state event) =
      some state.1 := by
  unfold config? OracleProtocol.waitingState
  rw [RawStore.decodeSnapshot_encodeState]
  simp only [Option.map_some]
  exact congrArg some (StateSnapshot.canonical_reachable
    program.graphWF state.2)

@[simp] theorem publicView?_idleState
    (codec : StorageCodec program) (state : program.State) :
    publicView? codec (OracleProtocol.idleState codec state) =
      some (program.publicView state) := by
  simp [publicView?, Program.publicView]

@[simp] theorem privateView?_idleState
    (codec : StorageCodec program) (who : Player) (state : program.State) :
    privateView? codec who (OracleProtocol.idleState codec state) =
      some (program.view who state) := by
  simp [privateView?, Program.view]

/-- Beginning an oracle request is an exact stutter under ideal public
observation. -/
@[simp] theorem publicView?_waitingState
    (codec : StorageCodec program) (state : program.State)
    (event : InternalEvent program.graph) :
    publicView? codec (OracleProtocol.waitingState codec state event) =
      some (program.publicView state) := by
  simp [publicView?, Program.publicView]

/-- Beginning an oracle request is also an exact stutter for every player's
ideal private observation. -/
@[simp] theorem privateView?_waitingState
    (codec : StorageCodec program) (who : Player) (state : program.State)
    (event : InternalEvent program.graph) :
    privateView? codec who
        (OracleProtocol.waitingState codec state event) =
      some (program.view who state) := by
  simp [privateView?, Program.view]

@[simp] theorem administrativeView_idleState
    (codec : StorageCodec program) (state : program.State) :
    administrativeView codec (OracleProtocol.idleState codec state) = none :=
  rfl

@[simp] theorem administrativeView_waitingState
    (codec : StorageCodec program) (state : program.State)
    (event : InternalEvent program.graph) :
    administrativeView codec
        (OracleProtocol.waitingState codec state event) = some event.node :=
  rfl

end IdealVisibility

end Vegas.Machine.Contract
