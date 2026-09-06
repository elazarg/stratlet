/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Machine.Contract.State

/-!
# Contract lifecycle state

The lifecycle boundary connects deployment and terminal readout to canonical
contract storage. Deployment is exactly the raw encoding of `Machine.init`.
Terminal readout decodes the snapshot, requires every graph node to be
complete, and evaluates the retained payoff code.

The resulting outcome is semantic settlement data. This module does not add
asset custody, transfers, withdrawal rules, aborts, or timeout behavior.
-/

noncomputable section

namespace Vegas.Machine.Contract

open EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} {program : Program Player L}

/-- Canonical raw storage installed when the contract is deployed. -/
def initialStore (program : Program Player L)
    (codec : StorageCodec program) :
    RawStore codec :=
  RawStore.encodeState codec program.init

/-- Deployment storage decodes to exactly the initial finite graph state. -/
@[simp] theorem decodeSnapshot_initialStore
    (program : Program Player L) (codec : StorageCodec program) :
    RawStore.decodeSnapshot (program := program) codec
        (initialStore program codec) =
      some (StateSnapshot.ofConfig program.init.1) := by
  exact RawStore.decodeSnapshot_encodeState codec program.init

/-- Every action is incomplete in canonical deployment storage. -/
@[simp] theorem readCompleted_initialStore
    (program : Program Player L) (codec : StorageCodec program)
    (node : Fin program.graph.nodeCount) :
    RawStore.readCompleted (Layout.canonical program) codec
        (initialStore program codec) node = some false := by
  simp [initialStore, RawStore.encodeState, Program.init,
    StateSnapshot.ofConfig, Config.initial]

/-- Executable completion scan over the finite graph node inventory. -/
def allCompleted (program : Program Player L)
    (snapshot : StateSnapshot program.graph) : Bool :=
  program.graph.nodeOrder.all fun node => decide (node ∈ snapshot.done)

/-- The finite completion scan recognizes exactly machine terminality. -/
theorem allCompleted_eq_true_iff (program : Program Player L)
    (snapshot : StateSnapshot program.graph) :
    allCompleted program snapshot = true ↔
      Terminal program.graph snapshot.toConfig := by
  simp [allCompleted, Terminal, Graph.mem_nodeOrder]

/-- Decode terminal settlement data from canonical raw storage. Nonterminal or
malformed storage has no outcome. -/
def terminalPayout? (program : Program Player L)
    (codec : StorageCodec program)
    (store : RawStore codec) : Option (Payout Player) :=
  match RawStore.decodeSnapshot (program := program) codec store with
  | none => none
  | some snapshot =>
      if allCompleted program snapshot then
        evalPayoffs? program.payoffs snapshot.toConfig.store
      else
        none

/-- On an encoded reachable state, terminal outcome decoding is exactly the
retained machine payoff evaluator, guarded only by machine terminality. -/
theorem terminalPayout?_encodeState
    (program : Program Player L) (codec : StorageCodec program)
    (state : program.State) :
    terminalPayout? program codec (RawStore.encodeState codec state) =
      if allCompleted program (StateSnapshot.ofConfig state.1) then
        evalPayoffs? program.payoffs state.1.store
      else
        none := by
  unfold terminalPayout?
  rw [RawStore.decodeSnapshot_encodeState]
  simp only
  rw [StateSnapshot.canonical_reachable program.graphWF state.2]

/-- Terminal encoded reachable storage exposes exactly the machine payoff. -/
theorem terminalPayout?_encodeState_of_terminal
    (program : Program Player L) (codec : StorageCodec program)
    (state : program.State) (hterminal : program.terminal state) :
    terminalPayout? program codec (RawStore.encodeState codec state) =
      evalPayoffs? program.payoffs state.1.store := by
  have hall :
      allCompleted program (StateSnapshot.ofConfig state.1) = true :=
    (allCompleted_eq_true_iff program
      (StateSnapshot.ofConfig state.1)).2 hterminal
  rw [terminalPayout?_encodeState, if_pos hall]

/-- Terminal encoded reachable storage always has a settlement outcome. -/
theorem terminalPayout?_encodeState_isSome
    (program : Program Player L) (codec : StorageCodec program)
    (state : program.State) (hterminal : program.terminal state) :
    (terminalPayout? program codec
      (RawStore.encodeState codec state)).isSome := by
  rcases program.existsPayoffOfTerminal state hterminal with
    ⟨outcome, houtcome⟩
  rw [terminalPayout?_encodeState_of_terminal program codec state hterminal,
    houtcome]
  rfl

/-- For a compiled source program, terminal contract storage exposes a payoff
of an actual source terminal environment. -/
theorem terminalPayout?_compile_encodeState
    (source : WFProgram Player L)
    (codec : StorageCodec (Machine.compile source))
    (state : (Machine.compile source).State)
    (hterminal : (Machine.compile source).terminal state) :
    ∃ sourceEnv :
        VEnv L (ToEventGraph.compile source.core).terminalCtx,
      terminalPayout? (Machine.compile source) codec
          (RawStore.encodeState codec state) =
        some (evalPayoffs
          (ToEventGraph.compile source.core).sourcePayoffs sourceEnv) := by
  rw [terminalPayout?_encodeState_of_terminal
    (Machine.compile source) codec state hterminal]
  exact Machine.compile_sourcePayoffOfTerminal source state hterminal

end Vegas.Machine.Contract
