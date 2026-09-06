/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.SourceAdequacy
import Vegas.EventGraph.Protocol
import Vegas.Machine.System

/-!
# Backend-neutral machine programs

`Machine.Program` is the first backend-neutral compilation target shared by
game analysis and gradual runtime lowering. Its graph contains typed storage, dependency-addressed
node code, guarded player inputs, finite chance laws, reveals, and payoff code.
Its operational surface is the evidence-carrying primitive event transition of
the graph.

The GameTheory execution protocol is a strategic presentation of this machine:
it closes internal events and batches independent player inputs into frontier
rounds. A concrete backend lowers the stored node code through small operational
systems, proving the appropriate refinement and information theorem at every
step.
-/

noncomputable section

namespace Vegas

namespace Machine

open EventGraph
open GameTheory.Math.Probability

/-- A checked executable program at the backend-neutral machine boundary. -/
structure Program (Player : Type) [DecidableEq Player] (L : IExpr) where
  graph : EventGraph.Graph Player L
  graphWF : graph.WF
  guardLive : GuardLive graph
  payoffs : List (Player × EventPayoff L)
  payoffsWF :
    ∀ payoff, payoff ∈ payoffs →
      ∀ ref, ref ∈ payoff.2.reads →
        graph.fieldRefPublic ref ∧
        graph.fieldAvailableBefore graph.nodeCount ref.field = true

namespace Program

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- Reachable semantic storage configurations of a machine program. -/
abbrev State (program : Program Player L) := ReachableConfig program.graph

/-- One currently valid primitive machine command.  Player commits, chance
draws, and reveals all name one graph node; the proof component is erased by a
backend after it emits the corresponding runtime checks. -/
abbrev Command (program : Program Player L) (state : program.State) :=
  AvailableEvent program.graph state.1

/-- Initial machine storage. -/
def init (program : Program Player L) : program.State :=
  ⟨Config.initial program.graph, Reachable.initial⟩

/-- Execute one valid primitive command. -/
def step (program : Program Player L) (state : program.State)
    (command : program.Command state) : FinDist program.State :=
  stepAvailable program.graph state command

/-- Machine termination means that every graph node has completed. -/
def terminal (program : Program Player L) (state : program.State) : Prop :=
  Terminal program.graph state.1

/-- Terminal reachable states contain every field needed by the retained
machine payoff projection. -/
theorem existsPayoffOfTerminal (program : Program Player L)
    (state : program.State) (hterminal : program.terminal state) :
    ∃ outcome,
      evalPayoffs? program.payoffs state.1.store = some outcome := by
  apply evalPayoffs?_isSome_of_available
  intro payoff hpayoff ref href
  have hwellFormed := program.payoffsWF payoff hpayoff ref href
  exact
    (reachable_storeCoherent program.graphWF state.2).hasRefOfAvailable
      hterminal hwellFormed.1 hwellFormed.2

/-- Public machine storage visible at a checkpoint. -/
def publicView (program : Program Player L) (state : program.State) :
    PublicObservation program.graph :=
  publicObserve program.graph state.1

/-- The machine storage visible to one player at a checkpoint. -/
def view (program : Program Player L) (who : Player) (state : program.State) :
    Observation program.graph who :=
  observe program.graph state.1 who

/-- Every nonterminal reachable state admits a primitive machine command. -/
theorem progress (program : Program Player L) {state : program.State}
    (hterminal : ¬ program.terminal state) :
    Nonempty (program.Command state) := by
  exact exists_availableEvent_of_not_terminal
    program.graphWF program.guardLive hterminal

/-- Every realized primitive command completes a fresh graph node. -/
theorem step_done_ssubset (program : Program Player L)
    (state : program.State) (command : program.Command state)
    {next : program.State} (hnext : next ∈ (program.step state command).support) :
    state.1.done ⊂ next.1.done := by
  exact done_ssubset_of_stepAvailable_support
    program.graph state command hnext

/-- Strategic execution protocol presented by the machine program. -/
def execution (program : Program Player L) [Fintype Player] :=
  toExecutionProtocol program.graph program.graphWF program.guardLive

/-- Public/private information model presented by the machine program. -/
def information (program : Program Player L) [Fintype Player] :=
  toInformationModel program.graph program.graphWF program.guardLive

/-- Compiled information remembers every player's own earlier information and
actions while abstracting from unrelated event ordering. -/
theorem perfectRecall (program : Program Player L) [Fintype Player] :
    program.information.PerfectRecall := by
  exact toInfoSignals_perfectRecall
    program.graph program.graphWF program.guardLive

/-- A canonical inhabitant of the pure-policy profile carrier. It is used only
as a fallback outside finite counterfactual site covers; reachable choices are
still supplied by the actual strategy. -/
noncomputable def defaultPureProfile
    (program : Program Player L) [Fintype Player] :
    (who : Player) → program.information.Policy who :=
  fun who info =>
    Classical.choice
      (choice_nonempty program.graph program.graphWF program.guardLive who info)

/-- The graph node count is a uniform strategic horizon. -/
theorem boundedHorizon (program : Program Player L) [Fintype Player] :
    program.execution.BoundedHorizon program.graph.nodeCount := by
  exact toExecutionProtocol_boundedHorizon
    program.graph program.graphWF program.guardLive

/-- The first operational lowering stage carried by a machine program. -/
def system (program : Program Player L) : System where
  State := program.State
  Command := program.Command
  init := program.init
  step := program.step
  terminal := program.terminal

/-- Public/private observations of the first operational lowering stage. -/
def observation (program : Program Player L) : program.system.Observation Player where
  Public := PublicObservation program.graph
  Private := Observation program.graph
  publicView := program.publicView
  privateView := program.view

end Program

/-- A terminal reachable compiled store contains every source binding retained
by the compiler certificate, including sealed bindings. -/
theorem sourceBindingsAvailableAtTerminal
    {Player : Type} [DecidableEq Player] {L : IExpr}
    (compiled : ToEventGraph.CompiledProgram Player L)
    (state : ReachableConfig compiled.graph)
    (hterminal : Terminal compiled.graph state.1) :
    ∀ {name bindTy}
      (h : VHasVar compiled.terminalCtx name bindTy),
      ∃ value,
        Store.getAs state.1.store
          (compiled.terminalState.fieldOf h) bindTy.base = some value := by
  intro name bindTy h
  rcases compiled.terminalState.fieldOf_spec h with
    ⟨spec, hget, hty, _howner⟩
  have hget' :
      compiled.graph.field? (compiled.terminalState.fieldOf h) =
        some spec := by
    rw [← compiled.terminal_graph_eq]
    exact hget
  have havailable :
      compiled.graph.fieldAvailableBefore compiled.graph.nodeCount
        (compiled.terminalState.fieldOf h) = true := by
    rw [← compiled.terminal_graph_eq]
    exact compiled.terminalState.fieldOf_available h
  have hcoherent :=
    reachable_storeCoherent compiled.graphWF state.2
  rcases hcoherent.hasFieldOfAvailable hterminal hget' havailable with
    ⟨value, hvalue⟩
  exact
    ⟨cast (congrArg L.Val hty) value,
      Store.getAs_cast state.1.store
        (compiled.terminalState.fieldOf h) hty hvalue⟩

/-- Terminal compiled payoff evaluation is exactly source payoff evaluation in
the source environment reconstructed from that machine store. -/
theorem sourcePayoffOfTerminal
    {Player : Type} [DecidableEq Player] {L : IExpr}
    (compiled : ToEventGraph.CompiledProgram Player L)
    (state : ReachableConfig compiled.graph)
    (hterminal : Terminal compiled.graph state.1) :
    ∃ sourceEnv : VEnv L compiled.terminalCtx,
      evalPayoffs? compiled.payoffs state.1.store =
        some (evalPayoffs compiled.sourcePayoffs sourceEnv) := by
  let available :
      ∀ {name bindTy}
        (h : VHasVar compiled.terminalCtx name bindTy),
        ∃ value,
          Store.getAs state.1.store
            (compiled.terminalState.fieldOf h) bindTy.base = some value :=
    fun h => sourceBindingsAvailableAtTerminal compiled state hterminal h
  exact
    ⟨ToEventGraph.sourceEnvOfStore compiled.terminalState
        state.1.store available,
      compiled.evalPayoffs_eq_sourceEnvOfStore state.1.store available⟩

/-- Package a checked event-graph compilation as a machine program. -/
def ofCompiled
    {Player : Type} [DecidableEq Player] {L : IExpr}
    (compiled : ToEventGraph.CompiledProgram Player L)
    (guardLive : GuardLive compiled.graph) : Program Player L where
  graph := compiled.graph
  graphWF := compiled.graphWF
  guardLive := guardLive
  payoffs := compiled.payoffs
  payoffsWF := compiled.payoffsWF

/-- Compile a checked Vegas source program to the backend-neutral machine IR. -/
def compile
    {Player : Type} [DecidableEq Player] {L : IExpr}
    (source : WFProgram Player L) : Program Player L :=
  let compiled := ToEventGraph.compile source.core
  ofCompiled compiled (ToEventGraph.compile_guardLive source.core source.legal)

/-- The canonical machine compilation retains an exact source-level terminal
payoff witness for every terminal reachable machine state. -/
theorem compile_sourcePayoffOfTerminal
    {Player : Type} [DecidableEq Player] {L : IExpr}
    (source : WFProgram Player L)
    (state : (compile source).State)
    (hterminal : (compile source).terminal state) :
    ∃ sourceEnv :
        VEnv L (ToEventGraph.compile source.core).terminalCtx,
      evalPayoffs? (compile source).payoffs state.1.store =
        some (evalPayoffs
          (ToEventGraph.compile source.core).sourcePayoffs sourceEnv) := by
  exact sourcePayoffOfTerminal
    (ToEventGraph.compile source.core) state hterminal

/-- Every terminal machine execution reconstructs a possible support-level
written-order source run with the same terminal payoff. -/
theorem compile_sourceStar
    {Player : Type} [DecidableEq Player] {L : IExpr}
    (source : WFProgram Player L)
    (state : (compile source).State)
    (hterminal : (compile source).terminal state) :
    ∃ terminalEnv :
        VEnv L (ToEventGraph.compile source.core).terminalCtx,
      SmallStep.Star
        { ctx := source.core.Γ, env := source.core.env,
          cont := source.core.prog }
        { ctx := (ToEventGraph.compile source.core).terminalCtx,
          env := terminalEnv,
          cont := .ret
            (ToEventGraph.compile source.core).sourcePayoffs } ∧
      evalPayoffs? (compile source).payoffs state.1.store =
        some (evalPayoffs
          (ToEventGraph.compile source.core).sourcePayoffs terminalEnv) := by
  exact ToEventGraph.compile_sourceStar source.core state.1 state.2 hterminal

end Machine

end Vegas
