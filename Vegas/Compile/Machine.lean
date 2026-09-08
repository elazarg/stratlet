/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.SourceAdequacy
import Vegas.Machine.Program

/-! # Checked-source compilation to backend-neutral machine programs

The machine carrier and its execution model are independent of the source
compiler. This module constructs that carrier from a checked source program
and transports source-support and terminal-payout adequacy.
-/

noncomputable section

namespace Vegas
namespace Machine

open EventGraph
open GameTheory.Math.Probability

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
written-order source run with matching terminal bindings and payout evaluation. -/
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
          (ToEventGraph.compile source.core).sourcePayoffs terminalEnv) ∧
      ∀ {name bindTy}
          (h : VHasVar (ToEventGraph.compile source.core).terminalCtx name bindTy),
        Store.getAs state.1.store
            ((ToEventGraph.compile source.core).terminalState.fieldOf h) bindTy.base =
          some (terminalEnv.get h) := by
  exact ToEventGraph.compile_sourceStar source.core state.1 state.2 hterminal

end Machine

end Vegas
