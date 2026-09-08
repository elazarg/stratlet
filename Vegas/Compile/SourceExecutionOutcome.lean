/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.SourceExecutionGraph
import Vegas.Compile.SourceOutcome
import Vegas.Compile.SourceObservation
import Vegas.Compile.SourceAdequacy

/-! # Terminal outcomes of coupled source execution -/

noncomputable section
namespace Vegas.ToEventGraph
open EventGraph GameTheory.Math.Probability
variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A coupled state at the compiler's terminal build state is a terminal graph
configuration. -/
theorem CoupledAt.terminal_of_terminalState
    (result : BuildResult P L)
    (out : CoupledAt result.graph result.terminalState) :
    Terminal result.graph out.current.graph.1 := by
  intro node
  rw [out.completedPrefix node, result.terminalNodes]
  exact node.isLt

/-- Decoding a terminal coupled graph store recovers its coupled source
environment, modulo the compiler's definitional terminal-context transport. -/
theorem decodeSourceOutcome_coupled
    {Γ : VCtx P L} (prog : VegasCore P L Γ)
    (fresh : FreshBindings prog) (state : BuildState P L Γ)
    (out : CoupledAt (compileCore prog fresh state).graph
      (compileCore prog fresh state).terminalState) :
    decodeSourceOutcome prog fresh state out.current.graph
        (out.terminal_of_terminalState (compileCore prog fresh state)) =
      cast (congrArg (VEnv L)
        (compileCore_terminalCtx_eq_sourceTerminalCtx prog fresh state))
        out.current.source := by
  let result := compileCore prog fresh state
  let hterminal := out.terminal_of_terminalState result
  let hctx := compileCore_terminalCtx_eq_sourceTerminalCtx prog fresh state
  have hdecode : result.decodeTerminalSource out.current.graph hterminal =
      out.current.source :=
    result.decodeTerminalSource_eq out.current.graph hterminal
      out.current.source out.current.agrees
  exact congrArg (fun env => cast (congrArg (VEnv L) hctx) env) hdecode

/-- The decoded graph-outcome marginal of coupled execution is its terminal
source-environment marginal, with only the terminal-context transport erased. -/
theorem runCoupledSource_decodeSourceOutcome [Fintype P]
    {Γ : VCtx P L} (prog : VegasCore P L Γ)
    (fresh : FreshBindings prog) (state : BuildState P L Γ)
    (policies : CommitPolicyProfile (compileCore prog fresh state).graph)
    (hguards : GuardLive (compileCore prog fresh state).graph)
    (current : CoupledAt (compileCore prog fresh state).graph state) :
    (runCoupledSource prog fresh state policies hguards current).map
        (fun out => decodeSourceOutcome prog fresh state out.current.graph
          (out.terminal_of_terminalState (compileCore prog fresh state))) =
      (runCoupledSource prog fresh state policies hguards current).map
        (fun out => cast (congrArg (VEnv L)
          (compileCore_terminalCtx_eq_sourceTerminalCtx prog fresh state))
          out.current.source) := by
  apply FinDist.map_congr_of_eq_on_support
  intro out _
  exact decodeSourceOutcome_coupled prog fresh state out

/-- Canonical empty-prefix coupling between a checked source program's input
environment and its compiled graph's initial store. -/
def compiledInitialCoupled (program : GraphProgram P L) :
    CoupledAt (compile program).graph
      (BuildState.fromInitial (initialState program.Γ program.env program.wctx)) := by
  let initial := initialState program.Γ program.env program.wctx
  let state := BuildState.fromInitial initial
  apply initialCoupledAt state program.env
  · intro name bindTy h
    let initialGraph : Graph P L :=
      { initialFields := initial.initialFields, nodes := [] }
    have hinitial : (compile program).graph.initialFields = initial.initialFields := by
      change (compileCore program.prog program.fresh state).initialFields =
        initial.initialFields
      exact (compileCore_initialFields program.prog program.fresh state).trans rfl
    have hfield : (compile program).graph.field? (initial.fieldOf h) =
        initialGraph.field? (initial.fieldOf h) := by
      have hlt := initial.fieldOf_lt h
      unfold Graph.field?
      rw [hinitial]
      simp [initialGraph, hlt]
    have hstore : (compile program).graph.initialStore (initial.fieldOf h) =
        initialGraph.initialStore (initial.fieldOf h) := by
      unfold Graph.initialStore
      exact congrArg
        (fun field => match field with
          | none => none
          | some spec => spec.initialValue?) hfield
    change Store.getAs (compile program).graph.initialStore
      (initial.fieldOf h) bindTy.base = some (program.env.get h)
    unfold Store.getAs
    rw [hstore]
    exact initialState_getAs program.env program.wctx h
  · rfl

/-- On the canonical initial coupling, observing the graph execution law is
the same as projecting the coupled terminal source environment. -/
theorem runPolicyNodes_observeSourceOutcome_eq_coupled [Fintype P]
    (program : GraphProgram P L) (legal : Legal program.prog)
    (policies : CommitPolicyProfile
      (compileCore program.prog program.fresh
        (BuildState.fromInitial
          (initialState program.Γ program.env program.wctx))).graph)
    (hguards : GuardLive
      (compileCore program.prog program.fresh
        (BuildState.fromInitial
          (initialState program.Γ program.env program.wctx))).graph) :
    let state := BuildState.fromInitial
      (initialState program.Γ program.env program.wctx)
    let current : CoupledAt (compileCore program.prog program.fresh state).graph state := by
      simpa [compile, state] using compiledInitialCoupled program
    (runPolicyNodes (compileCore program.prog program.fresh state).graphWF
      hguards policies current.current.graph
      (compileCore program.prog program.fresh state).graph.nodeOrder).map
        (observeSourceOutcome program legal) =
      (runCoupledSource program.prog program.fresh
        state
        policies hguards current).map
          (fun out => cast (congrArg (VEnv L)
            (compileCore_terminalCtx_eq_sourceTerminalCtx program.prog program.fresh
              state))
            out.current.source) := by
  dsimp only
  let state := BuildState.fromInitial (initialState program.Γ program.env program.wctx)
  let current : CoupledAt (compileCore program.prog program.fresh state).graph state := by
    simpa [compile, state] using compiledInitialCoupled program
  have hgraph := runCoupledSource_graph program.prog program.fresh state policies
    hguards current
  have hnodes : state.nodes.length = 0 := rfl
  rw [hnodes, List.drop_zero] at hgraph
  change _ = (runCoupledSource program.prog program.fresh state policies
    hguards current).map _
  rw [← hgraph, FinDist.map_comp]
  apply FinDist.map_congr_of_eq_on_support
  intro out _
  have hterminal := out.terminal_of_terminalState (compile program)
  unfold Function.comp
  rw [observeSourceOutcome_of_terminal program legal out.current.graph hterminal]
  exact decodeSourceOutcome_coupled program.prog program.fresh state out

end Vegas.ToEventGraph
