/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.SourceOutcome
import Vegas.EventGraph.Protocol

/-! # Source outcomes as observations of compiled executions

Terminal stores decode to the independently defined terminal source context.
A total observation also assigns an outcome to nonterminal states; bounded
complete runs never use that fallback.
-/

noncomputable section

namespace Vegas.ToEventGraph

open EventGraph GameTheory.Protocol GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A source outcome exists for every legal program and initial environment.
This supplies only the off-terminal fallback of a total decoder. -/
def sourceOutcomeFallback (program : GraphProgram P L) (legal : Legal program.prog) :
    VEnv L (sourceTerminalCtx program.prog) :=
  (denoteSource program.prog (legalSourceProfile program.prog legal)
    program.env).support_nonempty.choose

/-- Observe the complete source environment in a compiled terminal state.
The arbitrary fallback is used only outside terminal execution. -/
def observeSourceOutcome (program : GraphProgram P L) (legal : Legal program.prog)
    (state : ReachableConfig (compile program).graph) :
    VEnv L (sourceTerminalCtx program.prog) := by
  classical
  exact if hterminal : Terminal (compile program).graph state.1 then
    decodeSourceOutcome program.prog program.fresh
      (BuildState.fromInitial (initialState program.Γ program.env program.wctx)) state hterminal
  else sourceOutcomeFallback program legal

theorem observeSourceOutcome_of_terminal (program : GraphProgram P L)
    (legal : Legal program.prog) (state : ReachableConfig (compile program).graph)
    (hterminal : Terminal (compile program).graph state.1) :
    observeSourceOutcome program legal state =
      decodeSourceOutcome program.prog program.fresh
        (BuildState.fromInitial (initialState program.Γ program.env program.wctx))
        state hterminal := by
  rw [observeSourceOutcome, dif_pos hterminal]

/-- Every completed behavioral play uses terminal source decoding. This holds
for arbitrary native policies, independently of a source-policy translation. -/
theorem observeSourceOutcome_runBehavioral [Fintype P]
    (program : GraphProgram P L) (legal : Legal program.prog)
    (policies : ∀ who, (toInformationModel (compile program).graph
      (compile program).graphWF (compile_guardLive program legal)).BehavioralPolicy who)
    (history : (toExecutionProtocol (compile program).graph
      (compile program).graphWF (compile_guardLive program legal)).History)
    (hsupport : history ∈ ((toInformationModel (compile program).graph
      (compile program).graphWF (compile_guardLive program legal)).runBehavioral
      policies (compile program).graph.nodeCount).support) :
    ∃ hterminal : Terminal (compile program).graph history.state.1,
      observeSourceOutcome program legal history.state =
        decodeSourceOutcome program.prog program.fresh
          (BuildState.fromInitial (initialState program.Γ program.env program.wctx))
          history.state hterminal := by
  have hterminal := (toInformationModel (compile program).graph
    (compile program).graphWF (compile_guardLive program legal)).runBehavioralFrom_terminal_of_bound
      policies (toExecutionProtocol_boundedHorizon (compile program).graph
        (compile program).graphWF (compile_guardLive program legal)) _ _ hsupport
  exact ⟨hterminal, observeSourceOutcome_of_terminal program legal history.state hterminal⟩

end Vegas.ToEventGraph
