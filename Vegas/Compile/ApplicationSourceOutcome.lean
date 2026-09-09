/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationImageOutcome
import Vegas.Compile.ApplicationImageStateRefinement
import Vegas.Compile.SourceAdequacy

/-! # Source outcomes of finished generated applications

Runtime completion is a finite scan of the emitted node range. Combined with
the proof-facing application refinement relation, it yields an actual terminal
source execution and the matching executable public terminal readout.
-/

namespace Vegas.ApplicationImage

open EventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Executable completion check over the compiler-emitted node count. -/
def Memory.finished (memory : Memory P L) (nodeCount : Nat) : Bool :=
  (List.range nodeCount).all memory.done

private theorem State.Refines.terminal_of_finished
    {G : Graph P L} {state : State P L} {cfg : Config G}
    (hrefines : state.Refines cfg)
    (hfinished : state.memory.finished G.nodeCount = true) : Terminal G cfg := by
  intro node
  apply (hrefines.memory.completed node).mp
  apply List.all_eq_true.mp hfinished node.val
  exact List.mem_range.mpr node.isLt

end Vegas.ApplicationImage

namespace Vegas.ToEventGraph

open ApplicationImage EventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A finished refining application state determines a possible terminal
written-order source execution and exposes exactly its public terminal
bindings. This is a support-level safety statement, not a source strategy or
progress law. -/
theorem source_public_outcome_of_refines
    (source : GraphProgram P L)
    (native : ApplicationImage.State P L)
    (cfg : Config (compile source).graph)
    (hrefines : native.Refines cfg)
    (hfinished : native.memory.finished (compile source).graph.nodeCount = true) :
    ∃ terminalEnv : VEnv L (compile source).terminalCtx,
      SmallStep.Star
        { ctx := source.Γ, env := source.env, cont := source.prog }
        { ctx := (compile source).terminalCtx,
          env := terminalEnv,
          cont := .ret (compile source).sourcePayoffs } ∧
      (compile source).readPublicTerminal? native.memory =
        some terminalEnv.erasePubEnv := by
  have hterminal := hrefines.terminal_of_finished hfinished
  rcases compile_sourceStar source cfg hrefines.reachable hterminal with
    ⟨terminalEnv, hstar, _hpayoffs, hagrees⟩
  let reachableCfg : ReachableConfig (compile source).graph :=
    ⟨cfg, hrefines.reachable⟩
  have hdecode : (compile source).decodeTerminalSource reachableCfg hterminal =
      terminalEnv :=
    (compile source).decodeTerminalSource_eq reachableCfg hterminal terminalEnv hagrees
  refine ⟨terminalEnv, hstar, ?_⟩
  rw [(compile source).readPublicTerminal?_eq_decodeTerminalSource
    native.memory reachableCfg hrefines.memory hterminal, hdecode]

end Vegas.ToEventGraph

/-- info: 'Vegas.ToEventGraph.source_public_outcome_of_refines' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ToEventGraph.source_public_outcome_of_refines
