/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.SourceLaw
import Vegas.Core.Strategy

/-! # Terminal source outcomes of compiled programs -/

noncomputable section

namespace Vegas.ToEventGraph

open EventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- The compiler's dependent terminal context is the context obtained by
following the source continuations. -/
theorem compileCore_terminalCtx_eq_sourceTerminalCtx :
    {Γ : VCtx P L} → (prog : VegasCore P L Γ) →
      (fresh : FreshBindings prog) → (state : BuildState P L Γ) →
      (compileCore prog fresh state).terminalCtx = sourceTerminalCtx prog
  | _, .ret _, _, _ => rfl
  | _, .sample _ _ tail, fresh, state => by
      exact compileCore_terminalCtx_eq_sourceTerminalCtx tail fresh.2 _
  | _, .commit _ _ _ tail, fresh, state => by
      exact compileCore_terminalCtx_eq_sourceTerminalCtx tail fresh.2 _
  | _, .reveal _ _ _ _ tail, fresh, state => by
      exact compileCore_terminalCtx_eq_sourceTerminalCtx tail fresh.2 _

/-- Every binding in the compiler's terminal field map can be read from a
reachable terminal configuration. -/
theorem BuildResult.terminalBindingAvailable (result : BuildResult P L)
    (cfg : ReachableConfig result.graph) (hterminal : Terminal result.graph cfg.1) :
    ∀ {name bindTy} (h : VHasVar result.terminalCtx name bindTy),
      ∃ value, Store.getAs cfg.1.store
        (result.terminalState.fieldOf h) bindTy.base = some value := by
  intro name bindTy h
  rcases result.terminalState.fieldOf_spec h with ⟨spec, hget, hty, _⟩
  have hget' : result.graph.field? (result.terminalState.fieldOf h) = some spec := by
    rw [← result.terminal_graph_eq]
    exact hget
  have havailable : result.graph.fieldAvailableBefore result.graph.nodeCount
      (result.terminalState.fieldOf h) = true := by
    rw [← result.terminal_graph_eq]
    exact result.terminalState.fieldOf_available h
  rcases (reachable_storeCoherent result.graphWF cfg.2).hasFieldOfAvailable
      hterminal hget' havailable with ⟨value, hvalue⟩
  exact ⟨cast (congrArg L.Val hty) value,
    Store.getAs_cast cfg.1.store (result.terminalState.fieldOf h) hty hvalue⟩

/-- Decode the complete terminal source environment, including sealed fields,
from an actual terminal graph store. -/
def BuildResult.decodeTerminalSource (result : BuildResult P L)
    (cfg : ReachableConfig result.graph) (hterminal : Terminal result.graph cfg.1) :
    VEnv L result.terminalCtx :=
  sourceEnvOfStore result.terminalState cfg.1.store
    (result.terminalBindingAvailable cfg hterminal)

/-- Terminal decoding is inverse to compiler-store agreement. -/
theorem BuildResult.decodeTerminalSource_eq (result : BuildResult P L)
    (cfg : ReachableConfig result.graph) (hterminal : Terminal result.graph cfg.1)
    (env : VEnv L result.terminalCtx)
    (hagrees : result.terminalState.Agrees cfg.1.store env) :
    result.decodeTerminalSource cfg hterminal = env := by
  exact sourceEnvOfStore_eq_of_get result.terminalState cfg.1.store
    (result.terminalBindingAvailable cfg hterminal) env hagrees

/-- Decode a compiled terminal configuration directly into the source
semantics' independently defined outcome carrier. -/
def decodeSourceOutcome {Γ : VCtx P L} (prog : VegasCore P L Γ)
    (fresh : FreshBindings prog) (state : BuildState P L Γ)
    (cfg : ReachableConfig (compileCore prog fresh state).graph)
    (hterminal : Terminal (compileCore prog fresh state).graph cfg.1) :
    VEnv L (sourceTerminalCtx prog) := by
  rw [← compileCore_terminalCtx_eq_sourceTerminalCtx prog fresh state]
  exact (compileCore prog fresh state).decodeTerminalSource cfg hterminal

end Vegas.ToEventGraph
