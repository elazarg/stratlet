/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationImageRefinement
import Vegas.Compile.SourceOutcome

/-! # Public terminal outcomes of generated applications

The executable decoder in this file reads only compiler-allocated public
terminal fields.  Its result type omits sealed source bindings.  Full source
environments appear only as proof witnesses relating this public result to the
compiler's terminal decoder.
-/

namespace Vegas.ToEventGraph

open EventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

private def BuildState.tail {name : VarId} {bindTy : BindTy P L} {Γ : VCtx P L}
    (state : BuildState P L ((name, bindTy) :: Γ)) : BuildState P L Γ where
  initialFields := state.initialFields
  nodes := state.nodes
  wctx := state.wctx.tail
  fieldOf h := state.fieldOf (.there h)
  fieldOf_spec h := state.fieldOf_spec (.there h)
  fieldOf_available h := state.fieldOf_available (.there h)
  graphWF := state.graphWF

/-- Read the public projection of a typed source context through its compiler
field allocation. A missing or ill-typed public field makes the read fail;
sealed fields are never inspected. -/
def BuildState.readPublicEnv? : {Γ : VCtx P L} →
    BuildState P L Γ → Store L → Option (Env L.Val (erasePubVCtx Γ))
  | [], _, _ => some (Env.empty L.Val)
  | (_name, ⟨ty, .pub⟩) :: _Γ, state, store => do
      let value ← Store.getAs store (state.fieldOf VHasVar.here) ty
      let tail ← state.tail.readPublicEnv? store
      pure (Env.cons value tail)
  | (_name, ⟨_ty, .sealed _owner⟩) :: _Γ, state, store =>
      state.tail.readPublicEnv? store

/-- Executable public terminal readout for an application memory. -/
def BuildResult.readPublicTerminal? (result : BuildResult P L)
    (memory : ApplicationImage.Memory P L) :
    Option (Env L.Val (erasePubVCtx result.terminalCtx)) :=
  result.terminalState.readPublicEnv? memory.store

private theorem BuildState.readPublicEnv?_eq_erasePubEnv
    {Γ : VCtx P L} (state : BuildState P L Γ) (store : Store L)
    (env : VEnv L Γ)
    (hagrees : ∀ {name bindTy} (h : VHasVar Γ name bindTy),
      bindTy.owner = none →
        Store.getAs store (state.fieldOf h) bindTy.base = some (env.get h)) :
    state.readPublicEnv? store = some env.erasePubEnv := by
  induction Γ with
  | nil => rfl
  | cons head tail ih =>
      obtain ⟨name, bindTy⟩ := head
      cases bindTy with
      | mk ty visibility =>
          cases visibility with
          | pub =>
              rw [BuildState.readPublicEnv?]
              rw [hagrees VHasVar.here rfl]
              rw [ih]
              · rfl
              · intro query queryTy h howner
                exact hagrees (.there h) howner
          | sealed owner =>
              rw [BuildState.readPublicEnv?]
              apply ih
              intro query queryTy h howner
              exact hagrees (.there h) howner

/-- At a reachable terminal configuration, represented application memory has
the public data needed to decode the terminal public environment. The decoder
ignores any other retained operational data. The right side is the public
projection of the proof-only full source decoder. -/
theorem BuildResult.readPublicTerminal?_eq_decodeTerminalSource
    (result : BuildResult P L)
    (memory : ApplicationImage.Memory P L)
    (cfg : ReachableConfig result.graph)
    (hrep : memory.Represents cfg.1)
    (hterminal : Terminal result.graph cfg.1) :
    result.readPublicTerminal? memory =
      some (result.decodeTerminalSource cfg hterminal).erasePubEnv := by
  apply result.terminalState.readPublicEnv?_eq_erasePubEnv
  intro name bindTy binding hpublic
  have href : result.graph.fieldRefPublic
      { field := result.terminalState.fieldOf binding, ty := bindTy.base } := by
    rcases result.terminalState.fieldOf_spec binding with
      ⟨spec, hfield, hty, howner⟩
    rw [result.terminal_graph_eq] at hfield
    exact ⟨spec, hfield, hty, howner.trans hpublic⟩
  have hmemory := hrep.publicFields
    { field := result.terminalState.fieldOf binding, ty := bindTy.base } href
  have hsource := sourceEnvOfStore_get result.terminalState cfg.1.store
    (result.terminalBindingAvailable cfg hterminal) binding
  rw [hmemory, hsource]
  rfl

end Vegas.ToEventGraph

/-- info: 'Vegas.ToEventGraph.BuildResult.readPublicTerminal?_eq_decodeTerminalSource' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ToEventGraph.BuildResult.readPublicTerminal?_eq_decodeTerminalSource
