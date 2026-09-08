/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.Compiler

/-!
# Injectivity of compiler field allocation

The compiler assigns distinct graph fields to source bindings with distinct
names.  This file exposes that invariant without adding proof fields to the
compiler accumulators.
-/

namespace Vegas.ToEventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A dependent source-binding field map reflects equality of variable names. -/
def FieldOfNameInjective {Γ : VCtx P L}
    (fieldOf : {name : VarId} → {bindTy : BindTy P L} →
      VHasVar Γ name bindTy → Nat) : Prop :=
  ∀ {leftName leftTy} (left : VHasVar Γ leftName leftTy)
    {rightName rightTy} (right : VHasVar Γ rightName rightTy),
    fieldOf left = fieldOf right → leftName = rightName

namespace InitialState

theorem empty_fieldOfNameInjective :
    FieldOfNameInjective (InitialState.empty (P := P) (L := L)).fieldOf := by
  intro leftName leftTy left
  cases left

/-- Appending a fresh initial field preserves name injectivity. -/
theorem addField_fieldOfNameInjective {Γ : VCtx P L}
    (state : InitialState P L Γ) (hinjective : FieldOfNameInjective state.fieldOf)
    (name : VarId) (bindTy : BindTy P L) (value : L.Val bindTy.base)
    (hfresh : Fresh name Γ) :
    FieldOfNameInjective (state.addField name bindTy value hfresh).1.fieldOf := by
  intro leftName leftTy left rightName rightTy right heq
  cases left with
  | here =>
      cases right with
      | here => rfl
      | there right =>
          have hlt := state.fieldOf_lt right
          change state.initialFields.length = state.fieldOf right at heq
          omega
  | there left =>
      cases right with
      | here =>
          have hlt := state.fieldOf_lt left
          change state.fieldOf left = state.initialFields.length at heq
          omega
      | there right =>
          change state.fieldOf left = state.fieldOf right at heq
          exact hinjective left right heq

end InitialState

namespace BuildState

/-- Passing from initial-field allocation to body compilation preserves the
same source binding map. -/
theorem fromInitial_fieldOfNameInjective {Γ : VCtx P L}
    (state : InitialState P L Γ)
    (hinjective : FieldOfNameInjective state.fieldOf) :
    FieldOfNameInjective (BuildState.fromInitial state).fieldOf :=
  hinjective

/-- Appending an event gives its new source binding the next field, strictly
above every field already assigned by the accumulator. -/
theorem addEvent_fieldOfNameInjective {Γ : VCtx P L}
    (state : BuildState P L Γ) (hinjective : FieldOfNameInjective state.fieldOf)
    (name : VarId) (bindTy : BindTy P L) (sem : EventGraph.NodeSem P L)
    (hfresh : Fresh name Γ)
    (hnode :
      ({ initialFields := state.initialFields,
         nodes := state.nodes ++
           [{ ty := bindTy.base, owner := bindTy.owner, sem := sem }] } :
        EventGraph.Graph P L).nodeWFAt state.nextNode
        { ty := bindTy.base, owner := bindTy.owner, sem := sem }) :
    FieldOfNameInjective
      (state.addEvent name bindTy sem hfresh hnode).1.fieldOf := by
  intro leftName leftTy left rightName rightTy right heq
  cases left with
  | here =>
      cases right with
      | here => rfl
      | there right =>
          have hlt := state.fieldOf_lt right
          change state.nextField = state.fieldOf right at heq
          unfold nextField nextNode at heq
          omega
  | there left =>
      cases right with
      | here =>
          have hlt := state.fieldOf_lt left
          change state.fieldOf left = state.nextField at heq
          unfold nextField nextNode at heq
          omega
      | there right =>
          change state.fieldOf left = state.fieldOf right at heq
          exact hinjective left right heq

end BuildState

/-- The compiler's initial allocation is name-injective for every well-formed
initial source context. -/
theorem initialState_fieldOfNameInjective :
    {Γ : VCtx P L} → (env : VEnv L Γ) → (wctx : WFCtx Γ) →
      FieldOfNameInjective (initialState Γ env wctx).fieldOf
  | [], _env, _wctx => InitialState.empty_fieldOfNameInjective
  | (name, bindTy) :: Γ, env, wctx => by
      apply InitialState.addField_fieldOfNameInjective
      exact initialState_fieldOfNameInjective (VEnv.tail env) (WFCtx.tail wctx)

/-- Recursive source compilation preserves name injectivity in its terminal
field map. -/
theorem compileCore_terminal_fieldOfNameInjective :
    {Γ : VCtx P L} → (prog : VegasCore P L Γ) →
      (fresh : FreshBindings prog) → (state : BuildState P L Γ) →
      FieldOfNameInjective state.fieldOf →
      FieldOfNameInjective (compileCore prog fresh state).terminalState.fieldOf
  | _, .ret _payoffs, _fresh, _state, hinjective => hinjective
  | _, .sample name dist tail, fresh, state, hinjective => by
      rw [compileCore.eq_2]
      apply compileCore_terminal_fieldOfNameInjective
      exact BuildState.addEvent_fieldOfNameInjective state hinjective
        name _ _ fresh.1 _
  | _, .commit name who guard tail, fresh, state, hinjective => by
      rw [compileCore.eq_3]
      apply compileCore_terminal_fieldOfNameInjective
      exact BuildState.addEvent_fieldOfNameInjective state hinjective
        name _ _ fresh.1 _
  | _, .reveal name who source sourceProof tail, fresh, state, hinjective => by
      rw [compileCore.eq_4]
      apply compileCore_terminal_fieldOfNameInjective
      exact BuildState.addEvent_fieldOfNameInjective state hinjective
        name _ _ fresh.1 _

end Vegas.ToEventGraph
