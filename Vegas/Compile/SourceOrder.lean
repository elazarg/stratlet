/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.DecisionSite

/-! # Source-order dependencies of compiled decisions -/

noncomputable section

namespace Vegas.ToEventGraph

open EventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Every allocated initial field is represented by a source binding. -/
def InitialFieldsCovered {Γ : VCtx P L} (state : InitialState P L Γ) : Prop :=
  ∀ field, field < state.initialFields.length →
    ∃ (name : VarId) (bindTy : BindTy P L) (h : VHasVar Γ name bindTy),
      state.fieldOf h = field

theorem InitialState.empty_fieldsCovered :
    InitialFieldsCovered (InitialState.empty (P := P) (L := L)) := by
  intro field hfield
  change field < 0 at hfield
  omega

theorem InitialState.addField_fieldsCovered
    {Γ : VCtx P L} (state : InitialState P L Γ)
    (hcovered : InitialFieldsCovered state)
    (name : VarId) (bindTy : BindTy P L) (value : L.Val bindTy.base)
    (fresh : Fresh name Γ) :
    InitialFieldsCovered (state.addField name bindTy value fresh).1 := by
  intro field hfield
  by_cases hold : field < state.initialFields.length
  · rcases hcovered field hold with ⟨oldName, oldTy, old, heq⟩
    exact ⟨oldName, oldTy, .there old, heq⟩
  · have heq : field = state.initialFields.length := by
      change field < (state.initialFields ++ [_]).length at hfield
      simp only [List.length_append, List.length_singleton] at hfield
      omega
    exact ⟨name, bindTy, .here, by
      change state.initialFields.length = field
      exact heq.symm⟩

/-- Canonical allocation covers every field of an arbitrary checked initial
source context. -/
theorem initialState_fieldsCovered :
    {Γ : VCtx P L} → (env : VEnv L Γ) → (wctx : WFCtx Γ) →
      InitialFieldsCovered (initialState Γ env wctx)
  | [], _env, _wctx => InitialState.empty_fieldsCovered
  | (name, bindTy) :: Γ, env, wctx => by
      apply InitialState.addField_fieldsCovered
      exact initialState_fieldsCovered (VEnv.tail env) (WFCtx.tail wctx)

/-- Every field allocated so far is represented by a source binding. -/
def FieldsCovered {Γ : VCtx P L} (state : BuildState P L Γ) : Prop :=
  ∀ field, field < state.initialFields.length + state.nodes.length →
    ∃ (name : VarId) (bindTy : BindTy P L) (h : VHasVar Γ name bindTy),
      state.fieldOf h = field

theorem BuildState.empty_fieldsCovered :
    FieldsCovered (BuildState.fromInitial (InitialState.empty (P := P) (L := L))) := by
  intro field hfield
  change field < 0 at hfield
  omega

theorem BuildState.fromInitial_fieldsCovered
    {Γ : VCtx P L} (state : InitialState P L Γ)
    (hcovered : InitialFieldsCovered state) :
    FieldsCovered (BuildState.fromInitial state) := by
  intro field hfield
  change field < state.initialFields.length at hfield
  exact hcovered field hfield

theorem BuildState.addEvent_fieldsCovered
    {Γ : VCtx P L} (state : BuildState P L Γ) (hcovered : FieldsCovered state)
    (name : VarId) (bindTy : BindTy P L) (sem : NodeSem P L)
    (fresh : Fresh name Γ)
    (hnode :
      ({ initialFields := state.initialFields,
         nodes := state.nodes ++ [{ ty := bindTy.base, owner := bindTy.owner, sem := sem }] } :
        Graph P L).nodeWFAt state.nextNode
        { ty := bindTy.base, owner := bindTy.owner, sem := sem }) :
    FieldsCovered (state.addEvent name bindTy sem fresh hnode).1 := by
  intro field hfield
  by_cases hold : field < state.initialFields.length + state.nodes.length
  · rcases hcovered field hold with ⟨oldName, oldTy, old, heq⟩
    exact ⟨oldName, oldTy, .there old, heq⟩
  · have heq : field = state.initialFields.length + state.nodes.length := by
      simp only [BuildState.addEvent_initialFields, BuildState.addEvent_nodes,
        List.length_append, List.length_singleton] at hfield
      omega
    exact ⟨name, bindTy, .here, by simp [BuildState.addEvent_fieldOf_here,
      BuildState.nextField, BuildState.nextNode, heq]⟩

/-- Field coverage is retained while following compilation to a decision site. -/
theorem decisionSiteState_fieldsCovered
    {who : P} {Γ Δ : VCtx P L} {prog : VegasCore P L Γ}
    {x : VarId} {b : L.Ty}
    {guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    (site : SourceDecisionSite who prog Δ x b guard)
    (fresh : FreshBindings prog) (state : BuildState P L Γ)
    (hcovered : FieldsCovered state) :
    FieldsCovered (decisionSiteState site fresh state) := by
  induction site with
  | here => exact hcovered
  | sample site ih =>
      apply ih fresh.2
      unfold BuildState.addSampleEvent
      apply BuildState.addEvent_fieldsCovered state hcovered
  | commit site ih =>
      apply ih fresh.2
      unfold BuildState.addCommitEvent
      apply BuildState.addEvent_fieldsCovered state hcovered
  | reveal site ih =>
      apply ih fresh.2
      unfold BuildState.addRevealEvent
      apply BuildState.addEvent_fieldsCovered state hcovered

/-- No coverage premise is needed at the canonical compiler entry state. -/
theorem decisionSiteState_initial_fieldsCovered
    {who : P} {Γ Δ : VCtx P L} {prog : VegasCore P L Γ}
    {x : VarId} {b : L.Ty}
    {guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    (site : SourceDecisionSite who prog Δ x b guard)
    (fresh : FreshBindings prog) (env : VEnv L Γ) (wctx : WFCtx Γ) :
    FieldsCovered (decisionSiteState site fresh
      (BuildState.fromInitial (initialState Γ env wctx))) := by
  apply decisionSiteState_fieldsCovered
  apply BuildState.fromInitial_fieldsCovered
  exact initialState_fieldsCovered env wctx

private def VHasVar.toViewOfOwner
    {Γ : VCtx P L} {name : VarId} {bindTy : BindTy P L}
    (h : VHasVar Γ name bindTy) (who : P)
    (howner : bindTy.owner = none ∨ bindTy.owner = some who) :
    VHasVar (viewVCtx who Γ) name bindTy := by
  induction Γ with
  | nil => exact nomatch h
  | cons head tail ih =>
      obtain ⟨headName, headTy⟩ := head
      simp only [viewVCtx]
      split
      · cases h with
        | here => exact .here
        | there htail => exact .there (ih htail)
      · cases h with
        | here =>
            rename_i hhidden
            have hsee : canSee who bindTy := by
              cases bindTy with
              | mk base visibility =>
                  cases visibility with
                  | pub => simp [canSee, Visibility.canSee]
                  | sealed owner =>
                      rcases howner with hpublic | hsealed
                      · simp [BindTy.owner] at hpublic
                      · simp [BindTy.owner] at hsealed
                        exact show decide (who = owner) = true by simp [hsealed.symm]
            exact (hhidden hsee).elim
        | there htail => exact ih htail

/-- Every earlier same-owner commitment field is part of a later source
decision's choice information. -/
theorem earlierCommit_mem_decisionReads
    {who : P} {Γ Δ : VCtx P L} {prog : VegasCore P L Γ}
    {x : VarId} {b : L.Ty}
    {guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    (site : SourceDecisionSite who prog Δ x b guard)
    (fresh : FreshBindings prog) (state : BuildState P L Γ)
    (hcovered : FieldsCovered state)
    (earlier : Nat)
    (hearlier : earlier < (decisionSiteState site fresh state).nodes.length)
    (row : EventNode P L) (hrow :
      (decisionSiteState site fresh state).nodes[earlier]? = some row)
    {earlierGuard : EventGuard L}
    (hcommit : row.sem = .commit who earlierGuard) :
    ({ field := (decisionSiteState site fresh state).initialFields.length + earlier,
       ty := row.ty } : FieldRef L) ∈
      (eventGuardOf (decisionSiteState site fresh state) who guard).choiceReads := by
  let siteState := decisionSiteState site fresh state
  change earlier < siteState.nodes.length at hearlier
  have hsiteCovered : FieldsCovered siteState :=
    decisionSiteState_fieldsCovered site fresh state hcovered
  rcases hsiteCovered (siteState.initialFields.length + earlier) (by omega) with
    ⟨name, bindTy, binding, hfield⟩
  rcases siteState.fieldOf_spec binding with ⟨spec, hspec, hty, howner⟩
  have hnot : ¬ siteState.initialFields.length + earlier <
      siteState.initialFields.length := by omega
  have hrowOwner : row.owner = some who := by
    have hwf := siteState.graphWF earlier row hrow
    unfold Graph.nodeWFAt at hwf
    rw [hcommit] at hwf
    exact hwf.2.2.1
  have hspec' : spec =
      { ty := row.ty, owner := some who, source := .event earlier } := by
    rw [hfield] at hspec
    simp only [Graph.field?, dite_eq_ite, hnot, if_false, Nat.add_sub_cancel_left] at hspec
    rw [hrow] at hspec
    simpa [hrowOwner] using hspec.symm
  have hbindOwner : bindTy.owner = some who := by
    rw [← howner, hspec']
  have hbindTy : bindTy.base = row.ty := by
    rw [← hty, hspec']
  let visibleBinding := VHasVar.toViewOfOwner binding who (Or.inr hbindOwner)
  have hmem := fieldRefOfView_mem_visibleFieldRefs siteState who visibleBinding
  have hvisibleField :
      siteState.fieldOf (VHasVar.ofViewVCtx visibleBinding) =
        siteState.initialFields.length + earlier := by
    rw [siteState.fieldOf_eq_of_nodup (VHasVar.ofViewVCtx visibleBinding) binding,
      hfield]
  change siteState.fieldRefOfView who visibleBinding ∈
    (eventGuardOf siteState who guard).choiceReads at hmem
  simpa [BuildState.fieldRefOfView, hvisibleField, hbindTy] using hmem

end Vegas.ToEventGraph
