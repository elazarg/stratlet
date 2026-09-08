/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Core.Strategy
import Vegas.Compile.FieldMap
import Vegas.Compile.SourceAdequacy

/-!
# Locating source decisions in compiled graphs

This module follows a structural source decision occurrence through the same
state extensions used by `compileCore`, then identifies its exact commitment
row in the resulting graph.
-/

noncomputable section

namespace Vegas.ToEventGraph

open EventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- The compiler state immediately before a source decision occurrence. -/
def decisionSiteState {who : P} :
    {Γ : VCtx P L} → {prog : VegasCore P L Γ} →
      {Δ : VCtx P L} → {x : VarId} → {b : L.Ty} →
      {guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Δ)) L.bool} →
      SourceDecisionSite who prog Δ x b guard → FreshBindings prog →
      BuildState P L Γ → BuildState P L Δ
  | _, _, _, _, _, _, .here _ _, _, state => state
  | _, _, _, _, _, _, .sample (sampleName := name) (dist := dist) site, fresh, state =>
      decisionSiteState site fresh.2 (state.addSampleEvent name dist fresh.1).1
  | _, _, _, _, _, _, .commit (commitName := name) (actor := actor)
      (commitGuard := outerGuard) site, fresh, state =>
      decisionSiteState site fresh.2
        (state.addCommitEvent name actor outerGuard fresh.1).1
  | _, _, _, _, _, _, .reveal (publicName := name) (actor := actor)
      (source := source) site, fresh, state =>
      decisionSiteState site fresh.2
        (state.addRevealEvent name actor source fresh.1).1

/-- Following compilation to a decision site preserves injectivity of the
source-name-to-field allocation. -/
theorem decisionSiteState_fieldOfNameInjective
    {who : P} {Γ Δ : VCtx P L} {prog : VegasCore P L Γ}
    {x : VarId} {b : L.Ty}
    {guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    (site : SourceDecisionSite who prog Δ x b guard)
    (fresh : FreshBindings prog) (state : BuildState P L Γ)
    (hinjective : FieldOfNameInjective state.fieldOf) :
    FieldOfNameInjective (decisionSiteState site fresh state).fieldOf := by
  induction site with
  | here => exact hinjective
  | sample site ih =>
      apply ih fresh.2
      unfold BuildState.addSampleEvent
      apply BuildState.addEvent_fieldOfNameInjective state hinjective
  | commit site ih =>
      apply ih fresh.2
      unfold BuildState.addCommitEvent
      apply BuildState.addEvent_fieldOfNameInjective state hinjective
  | reveal site ih =>
      apply ih fresh.2
      unfold BuildState.addRevealEvent
      apply BuildState.addEvent_fieldOfNameInjective state hinjective

/-- Nodes accumulated before a decision site remain a prefix of the complete
compiled graph. -/
theorem decisionSiteState_nodes_prefix
    {who : P} {Γ Δ : VCtx P L} {prog : VegasCore P L Γ}
    {x : VarId} {b : L.Ty}
    {guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    (site : SourceDecisionSite who prog Δ x b guard)
    (fresh : FreshBindings prog) (state : BuildState P L Γ) :
    (decisionSiteState site fresh state).nodes <+:
      (compileCore prog fresh state).nodes := by
  induction site with
  | here => exact compileCore_nodes_prefix _ fresh state
  | sample site ih => simpa [decisionSiteState, compileCore] using ih fresh.2 _
  | commit site ih => simpa [decisionSiteState, compileCore] using ih fresh.2 _
  | reveal site ih => simpa [decisionSiteState, compileCore] using ih fresh.2 _

@[simp] theorem decisionSiteState_initialFields
    {who : P} {Γ Δ : VCtx P L} {prog : VegasCore P L Γ}
    {x : VarId} {b : L.Ty}
    {guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    (site : SourceDecisionSite who prog Δ x b guard)
    (fresh : FreshBindings prog) (state : BuildState P L Γ) :
    (decisionSiteState site fresh state).initialFields = state.initialFields := by
  induction site with
  | here => rfl
  | sample site ih =>
      simp only [decisionSiteState]
      rw [ih fresh.2]
      simp
  | commit site ih =>
      simp only [decisionSiteState]
      rw [ih fresh.2]
      simp
  | reveal site ih =>
      simp only [decisionSiteState]
      rw [ih fresh.2]
      simp

/-- A source decision occurrence compiles to the commitment row constructed
from its exact pre-decision compiler state. -/
theorem decisionSite_compiledRow
    {who : P} {Γ Δ : VCtx P L} {prog : VegasCore P L Γ}
    {x : VarId} {b : L.Ty}
    {guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    (site : SourceDecisionSite who prog Δ x b guard)
    (fresh : FreshBindings prog) (state : BuildState P L Γ) :
    let siteState := decisionSiteState site fresh state
    let result := compileCore prog fresh state
    ∃ node : Fin result.graph.nodeCount,
      (node : Nat) = siteState.nodes.length ∧
      result.graph.nodes[node]? = some (siteState.commitEvent who guard) := by
  induction site with
  | @here Γ x b guard tail =>
      dsimp [decisionSiteState]
      let added := state.addCommitEvent x who guard fresh.1
      let result := compileCore tail fresh.2 added.1
      have hprefix : added.1.nodes <+: result.nodes :=
        compileCore_nodes_prefix tail fresh.2 added.1
      have hlt : state.nodes.length < result.nodes.length := by
        rcases hprefix with ⟨suffix, hsuffix⟩
        rw [← hsuffix]
        simp [added]
      let node : Fin result.graph.nodeCount :=
        ⟨state.nodes.length, by
          simpa [BuildResult.graph, Graph.nodeCount] using hlt⟩
      refine ⟨node, rfl, ?_⟩
      change result.nodes[(node : Nat)]? = some (state.commitEvent who guard)
      rcases hprefix with ⟨suffix, hsuffix⟩
      rw [← hsuffix]
      simp [node, added]
  | sample site ih =>
      simpa [decisionSiteState, compileCore] using (ih fresh.2 _)
  | commit site ih =>
      simpa [decisionSiteState, compileCore] using (ih fresh.2 _)
  | reveal site ih =>
      simpa [decisionSiteState, compileCore] using (ih fresh.2 _)

/-- Field lookup before a decision site agrees with lookup in the final
compiled graph. -/
theorem decisionSiteState_field?_eq_compileCore
    {who : P} {Γ Δ : VCtx P L} {prog : VegasCore P L Γ}
    {x : VarId} {b : L.Ty}
    {guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    (site : SourceDecisionSite who prog Δ x b guard)
    (fresh : FreshBindings prog) (state : BuildState P L Γ)
    (field : Nat)
    (hfield : field < (decisionSiteState site fresh state).initialFields.length +
      (decisionSiteState site fresh state).nodes.length) :
    ({ initialFields := (decisionSiteState site fresh state).initialFields,
       nodes := (decisionSiteState site fresh state).nodes } : Graph P L).field? field =
      (compileCore prog fresh state).graph.field? field := by
  have hinitial := decisionSiteState_initialFields site fresh state
  have hfinalInitial := compileCore_initialFields prog fresh state
  rcases decisionSiteState_nodes_prefix site fresh state with ⟨suffix, hsuffix⟩
  unfold Graph.field? BuildResult.graph
  rw [hinitial, hfinalInitial]
  by_cases hinit : field < state.initialFields.length
  · simp [hinit]
  · have hnode : field - state.initialFields.length <
        (decisionSiteState site fresh state).nodes.length := by
      rw [hinitial] at hfield
      omega
    simp only [hinit]
    rw [← hsuffix, List.getElem?_append_left hnode]

/-- A graph node has commitment semantics, without choosing a source-level
representation for its guard. -/
def IsCommitNode {G : Graph P L} (node : Fin G.nodeCount) : Prop :=
  ∃ row actor guard, G.nodes[node]? = some row ∧ row.sem = .commit actor guard

/-- A compiled node is the exact row of a structural source decision
occurrence. -/
def CompiledDecisionAt
    {Γ : VCtx P L} (prog : VegasCore P L Γ) (fresh : FreshBindings prog)
    (state : BuildState P L Γ)
    (node : Fin (compileCore prog fresh state).graph.nodeCount) : Prop :=
  ∃ (who : P) (ctx : VCtx P L) (name : VarId) (ty : L.Ty)
      (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who ctx)) L.bool)
      (site : SourceDecisionSite who prog ctx name ty guard),
    (node : Nat) = (decisionSiteState site fresh state).nodes.length ∧
    (compileCore prog fresh state).graph.nodes[node]? =
      some ((decisionSiteState site fresh state).commitEvent who guard)

private theorem currentNode_row
    {Γ : VCtx P L} (state : BuildState P L Γ)
    (event : EventNode P L) (result : BuildResult P L)
    (hprefix : state.nodes ++ [event] <+: result.nodes)
    (node : Fin result.graph.nodeCount) (hnode : (node : Nat) = state.nodes.length) :
    result.graph.nodes[node]? = some event := by
  change result.nodes[(node : Nat)]? = some event
  rcases hprefix with ⟨suffix, hsuffix⟩
  rw [← hsuffix, hnode]
  simp

/-- Every commitment row newly emitted while compiling a suffix comes from a
structural source decision site. -/
theorem compileCore_commitNode_covered :
    {Γ : VCtx P L} → (prog : VegasCore P L Γ) →
      (fresh : FreshBindings prog) → (state : BuildState P L Γ) →
      (node : Fin (compileCore prog fresh state).graph.nodeCount) →
      state.nodes.length ≤ (node : Nat) → IsCommitNode node →
      CompiledDecisionAt prog fresh state node
  | _Γ, .ret _, _fresh, state, node, hnew, _hcommit => by
      have hlt := node.isLt
      change (node : Nat) < state.nodes.length at hlt
      omega
  | Γ, .sample name dist tail, fresh, state, node, hnew, hcommit => by
      let event := state.sampleEvent dist
      let added := state.addSampleEvent name dist fresh.1
      let result := compileCore tail fresh.2 added.1
      have hprefix : state.nodes ++ [event] <+: result.nodes := by
        simpa [added, event] using compileCore_nodes_prefix tail fresh.2 added.1
      by_cases hcurrent : (node : Nat) = state.nodes.length
      · rcases hcommit with ⟨row, actor, guard, hrow, hsem⟩
        have := (currentNode_row state event result hprefix node hcurrent).symm.trans hrow
        have hrowEq := Option.some.inj this
        subst row
        simp [event] at hsem
      · have hlater : added.1.nodes.length ≤ (node : Nat) := by
          simp [added]
          omega
        rcases compileCore_commitNode_covered tail fresh.2 added.1 node hlater hcommit with
          ⟨who, ctx, sourceName, ty, guard, site, hnode, hrow⟩
        refine ⟨who, ctx, sourceName, ty, guard,
          SourceDecisionSite.sample (Γ := Γ) (sampleName := name) (dist := dist) site,
          ?_, ?_⟩
        · change (node : Nat) = (decisionSiteState site fresh.2 added.1).nodes.length
          exact hnode
        · change (compileCore tail fresh.2 added.1).graph.nodes[node]? =
            some ((decisionSiteState site fresh.2 added.1).commitEvent who guard)
          exact hrow
  | Γ, .commit name actor guard tail, fresh, state, node, hnew, hcommit => by
      let event := state.commitEvent actor guard
      let added := state.addCommitEvent name actor guard fresh.1
      let result := compileCore tail fresh.2 added.1
      have hprefix : state.nodes ++ [event] <+: result.nodes := by
        simpa [added, event] using compileCore_nodes_prefix tail fresh.2 added.1
      by_cases hcurrent : (node : Nat) = state.nodes.length
      · exact ⟨actor, _, name, _, guard, .here guard tail, hcurrent,
          currentNode_row state event result hprefix node hcurrent⟩
      · have hlater : added.1.nodes.length ≤ (node : Nat) := by
          simp [added]
          omega
        rcases compileCore_commitNode_covered tail fresh.2 added.1 node hlater hcommit with
          ⟨who, ctx, sourceName, ty, sourceGuard, site, hnode, hrow⟩
        refine ⟨who, ctx, sourceName, ty, sourceGuard,
          SourceDecisionSite.commit (Γ := Γ) (commitName := name) (actor := actor)
            (commitGuard := guard) site, ?_, ?_⟩
        · change (node : Nat) = (decisionSiteState site fresh.2 added.1).nodes.length
          exact hnode
        · change (compileCore tail fresh.2 added.1).graph.nodes[node]? =
            some ((decisionSiteState site fresh.2 added.1).commitEvent who sourceGuard)
          exact hrow
  | Γ, .reveal name actor sourceName source tail, fresh, state, node, hnew, hcommit => by
      let event := state.revealEvent actor source
      let added := state.addRevealEvent name actor source fresh.1
      let result := compileCore tail fresh.2 added.1
      have hprefix : state.nodes ++ [event] <+: result.nodes := by
        simpa [added, event] using compileCore_nodes_prefix tail fresh.2 added.1
      by_cases hcurrent : (node : Nat) = state.nodes.length
      · rcases hcommit with ⟨row, commitActor, guard, hrow, hsem⟩
        have := (currentNode_row state event result hprefix node hcurrent).symm.trans hrow
        have hrowEq := Option.some.inj this
        subst row
        simp [event] at hsem
      · have hlater : added.1.nodes.length ≤ (node : Nat) := by
          simp [added]
          omega
        rcases compileCore_commitNode_covered tail fresh.2 added.1 node hlater hcommit with
          ⟨who, ctx, decisionName, ty, guard, site, hnode, hrow⟩
        refine ⟨who, ctx, decisionName, ty, guard,
          SourceDecisionSite.reveal (Γ := Γ) (publicName := name) (actor := actor)
            (source := source) site, ?_, ?_⟩
        · change (node : Nat) = (decisionSiteState site fresh.2 added.1).nodes.length
          exact hnode
        · change (compileCore tail fresh.2 added.1).graph.nodes[node]? =
            some ((decisionSiteState site fresh.2 added.1).commitEvent who guard)
          exact hrow

end Vegas.ToEventGraph
