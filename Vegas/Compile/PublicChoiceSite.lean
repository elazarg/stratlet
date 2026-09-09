/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.DecisionSite
import Vegas.Compile.PublicChoice

/-! # Source-certified adjacent public choices -/

noncomputable section

namespace Vegas

open EventGraph ToEventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- An ordinary source decision whose immediate continuation reveals that
same decision. This is occurrence evidence, not a new source constructor. -/
structure PublicChoiceSite {Γ : VCtx P L} (prog : VegasCore P L Γ) where
  context : VCtx P L
  choiceName : VarId
  publicName : VarId
  owner : P
  ty : L.Ty
  guard : L.Expr ((choiceName, ty) :: eraseVCtx (viewVCtx owner context)) L.bool
  tail : VegasCore P L
    ((publicName, .pub ty) :: (choiceName, .sealed owner ty) :: context)
  decision : SourceDecisionSite owner prog context choiceName ty guard
  adjacent : decision.continuation =
    .reveal publicName owner choiceName .here tail

namespace PublicChoiceSite

def siteState {Γ : VCtx P L} {prog : VegasCore P L Γ}
    (site : PublicChoiceSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) : BuildState P L site.context :=
  decisionSiteState site.decision fresh state

private theorem siteFresh {Γ : VCtx P L} {prog : VegasCore P L Γ}
    (site : PublicChoiceSite prog) (fresh : FreshBindings prog) :
    FreshBindings (.commit site.choiceName site.owner site.guard site.decision.continuation) := by
  exact site.decision.decision_fresh fresh

private theorem compiledRows {Γ : VCtx P L} {prog : VegasCore P L Γ}
    {context : VCtx P L} {choiceName publicName : VarId} {owner : P} {ty : L.Ty}
    {guard : L.Expr ((choiceName, ty) :: eraseVCtx (viewVCtx owner context)) L.bool}
    (decision : SourceDecisionSite owner prog context choiceName ty guard)
    (tail : VegasCore P L ((publicName, .pub ty) :: (choiceName, .sealed owner ty) :: context))
    (adjacent : decision.continuation = .reveal publicName owner choiceName .here tail)
    (fresh : FreshBindings prog)
    (state : BuildState P L Γ) :
    let current := decisionSiteState decision fresh state
    let result := compileCore prog fresh state
    ∃ choice publication : Fin result.graph.nodeCount,
      (choice : Nat) = current.nodes.length ∧
      (publication : Nat) = current.nodes.length + 1 ∧
      result.graph.nodes[choice]? = some (current.commitEvent owner guard) ∧
      result.graph.nodes[publication]? = some
        ((current.addCommitEvent choiceName owner guard
          (decision.decision_fresh fresh).1).1.revealEvent owner .here) := by
  induction decision with
  | @here context choiceName ty guard continuation =>
      dsimp [decisionSiteState]
      have hadjacent := adjacent
      dsimp [SourceDecisionSite.continuation] at hadjacent
      subst continuation
      let committed := state.addCommitEvent choiceName owner guard fresh.1
      let revealed := committed.1.addRevealEvent publicName owner .here fresh.2.1
      let result := compileCore tail fresh.2.2 revealed.1
      have hprefix : revealed.1.nodes <+: result.nodes :=
        compileCore_nodes_prefix _ fresh.2.2 revealed.1
      rcases hprefix with ⟨suffix, hsuffix⟩
      have hchoice : state.nodes.length < result.nodes.length := by
        rw [← hsuffix]
        simp [revealed, committed]
      have hpublication : state.nodes.length + 1 < result.nodes.length := by
        rw [← hsuffix]
        simp [revealed, committed]
      let choice : Fin result.graph.nodeCount := ⟨state.nodes.length, by
        simpa [BuildResult.graph, Graph.nodeCount] using hchoice⟩
      let publication : Fin result.graph.nodeCount := ⟨state.nodes.length + 1, by
        simpa [BuildResult.graph, Graph.nodeCount] using hpublication⟩
      refine ⟨choice, publication, rfl, rfl, ?_, ?_⟩
      · change result.nodes[state.nodes.length]? = some (state.commitEvent _ _)
        rw [← hsuffix]
        simp [revealed, committed]
      · change result.nodes[state.nodes.length + 1]? =
          some (committed.1.revealEvent _ .here)
        rw [← hsuffix]
        simp [revealed, committed]
  | sample decision ih =>
      exact ih tail adjacent fresh.2 (state.addSampleEvent _ _ fresh.1).1
  | commit decision ih =>
      exact ih tail adjacent fresh.2 (state.addCommitEvent _ _ _ fresh.1).1
  | reveal decision ih =>
      exact ih tail adjacent fresh.2 (state.addRevealEvent _ _ _ fresh.1).1

def choiceNode {Γ : VCtx P L} {prog : VegasCore P L Γ}
    (site : PublicChoiceSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) : Fin (compileCore prog fresh state).graph.nodeCount :=
  ⟨(site.siteState fresh state).nodes.length, by
    rcases compiledRows site.decision site.tail site.adjacent fresh state with
      ⟨choice, _, hchoice, _⟩
    change (decisionSiteState site.decision fresh state).nodes.length < _
    rw [← hchoice]
    exact choice.isLt⟩

def publicationNode {Γ : VCtx P L} {prog : VegasCore P L Γ}
    (site : PublicChoiceSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) : Fin (compileCore prog fresh state).graph.nodeCount :=
  ⟨(site.siteState fresh state).nodes.length + 1, by
    rcases compiledRows site.decision site.tail site.adjacent fresh state with
      ⟨_, publication, _, hpublication, _⟩
    change (decisionSiteState site.decision fresh state).nodes.length + 1 < _
    rw [← hpublication]
    exact publication.isLt⟩

@[simp] theorem choiceNode_val {Γ : VCtx P L} {prog : VegasCore P L Γ}
    (site : PublicChoiceSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) :
    (choiceNode site fresh state : Nat) = (site.siteState fresh state).nodes.length := rfl

@[simp] theorem publicationNode_val {Γ : VCtx P L} {prog : VegasCore P L Γ}
    (site : PublicChoiceSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) :
    (publicationNode site fresh state : Nat) =
      (site.siteState fresh state).nodes.length + 1 := rfl

theorem choiceNode_row {Γ : VCtx P L} {prog : VegasCore P L Γ}
    (site : PublicChoiceSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) :
    (compileCore prog fresh state).graph.nodes[choiceNode site fresh state]? =
      some ((site.siteState fresh state).commitEvent site.owner site.guard) := by
  rcases compiledRows site.decision site.tail site.adjacent fresh state with
    ⟨choice, _, hchoice, _, hrow, _⟩
  have heq : choice = choiceNode site fresh state := Fin.ext (hchoice.trans rfl.symm)
  simpa [siteState, heq] using hrow

theorem publicationNode_row {Γ : VCtx P L} {prog : VegasCore P L Γ}
    (site : PublicChoiceSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) :
    (compileCore prog fresh state).graph.nodes[publicationNode site fresh state]? = some
      (((site.siteState fresh state).addCommitEvent site.choiceName site.owner site.guard
        (site.siteFresh fresh).1).1.revealEvent site.owner .here) := by
  rcases compiledRows site.decision site.tail site.adjacent fresh state with
    ⟨_, publication, _, hpublication, _, hrow⟩
  have heq : publication = publicationNode site fresh state :=
    Fin.ext (hpublication.trans rfl.symm)
  simpa [siteState, heq] using hrow

theorem choiceNode_type {Γ : VCtx P L} {prog : VegasCore P L Γ}
    (site : PublicChoiceSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) :
    ((compileCore prog fresh state).graph.nodeRow (choiceNode site fresh state)).ty = site.ty := by
  have hcanonical := (compileCore prog fresh state).graph.nodes_get?_nodeRow
    (choiceNode site fresh state)
  exact congrArg EventNode.ty (Option.some.inj
    (hcanonical.symm.trans (choiceNode_row site fresh state)))

theorem publicationNode_type {Γ : VCtx P L} {prog : VegasCore P L Γ}
    (site : PublicChoiceSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) :
    ((compileCore prog fresh state).graph.nodeRow
      (publicationNode site fresh state)).ty = site.ty := by
  have hcanonical := (compileCore prog fresh state).graph.nodes_get?_nodeRow
    (publicationNode site fresh state)
  exact congrArg EventNode.ty (Option.some.inj
    (hcanonical.symm.trans (publicationNode_row site fresh state)))

theorem publicationNode_sem {Γ : VCtx P L} {prog : VegasCore P L Γ}
    (site : PublicChoiceSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) :
    ((compileCore prog fresh state).graph.nodeRow
      (publicationNode site fresh state)).sem =
        .reveal ((compileCore prog fresh state).graph.nodeTarget
          (choiceNode site fresh state)) := by
  have hpublication := Option.some.inj
    ((compileCore prog fresh state).graph.nodes_get?_nodeRow
      (publicationNode site fresh state) |>.symm.trans (publicationNode_row site fresh state))
  have hinitial : (compileCore prog fresh state).graph.initialFields = state.initialFields := by
    exact compileCore_initialFields prog fresh state
  rw [hpublication]
  change NodeSem.reveal
      (((site.siteState fresh state).addCommitEvent site.choiceName site.owner site.guard
        (site.siteFresh fresh).1).1.fieldOf (.here)) =
    NodeSem.reveal ((compileCore prog fresh state).graph.nodeTarget
      (choiceNode site fresh state))
  apply congrArg NodeSem.reveal
  unfold Graph.nodeTarget
  rw [hinitial]
  simp [choiceNode, siteState, BuildState.nextField, BuildState.nextNode,
    decisionSiteState_initialFields]

/-- Runtime endpoint generated from the compiler-certified adjacent nodes.
Public executability of its validator is a separate obligation. -/
def runtimeSite {Γ : VCtx P L} {prog : VegasCore P L Γ}
    (site : PublicChoiceSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) : Interaction.PublicChoice P :=
  (compileCore prog fresh state).graph.publicChoice site.owner
    (choiceNode site fresh state) (publicationNode site fresh state)

end PublicChoiceSite

end Vegas
