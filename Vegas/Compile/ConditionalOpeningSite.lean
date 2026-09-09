/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Core.OpeningSite
import Vegas.Compile.ConditionalPublication
import Vegas.Compile.DecisionSite

/-! # Compiled metadata for accounted conditional-opening sites -/

noncomputable section

namespace Vegas

open EventGraph ToEventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

namespace CommitmentAccounting.OpeningSite

/-- The accounted source site compiles to its commitment node immediately
followed by the deterministic publication node. -/
theorem compiledRows {Γ : VCtx P L} {pending : Finset VarId}
    {prog : VegasCore P L Γ} {plan : CommitmentAccounting pending prog}
    (site : plan.OpeningSite) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) :
    let found := site.data
    let siteState := decisionSiteState found.decision fresh state
    let result := compileCore prog fresh state
    ∃ choice publication : Fin result.graph.nodeCount,
      (choice : Nat) = siteState.nodes.length ∧
      (publication : Nat) = siteState.nodes.length + 1 ∧
      result.graph.nodes[choice]? = some (siteState.commitEvent found.owner found.guard) ∧
      result.graph.nodes[publication]? = some
        ((siteState.addCommitEvent found.copyName found.owner found.guard
          (site.siteFresh fresh).1).1.revealEvent found.owner .here) := by
  induction site with
  | @here Γ pending copyName publicName who copyTy guard tail spec unresolved hcopy accounted =>
      dsimp [CommitmentAccounting.OpeningSite.data, decisionSiteState]
      let committed := state.addCommitEvent copyName who guard fresh.1
      let revealed := committed.1.addRevealEvent publicName who .here fresh.2.1
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
          some (committed.1.revealEvent _ (.here))
        rw [← hsuffix]
        simp [revealed, committed]
  | sample site ih =>
      exact ih fresh.2 (state.addSampleEvent _ _ fresh.1).1
  | commit site ih =>
      exact ih fresh.2 (state.addCommitEvent _ _ _ fresh.1).1
  | reveal site ih =>
      exact ih fresh.2 (state.addRevealEvent _ _ _ fresh.1).1
  | openingTail site ih =>
      exact ih fresh.2.2
        (((state.addCommitEvent _ _ _ fresh.1).1).addRevealEvent _ _ .here fresh.2.1).1

/-- The compiler-generated identifier of the optional choice node. -/
def choiceNode {Γ : VCtx P L} {pending : Finset VarId}
    {prog : VegasCore P L Γ} {plan : CommitmentAccounting pending prog}
    (site : plan.OpeningSite) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) : Fin (compileCore prog fresh state).graph.nodeCount :=
  ⟨(decisionSiteState site.data.decision fresh state).nodes.length, by
    rcases compiledRows site fresh state with ⟨choice, _, hchoice, _⟩
    rw [← hchoice]
    exact choice.isLt⟩

/-- The immediately following compiler-generated publication identifier. -/
def publicationNode {Γ : VCtx P L} {pending : Finset VarId}
    {prog : VegasCore P L Γ} {plan : CommitmentAccounting pending prog}
    (site : plan.OpeningSite) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) : Fin (compileCore prog fresh state).graph.nodeCount :=
  ⟨(decisionSiteState site.data.decision fresh state).nodes.length + 1, by
    rcases compiledRows site fresh state with ⟨_, publication, _, hpublication, _⟩
    rw [← hpublication]
    exact publication.isLt⟩

@[simp] theorem choiceNode_val {Γ : VCtx P L} {pending : Finset VarId}
    {prog : VegasCore P L Γ} {plan : CommitmentAccounting pending prog}
    (site : plan.OpeningSite) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) :
    (choiceNode site fresh state : Nat) =
      (decisionSiteState site.data.decision fresh state).nodes.length := rfl

@[simp] theorem publicationNode_val {Γ : VCtx P L} {pending : Finset VarId}
    {prog : VegasCore P L Γ} {plan : CommitmentAccounting pending prog}
    (site : plan.OpeningSite) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) :
    (publicationNode site fresh state : Nat) =
      (decisionSiteState site.data.decision fresh state).nodes.length + 1 := rfl

/-- Exact row emitted for the canonical choice identifier. -/
theorem choiceNode_row {Γ : VCtx P L} {pending : Finset VarId}
    {prog : VegasCore P L Γ} {plan : CommitmentAccounting pending prog}
    (site : plan.OpeningSite) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) :
    (compileCore prog fresh state).graph.nodes[choiceNode site fresh state]? =
      some ((decisionSiteState site.data.decision fresh state).commitEvent
        site.data.owner site.data.guard) := by
  rcases compiledRows site fresh state with ⟨choice, _, hchoice, _, hrow, _⟩
  have heq : choice = choiceNode site fresh state := Fin.ext (hchoice.trans rfl.symm)
  simpa [heq] using hrow

/-- Exact row emitted for the canonical publication identifier. -/
theorem publicationNode_row {Γ : VCtx P L} {pending : Finset VarId}
    {prog : VegasCore P L Γ} {plan : CommitmentAccounting pending prog}
    (site : plan.OpeningSite) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) :
    (compileCore prog fresh state).graph.nodes[publicationNode site fresh state]? = some
      (((decisionSiteState site.data.decision fresh state).addCommitEvent
        site.data.copyName site.data.owner site.data.guard (site.siteFresh fresh).1).1.revealEvent
          site.data.owner .here) := by
  rcases compiledRows site fresh state with ⟨_, publication, _, hpublication, _, hrow⟩
  have heq : publication = publicationNode site fresh state :=
    Fin.ext (hpublication.trans rfl.symm)
  simpa [heq] using hrow

theorem publicationNode_ne_choiceNode {Γ : VCtx P L} {pending : Finset VarId}
    {prog : VegasCore P L Γ} {plan : CommitmentAccounting pending prog}
    (site : plan.OpeningSite) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) :
    publicationNode site fresh state ≠ choiceNode site fresh state := by
  intro heq
  have := congrArg Fin.val heq
  simp at this

/-- The publication row has the certificate's copy type. -/
theorem publicationNode_type {Γ : VCtx P L} {pending : Finset VarId}
    {prog : VegasCore P L Γ} {plan : CommitmentAccounting pending prog}
    (site : plan.OpeningSite) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) :
    ((compileCore prog fresh state).graph.nodeRow
      (publicationNode site fresh state)).ty = site.data.copyTy := by
  have hcanonical := (compileCore prog fresh state).graph.nodes_get?_nodeRow
    (publicationNode site fresh state)
  have hrow := Option.some.inj (hcanonical.symm.trans (publicationNode_row site fresh state))
  exact congrArg EventNode.ty hrow

/-- The compiler field allocated to the original sealed source. This is not a
backend commitment slot: an adapter must supply that allocation separately. -/
def sourceField {Γ : VCtx P L} {pending : Finset VarId}
    {prog : VegasCore P L Γ} {plan : CommitmentAccounting pending prog}
    (site : plan.OpeningSite) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) : Nat :=
  (decisionSiteState site.data.decision fresh state).fieldOf site.data.specification.binding

/-- The original binding named by the conditional-opening certificate remains
a typed field in the final compiled graph. It need not have a producer node:
it may be an initial sealed field. -/
theorem compiledSourceField {Γ : VCtx P L} {pending : Finset VarId}
    {prog : VegasCore P L Γ} {plan : CommitmentAccounting pending prog}
    (site : plan.OpeningSite) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) :
    let found := site.data
    let result := compileCore prog fresh state
    ∃ spec : FieldSpec P L,
      result.graph.field? (sourceField site fresh state) = some spec ∧
      spec.ty = found.specification.secretTy ∧ spec.owner = some found.owner := by
  dsimp only
  let found := site.data
  let siteState := decisionSiteState found.decision fresh state
  rcases siteState.fieldOf_spec found.specification.binding with
    ⟨spec, hfield, hty, howner⟩
  refine ⟨spec, ?_, hty, howner⟩
  change (compileCore prog fresh state).graph.field?
    (siteState.fieldOf found.specification.binding) = some spec
  rw [← decisionSiteState_field?_eq_compileCore found.decision fresh state
    (siteState.fieldOf found.specification.binding) (siteState.fieldOf_lt _)]
  exact hfield

/-- The two output fields are the canonical targets of the adjacent compiled
nodes. These equations expose their positions without assuming that the
original sealed source itself has a producer node. -/
theorem compiledTargets {Γ : VCtx P L} {pending : Finset VarId}
    {prog : VegasCore P L Γ} {plan : CommitmentAccounting pending prog}
    (site : plan.OpeningSite) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) :
    let found := site.data
    let siteState := decisionSiteState found.decision fresh state
    let result := compileCore prog fresh state
    ∃ choice publication : Fin result.graph.nodeCount,
      (choice : Nat) = siteState.nodes.length ∧
      (publication : Nat) = siteState.nodes.length + 1 ∧
      result.graph.nodeTarget choice =
        siteState.initialFields.length + siteState.nodes.length ∧
      result.graph.nodeTarget publication =
        siteState.initialFields.length + siteState.nodes.length + 1 := by
  dsimp only
  rcases compiledRows site fresh state with
    ⟨choice, publication, hchoice, hpublication, _⟩
  have hinitial : (compileCore prog fresh state).graph.initialFields =
      (decisionSiteState site.data.decision fresh state).initialFields := by
    change (compileCore prog fresh state).initialFields = _
    rw [compileCore_initialFields, decisionSiteState_initialFields]
  refine ⟨choice, publication, hchoice, hpublication, ?_, ?_⟩
  · simp only [Graph.nodeTarget, hchoice, hinitial]
  · simp only [Graph.nodeTarget, hpublication, hinitial]
    omega

/-- The publication is exactly a reveal of the canonical choice node's output
field, rather than a merely adjacent reveal of an arbitrary source. -/
theorem publicationNode_sem {Γ : VCtx P L} {pending : Finset VarId}
    {prog : VegasCore P L Γ} {plan : CommitmentAccounting pending prog}
    (site : plan.OpeningSite) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) :
    ((compileCore prog fresh state).graph.nodeRow
      (publicationNode site fresh state)).sem =
        .reveal ((compileCore prog fresh state).graph.nodeTarget
          (choiceNode site fresh state)) := by
  have hcanonical := (compileCore prog fresh state).graph.nodes_get?_nodeRow
    (publicationNode site fresh state)
  have hrow := Option.some.inj (hcanonical.symm.trans (publicationNode_row site fresh state))
  have htargets := compiledTargets site fresh state
  rcases htargets with ⟨choice, publication, hchoice, hpublication, hchoiceTarget, _⟩
  have hchoiceEq : choice = choiceNode site fresh state := Fin.ext (hchoice.trans rfl.symm)
  have hpublicationEq : publication = publicationNode site fresh state :=
    Fin.ext (hpublication.trans rfl.symm)
  subst choice
  subst publication
  rw [hrow]
  simp only [BuildState.addCommitEvent_fieldOf_here]
  exact congrArg NodeSem.reveal hchoiceTarget.symm

/-- Emit the public runtime classifier from compiler-generated node ids. The
backend source slot is explicit because graph fields and commitment keys are
different namespaces, especially for initial sealed inputs. -/
def runtimeSite {Γ : VCtx P L} {pending : Finset VarId}
    {prog : VegasCore P L Γ} {plan : CommitmentAccounting pending prog}
    (site : plan.OpeningSite) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) (sourceSlot deadline : Nat) :
    Interaction.ConditionalPublication P :=
  (compileCore prog fresh state).graph.conditionalPublication site.data.owner sourceSlot
    (choiceNode site fresh state) (publicationNode site fresh state) deadline

end CommitmentAccounting.OpeningSite

end Vegas
