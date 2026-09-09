/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Core.OpeningSite
import Vegas.Compile.ConditionalPublication
import Vegas.Compile.PublicChoiceSite

/-! # Source-certified conditional publications

A conditional publication is an ordinary adjacent public choice together with
the certificate identifying that choice as a decline or an opening of an
existing sealed binding. The ordinary choice metadata is shared rather than
recompiled here.
-/

noncomputable section

namespace Vegas

open EventGraph ToEventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- An adjacent public choice whose legal values are certified as either a
decline or a publication of one existing sealed binding. -/
structure ConditionalPublicationSite {Γ : VCtx P L} (prog : VegasCore P L Γ) where
  choice : PublicChoiceSite prog
  specification : ConditionalOpening choice.guard

namespace ConditionalPublicationSite

/-- The canonical conditional-publication occurrence at the current source
cursor. -/
def atHead {Γ : VCtx P L} (name publicName : VarId) (who : P)
    {ty : L.Ty} (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ))
    (specification : ConditionalOpening guard) :
    ConditionalPublicationSite
      (.commit name who guard (.reveal publicName who name .here tail)) where
  choice := PublicChoiceSite.atHead name publicName who guard tail
  specification := specification

/-- The compiler field allocated to the original sealed source. This is not a
backend commitment slot: an adapter supplies that allocation separately. -/
def sourceField {Γ : VCtx P L} {prog : VegasCore P L Γ}
    (site : ConditionalPublicationSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) : Nat :=
  (site.choice.siteState fresh state).fieldOf site.specification.binding

/-- The original binding named by the conditional-publication certificate
remains a typed, same-owner field in the final compiled graph. It need not have
a producer node because it may be an initial sealed field. -/
theorem compiledSourceField {Γ : VCtx P L} {prog : VegasCore P L Γ}
    (site : ConditionalPublicationSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) :
    let result := compileCore prog fresh state
    ∃ spec : FieldSpec P L,
      result.graph.field? (site.sourceField fresh state) = some spec ∧
      spec.ty = site.specification.secretTy ∧ spec.owner = some site.choice.owner := by
  dsimp only
  rcases (site.choice.siteState fresh state).fieldOf_spec site.specification.binding with
    ⟨spec, hfield, hty, howner⟩
  refine ⟨spec, ?_, hty, howner⟩
  change (compileCore prog fresh state).graph.field?
    ((site.choice.siteState fresh state).fieldOf site.specification.binding) = some spec
  rw [← decisionSiteState_field?_eq_compileCore site.choice.decision fresh state
    ((site.choice.siteState fresh state).fieldOf site.specification.binding)
    ((site.choice.siteState fresh state).fieldOf_lt _)]
  exact hfield

/-- Runtime endpoint generated from the shared public-choice nodes and the
certificate's separately allocated source commitment slot. -/
def runtimeSite {Γ : VCtx P L} {prog : VegasCore P L Γ}
    (site : ConditionalPublicationSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) (sourceSlot deadline : Nat) :
    Interaction.ConditionalPublication P :=
  (compileCore prog fresh state).graph.conditionalPublication site.choice.owner sourceSlot
    (site.choice.choiceNode fresh state) (site.choice.publicationNode fresh state) deadline

end ConditionalPublicationSite

namespace CommitmentAccounting.OpeningSite

private theorem data_adjacent {Γ : VCtx P L} {pending : Finset VarId}
    {prog : VegasCore P L Γ} {plan : CommitmentAccounting pending prog}
    (site : plan.OpeningSite) :
    let found := site.data
    found.decision.continuation =
      .reveal found.publicName found.owner found.copyName .here found.tail := by
  induction site with
  | here => rfl
  | sample site ih => exact ih
  | commit site ih => exact ih
  | reveal site ih => exact ih
  | openingTail site ih => exact ih

/-- Forget the accounting path while retaining its adjacent public-choice
occurrence and conditional-opening certificate. -/
def conditionalPublicationSite {Γ : VCtx P L} {pending : Finset VarId}
    {prog : VegasCore P L Γ} {plan : CommitmentAccounting pending prog}
    (site : plan.OpeningSite) : ConditionalPublicationSite prog :=
  let found := site.data
  { choice :=
      { context := found.context
        choiceName := found.copyName
        publicName := found.publicName
        owner := found.owner
        ty := found.copyTy
        guard := found.guard
        tail := found.tail
        decision := found.decision
        adjacent := site.data_adjacent }
    specification := found.specification }

end CommitmentAccounting.OpeningSite

end Vegas
