/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ConditionalPublicationSite
import Vegas.Compile.ConditionalResolution
import Vegas.Compile.SourceLaw

/-! # Executing a compiled conditional-publication site

The generated readiness test and the source guard justify two existing graph
steps. The result is a local execution correspondence at a represented source
checkpoint, not a whole-interaction strategy translation. In particular,
atomic publication and intermediate graph observations are not identified.
-/

noncomputable section

namespace Vegas.ConditionalPublicationSite

open Vegas.EventGraph Vegas.ToEventGraph Interaction

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {Γ : VCtx P L} {prog : VegasCore P L Γ}

/-- The decoded graph effect of one accepted publication transaction. This
uses the actual source-generated node identifiers and source value encoding. -/
def completePublication (site : ConditionalPublicationSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) (cfg : Config (compileCore prog fresh state).graph)
    (result : Option (L.Val site.specification.secretTy)) :
    Config (compileCore prog fresh state).graph :=
  let value : TypedValue L := ⟨site.choice.ty, site.specification.encoding.symm result⟩
  (cfg.completeNode (site.choice.choiceNode fresh state) value).completeNode
    (site.choice.publicationNode fresh state) value

/-- An accepted readiness check and a legal source value justify the exact
decoded macro by the existing commitment and deterministic-reveal kernels. -/
theorem completePublication_reachable
    (site : ConditionalPublicationSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) (cfg : Config (compileCore prog fresh state).graph)
    (env : VEnv L site.choice.context)
    (hagrees : (decisionSiteState site.choice.decision fresh state).Agrees cfg.store env)
    (sourceSlot deadline : Nat) (accepted : Option (CommitmentHandle P Nat))
    (done : Nat → Bool)
    (hcompleted : ∀ node : Fin (compileCore prog fresh state).graph.nodeCount,
      done node.val = true ↔ node ∈ cfg.done)
    (hready : (runtimeSite site fresh state sourceSlot deadline).ready accepted done = true)
    (result : Option (L.Val site.specification.secretTy))
    (hlegal : evalGuard site.choice.guard (site.specification.encoding.symm result)
      ((env.toView site.choice.owner).eraseEnv) = true)
    (hreachable : Reachable (compileCore prog fresh state).graph cfg) :
    Reachable (compileCore prog fresh state).graph
      (completePublication site fresh state cfg result) := by
  let G := (compileCore prog fresh state).graph
  let choice := site.choice.choiceNode fresh state
  let publication := site.choice.publicationNode fresh state
  let chosen := site.specification.encoding.symm result
  have hreadiness := G.conditionalPublication_ready cfg site.choice.owner sourceSlot
    choice publication deadline accepted done hcompleted hready
  let written : TypedValue L := ⟨site.choice.ty, chosen⟩
  have step : CommitStep G cfg site.choice.owner
      ⟨choice, written⟩ := by
    exact (decisionSiteState site.choice.decision fresh state).sourceCommitStep
      site.choice.owner site.choice.guard cfg env hagrees choice
      (site.choice.choiceNode_row fresh state) hreadiness.1 chosen hlegal
  have hpublication : Ready G
      (cfg.completeNode choice written) publication :=
    publication_ready_after_choice cfg choice publication _
      (site.choice.publicationNode_ne_choiceNode fresh state) hreadiness.2.1 hreadiness.2.2
  exact reachable_choice_publication cfg site.choice.owner choice publication written
    (site.choice.publicationNode_type fresh state).symm step
    (site.choice.publicationNode_sem fresh state) hpublication hreachable

/-- A runtime-accepted resolution executes the generated pair of graph nodes
when the commitment service, completion readout, and opening validator agree
with the represented source checkpoint. These are local state/validation
premises; no scheduling, settlement, or strategic correspondence is assumed. -/
theorem runtime_resolution_reachable
    (site : ConditionalPublicationSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) (cfg : Config (compileCore prog fresh state).graph)
    (env : VEnv L site.choice.context)
    (hagrees : (decisionSiteState site.choice.decision fresh state).Agrees cfg.store env)
    (sourceSlot deadline now : Nat)
    (service : IdealCommitments P Nat (L.Val site.specification.secretTy))
    (accepted : Option (CommitmentHandle P Nat)) (done : Nat → Bool)
    (canOpen : L.Val site.specification.secretTy → Bool)
    (message : Message P
      (ConditionalPublication.Payload P (L.Val site.specification.secretTy)))
    (hcompleted : ∀ node : Fin (compileCore prog fresh state).graph.nodeCount,
      done node.val = true ↔ node ∈ cfg.done)
    (hstored : service.lookup (site.choice.owner, sourceSlot) =
      some (env.get site.specification.binding))
    (hcanOpen : canOpen (env.get site.specification.binding) = true →
      evalGuard site.choice.guard
        (site.specification.encoding.symm (some (env.get site.specification.binding)))
        ((env.toView site.choice.owner).eraseEnv) = true)
    (result : Option (L.Val site.specification.secretTy))
    (hresolve : (runtimeSite site fresh state sourceSlot deadline).resolve?
      now service.verify accepted done canOpen message = some result)
    (hreachable : Reachable (compileCore prog fresh state).graph cfg) :
    Reachable (compileCore prog fresh state).graph
      (completePublication site fresh state cfg result) := by
  have hlegal := site.specification.runtime_resolution_legal
    (runtimeSite site fresh state sourceSlot deadline) rfl now service accepted done canOpen
    message env hstored hcanOpen result hresolve
  have hready := (runtimeSite site fresh state sourceSlot deadline).resolve_success_inversion
    now service.verify accepted done canOpen message result hresolve
  exact completePublication_reachable site fresh state cfg env hagrees sourceSlot deadline
    accepted done hcompleted hready result hlegal.2 hreachable

/-- The macro preserves the original sealed field in the actual graph store,
not just in the source environment or the responder's visible projection. -/
theorem completePublication_sourceField
    (site : ConditionalPublicationSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) (cfg : Config (compileCore prog fresh state).graph)
    (result : Option (L.Val site.specification.secretTy)) :
    (completePublication site fresh state cfg result).store (sourceField site fresh state) =
      cfg.store (sourceField site fresh state) := by
  let before := decisionSiteState site.choice.decision fresh state
  have hlt : sourceField site fresh state < before.nextField :=
    before.fieldOf_lt site.specification.binding
  have hchoice : (compileCore prog fresh state).graph.nodeTarget
      (site.choice.choiceNode fresh state) = before.nextField := by
    simp only [Graph.nodeTarget, PublicChoiceSite.choiceNode_val,
      BuildState.nextField, BuildState.nextNode]
    change (compileCore prog fresh state).initialFields.length + _ = _
    rw [compileCore_initialFields]
    simp only [before, decisionSiteState_initialFields, PublicChoiceSite.siteState]
  have hpublication : (compileCore prog fresh state).graph.nodeTarget
      (site.choice.publicationNode fresh state) = before.nextField + 1 := by
    simp only [Graph.nodeTarget, PublicChoiceSite.publicationNode_val,
      BuildState.nextField, BuildState.nextNode]
    change (compileCore prog fresh state).initialFields.length + _ = _
    rw [compileCore_initialFields]
    simp only [before, decisionSiteState_initialFields, PublicChoiceSite.siteState]
    omega
  have hneChoice : sourceField site fresh state ≠
      (compileCore prog fresh state).graph.nodeTarget (site.choice.choiceNode fresh state) := by
    rw [hchoice]
    omega
  have hnePublication : sourceField site fresh state ≠
      (compileCore prog fresh state).graph.nodeTarget
        (site.choice.publicationNode fresh state) := by
    rw [hpublication]
    omega
  simp only [completePublication, Config.completeNode, Store.set,
    if_neg hnePublication, if_neg hneChoice]

end Vegas.ConditionalPublicationSite

/--
info: 'Vegas.ConditionalPublicationSite.runtime_resolution_reachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Vegas.ConditionalPublicationSite.runtime_resolution_reachable
