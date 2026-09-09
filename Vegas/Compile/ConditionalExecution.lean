/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ConditionalOpeningSite
import Vegas.Compile.ConditionalResolution
import Vegas.Compile.SourceLaw

/-! # Executing a compiled conditional-publication site

The generated readiness test and the source guard justify two existing graph
steps. The result is a local execution correspondence at a represented source
checkpoint, not a whole-interaction strategy translation. In particular,
atomic publication and intermediate graph observations are not identified.
-/

noncomputable section

namespace Vegas.CommitmentAccounting.OpeningSite

open Vegas.EventGraph Vegas.ToEventGraph Interaction

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
variable {plan : CommitmentAccounting pending prog}

/-- The decoded graph effect of one accepted publication transaction. This
uses the actual source-generated node identifiers and source value encoding. -/
def completePublication (site : plan.OpeningSite) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) (cfg : Config (compileCore prog fresh state).graph)
    (result : Option (L.Val site.data.specification.secretTy)) :
    Config (compileCore prog fresh state).graph :=
  let value : TypedValue L := ⟨site.data.copyTy, site.data.specification.encoding.symm result⟩
  (cfg.completeNode (choiceNode site fresh state) value).completeNode
    (publicationNode site fresh state) value

/-- An accepted readiness check and a legal source value justify the exact
decoded macro by the existing commitment and deterministic-reveal kernels. -/
theorem completePublication_reachable
    (site : plan.OpeningSite) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) (cfg : Config (compileCore prog fresh state).graph)
    (env : VEnv L site.data.context)
    (hagrees : (decisionSiteState site.data.decision fresh state).Agrees cfg.store env)
    (sourceSlot deadline : Nat) (accepted : Option (CommitmentHandle P Nat))
    (done : Nat → Bool)
    (hcompleted : ∀ node : Fin (compileCore prog fresh state).graph.nodeCount,
      done node.val = true ↔ node ∈ cfg.done)
    (hready : (runtimeSite site fresh state sourceSlot deadline).ready accepted done = true)
    (result : Option (L.Val site.data.specification.secretTy))
    (hlegal : evalGuard site.data.guard (site.data.specification.encoding.symm result)
      ((env.toView site.data.owner).eraseEnv) = true)
    (hreachable : Reachable (compileCore prog fresh state).graph cfg) :
    Reachable (compileCore prog fresh state).graph
      (completePublication site fresh state cfg result) := by
  let G := (compileCore prog fresh state).graph
  let choice := choiceNode site fresh state
  let publication := publicationNode site fresh state
  let chosen := site.data.specification.encoding.symm result
  have hreadiness := G.conditionalPublication_ready cfg site.data.owner sourceSlot
    choice publication deadline accepted done hcompleted hready
  have htype : (G.nodeRow publication).ty = site.data.copyTy :=
    publicationNode_type site fresh state
  let value : L.Val (G.nodeRow publication).ty := cast (congrArg L.Val htype.symm) chosen
  have hvalue : (⟨(G.nodeRow publication).ty, value⟩ : TypedValue L) =
      ⟨site.data.copyTy, chosen⟩ := by
    apply TypedValue.eq_mk_of_as?_eq_some
    simp [TypedValue.as?, htype, value]
  have step : CommitStep G cfg site.data.owner
      ⟨choice, ⟨(G.nodeRow publication).ty, value⟩⟩ := by
    rw [hvalue]
    exact (decisionSiteState site.data.decision fresh state).sourceCommitStep
      site.data.owner site.data.guard cfg env hagrees choice
      (choiceNode_row site fresh state) hreadiness.1 chosen hlegal
  have hpublication : Ready G
      (cfg.completeNode choice ⟨(G.nodeRow publication).ty, value⟩) publication :=
    publication_ready_after_choice cfg choice publication _
      (publicationNode_ne_choiceNode site fresh state) hreadiness.2.1 hreadiness.2.2
  have hnext := reachable_choice_publication cfg site.data.owner choice publication value
    step (publicationNode_sem site fresh state) hpublication hreachable
  rw [hvalue] at hnext
  exact hnext

/-- A runtime-accepted resolution executes the generated pair of graph nodes
when the commitment service, completion readout, and opening validator agree
with the represented source checkpoint. These are local state/validation
premises; no scheduling, settlement, or strategic correspondence is assumed. -/
theorem runtime_resolution_reachable
    (site : plan.OpeningSite) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) (cfg : Config (compileCore prog fresh state).graph)
    (env : VEnv L site.data.context)
    (hagrees : (decisionSiteState site.data.decision fresh state).Agrees cfg.store env)
    (sourceSlot deadline now : Nat)
    (service : IdealCommitments P Nat (L.Val site.data.specification.secretTy))
    (accepted : Option (CommitmentHandle P Nat)) (done : Nat → Bool)
    (canOpen : L.Val site.data.specification.secretTy → Bool)
    (message : Message P
      (ConditionalPublication.Payload P (L.Val site.data.specification.secretTy)))
    (hcompleted : ∀ node : Fin (compileCore prog fresh state).graph.nodeCount,
      done node.val = true ↔ node ∈ cfg.done)
    (hstored : service.lookup (site.data.owner, sourceSlot) =
      some (env.get site.data.specification.binding))
    (hcanOpen : canOpen (env.get site.data.specification.binding) = true →
      evalGuard site.data.guard
        (site.data.specification.encoding.symm (some (env.get site.data.specification.binding)))
        ((env.toView site.data.owner).eraseEnv) = true)
    (result : Option (L.Val site.data.specification.secretTy))
    (hresolve : (runtimeSite site fresh state sourceSlot deadline).resolve?
      now service.verify accepted done canOpen message = some result)
    (hreachable : Reachable (compileCore prog fresh state).graph cfg) :
    Reachable (compileCore prog fresh state).graph
      (completePublication site fresh state cfg result) := by
  have hlegal := site.data.specification.runtime_resolution_legal
    (runtimeSite site fresh state sourceSlot deadline) rfl now service accepted done canOpen
    message env hstored hcanOpen result hresolve
  have hready := (runtimeSite site fresh state sourceSlot deadline).resolve_success_inversion
    now service.verify accepted done canOpen message result hresolve
  exact completePublication_reachable site fresh state cfg env hagrees sourceSlot deadline
    accepted done hcompleted hready result hlegal.2 hreachable

/-- The macro preserves the original sealed field in the actual graph store,
not just in the source environment or the responder's visible projection. -/
theorem completePublication_sourceField
    (site : plan.OpeningSite) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) (cfg : Config (compileCore prog fresh state).graph)
    (result : Option (L.Val site.data.specification.secretTy)) :
    (completePublication site fresh state cfg result).store (sourceField site fresh state) =
      cfg.store (sourceField site fresh state) := by
  let before := decisionSiteState site.data.decision fresh state
  have hlt : sourceField site fresh state < before.nextField :=
    before.fieldOf_lt site.data.specification.binding
  have hchoice : (compileCore prog fresh state).graph.nodeTarget
      (choiceNode site fresh state) = before.nextField := by
    simp only [Graph.nodeTarget, choiceNode_val, BuildState.nextField, BuildState.nextNode]
    change (compileCore prog fresh state).initialFields.length + _ = _
    rw [compileCore_initialFields]
    simp only [before, decisionSiteState_initialFields]
  have hpublication : (compileCore prog fresh state).graph.nodeTarget
      (publicationNode site fresh state) = before.nextField + 1 := by
    simp only [Graph.nodeTarget, publicationNode_val, BuildState.nextField, BuildState.nextNode]
    change (compileCore prog fresh state).initialFields.length + _ = _
    rw [compileCore_initialFields]
    simp only [before, decisionSiteState_initialFields]
    omega
  have hneChoice : sourceField site fresh state ≠
      (compileCore prog fresh state).graph.nodeTarget (choiceNode site fresh state) := by
    rw [hchoice]
    omega
  have hnePublication : sourceField site fresh state ≠
      (compileCore prog fresh state).graph.nodeTarget (publicationNode site fresh state) := by
    rw [hpublication]
    omega
  simp only [completePublication, Config.completeNode, Store.set,
    if_neg hnePublication, if_neg hneChoice]

end Vegas.CommitmentAccounting.OpeningSite

/--
info: 'Vegas.CommitmentAccounting.OpeningSite.runtime_resolution_reachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Vegas.CommitmentAccounting.OpeningSite.runtime_resolution_reachable
