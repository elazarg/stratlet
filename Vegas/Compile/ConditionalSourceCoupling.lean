/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.PublicChoiceSourceCoupling

/-! # Source continuations after conditional publication

Canonical opening and decline messages execute the same adjacent source pair.
Readiness follows from the source prefix and the accepted binding identity.
Opening additionally needs the claimed value in the frozen snapshot; declining
has no such requirement. The commitment-backed endpoint requires an actual
accepted binding even when the corresponding source value is already public.
-/

noncomputable section

namespace Vegas.ConditionalPublicationSite

open EventGraph ToEventGraph Interaction

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Completion of the written source prefix supplies all external dependency
checks. The accepted handle is an additional representation obligation: public
storage of the source field alone does not supply it. -/
theorem ready_at_source_prefix
    {Γ : VCtx P L} {name publicName : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ))
    (spec : ConditionalOpening guard)
    (fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail)))
    (build : BuildState P L Γ) (sourceSlot deadline : Nat)
    (current : CoupledAt
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh build).graph build)
    (native : ApplicationImage.State P L)
    (hrefines : native.Refines current.current.graph.1)
    (haccepted : native.memory.accepted (build.fieldOf spec.binding) = some (who, sourceSlot)) :
    ((atHead name publicName who guard tail spec).runtimeSite fresh build sourceSlot deadline).ready
      (native.memory.accepted (build.fieldOf spec.binding)) native.memory.done = true := by
  have hpublic := PublicChoiceSite.ready_at_source_prefix guard tail fresh build current
    native.memory.done hrefines.memory.completed
  simpa only [runtimeSite, Graph.conditionalPublication, ConditionalPublication.ready,
    haccepted, beq_self_eq_true, Bool.true_and, atHead, PublicChoiceSite.atHead,
    PublicChoiceSite.runtimeSite,
    Graph.publicChoice, PublicChoice.ready] using hpublic

/-- Actual inclusion realizes the selected legal source opening or decline and
preserves its exact continuation. Snapshot availability is needed only for the
opening branch. No bound on the current clock is assumed: an unresolved endpoint
accepts its owner's request even after the deadline. -/
theorem include_source_coupling
    {Γ : VCtx P L} {name publicName : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ))
    (spec : ConditionalOpening guard)
    (fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail)))
    (build : BuildState P L Γ) (sourceSlot deadline : Nat)
    (current : CoupledAt
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh build).graph build)
    (image : ApplicationImage P L) (execution : image.application.State)
    (hrefines : execution.application.Refines current.current.graph.1)
    (heligible : (atHead name publicName who guard tail spec).PubliclyValidatable fresh build)
    (haccepted : execution.application.memory.accepted (build.fieldOf spec.binding) =
      some (who, sourceSlot))
    (address serial : Nat)
    (hcode : image.lookup address = some (.conditional
      ((atHead name publicName who guard tail spec).code fresh build sourceSlot deadline)))
    (chosen : L.Val ty)
    (hlookup : execution.pool.lookup (who, serial) = some ⟨(who, serial), .conditional address
      (((atHead name publicName who guard tail spec).code
        fresh build sourceSlot deadline).requestPayload
        (spec.encoding chosen))⟩)
    (hlegal : evalGuard guard chosen ((current.current.source.toView who).eraseEnv) = true)
    (hfrozen : ∀ value, spec.encoding chosen = some value →
      (execution.application.frozen (build.fieldOf spec.binding)).bind
        (fun typed => typed.as? spec.secretTy) = some value) :
    ∃ next : CoupledAt
        (compileCore (.commit name who guard (.reveal publicName who name .here tail))
          fresh build).graph
        (((build.addCommitEvent name who guard fresh.1).1).addRevealEvent
          publicName who .here fresh.2.1).1,
      next.current.source = (current.current.source.cons chosen).cons chosen ∧
      (image.application.includePending execution (who, serial)).application.Refines
        next.current.graph.1 := by
  let site := atHead name publicName who guard tail spec
  let G := (compileCore (.commit name who guard (.reveal publicName who name .here tail))
    fresh build).graph
  let code := site.code fresh build sourceSlot deadline
  let choice := site.choice.choiceNode fresh build
  let publication := site.choice.publicationNode fresh build
  have hready := ready_at_source_prefix guard tail spec fresh build sourceSlot deadline current
    execution.application hrefines haccepted
  have hhandle := canonical_request_accepted image site fresh build sourceSlot deadline address
    hcode execution.application current.current.graph.1.store current.current.source heligible
    current.current.agrees hrefines.memory.publicFields hready chosen hlegal hfrozen serial
  have hincluded := image.include_accepted execution (who, serial)
    ⟨(who, serial), .conditional address (code.requestPayload (spec.encoding chosen))⟩
    (execution.application.publishConditional code (spec.encoding chosen)) hlookup hhandle
  obtain ⟨next, hsource, hgraph⟩ :=
    PublicChoiceSite.source_successor guard tail fresh build current chosen hlegal
  have hpublic := PublicChoiceSite.ready_at_source_prefix guard tail fresh build current
    execution.application.memory.done hrefines.memory.completed
  have hnodes := G.publicChoice_ready current.current.graph.1 who choice publication
    execution.application.memory.done hrefines.memory.completed hpublic
  have hmemory := execution.application.publishConditional_represents current.current.graph.1
    hrefines.memory code choice publication rfl rfl rfl rfl (spec.encoding chosen)
  change (execution.application.publishConditional code (spec.encoding chosen)).memory.Represents
    ((current.current.graph.1.completeNode choice
      ⟨ty, spec.encoding.symm (spec.encoding chosen)⟩).completeNode publication
        ⟨ty, spec.encoding.symm (spec.encoding chosen)⟩) at hmemory
  rw [Equiv.symm_apply_apply] at hmemory
  have hbindings := hrefines.bindings.completePair hrefines.reachable choice publication
    ⟨ty, chosen⟩ hnodes.1.1 hnodes.2.1
  have hnext : (execution.application.publishConditional code (spec.encoding chosen)).Refines
      next.current.graph.1 := by
    refine ⟨?_, next.current.graph.2, ?_⟩
    · rw [hgraph]
      exact hmemory
    · rw [hgraph]
      exact hbindings
  refine ⟨next, hsource, ?_⟩
  have hstate : (image.application.includePending execution (who, serial)).application =
      execution.application.publishConditional code (spec.encoding chosen) := hincluded.1
  exact hstate.symm ▸ hnext

end Vegas.ConditionalPublicationSite

/-- info: 'Vegas.ConditionalPublicationSite.ready_at_source_prefix' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ConditionalPublicationSite.ready_at_source_prefix

/-- info: 'Vegas.ConditionalPublicationSite.include_source_coupling' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ConditionalPublicationSite.include_source_coupling
