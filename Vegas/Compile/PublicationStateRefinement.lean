/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationImageStateRefinement
import Vegas.Compile.ConditionalImageRefinement

/-! # Full-state refinement for generated publication endpoints

The checkpoint-local publication laws lift from public memory and graph
reachability to the complete application-image refinement relation.  Existing
accepted bindings remain fixed because both generated publication updates
leave the accepted-handle and frozen-snapshot maps unchanged.
-/

noncomputable section

namespace Vegas

open EventGraph ToEventGraph Interaction

private theorem frozen_consistent_at_equal_type
    {L : IExpr} (frozen : Option (TypedValue L))
    (store : Store L) (field : Nat) {storedTy requestedTy : L.Ty}
    (hty : storedTy = requestedTy) (bound : L.Val storedTy)
    (hstored : Store.getAs store field storedTy = some bound)
    (hfrozen : ∀ recovered,
      frozen.bind (fun typed => typed.as? storedTy) = some recovered →
        recovered = bound) :
    ∀ value, frozen.bind (fun typed => typed.as? requestedTy) = some value →
      Store.getAs store field requestedTy = some value := by
  subst requestedTy
  intro value hrecovered
  have heq := hfrozen value hrecovered
  simpa [heq] using hstored

namespace PublicChoiceSite

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {Γ : VCtx P L} {prog : VegasCore P L Γ}

/-- Resolution at an ordinary generated public-choice endpoint preserves the
full native-to-graph refinement relation. -/
theorem resolution_refines
    (site : PublicChoiceSite prog) (fresh : FreshBindings prog)
    (build : BuildState P L Γ)
    (native : ApplicationImage.State P L)
    (cfg : Config (compileCore prog fresh build).graph)
    (hrefines : native.Refines cfg)
    (heligible : site.PubliclyValidatable fresh build)
    (message : Message P (L.Val site.ty)) (value : L.Val site.ty)
    (hresolve : (site.code fresh build).endpoint.resolve? native.memory.done
      ((site.code fresh build).guard.validate native.memory.store) message = some value) :
    (native.publish (site.code fresh build) value).Refines
      (site.completePublication fresh build cfg value) := by
  let G := (compileCore prog fresh build).graph
  let choice := site.choiceNode fresh build
  let publication := site.publicationNode fresh build
  let written : TypedValue L := ⟨site.ty, value⟩
  have haccepted := ((site.code fresh build).endpoint.resolve_iff
    native.memory.done ((site.code fresh build).guard.validate native.memory.store)
    message value).mp hresolve
  have hreadiness := G.publicChoice_ready cfg site.owner choice publication
    native.memory.done hrefines.memory.completed haccepted.1
  have hlower := native.publicChoice_resolution_refines site fresh build cfg
    hrefines.memory heligible hrefines.reachable message value hresolve
  refine ⟨hlower.1, hlower.2, ?_⟩
  have hbindings := hrefines.bindings.completePair hrefines.reachable
    choice publication written hreadiness.1.1 hreadiness.2.1
  simpa [ApplicationImage.State.BindingsRepresent, ApplicationImage.State.publish,
    ApplicationImage.Memory.publish,
    PublicChoiceSite.completePublication, written] using hbindings

end PublicChoiceSite

namespace CommitmentAccounting.OpeningSite

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
variable {plan : CommitmentAccounting pending prog}

/-- Resolution at a generated conditional endpoint preserves the full
native-to-graph relation.  Snapshot consistency needed by the local graph law
is derived from the accepted canonical handle and the existing binding
provenance component, rather than exposed as an additional premise. -/
theorem resolution_refines
    (site : plan.OpeningSite) (fresh : FreshBindings prog)
    (build : BuildState P L Γ) (sourceSlot deadline : Nat)
    (initial : VEnv L Γ) (legal : Legal prog)
    (native : ApplicationImage.State P L)
    (cfg : Config (compileCore prog fresh build).graph)
    (hrefines : native.Refines cfg)
    (heligible : site.PubliclyValidatable fresh build)
    (message : Message P
      (ConditionalPublication.Payload P (L.Val site.data.specification.secretTy)))
    (result : Option (L.Val site.data.specification.secretTy))
    (hresolve : (site.code fresh build sourceSlot deadline).endpoint.resolve?
      native.memory.clock (native.verify (site.code fresh build sourceSlot deadline))
      (native.memory.accepted (site.sourceField fresh build)) native.memory.done
      ((site.code fresh build sourceSlot deadline).canOpen native.memory.store)
      message = some result) :
    (native.publishConditional (site.code fresh build sourceSlot deadline) result).Refines
      (site.completePublication fresh build cfg result) := by
  let G := (compileCore prog fresh build).graph
  let choice := site.choiceNode fresh build
  let publication := site.publicationNode fresh build
  let code := site.code fresh build sourceSlot deadline
  let written : TypedValue L :=
    ⟨site.data.copyTy, site.data.specification.encoding.symm result⟩
  have hruntimeReady := code.endpoint.resolve_success_inversion native.memory.clock
    (native.verify code) (native.memory.accepted code.sourceField) native.memory.done
    (code.canOpen native.memory.store) message result hresolve
  have hreadyParts := hruntimeReady
  simp only [ConditionalPublication.ready, Bool.and_eq_true, beq_iff_eq,
    Bool.not_eq_true'] at hreadyParts
  have haccepted : native.memory.accepted (site.sourceField fresh build) =
      some (site.data.owner, sourceSlot) := by
    exact hreadyParts.1.1.1
  obtain ⟨spec, bound, hfield, _howner, hstored, hfrozen⟩ :=
    hrefines.bindings (site.sourceField fresh build) (site.data.owner, sourceSlot)
      haccepted
  obtain ⟨sourceSpec, hsourceField, hsourceTy, _hsourceOwner⟩ :=
    site.compiledSourceField fresh build
  have hspec : spec = sourceSpec :=
    Option.some.inj (hfield.symm.trans hsourceField)
  subst spec
  have hbinding : ∀ value,
      (native.frozen (site.sourceField fresh build)).bind
          (fun typed => typed.as? site.data.specification.secretTy) = some value →
        Store.getAs cfg.store (site.sourceField fresh build)
          site.data.specification.secretTy = some value := by
    exact frozen_consistent_at_equal_type
      (native.frozen (site.sourceField fresh build)) cfg.store
      (site.sourceField fresh build) hsourceTy bound hstored hfrozen
  have hlower := site.conditional_resolution_refines fresh build sourceSlot deadline
    initial legal native cfg hrefines.memory hrefines.reachable heligible hbinding
    message result hresolve
  have hreadiness := G.conditionalPublication_ready cfg site.data.owner sourceSlot
    choice publication deadline (native.memory.accepted code.sourceField)
    native.memory.done hrefines.memory.completed hruntimeReady
  refine ⟨hlower.1, hlower.2, ?_⟩
  have hbindings := hrefines.bindings.completePair hrefines.reachable
    choice publication written hreadiness.1.1 hreadiness.2.1
  simpa [ApplicationImage.State.BindingsRepresent,
    ApplicationImage.State.publishConditional,
    CommitmentAccounting.OpeningSite.completePublication, written] using hbindings

end CommitmentAccounting.OpeningSite

end Vegas

/-- info: 'Vegas.PublicChoiceSite.resolution_refines' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.PublicChoiceSite.resolution_refines

/-- info: 'Vegas.CommitmentAccounting.OpeningSite.resolution_refines' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.CommitmentAccounting.OpeningSite.resolution_refines
