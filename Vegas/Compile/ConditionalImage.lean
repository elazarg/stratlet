/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationImage
import Vegas.Compile.ConditionalOpeningValidation

/-! # Generated binding and conditional-publication instructions

The instructions use the same compiler allocation as ordinary public choices.
Opaque binding admission does not establish source guard legality. Generated
application plans require unrestricted original guards until a binding
validation mechanism is supplied; controller legality alone does not constrain
arbitrary runtime deviations.
Conditional validation checks the retained source guard using public fields
and the acceptance-time verified claim. No source environment is runtime data.
-/

noncomputable section

namespace Vegas

open EventGraph ToEventGraph Interaction

variable {P : Type} [DecidableEq P] {L : IExpr}

namespace SourceDecisionSite

/-- The exact graph node allocated to this source decision occurrence. -/
def compiledNode {who : P} {Γ Δ : VCtx P L} {prog : VegasCore P L Γ}
    {name : VarId} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    (site : SourceDecisionSite who prog Δ name ty guard)
    (fresh : FreshBindings prog) (state : BuildState P L Γ) :
    Fin (compileCore prog fresh state).graph.nodeCount :=
  ⟨(decisionSiteState site fresh state).nodes.length, by
    rcases decisionSite_compiledRow site fresh state with ⟨node, hnode, _⟩
    rw [← hnode]
    exact node.isLt⟩

/-- Generate opaque binding metadata. Assembly supplies the service slot;
structural application plans use the compiler's source-field address. -/
def bindingCode {who : P} {Γ Δ : VCtx P L} {prog : VegasCore P L Γ}
    {name : VarId} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    (site : SourceDecisionSite who prog Δ name ty guard)
    (fresh : FreshBindings prog) (state : BuildState P L Γ) (sourceSlot : Nat) :
    BindingCode P where
  owner := who
  node := (site.compiledNode fresh state).val
  sourceField := (compileCore prog fresh state).graph.nodeTarget
    (site.compiledNode fresh state)
  sourceSlot := sourceSlot
  requires := (compileCore prog fresh state).graph.messagePrerequisites
    (site.compiledNode fresh state)

end SourceDecisionSite

namespace CommitmentAccounting.OpeningSite

variable {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
variable {plan : CommitmentAccounting pending prog}

/-- Emit a conditional-publication instruction from its source occurrence,
accounting certificate, and compiler-allocated node and field addresses. -/
def code (site : plan.OpeningSite) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) (sourceSlot deadline : Nat) : ConditionalCode P L where
  endpoint := site.runtimeSite fresh state sourceSlot deadline
  guard := site.compiledGuard fresh state
  secretTy := site.data.specification.secretTy
  sourceField := site.sourceField fresh state
  encoding := site.data.specification.encoding
  choiceField := (compileCore prog fresh state).graph.nodeTarget
    (site.choiceNode fresh state)
  publicationField := (compileCore prog fresh state).graph.nodeTarget
    (site.publicationNode fresh state)

/-- Any resolved native result is source-legal, including declines and expiry
from an unopenable binding. The snapshot premise only constrains values that
can actually be recovered; it does not assume that a valid opening exists. -/
theorem code_resolution_source_legal
    (site : plan.OpeningSite) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) (sourceSlot deadline : Nat)
    (native : ApplicationImage.State P L) (representedStore : Store L)
    (env : VEnv L site.data.context)
    (heligible : site.PubliclyValidatable fresh state)
    (hagrees : (decisionSiteState site.data.decision fresh state).Agrees
      representedStore env)
    (hpublicStore : ∀ ref, (compileCore prog fresh state).graph.fieldRefPublic ref →
      Store.getAs native.memory.store ref.field ref.ty =
        Store.getAs representedStore ref.field ref.ty)
    (hbinding : ∀ value,
      (native.frozen (site.sourceField fresh state)).bind
          (fun typed => typed.as? site.data.specification.secretTy) = some value →
        value = env.get site.data.specification.binding)
    (message : Message P
      (ConditionalPublication.Payload P (L.Val site.data.specification.secretTy)))
    (result : Option (L.Val site.data.specification.secretTy))
    (hresolve : (site.code fresh state sourceSlot deadline).endpoint.resolve?
      native.memory.clock (native.verify (site.code fresh state sourceSlot deadline))
      (native.memory.accepted (site.sourceField fresh state)) native.memory.done
      ((site.code fresh state sourceSlot deadline).canOpen native.memory.store)
      message = some result) :
    (result = none ∨ result = some (env.get site.data.specification.binding)) ∧
      evalGuard site.data.guard (site.data.specification.encoding.symm result)
        ((env.toView site.data.owner).eraseEnv) = true := by
  let emitted := site.code fresh state sourceSlot deadline
  cases result with
  | none => exact ⟨Or.inl rfl, site.data.specification.decline_legal env⟩
  | some value =>
      have hverified := emitted.endpoint.resolve_some_verified native.memory.clock
        (native.verify emitted) (native.memory.accepted (site.sourceField fresh state))
        native.memory.done (emitted.canOpen native.memory.store) message value hresolve
      have hfrozen : (native.frozen (site.sourceField fresh state)).bind
          (fun typed => typed.as? site.data.specification.secretTy) = some value := by
        simpa [ApplicationImage.State.verify, emitted, code] using hverified
      have hvalue := hbinding value hfrozen
      refine ⟨Or.inr (congrArg some hvalue), ?_⟩
      have hcanOpen := emitted.endpoint.resolve_some_canOpen native.memory.clock
        (native.verify emitted) (native.memory.accepted (site.sourceField fresh state))
        native.memory.done (emitted.canOpen native.memory.store) message value hresolve
      change site.canOpen fresh state native.memory.store value = true at hcanOpen
      rw [site.canOpen_source fresh state representedStore native.memory.store env
        heligible hagrees hpublicStore value hvalue] at hcanOpen
      exact hcanOpen

end CommitmentAccounting.OpeningSite

end Vegas

/-- info: 'Vegas.CommitmentAccounting.OpeningSite.code_resolution_source_legal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.CommitmentAccounting.OpeningSite.code_resolution_source_legal
