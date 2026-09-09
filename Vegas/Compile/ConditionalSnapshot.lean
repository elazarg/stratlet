/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationImageReadoutAvailability
import Vegas.Compile.ConditionalPublicationSite
import Vegas.Compile.SourceExecution

/-! # Source identity of generated conditional snapshots

Typed registration provenance, native refinement, and source/store agreement
identify a canonical accepted snapshot with the original sealed source value.
No separate source-snapshot invariant is required at the conditional phase.
-/

noncomputable section

namespace Vegas.ConditionalPublicationSite

open EventGraph ToEventGraph Interaction

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A canonical accepted handle at a generated conditional source field
decodes to exactly the value of that field in the coupled source environment. -/
theorem frozen_source_binding
    {Γ : VCtx P L} {prog : VegasCore P L Γ}
    (site : ConditionalPublicationSite prog) (fresh : FreshBindings prog)
    (build : BuildState P L Γ)
    (image : ApplicationImage P L)
    (history : List image.application.PlayerEntry)
    (native : ApplicationImage.State P L)
    (cfg : Config (compileCore prog fresh build).graph)
    (hrefines : native.Refines cfg)
    (hbindings : image.RegisteredBindings site.choice.owner
      (fun slot typed => ∃ spec : FieldSpec P L,
        (compileCore prog fresh build).graph.field? slot = some spec ∧
          typed.ty = spec.ty) history native)
    (env : VEnv L site.choice.context)
    (hagrees : (site.choice.siteState fresh build).Agrees cfg.store env)
    (haccepted : native.memory.accepted (site.sourceField fresh build) =
      some (site.choice.owner, site.sourceField fresh build)) :
    (native.frozen (site.sourceField fresh build)).bind
        (fun typed => typed.as? site.specification.secretTy) =
      some (env.get site.specification.binding) := by
  obtain ⟨spec, hfield, htype, _⟩ := site.compiledSourceField fresh build
  obtain ⟨recovered, hfrozen, hstored⟩ :=
    hbindings.frozen_getAs_of_accepted image site.choice.owner history native
      cfg hrefines (site.sourceField fresh build) spec
      hfield htype haccepted
  have hsource : Store.getAs cfg.store
      (site.sourceField fresh build) site.specification.secretTy =
        some (env.get site.specification.binding) := by
    simpa only [sourceField] using hagrees site.specification.binding
  have heq : recovered = env.get site.specification.binding :=
    Option.some.inj (hstored.symm.trans hsource)
  exact hfrozen.trans (congrArg some heq)

/-- Consequently every successful branch of a legal conditional source
choice has the exact frozen value required by the generated phase law. -/
theorem legal_choice_frozen
    {Γ : VCtx P L} {name publicName : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ))
    (spec : ConditionalOpening guard)
    (fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail)))
    (build : BuildState P L Γ)
    (current : CoupledAt
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh build).graph build)
    (image : ApplicationImage P L)
    (history : List image.application.PlayerEntry)
    (native : ApplicationImage.State P L)
    (hrefines : native.Refines current.current.graph.1)
    (hbindings : image.RegisteredBindings who
      (fun slot typed => ∃ fieldSpec : FieldSpec P L,
        (compileCore (.commit name who guard (.reveal publicName who name .here tail))
          fresh build).graph.field? slot = some fieldSpec ∧
            typed.ty = fieldSpec.ty) history native)
    (haccepted : native.memory.accepted (build.fieldOf spec.binding) =
      some (who, build.fieldOf spec.binding))
    (chosen : L.Val ty)
    (hlegal : evalGuard guard chosen
      ((current.current.source.toView who).eraseEnv) = true) :
    ∀ value, spec.encoding chosen = some value →
      (native.frozen (build.fieldOf spec.binding)).bind
        (fun typed => typed.as? spec.secretTy) = some value := by
  let site := atHead name publicName who guard tail spec
  have hfrozen := site.frozen_source_binding fresh build image history native
    current.current.graph.1 hrefines hbindings current.current.source
    current.current.agrees haccepted
  intro value h
  have hvalue := spec.successful_value_eq_binding
    current.current.source chosen value hlegal h
  exact hfrozen.trans (congrArg some hvalue.symm)

end Vegas.ConditionalPublicationSite

/-- info: 'Vegas.ConditionalPublicationSite.frozen_source_binding' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ConditionalPublicationSite.frozen_source_binding

/-- info: 'Vegas.ConditionalPublicationSite.legal_choice_frozen' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ConditionalPublicationSite.legal_choice_frozen
