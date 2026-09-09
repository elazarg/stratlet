/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.PublicChoiceSite
import Vegas.Compile.PublicGuard
import Vegas.Compile.SourceLaw

/-! # Source correctness of generated public-choice validators -/

noncomputable section

namespace Vegas

open EventGraph ToEventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

namespace PublicChoiceSite

/-- The retained compiler guard at this ordinary source decision. -/
def compiledGuard {Γ : VCtx P L} {prog : VegasCore P L Γ}
    (site : PublicChoiceSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) : EventGuard L :=
  eventGuardOf (site.siteState fresh state) site.owner site.guard

/-- Executable validation reads only the compiled guard's dependency
footprint from the supplied public store. -/
def validator {Γ : VCtx P L} {prog : VegasCore P L Γ}
    (site : PublicChoiceSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) (publicStore : Store L) : L.Val site.ty → Bool :=
  (site.compiledGuard fresh state).validate publicStore

/-- Eligibility of this generated validator for execution against a public
store. This condition concerns only syntactic guard dependencies, not the
owner's entire source view. -/
def PubliclyValidatable {Γ : VCtx P L} {prog : VegasCore P L Γ}
    (site : PublicChoiceSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) : Prop :=
  (site.compiledGuard fresh state).PubliclyValidatable
    (compileCore prog fresh state).graph

/-- At matching dependency values, the executable public validator is exactly
the source guard. The source environment and represented store occur only in
this correctness statement, never in `validator`. -/
theorem validator_source {Γ : VCtx P L} {prog : VegasCore P L Γ}
    (site : PublicChoiceSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) (representedStore publicStore : Store L)
    (env : VEnv L site.context)
    (hagrees : (site.siteState fresh state).Agrees representedStore env)
    (hpublic : ∀ ref
      (_href : ref ∈ (site.compiledGuard fresh state).validationReads),
      Store.getAs publicStore ref.field ref.ty =
        Store.getAs representedStore ref.field ref.ty)
    (chosen : L.Val site.ty) :
    site.validator fresh state publicStore chosen =
      evalGuard site.guard chosen ((env.toView site.owner).eraseEnv) := by
  let current := site.siteState fresh state
  let guard := site.compiledGuard fresh state
  have havailable := visibleFieldRefs_store_available current site.owner representedStore
    hagrees.available
  let reads := ReadEnv.ofStore representedStore (visibleFieldRefs current site.owner) havailable
  have hreads : ReadEnv.ofStore? representedStore (visibleFieldRefs current site.owner) =
      some reads := by
    unfold ReadEnv.ofStore?
    rw [dif_pos havailable]
  have hvalidation : guard.validate publicStore chosen = guard.eval chosen reads := by
    apply guard.validate_eq_eval publicStore chosen reads
    intro ref href
    rw [hpublic ref href]
    exact ReadEnv.ofStore?_read hreads
      (guard.validationReads_subset_choiceReads href)
  rw [show site.validator fresh state publicStore chosen =
      guard.validate publicStore chosen by rfl, hvalidation]
  change (eventGuardOf current site.owner site.guard).eval chosen reads = _
  rw [eventGuardOf_eval_eq_eval,
    viewEnvOfReadEnv_eq_sourceView current site.owner representedStore env
      (hagrees.view site.owner) reads hreads]

end PublicChoiceSite

end Vegas
