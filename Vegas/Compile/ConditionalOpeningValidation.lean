/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ConditionalOpeningSite
import Vegas.Compile.PublicGuard
import Vegas.Compile.SourceLaw

/-! # Dependency-local validation of conditional openings

The commitment service first verifies a claimed source value. The generated
opening validator then inserts that value transiently at the compiler's typed
source reference and evaluates the retained source guard. Every other
syntactic dependency of the guard must be a public field.

The source environment and represented store below occur only in correctness
proofs. They are not inputs to the executable validator.
-/

noncomputable section

namespace Vegas.CommitmentAccounting.OpeningSite

open Vegas.EventGraph Vegas.ToEventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
variable {plan : CommitmentAccounting pending prog}

/-- Retained executable guard for the accounted source decision. -/
def compiledGuard (site : plan.OpeningSite) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) : EventGuard L :=
  eventGuardOf (decisionSiteState site.data.decision fresh state)
    site.data.owner site.data.guard

/-- The exact typed graph reference of the earlier sealed source. Eligibility
uses typed-reference equality, not numeric-address equality alone. -/
def sourceRef (site : plan.OpeningSite) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) : FieldRef L where
  field := sourceField site fresh state
  ty := site.data.specification.secretTy

/-- Every syntactic guard dependency is either the one verified sealed source
or an ordinary public graph field. Full choice information is intentionally
not required by validation. -/
def PubliclyValidatable (site : plan.OpeningSite) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) : Prop :=
  ∀ ref, ref ∈ (site.compiledGuard fresh state).validationReads →
    ref = site.sourceRef fresh state ∨
      (compileCore prog fresh state).graph.fieldRefPublic ref

/-- Supply the already verified claim only to this guard evaluation. The
private source does not become persistent public application memory. -/
def verificationStore (site : plan.OpeningSite) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) (publicStore : Store L)
    (claimed : L.Val site.data.specification.secretTy) : Store L :=
  publicStore.set (sourceField site fresh state)
    ⟨site.data.specification.secretTy, claimed⟩

/-- Executable opening predicate generated from compiler code, a public store,
and the value authenticated by the commitment service. -/
def canOpen (site : plan.OpeningSite) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) (publicStore : Store L)
    (claimed : L.Val site.data.specification.secretTy) : Bool :=
  (site.compiledGuard fresh state).validate
    (site.verificationStore fresh state publicStore claimed)
    (site.data.specification.encoding.symm (some claimed))

private theorem public_ref_ne_source_field
    (site : plan.OpeningSite) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) (ref : FieldRef L)
    (hpublic : (compileCore prog fresh state).graph.fieldRefPublic ref) :
    ref.field ≠ sourceField site fresh state := by
  intro heq
  rcases site.compiledSourceField fresh state with
    ⟨sourceSpec, hsource, _hsourceTy, hsourceOwner⟩
  rcases hpublic with ⟨publicSpec, hpublic, _hpublicTy, hpublicOwner⟩
  rw [heq] at hpublic
  have hspec : publicSpec = sourceSpec := Option.some.inj (hpublic.symm.trans hsource)
  rw [hspec, hsourceOwner] at hpublicOwner
  cases hpublicOwner

/-- The executable predicate is exactly the source guard when the verified
claim is the represented source value, every other dependency is public, and
the runtime public store agrees with the represented store on public fields. -/
theorem canOpen_source
    (site : plan.OpeningSite) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) (representedStore publicStore : Store L)
    (env : VEnv L site.data.context)
    (heligible : site.PubliclyValidatable fresh state)
    (hagrees : (decisionSiteState site.data.decision fresh state).Agrees
      representedStore env)
    (hpublicStore : ∀ ref,
      (compileCore prog fresh state).graph.fieldRefPublic ref →
        Store.getAs publicStore ref.field ref.ty =
          Store.getAs representedStore ref.field ref.ty)
    (claimed : L.Val site.data.specification.secretTy)
    (hclaimed : claimed = env.get site.data.specification.binding) :
    site.canOpen fresh state publicStore claimed =
      evalGuard site.data.guard
        (site.data.specification.encoding.symm (some claimed))
        ((env.toView site.data.owner).eraseEnv) := by
  let current := decisionSiteState site.data.decision fresh state
  let guard := site.compiledGuard fresh state
  have havailable := visibleFieldRefs_store_available current site.data.owner
    representedStore hagrees.available
  let reads := ReadEnv.ofStore representedStore
    (visibleFieldRefs current site.data.owner) havailable
  have hreads : ReadEnv.ofStore? representedStore
      (visibleFieldRefs current site.data.owner) = some reads := by
    unfold ReadEnv.ofStore?
    rw [dif_pos havailable]
  have hvalidation : guard.validate
      (site.verificationStore fresh state publicStore claimed)
      (site.data.specification.encoding.symm (some claimed)) =
      guard.eval (site.data.specification.encoding.symm (some claimed)) reads := by
    apply guard.validate_eq_eval
    intro ref href
    have hread := ReadEnv.ofStore?_read hreads
      (guard.validationReads_subset_choiceReads href)
    rcases heligible ref href with hsource | hpublic
    · subst ref
      calc
        Store.getAs (site.verificationStore fresh state publicStore claimed)
            (site.sourceRef fresh state).field (site.sourceRef fresh state).ty =
            some claimed := by
              simp [verificationStore, sourceRef, Store.getAs, Store.set,
                TypedValue.as?]
        _ = some (env.get site.data.specification.binding) := by rw [hclaimed]
        _ = Store.getAs representedStore (site.sourceRef fresh state).field
            (site.sourceRef fresh state).ty := by
              symm
              simpa [sourceRef, sourceField] using
                hagrees site.data.specification.binding
        _ = some (reads.read (site.sourceRef fresh state)
            (guard.validationReads_subset_choiceReads href)) := hread
    · calc
        Store.getAs (site.verificationStore fresh state publicStore claimed)
            ref.field ref.ty = Store.getAs publicStore ref.field ref.ty := by
              exact Store.getAs_set_ne publicStore
                (public_ref_ne_source_field site fresh state ref hpublic)
                ⟨site.data.specification.secretTy, claimed⟩ ref.ty
        _ = Store.getAs representedStore ref.field ref.ty := hpublicStore ref hpublic
        _ = some (reads.read ref
            (guard.validationReads_subset_choiceReads href)) := hread
  rw [show site.canOpen fresh state publicStore claimed =
      guard.validate (site.verificationStore fresh state publicStore claimed)
        (site.data.specification.encoding.symm (some claimed)) by rfl,
    hvalidation]
  dsimp only [guard, compiledGuard]
  rw [eventGuardOf_eval_eq_eval,
    viewEnvOfReadEnv_eq_sourceView current site.data.owner representedStore env
      (hagrees.view site.data.owner) reads hreads]

end Vegas.CommitmentAccounting.OpeningSite

/--
info: 'Vegas.CommitmentAccounting.OpeningSite.canOpen_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.CommitmentAccounting.OpeningSite.canOpen_source
