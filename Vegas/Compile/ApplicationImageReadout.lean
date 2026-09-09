/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationImageStateRefinement
import Vegas.Compile.SourceLaw
import Vegas.Compile.DecisionSite
import Interaction.ChoiceController

/-! # Owner-local readout of generated application fields

Resolved public fields take precedence over private command history. In
particular, an expired conditional copy is read as its resolved decline, even
when the owner previously attempted to open it. Only an accepted canonical
original binding can fall back to the owner's private registration cache.

The executable readout uses no source environment or private service state.
Its correctness theorem requires cache/snapshot correspondence and operational
availability. These are strategy-lifting obligations, not consequences of
native refinement for arbitrary player policies. Slots equal source fields in
the structural application compiler.
-/

noncomputable section

namespace Vegas.ApplicationImage

open EventGraph ToEventGraph Interaction Interaction.MessageApplication

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Canonical private registration at a compiler-allocated slot. Dynamic type
checking happens when the source read footprint is loaded. -/
def registrationEncoding (slot : Nat) :
    ChoiceEncoding (TypedValue L) (PrivateCommand L) where
  encode value := .register slot value
  decode
    | .register actual value => if actual = slot then some value else none
  decode_encode _ := by simp
  decode_sound command value hdecode := by
    cases command with
    | register actual typed =>
        simp only at hdecode
        split at hdecode
        · rename_i hslot
          subst actual
          cases Option.some.inj hdecode
          rfl
        · cases hdecode

/-- Sample-once private memory for an original binding. Submissions, including
opening attempts, cannot populate this cache. -/
def registrationCache (image : ApplicationImage P L) (slot : Nat)
    (history : List image.application.PlayerEntry) : Option (TypedValue L) :=
  ((registrationEncoding slot).privateCommand image.application).cachedValue
    image.application history

/-- Reconstruct allocated fields using only current public memory and the
owner's own recorded registrations. A public result is authoritative. -/
def ownerReadStore (image : ApplicationImage P L) (who : P)
    (history : List image.application.PlayerEntry) (memory : Memory P L) : Store L :=
  fun field => match memory.store field with
    | some value => some value
    | none => if memory.accepted field = some (who, field) then
        image.registrationCache field history else none

/-- Load the complete declared choice footprint, not just guard dependencies.
Missing or ill-typed inputs cause a wait in the consuming choice controller. -/
def ownerReadout? (image : ApplicationImage P L) (who : P)
    (refs : Finset (FieldRef L)) (history : List image.application.PlayerEntry)
    (view : image.application.View) : Option (ReadEnv L refs) :=
  ReadEnv.ofStoreExec? (image.ownerReadStore who history view.application) refs

theorem ownerReadStore_public (image : ApplicationImage P L) (who : P)
    (history : List image.application.PlayerEntry) (memory : Memory P L)
    (field : Nat) (value : TypedValue L) (hstored : memory.store field = some value) :
    image.ownerReadStore who history memory field = some value := by
  simp [ownerReadStore, hstored]

/-- Appending traffic cannot replace an already recorded private choice. This
is a cache law, not a claim that arbitrary re-registration preserves the
snapshot subsequently accepted by the runtime. -/
theorem registrationCache_append (image : ApplicationImage P L) (slot : Nat)
    (history suffix : List image.application.PlayerEntry) (value : TypedValue L)
    (hcache : image.registrationCache slot history = some value) :
    image.registrationCache slot (history ++ suffix) = some value := by
  exact ChoiceEncoding.cachedValue_append_of_some _ _ history suffix value hcache

/-- A controller's first registration agrees with the snapshot accepted for
that original binding. No condition is needed for already-public fields. -/
def RegistrationMatches (image : ApplicationImage P L) (who : P)
    (history : List image.application.PlayerEntry) (native : State P L) : Prop :=
  ∀ field value, native.memory.store field = none →
    native.memory.accepted field = some (who, field) →
    image.registrationCache field history = some value →
      native.frozen field = some value

/-- Every successfully reconstructed, correctly typed graph field has its
represented value. Public values use memory refinement; private values use
the accepted binding's checked snapshot provenance. -/
theorem ownerReadStore_getAs
    (image : ApplicationImage P L) (who : P)
    (history : List image.application.PlayerEntry) (native : State P L)
    {G : Graph P L} (cfg : Config G) (hrefines : native.Refines cfg)
    (hcache : image.RegistrationMatches who history native)
    (ref : FieldRef L) (spec : FieldSpec P L)
    (hfield : G.field? ref.field = some spec) (htype : spec.ty = ref.ty)
    (value : L.Val ref.ty)
    (hread : Store.getAs (image.ownerReadStore who history native.memory)
      ref.field ref.ty = some value) :
    Store.getAs cfg.store ref.field ref.ty = some value := by
  rcases ref with ⟨field, ty⟩
  dsimp only at htype hread ⊢
  subst ty
  cases hpublic : native.memory.store field with
  | some typed =>
      have hstored := hrefines.memory.stored field typed hpublic
      simpa [Store.getAs, ownerReadStore, hpublic, hstored] using hread
  | none =>
      by_cases haccepted : native.memory.accepted field = some (who, field)
      · simp only [Store.getAs, ownerReadStore, hpublic, if_pos haccepted] at hread
        cases hrecorded : image.registrationCache field history with
        | none => simp [hrecorded] at hread
        | some typed =>
            have hfrozen := hcache field typed hpublic haccepted hrecorded
            obtain ⟨actual, bound, hactual, _, hbound, hconsistent⟩ :=
              hrefines.bindings field (who, field) haccepted
            have hspec : actual = spec := Option.some.inj (hactual.symm.trans hfield)
            subst actual
            have hrecovered : (native.frozen field).bind
                (fun stored => stored.as? spec.ty) = some value := by
              simpa [hfrozen, hrecorded] using hread
            have heq := hconsistent value hrecovered
            rw [← heq] at hbound
            exact hbound
      · simp [Store.getAs, ownerReadStore, hpublic, haccepted] at hread

/-- Native inputs suffice to reconstruct the complete source-visible context
when all declared reads are available and cached originals match their frozen
snapshots. No private graph store is passed to the executable loader. -/
theorem ownerReadStore_view_agrees
    (image : ApplicationImage P L) (who : P)
    (history : List image.application.PlayerEntry) (native : State P L)
    {G : Graph P L} (cfg : Config G) (hrefines : native.Refines cfg)
    (hcache : image.RegistrationMatches who history native)
    {Γ : VCtx P L} (build : BuildState P L Γ) (env : VEnv L Γ)
    (hsource : build.ViewAgrees who cfg.store env)
    (hfields : ∀ ref ∈ visibleFieldRefs build who,
      ∃ spec, G.field? ref.field = some spec ∧ spec.ty = ref.ty)
    (havailable : ∀ ref ∈ visibleFieldRefs build who,
      (Store.getAs (image.ownerReadStore who history native.memory) ref.field ref.ty).isSome) :
    build.ViewAgrees who (image.ownerReadStore who history native.memory) env := by
  intro name bindTy binding
  let ref := build.fieldRefOfView who binding
  have href : ref ∈ visibleFieldRefs build who :=
    fieldRefOfView_mem_visibleFieldRefs build who binding
  obtain ⟨value, hread⟩ := Option.isSome_iff_exists.mp (havailable ref href)
  obtain ⟨spec, hfield, htype⟩ := hfields ref href
  have hrepresented := image.ownerReadStore_getAs who history native cfg hrefines
    hcache ref spec hfield htype value hread
  have heq := Option.some.inj (hrepresented.symm.trans (hsource binding))
  exact hread.trans (congrArg some heq)

/-- Transfer a successful local load to the represented graph store. The
footprint can belong to any consumer; source environments are unnecessary. -/
theorem ownerReadout?_graph_reads
    (image : ApplicationImage P L) (who : P)
    (history : List image.application.PlayerEntry) (view : image.application.View)
    (native : State P L) (hview : view.application = native.memory)
    {G : Graph P L} (cfg : Config G) (hrefines : native.Refines cfg)
    (hcache : image.RegistrationMatches who history native)
    (refs : Finset (FieldRef L))
    (hfields : ∀ ref ∈ refs,
      ∃ spec, G.field? ref.field = some spec ∧ spec.ty = ref.ty)
    (reads : ReadEnv L refs)
    (hreadout : image.ownerReadout? who refs history view = some reads) :
    ReadEnv.ofStore? cfg.store refs = some reads := by
  have hreads : ReadEnv.ofStore? (image.ownerReadStore who history native.memory)
      refs = some reads := by
    apply ReadEnv.ofStore?_eq_some_of_ofStoreExec?_eq_some
    simpa only [ownerReadout?, hview] using hreadout
  apply ReadEnv.ofStore?_eq_of_getAs_eq hreads
  intro ref href
  obtain ⟨spec, hfield, htype⟩ := hfields ref href
  have hlocal := ReadEnv.ofStore?_read hreads href
  exact hlocal.trans (image.ownerReadStore_getAs who history native cfg hrefines
    hcache ref spec hfield htype (reads.read ref href) hlocal).symm

/-- A successful local load recovers exactly the source-visible environment.
Successful loading discharges availability; snapshot correspondence remains a
separate, explicit hypothesis about the generated controller's execution. -/
theorem ownerReadout?_source_view
    (image : ApplicationImage P L) (who : P)
    (history : List image.application.PlayerEntry) (view : image.application.View)
    (native : State P L) (hview : view.application = native.memory)
    {G : Graph P L} (cfg : Config G) (hrefines : native.Refines cfg)
    (hcache : image.RegistrationMatches who history native)
    {Γ : VCtx P L} (build : BuildState P L Γ) (env : VEnv L Γ)
    (hsource : build.ViewAgrees who cfg.store env)
    (hfields : ∀ ref ∈ visibleFieldRefs build who,
      ∃ spec, G.field? ref.field = some spec ∧ spec.ty = ref.ty)
    (reads : ReadEnv L (visibleFieldRefs build who))
    (hreadout : image.ownerReadout? who (visibleFieldRefs build who) history view =
      some reads) :
    viewEnvOfReadEnv build who reads = (env.toView who).eraseEnv := by
  exact viewEnvOfReadEnv_eq_sourceView build who cfg.store env hsource reads
    (image.ownerReadout?_graph_reads who history view native hview cfg hrefines
      hcache (visibleFieldRefs build who) hfields reads hreadout)

end Vegas.ApplicationImage

namespace Vegas.SourceDecisionSite

open EventGraph ToEventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- For a compiled source occurrence, typed field metadata is supplied by the
compiler itself. A successful owner-local load therefore gives exactly the
reads at that graph decision, under native and cache refinement. -/
theorem ownerReadout?_graph_reads
    {who : P} {Γ Δ : VCtx P L} {prog : VegasCore P L Γ}
    {name : VarId} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    (site : SourceDecisionSite who prog Δ name ty guard)
    (fresh : FreshBindings prog) (build : BuildState P L Γ)
    (image : ApplicationImage P L)
    (history : List image.application.PlayerEntry) (view : image.application.View)
    (native : ApplicationImage.State P L) (hview : view.application = native.memory)
    (cfg : Config (compileCore prog fresh build).graph) (hrefines : native.Refines cfg)
    (hcache : image.RegistrationMatches who history native)
    (reads : ReadEnv L
      (eventGuardOf (decisionSiteState site fresh build) who guard).choiceReads)
    (hreadout : image.ownerReadout? who
      (eventGuardOf (decisionSiteState site fresh build) who guard).choiceReads
        history view = some reads) :
    ReadEnv.ofStore? cfg.store
      (eventGuardOf (decisionSiteState site fresh build) who guard).choiceReads = some reads := by
  apply image.ownerReadout?_graph_reads who history view native hview cfg hrefines
    hcache _ _ reads hreadout
  intro ref href
  obtain ⟨name, bindTy, binding, rfl⟩ := (mem_fieldRefsOfCtx_iff _ ref).mp href
  let cursor := decisionSiteState site fresh build
  obtain ⟨spec, hfield, htype, _⟩ := cursor.fieldOf_spec binding.ofViewVCtx
  refine ⟨spec, ?_, htype⟩
  rw [← decisionSiteState_field?_eq_compileCore site fresh build _
    (cursor.fieldOf_lt binding.ofViewVCtx)]
  exact hfield

end Vegas.SourceDecisionSite

/-- info: 'Vegas.ApplicationImage.ownerReadStore_view_agrees' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.ownerReadStore_view_agrees

/-- info: 'Vegas.SourceDecisionSite.ownerReadout?_graph_reads' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceDecisionSite.ownerReadout?_graph_reads
