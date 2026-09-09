/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.ChoiceController
import Vegas.Compile.PublicChoiceValidation

/-! # Message controllers for compiled public choices

This adapter turns one source decision kernel into an observation-local message
controller for its generated public-choice endpoint. Runtime execution reads
only the principal's own command history and application view. Source
environments and represented stores occur solely in the refinement theorems.

Public eligibility of the generated validator remains a separate obligation;
the acceptance theorem assumes agreement on its actual dependency footprint.
-/

noncomputable section

namespace Vegas.PublicChoiceSite

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {Γ : VCtx P L} {prog : VegasCore P L Γ}

/-- The complete compiler-declared readout consumed by a source choice. -/
abbrev ChoiceReads (site : PublicChoiceSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) :=
  ReadEnv L (site.compiledGuard fresh state).choiceReads

/-- Adapt one source decision policy to the sample-once message controller.
The executable readout receives only the owner's history and current runtime
view. The source policy's legality proof is erased before payload encoding. -/
def controller (site : PublicChoiceSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) (app : MessageApplication P)
    (codec : SubmissionCodec (L.Val site.ty) app.Payload)
    (done : app.View → Nat → Bool)
    (readout? : List app.PlayerEntry → app.View → Option (ChoiceReads site fresh state))
    (sourcePolicy :
      (visible : Env L.Val (eraseVCtx (viewVCtx site.owner site.context))) →
        FinDist { value : L.Val site.ty //
          evalGuard site.guard value visible = true })
    (retry : List app.PlayerEntry → app.View → Bool) :
    ChoiceController app (L.Val site.ty) (ChoiceReads site fresh state) where
  codec := codec
  ready := fun view => (site.runtimeSite fresh state).ready (done view)
  resolved := fun view => done view (site.runtimeSite fresh state).publicationNode
  readout? := readout?
  kernel := fun reads =>
    (compileSourceDecision (site.siteState fresh state) site.owner site.guard
      sourcePolicy reads).map Subtype.val
  retry := retry

/-- On the first uncached submission, a matching runtime readout emits exactly
the source decision law, after erasing its legality witness and encoding the
chosen value as a submission payload. -/
theorem controller_first_submission_source_law
    (site : PublicChoiceSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) (app : MessageApplication P)
    (codec : SubmissionCodec (L.Val site.ty) app.Payload)
    (done : app.View → Nat → Bool)
    (readout? : List app.PlayerEntry → app.View → Option (ChoiceReads site fresh state))
    (sourcePolicy :
      (visible : Env L.Val (eraseVCtx (viewVCtx site.owner site.context))) →
        FinDist { value : L.Val site.ty //
          evalGuard site.guard value visible = true })
    (retry : List app.PlayerEntry → app.View → Bool)
    (history : List app.PlayerEntry) (view : app.View)
    (representedStore : Store L) (env : VEnv L site.context)
    (reads : ChoiceReads site fresh state)
    (hresolved : done view (site.runtimeSite fresh state).publicationNode = false)
    (hcache : codec.cachedValue app history = none)
    (hready : (site.runtimeSite fresh state).ready (done view) = true)
    (hreadout : readout? history view = some reads)
    (hagrees : (site.siteState fresh state).ViewAgrees site.owner representedStore env)
    (hreads : ReadEnv.ofStore? representedStore
      (site.compiledGuard fresh state).choiceReads = some reads) :
    (site.controller fresh state app codec done readout? sourcePolicy retry).policy
        app history view =
      (sourcePolicy ((env.toView site.owner).eraseEnv)).map fun choice =>
        .submit (codec.encode choice.1) := by
  let adapted := site.controller fresh state app codec done readout? sourcePolicy retry
  calc
    adapted.policy app history view =
        (adapted.kernel reads).map fun value => .submit (codec.encode value) :=
      adapted.policy_of_uncached_ready app history view reads
        hresolved hcache hready hreadout
    _ = (sourcePolicy ((env.toView site.owner).eraseEnv)).map fun choice =>
        .submit (codec.encode choice.1) := by
      dsimp only [adapted, controller]
      have hlaw := compileSourceDecision_law (site.siteState fresh state)
        site.owner site.guard sourcePolicy representedStore env hagrees reads hreads
      have hmapped := congrArg
        (FinDist.map (fun value : L.Val site.ty =>
          PlayerCommand.submit (codec.encode value))) hlaw
      simpa only [FinDist.map_comp, Function.comp_def] using hmapped

/-- Every value supported by the adapter's compiled kernel carries the source
guard certificate needed by the generated public validator. At matching
public dependencies, its canonical owner-authored request is accepted by the
actual generated endpoint. -/
theorem controller_submission_resolves
    (site : PublicChoiceSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) (app : MessageApplication P)
    (codec : SubmissionCodec (L.Val site.ty) app.Payload)
    (doneView : app.View → Nat → Bool)
    (readout? : List app.PlayerEntry → app.View → Option (ChoiceReads site fresh state))
    (sourcePolicy :
      (visible : Env L.Val (eraseVCtx (viewVCtx site.owner site.context))) →
        FinDist { value : L.Val site.ty //
          evalGuard site.guard value visible = true })
    (retry : List app.PlayerEntry → app.View → Bool)
    (representedStore publicStore : Store L) (env : VEnv L site.context)
    (reads : ChoiceReads site fresh state) (done : Nat → Bool)
    (hagrees : (site.siteState fresh state).Agrees representedStore env)
    (hreads : ReadEnv.ofStore? representedStore
      (site.compiledGuard fresh state).choiceReads = some reads)
    (hpublic : ∀ ref
      (_href : ref ∈ (site.compiledGuard fresh state).validationReads),
      Store.getAs publicStore ref.field ref.ty =
        Store.getAs representedStore ref.field ref.ty)
    (hready : (site.runtimeSite fresh state).ready done = true)
    (value : L.Val site.ty)
    (hvalue : value ∈
      ((site.controller fresh state app codec doneView readout? sourcePolicy retry).kernel
        reads).support)
    (serial : Nat) :
    (site.runtimeSite fresh state).resolve? done
        (site.validator fresh state publicStore)
        ⟨(site.owner, serial), value⟩ = some value := by
  change value ∈ ((compileSourceDecision (site.siteState fresh state) site.owner
    site.guard sourcePolicy reads).map Subtype.val).support at hvalue
  rw [FinDist.support_map] at hvalue
  obtain ⟨chosen, _, hchosen⟩ := hvalue
  subst value
  have hlegal := chosen.2
  rw [eventGuardOf_eval_eq_eval,
    viewEnvOfReadEnv_eq_sourceView (site.siteState fresh state) site.owner
      representedStore env (hagrees.view site.owner) reads hreads] at hlegal
  have hvalid : site.validator fresh state publicStore chosen.1 = true := by
    rw [site.validator_source fresh state representedStore publicStore env
      hagrees hpublic chosen.1]
    exact hlegal
  exact ((site.runtimeSite fresh state).resolve_request done
    (site.validator fresh state publicStore) serial chosen.1).2 ⟨hready, hvalid⟩

end Vegas.PublicChoiceSite
