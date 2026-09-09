/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.PublicChoiceImage
import Vegas.Compile.PublicChoiceController
import Interaction.ChoiceControllerHistory

/-! # Source controllers for generated public-message images

The emitted packet and the image handler share the publication address and
dynamic value type. Full source-view reconstruction remains an executable
readout supplied by application assembly; guard dependencies alone do not
describe the choosing player's information.
-/

noncomputable section

namespace Vegas

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

namespace ApplicationImage

/-- Canonical encoding for one typed publication address. -/
def choiceEncoding (address : Nat) (ty : L.Ty) :
    ChoiceEncoding (L.Val ty) (Payload L) where
  encode value := .choice address ⟨ty, value⟩
  decode payload := match payload with
    | .choice actual typed => if actual = address then typed.as? ty else none
    | .malformed _ => none
  decode_encode := by intro value; simp [TypedValue.as?]
  decode_sound := by
    intro payload value hdecode
    cases payload with
    | malformed data => cases hdecode
    | choice actual typed =>
        simp only at hdecode
        split at hdecode
        · rename_i haddress
          subst actual
          rw [typed.eq_mk_of_as?_eq_some ty value hdecode]
        · cases hdecode

/-- An encoded choice for one endpoint cannot occupy another's cache. -/
theorem choiceEncoding_other_address (address other : Nat) (ty otherTy : L.Ty)
    (value : L.Val otherTy) (hne : other ≠ address) :
    (choiceEncoding address ty).decode
      ((choiceEncoding other otherTy).encode value) = none := by
  simp [choiceEncoding, hne]

end ApplicationImage

namespace PublicChoiceSite

variable {Γ : VCtx P L} {prog : VegasCore P L Γ}

/-- Install the source decision kernel with the same address and type as its
generated handler. The only readout inputs are local history and runtime view. -/
def imageController (site : PublicChoiceSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) (image : ApplicationImage P L)
    (readout? : List image.application.PlayerEntry → image.application.View →
      Option (site.ChoiceReads fresh state))
    (sourcePolicy :
      (visible : Env L.Val (eraseVCtx (viewVCtx site.owner site.context))) →
        FinDist { value : L.Val site.ty //
          evalGuard site.guard value visible = true })
    (retry : List image.application.PlayerEntry → image.application.View → Bool) :=
  site.controller fresh state image.application
    (ApplicationImage.choiceEncoding (site.runtimeSite fresh state).publicationNode site.ty)
    (fun view => view.application.done) readout? sourcePolicy retry

/-- Every packet encoded by a generated controller is accepted by the same
image instruction exactly when the source guard holds at the represented,
ready public checkpoint. Canonical packet typing and dispatch are conclusions
of the encoding and instruction lookup, not restrictions on the raw message
alphabet. Loading that generated instruction remains an explicit premise. -/
theorem image_encoded_accepts_iff
    (site : PublicChoiceSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) (image : ApplicationImage P L)
    (memory : ApplicationImage.Memory L) (representedStore : Store L)
    (env : VEnv L site.context)
    (heligible : site.PubliclyValidatable fresh state)
    (hagrees : (site.siteState fresh state).Agrees representedStore env)
    (hpublicStore : ∀ ref,
      (compileCore prog fresh state).graph.fieldRefPublic ref →
        Store.getAs memory.store ref.field ref.ty =
          Store.getAs representedStore ref.field ref.ty)
    (hready : (site.runtimeSite fresh state).ready memory.done = true)
    (hcode : image.lookup (site.runtimeSite fresh state).publicationNode =
      some (site.code fresh state))
    (serial : Nat) (value : L.Val site.ty) :
    image.handle memory
        ⟨(site.owner, serial),
          (ApplicationImage.choiceEncoding
            (site.runtimeSite fresh state).publicationNode site.ty).encode value⟩ =
        some (memory.publish (site.code fresh state) value) ↔
      evalGuard site.guard value ((env.toView site.owner).eraseEnv) = true := by
  rw [show (ApplicationImage.choiceEncoding
      (site.runtimeSite fresh state).publicationNode site.ty).encode value =
      ApplicationImage.Payload.choice (site.runtimeSite fresh state).publicationNode
        ⟨site.ty, value⟩ by rfl]
  erw [image.handle_choice memory _ (site.code fresh state) hcode _ value]
  have hresolve := site.code_resolves_iff_source_legal fresh state representedStore
    memory.store env heligible hagrees hpublicStore memory.done hready serial value
  cases hresult : (site.code fresh state).endpoint.resolve? memory.done
      ((site.code fresh state).guard.validate memory.store)
      ⟨(site.owner, serial), value⟩ with
  | none => simpa only [hresult, Option.map_none, reduceCtorEq] using hresolve
  | some accepted =>
      have hvalue : accepted = value :=
        ((site.code fresh state).endpoint.resolve_iff memory.done
          ((site.code fresh state).guard.validate memory.store) _ accepted).mp hresult
          |>.2.2.2.symm
      subst accepted
      simpa only [hresult, Option.map_some, eq_self_iff_true] using hresolve

/-- Every command supported by a first ready call of the generated controller
is a correctly addressed source-legal submission accepted by the image at that
checkpoint. This quantifies over arbitrary randomized source kernels. -/
theorem imageController_first_submission_accepted
    (site : PublicChoiceSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) (image : ApplicationImage P L)
    (readout? : List image.application.PlayerEntry → image.application.View →
      Option (site.ChoiceReads fresh state))
    (sourcePolicy :
      (visible : Env L.Val (eraseVCtx (viewVCtx site.owner site.context))) →
        FinDist { value : L.Val site.ty //
          evalGuard site.guard value visible = true })
    (retry : List image.application.PlayerEntry → image.application.View → Bool)
    (history : List image.application.PlayerEntry) (view : image.application.View)
    (representedStore : Store L) (env : VEnv L site.context)
    (reads : site.ChoiceReads fresh state)
    (heligible : site.PubliclyValidatable fresh state)
    (hagrees : (site.siteState fresh state).Agrees representedStore env)
    (hpublicStore : ∀ ref,
      (compileCore prog fresh state).graph.fieldRefPublic ref →
        Store.getAs view.application.store ref.field ref.ty =
          Store.getAs representedStore ref.field ref.ty)
    (hcode : image.lookup (site.runtimeSite fresh state).publicationNode =
      some (site.code fresh state))
    (hready : (site.runtimeSite fresh state).ready view.application.done = true)
    (hcache : ((ApplicationImage.choiceEncoding
        (site.runtimeSite fresh state).publicationNode site.ty).submission
          image.application).cachedValue image.application history = none)
    (hreadout : readout? history view = some reads)
    (hreads : ReadEnv.ofStore? representedStore
      (site.compiledGuard fresh state).choiceReads = some reads)
    (command : image.application.PlayerCommand)
    (hcommand : command ∈
      ((site.imageController fresh state image readout? sourcePolicy retry).policy
        image.application history view).support)
    (serial : Nat) :
    ∃ value : L.Val site.ty,
      evalGuard site.guard value ((env.toView site.owner).eraseEnv) = true ∧
      command = .submit (.choice (site.runtimeSite fresh state).publicationNode
        ⟨site.ty, value⟩) ∧
      image.handle view.application ⟨(site.owner, serial),
          .choice (site.runtimeSite fresh state).publicationNode ⟨site.ty, value⟩⟩ =
        some (view.application.publish (site.code fresh state) value) := by
  have hresolved : view.application.done
      (site.runtimeSite fresh state).publicationNode = false := by
    simp only [PublicChoice.ready, Bool.and_eq_true, Bool.not_eq_true'] at hready
    exact hready.1.2
  have hlaw := site.controller_first_submission_source_law fresh state image.application
    (ApplicationImage.choiceEncoding (site.runtimeSite fresh state).publicationNode site.ty)
    (fun current => current.application.done) readout? sourcePolicy retry history view
    representedStore env reads hresolved hcache hready hreadout
    (hagrees.view site.owner) hreads
  change command ∈ ((site.controller fresh state image.application
    (ApplicationImage.choiceEncoding (site.runtimeSite fresh state).publicationNode site.ty)
    (fun current => current.application.done) readout? sourcePolicy retry).policy
      image.application history view).support at hcommand
  rw [hlaw, FinDist.support_map] at hcommand
  obtain ⟨chosen, _, hchosen⟩ := hcommand
  refine ⟨chosen.1, chosen.2, hchosen.symm, ?_⟩
  exact (site.image_encoded_accepts_iff fresh state image view.application
    representedStore env heligible hagrees hpublicStore hready hcode serial chosen.1).2 chosen.2

end PublicChoiceSite

end Vegas

/-- info: 'Vegas.PublicChoiceSite.imageController_first_submission_accepted' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.PublicChoiceSite.imageController_first_submission_accepted
