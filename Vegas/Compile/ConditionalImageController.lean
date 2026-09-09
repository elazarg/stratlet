/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationImage
import Vegas.Compile.ConditionalOpeningController

/-! # Source controllers for generated conditional-publication images

This module supplies the typed payload transport between a certified
conditional-publication occurrence and `ApplicationImage`. Choice readout is
still provided by application assembly because it includes the choosing
player's full source-visible information, not only public guard dependencies.
-/

noncomputable section

namespace Vegas

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

namespace ApplicationImage

/-- Canonical dynamic image payload for a typed conditional-publication
request. Decoding checks the type of opening claims and rejects every other
image payload constructor. -/
def conditionalTransport (secretTy : L.Ty) :
    ChoiceEncoding
      (Nat × ConditionalPublication.Payload P (L.Val secretTy))
      (Payload P L) where
  encode
    | (address, .opening handle value) =>
        .conditional address (.opening handle ⟨secretTy, value⟩)
    | (address, .decline) => .conditional address .decline
    | (address, .expire) => .conditional address .expire
    | (address, .cleartext value) =>
        .conditional address (.cleartext ⟨secretTy, value⟩)
    | (address, .malformed) => .conditional address .malformed
  decode
    | .conditional address (.opening handle typed) =>
        (typed.as? secretTy).map fun value => (address, .opening handle value)
    | .conditional address .decline => some (address, .decline)
    | .conditional address .expire => some (address, .expire)
    | .conditional address (.cleartext typed) =>
        (typed.as? secretTy).map fun value => (address, .cleartext value)
    | .conditional address .malformed => some (address, .malformed)
    | _ => none
  decode_encode value := by
    rcases value with ⟨address, payload⟩
    cases payload <;> simp [TypedValue.as?]
  decode_sound wire value hdecode := by
    rcases value with ⟨address, payload⟩
    cases wire with
    | conditional actual raw =>
        cases raw with
        | opening handle typed =>
            simp only at hdecode
            rw [Option.map_eq_some_iff] at hdecode
            obtain ⟨decoded, htyped, heq⟩ := hdecode
            cases heq
            rw [typed.eq_mk_of_as?_eq_some secretTy decoded htyped]
        | decline => cases Option.some.inj hdecode; rfl
        | expire => cases Option.some.inj hdecode; rfl
        | cleartext typed =>
            simp only at hdecode
            rw [Option.map_eq_some_iff] at hdecode
            obtain ⟨decoded, htyped, heq⟩ := hdecode
            cases heq
            rw [typed.eq_mk_of_as?_eq_some secretTy decoded htyped]
        | malformed => cases Option.some.inj hdecode; rfl
    | _ => cases hdecode

end ApplicationImage

namespace ConditionalPublicationSite

variable {Γ : VCtx P L} {prog : VegasCore P L Γ}

/-- Install a conditional source decision with the payload, accepted-binding,
and completion projections used by the generated image handler. -/
def imageController (site : ConditionalPublicationSite prog)
    (fresh : FreshBindings prog) (state : BuildState P L Γ)
    (sourceSlot deadline : Nat) (image : ApplicationImage P L)
    (readout? : List image.application.PlayerEntry → image.application.View →
      Option (site.ChoiceReads fresh state))
    (sourcePolicy :
      (visible : Env L.Val
        (eraseVCtx (viewVCtx site.choice.owner site.choice.context))) →
        FinDist { value : L.Val site.choice.ty //
          evalGuard site.choice.guard value visible = true })
    (retry : List image.application.PlayerEntry → image.application.View → Bool) :=
  site.controller fresh state sourceSlot deadline image.application
    (ApplicationImage.conditionalTransport site.specification.secretTy)
    (fun view => view.application.accepted (site.sourceField fresh state))
    (fun view => view.application.done) readout? sourcePolicy retry

/-- A first uncached, ready image-controller invocation has exactly the source
decision law and emits the canonical dynamically typed conditional payload. -/
theorem imageController_first_submission_source_law
    (site : ConditionalPublicationSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) (sourceSlot deadline : Nat)
    (image : ApplicationImage P L)
    (readout? : List image.application.PlayerEntry → image.application.View →
      Option (site.ChoiceReads fresh state))
    (sourcePolicy :
      (visible : Env L.Val
        (eraseVCtx (viewVCtx site.choice.owner site.choice.context))) →
        FinDist { value : L.Val site.choice.ty //
          evalGuard site.choice.guard value visible = true })
    (retry : List image.application.PlayerEntry → image.application.View → Bool)
    (history : List image.application.PlayerEntry) (view : image.application.View)
    (representedStore : Store L) (env : VEnv L site.choice.context)
    (reads : site.ChoiceReads fresh state)
    (hresolved : view.application.done
      (site.runtimeSite fresh state sourceSlot deadline).publicationNode = false)
    (hcache :
      ((site.choiceEncoding fresh state sourceSlot deadline
        (ApplicationImage.conditionalTransport site.specification.secretTy)).submission
          image.application).cachedValue image.application history = none)
    (hready : (site.runtimeSite fresh state sourceSlot deadline).ready
      (view.application.accepted (site.sourceField fresh state))
      view.application.done = true)
    (hreadout : readout? history view = some reads)
    (hagrees : (site.choice.siteState fresh state).ViewAgrees
      site.choice.owner representedStore env)
    (hreads : ReadEnv.ofStore? representedStore
      (site.choice.compiledGuard fresh state).choiceReads = some reads) :
    (site.imageController fresh state sourceSlot deadline image readout?
     sourcePolicy retry).policy image.application history view =
      (sourcePolicy ((env.toView site.choice.owner).eraseEnv)).map fun choice =>
        .submit ((ApplicationImage.conditionalTransport site.specification.secretTy).encode
          ((site.runtimeSite fresh state sourceSlot deadline).publicationNode,
            (site.runtimeSite fresh state sourceSlot deadline).requestPayload
              (site.specification.encoding choice.1))) := by
  exact site.controller_first_submission_source_law fresh state sourceSlot deadline
    image.application (ApplicationImage.conditionalTransport site.specification.secretTy)
    (fun current => current.application.accepted (site.sourceField fresh state))
    (fun current => current.application.done) readout? sourcePolicy retry history view
    representedStore env reads hresolved hcache hready hreadout hagrees hreads

end ConditionalPublicationSite

end Vegas
