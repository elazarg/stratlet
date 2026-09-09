/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.ConditionalPublicationRouting
import Vegas.Compile.ConditionalPublicationSite
import Vegas.Compile.ConditionalResolution
import Vegas.Compile.PublicChoiceValidation
import Vegas.Compile.SourceLaw

/-! # Message controllers for compiled conditional openings

This adapter compiles one certified conditional-opening decision into a
sample-once message controller. Its executable inputs are restricted to the
owner's command history and current application view. Source environments and
represented stores occur only in the refinement theorems.

Application assembly must install the policy at the declared owner, supply the
actual readiness projections, and connect the same transport decoder to the
addressed handler. The local laws below do not establish that assembly or its
strategic correspondence.
-/

noncomputable section

namespace Vegas.ConditionalPublicationSite

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {Γ : VCtx P L} {prog : VegasCore P L Γ}

/-- The complete compiler-declared readout consumed by the opening choice. -/
abbrev ChoiceReads (site : ConditionalPublicationSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) :=
  ReadEnv L (site.choice.compiledGuard fresh state).choiceReads

/-- Canonical application encoding of a source opening choice. The source
certificate first maps the chosen copy value to decline/open, the generated
publication identity addresses that request, and the application transport
embeds the addressed request in its payload type. -/
def choiceEncoding (site : ConditionalPublicationSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) (sourceSlot deadline : Nat)
    {Wire : Type*}
    (transport : ChoiceEncoding
      (Nat × ConditionalPublication.Payload P
        (L.Val site.specification.secretTy)) Wire) :
    ChoiceEncoding (L.Val site.choice.ty) Wire :=
  (((runtimeSite site fresh state sourceSlot deadline).addressedChoiceEncoding
      (Value := L.Val site.specification.secretTy)).reindex
        site.specification.encoding).trans transport

/-- Adapt the source opening decision to an observation-local, sample-once
application controller. -/
def controller (site : ConditionalPublicationSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) (sourceSlot deadline : Nat)
    (app : MessageApplication P)
    (transport : ChoiceEncoding
      (Nat × ConditionalPublication.Payload P
        (L.Val site.specification.secretTy)) app.Payload)
    (accepted : app.View → Option (CommitmentHandle P Nat))
    (done : app.View → Nat → Bool)
    (readout? : List app.PlayerEntry → app.View → Option (ChoiceReads site fresh state))
    (sourcePolicy :
      (visible : Env L.Val
        (eraseVCtx (viewVCtx site.choice.owner site.choice.context))) →
        FinDist { value : L.Val site.choice.ty //
          evalGuard site.choice.guard value visible = true })
    (retry : List app.PlayerEntry → app.View → Bool) :
    ChoiceController app (L.Val site.choice.ty) (ChoiceReads site fresh state) where
  codec := (site.choiceEncoding fresh state sourceSlot deadline transport).submission app
  ready := fun view =>
    (runtimeSite site fresh state sourceSlot deadline).ready (accepted view) (done view)
  resolved := fun view =>
    done view (runtimeSite site fresh state sourceSlot deadline).publicationNode
  readout? := readout?
  kernel := fun reads =>
    (compileSourceDecision (site.choice.siteState fresh state)
      site.choice.owner site.choice.guard sourcePolicy reads).map Subtype.val
  retry := retry

/-- The first uncached ready emission has exactly the source decision law,
with its legality witness erased and its value passed through the generated
address and application transport. -/
theorem controller_first_submission_source_law
    (site : ConditionalPublicationSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) (sourceSlot deadline : Nat)
    (app : MessageApplication P)
    (transport : ChoiceEncoding
      (Nat × ConditionalPublication.Payload P
        (L.Val site.specification.secretTy)) app.Payload)
    (accepted : app.View → Option (CommitmentHandle P Nat))
    (done : app.View → Nat → Bool)
    (readout? : List app.PlayerEntry → app.View → Option (ChoiceReads site fresh state))
    (sourcePolicy :
      (visible : Env L.Val
        (eraseVCtx (viewVCtx site.choice.owner site.choice.context))) →
        FinDist { value : L.Val site.choice.ty //
          evalGuard site.choice.guard value visible = true })
    (retry : List app.PlayerEntry → app.View → Bool)
    (history : List app.PlayerEntry) (view : app.View)
    (representedStore : Store L) (env : VEnv L site.choice.context)
    (reads : ChoiceReads site fresh state)
    (hresolved : done view
      (runtimeSite site fresh state sourceSlot deadline).publicationNode = false)
    (hcache :
      ((site.choiceEncoding fresh state sourceSlot deadline transport).submission app).cachedValue
        app history = none)
    (hready : (runtimeSite site fresh state sourceSlot deadline).ready
      (accepted view) (done view) = true)
    (hreadout : readout? history view = some reads)
    (hagrees : (site.choice.siteState fresh state).ViewAgrees
      site.choice.owner representedStore env)
    (hreads : ReadEnv.ofStore? representedStore
      (site.choice.compiledGuard fresh state).choiceReads = some reads) :
    (site.controller fresh state sourceSlot deadline app transport accepted done
        readout? sourcePolicy retry).policy app history view =
      (sourcePolicy ((env.toView site.choice.owner).eraseEnv)).map fun choice =>
        .submit (transport.encode
          ((runtimeSite site fresh state sourceSlot deadline).publicationNode,
            (runtimeSite site fresh state sourceSlot deadline).requestPayload
              (site.specification.encoding choice.1))) := by
  let adapted := site.controller fresh state sourceSlot deadline app transport
    accepted done readout? sourcePolicy retry
  calc
    adapted.policy app history view =
        (adapted.kernel reads).map adapted.codec.encode :=
      adapted.policy_of_uncached_ready app history view reads
        hresolved hcache hready hreadout
    _ = (sourcePolicy ((env.toView site.choice.owner).eraseEnv)).map fun choice =>
        .submit (transport.encode
          ((runtimeSite site fresh state sourceSlot deadline).publicationNode,
            (runtimeSite site fresh state sourceSlot deadline).requestPayload
              (site.specification.encoding choice.1))) := by
      have hlaw := compileSourceDecision_law
        (site.choice.siteState fresh state) site.choice.owner
        site.choice.guard sourcePolicy representedStore env hagrees reads hreads
      have hmapped := congrArg
        (FinDist.map (fun value : L.Val site.choice.ty =>
          PlayerCommand.submit (transport.encode
            ((runtimeSite site fresh state sourceSlot deadline).publicationNode,
              (runtimeSite site fresh state sourceSlot deadline).requestPayload
                (site.specification.encoding value))))) hlaw
      simpa only [adapted, controller, choiceEncoding, ChoiceEncoding.submission,
        ChoiceEncoding.trans, ChoiceEncoding.reindex,
        ConditionalPublication.addressedChoiceEncoding, ChoiceEncoding.atEndpoint,
        ConditionalPublication.choiceEncoding, FinDist.map_comp, Function.comp_def] using hmapped

/-- Every value supported by the compiled opening kernel resolves through the
generated addressed handler when the accepted binding, stored value,
readiness, and opening predicate satisfy the source certificate. -/
theorem controller_submission_resolves
    (site : ConditionalPublicationSite prog) (fresh : FreshBindings prog)
    (state : BuildState P L Γ) (sourceSlot deadline now : Nat)
    (app : MessageApplication P)
    (transport : ChoiceEncoding
      (Nat × ConditionalPublication.Payload P
        (L.Val site.specification.secretTy)) app.Payload)
    (acceptedView : app.View → Option (CommitmentHandle P Nat))
    (doneView : app.View → Nat → Bool)
    (readout? : List app.PlayerEntry → app.View → Option (ChoiceReads site fresh state))
    (sourcePolicy :
      (visible : Env L.Val
        (eraseVCtx (viewVCtx site.choice.owner site.choice.context))) →
        FinDist { value : L.Val site.choice.ty //
          evalGuard site.choice.guard value visible = true })
    (retry : List app.PlayerEntry → app.View → Bool)
    (representedStore : Store L) (env : VEnv L site.choice.context)
    (reads : ChoiceReads site fresh state)
    (hagrees : (site.choice.siteState fresh state).ViewAgrees
      site.choice.owner representedStore env)
    (hreads : ReadEnv.ofStore? representedStore
      (site.choice.compiledGuard fresh state).choiceReads = some reads)
    (service : IdealCommitments P Nat
      (L.Val site.specification.secretTy))
    (accepted : Option (CommitmentHandle P Nat)) (done : Nat → Bool)
    (canOpen : L.Val site.specification.secretTy → Bool)
    (hstored : service.lookup (site.choice.owner, sourceSlot) =
      some (env.get site.specification.binding))
    (hready : (runtimeSite site fresh state sourceSlot deadline).ready accepted done = true)
    (hcanOpen :
      evalGuard site.choice.guard
          (site.specification.encoding.symm
            (some (env.get site.specification.binding)))
          ((env.toView site.choice.owner).eraseEnv) = true →
        canOpen (env.get site.specification.binding) = true)
    (value : L.Val site.choice.ty)
    (hvalue : value ∈
      ((site.controller fresh state sourceSlot deadline app transport
        acceptedView doneView readout? sourcePolicy retry).kernel reads).support)
    (serial : Nat) :
    (runtimeSite site fresh state sourceSlot deadline).resolveAddressed?
        now service.verify accepted done canOpen
        ⟨(site.choice.owner, serial),
          ((runtimeSite site fresh state sourceSlot deadline).publicationNode,
            (runtimeSite site fresh state sourceSlot deadline).requestPayload
              (site.specification.encoding value))⟩ =
      some (site.specification.encoding value) := by
  change value ∈
    ((compileSourceDecision (site.choice.siteState fresh state)
      site.choice.owner site.choice.guard sourcePolicy reads).map Subtype.val).support at hvalue
  rw [FinDist.support_map] at hvalue
  obtain ⟨chosen, _, hchosen⟩ := hvalue
  subst value
  have hlegal := chosen.2
  rw [eventGuardOf_eval_eq_eval,
    viewEnvOfReadEnv_eq_sourceView
      (site.choice.siteState fresh state) site.choice.owner
      representedStore env hagrees reads hreads] at hlegal
  rw [ConditionalPublication.resolveAddressed?_addressed]
  exact site.specification.legal_choice_resolves
    (runtimeSite site fresh state sourceSlot deadline) rfl now service accepted done
    canOpen env hstored hready hcanOpen serial chosen.1 hlegal

end Vegas.ConditionalPublicationSite
