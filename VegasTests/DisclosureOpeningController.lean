/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosureInitialChoiceController
import VegasTests.DisclosurePublicChoiceController

/-! # Source-generated controller for optional disclosure

The owner's opening controller reconstructs its complete source view from its
own recorded initial choice and public application fields. A public initial
default overrides the private record. Source environments occur only in the
correspondence proofs.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Vegas EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {window : Nat}

abbrev OpeningDecision :=
  (visible : Env simpleExpr.Val (eraseVCtx
    (viewVCtx Publication.accountingSite.data.owner
      Publication.accountingSite.data.context))) →
    FinDist {value : simpleExpr.Val Publication.accountingSite.data.copyTy //
      evalGuard Publication.accountingSite.data.guard value visible = true}

/-- The application constructor is a canonical transport for addressed
conditional-publication requests. Other application payloads are outside its
decoding domain. -/
def openingTransport :
    ChoiceEncoding (Nat × ConditionalPublication.Payload TestPlayer Bool) Payload where
  encode request := .publish request.1 request.2
  decode
    | .publish endpoint request => some (endpoint, request)
    | _ => none
  decode_encode _ := rfl
  decode_sound payload request hdecode := by
    rcases request with ⟨requestedEndpoint, requestedPayload⟩
    cases payload <;> simp_all

/-- Canonical opening payloads are independent of the timeout attached to the
runtime publication site. -/
def openingPayloadEncoding : ChoiceEncoding (Option Bool) Payload :=
  Publication.accountingSite.choiceEncoding source.fresh compilerInitial
    0 0 openingTransport

/-- Canonical opening choices as actual player submission commands. -/
def openingCommandEncoding :
    ChoiceEncoding (Option Bool) (application window).PlayerCommand :=
  openingPayloadEncoding.submission (application window)

@[simp] theorem openingTransport_decode_publish (endpoint : Nat)
    (request : ConditionalPublication.Payload TestPlayer Bool) :
    openingTransport.decode (.publish endpoint request) = some (endpoint, request) := rfl

@[simp] theorem openingPayloadEncoding_encode_none :
    openingPayloadEncoding.encode none = .publish 5 .decline := rfl

@[simp] theorem openingPayloadEncoding_encode_some (value : Bool) :
    openingPayloadEncoding.encode (some value) =
      .publish 5 (.opening (0, 0) value) := rfl

@[simp] theorem openingPayloadEncoding_decode_expire :
    openingPayloadEncoding.decode (.publish 5 .expire) = none := rfl

theorem opening_specification :
    Publication.accountingSite.data.specification = DisclosureAccounting.optionalSpec := rfl

/-- The source value supplied to the opening decision. Commitments require the
actual slot-zero private command in the owner's history; a public default is
already a public source value. -/
def openingBound? (history : List (application window).PlayerEntry)
    (view : (application window).View) : Option Bool :=
  match view.application.accepted with
  | some (.commitment handle) =>
      if handle = (0, 0) then initialCachedValue window history else none
  | some (.publicDefault value) => some value
  | none => none

theorem openingBound?_commitment (history : List (application window).PlayerEntry)
    (view : (application window).View) (value : Bool)
    (haccepted : view.application.accepted = some (.commitment (0, 0)))
    (hcache : initialCachedValue window history = some value) :
    openingBound? history view = some value := by
  simp [openingBound?, haccepted, hcache]

theorem openingBound?_publicDefault (history : List (application window).PlayerEntry)
    (view : (application window).View) (value : Bool)
    (haccepted : view.application.accepted = some (.publicDefault value)) :
    openingBound? history view = some value := by
  simp [openingBound?, haccepted]

/-- Materialize all four fields visible at the source opening decision. -/
def openingReadStore (history : List (application window).PlayerEntry)
    (view : (application window).View) : Store simpleExpr
  | 0 => (openingBound? history view).map fun value => ⟨.bool, value⟩
  | 1 | 2 => if view.application.markerDone then some ⟨.bool, false⟩ else none
  | 3 => view.application.signal.map fun value => ⟨.bool, value⟩
  | _ => none

theorem opening_choiceReads :
    (eventGuardOf
      (decisionSiteState Publication.accountingSite.data.decision source.fresh
        compilerInitial)
      (0 : TestPlayer) Publication.accountingSite.data.guard).choiceReads =
      {{ field := 3, ty := .bool }, { field := 2, ty := .bool },
        { field := 1, ty := .bool }, { field := 0, ty := .bool }} := rfl

def openingReadout? (history : List (application window).PlayerEntry)
    (view : (application window).View) :
    Option (Publication.accountingSite.ChoiceReads source.fresh compilerInitial) :=
  ReadEnv.ofStoreExec? (openingReadStore history view)
    (eventGuardOf
      (decisionSiteState Publication.accountingSite.data.decision source.fresh
        compilerInitial)
      (0 : TestPlayer) Publication.accountingSite.data.guard).choiceReads

/-- The native read store represents the complete source-visible environment,
including the private initial source recovered from command history. -/
theorem openingReadStore_view_agrees
    (history : List (application window).PlayerEntry)
    (view : (application window).View) (secret signal : Bool)
    (hbound : openingBound? history view = some secret)
    (hmarker : view.application.markerDone = true)
    (hsignal : view.application.signal = some signal) :
    (decisionSiteState Publication.accountingSite.data.decision source.fresh
      compilerInitial).ViewAgrees 0 (openingReadStore history view)
        (openingEnv secret signal) := by
  intro name ty binding
  cases binding with
  | here =>
      change Store.getAs (openingReadStore history view) 3 .bool = some signal
      simp [Store.getAs, openingReadStore, hsignal, TypedValue.as?]
  | there binding =>
      cases binding with
      | here =>
          change Store.getAs (openingReadStore history view) 2 .bool = some false
          simp [Store.getAs, openingReadStore, hmarker, TypedValue.as?]
      | there binding =>
          cases binding with
          | here =>
              change Store.getAs (openingReadStore history view) 1 .bool = some false
              simp [Store.getAs, openingReadStore, hmarker, TypedValue.as?]
          | there binding =>
              cases binding with
              | here =>
                  change Store.getAs (openingReadStore history view) 0 .bool = some secret
                  simp [Store.getAs, openingReadStore, hbound, TypedValue.as?]
              | there binding => cases binding

theorem openingReadout_available
    (history : List (application window).PlayerEntry)
    (view : (application window).View) (secret signal : Bool)
    (hbound : openingBound? history view = some secret)
    (hmarker : view.application.markerDone = true)
    (hsignal : view.application.signal = some signal) :
    ∃ reads, openingReadout? history view = some reads := by
  have available : ∀ ref, ref ∈
      (eventGuardOf
        (decisionSiteState Publication.accountingSite.data.decision source.fresh
          compilerInitial)
        (0 : TestPlayer) Publication.accountingSite.data.guard).choiceReads →
      (Store.getAs (openingReadStore history view) ref.field ref.ty).isSome := by
    intro ref href
    rw [opening_choiceReads] at href
    simp only [Finset.mem_insert, Finset.mem_singleton] at href
    rcases href with rfl | rfl | rfl | rfl <;>
      simp [Store.getAs, openingReadStore, hbound, hmarker, hsignal, TypedValue.as?]
  let reads := ReadEnv.ofStoreChecked (openingReadStore history view)
    (eventGuardOf
      (decisionSiteState Publication.accountingSite.data.decision source.fresh
        compilerInitial)
      (0 : TestPlayer) Publication.accountingSite.data.guard).choiceReads available
  refine ⟨reads, ?_⟩
  unfold openingReadout? ReadEnv.ofStoreExec?
  rw [dif_pos available]

theorem openingReadout_none_of_bound_none
    (history : List (application window).PlayerEntry)
    (view : (application window).View)
    (hbound : openingBound? history view = none) :
    openingReadout? history view = none := by
  unfold openingReadout? ReadEnv.ofStoreExec?
  split
  · rename_i available
    have hsource := available ({ field := 0, ty := .bool } : FieldRef simpleExpr) (by
      rw [opening_choiceReads]
      simp)
    simp [Store.getAs, openingReadStore, hbound] at hsource
  · rfl

/-- Fixed-deadline metadata used by the observation-local native policy. -/
def openingController (deadline : Nat) (policy : OpeningDecision)
    (retry : List (application window).PlayerEntry → (application window).View → Bool) :=
  Publication.accountingSite.controller source.fresh compilerInitial 0 deadline
    (application window) openingTransport
    (fun view => view.application.accepted.map DisclosureBinding.reference)
    (fun view => view.application.done) openingReadout? policy retry

@[simp] theorem openingController_codec (deadline : Nat) (policy : OpeningDecision)
    (retry : List (application window).PlayerEntry → (application window).View → Bool) :
    (openingController (window := window) deadline policy retry).codec =
      openingCommandEncoding := rfl

theorem openingController_ready_iff (deadline : Nat) (policy : OpeningDecision)
    (retry : List (application window).PlayerEntry → (application window).View → Bool)
    (view : (application window).View) :
    (openingController (window := window) deadline policy retry).ready view = true ↔
      (∃ binding, view.application.accepted = some binding ∧
        binding.reference = (0, 0)) ∧
      view.application.markerDone = true ∧
      view.application.signal.isSome = true ∧
      view.application.publication = none := by
  change (Publication.publicationSite deadline).ready
    (view.application.accepted.map DisclosureBinding.reference)
      view.application.done = true ↔ _
  simp [ConditionalPublication.ready, PublicState.done]
  aesop

/-- Boolean normal form of the generated opening endpoint's readiness. -/
theorem openingController_ready (deadline : Nat) (policy : OpeningDecision)
    (retry : List (application window).PlayerEntry → (application window).View → Bool)
    (view : (application window).View) :
    (openingController (window := window) deadline policy retry).ready view =
      (decide (view.application.accepted.map DisclosureBinding.reference = some (0, 0)) &&
        view.application.markerDone && view.application.signal.isSome &&
          view.application.publication.isNone) := by
  rw [Bool.eq_iff_iff, openingController_ready_iff]
  simp [Bool.and_eq_true]
  aesop

/-- Instantiate the generated endpoint at the public deadline armed by the
observed signal. -/
def openingPolicy (policy : OpeningDecision)
    (retry : List (application window).PlayerEntry → (application window).View → Bool) :
    (application window).PlayerPolicy := fun history view =>
  (openingController (view.application.signalAt + window) policy retry).policy
    (application window) history view

/-- The first uncached publication has exactly the source behavioral law. -/
theorem openingPolicy_first_submission (policy : OpeningDecision)
    (retry : List (application window).PlayerEntry → (application window).View → Bool)
    (history : List (application window).PlayerEntry) (view : (application window).View)
    (binding : DisclosureBinding) (secret signal : Bool)
    (hcache : openingCommandEncoding.cachedValue (application window) history = none)
    (haccepted : view.application.accepted = some binding)
    (hreference : binding.reference = (0, 0))
    (hbound : openingBound? history view = some secret)
    (hmarker : view.application.markerDone = true)
    (hsignal : view.application.signal = some signal)
    (hpublication : view.application.publication = none) :
    openingPolicy policy retry history view =
      (policy (((openingEnv secret signal).toView 0).eraseEnv)).map fun chosen =>
        .submit (.publish 5 ((Publication.publicationSite
          (view.application.signalAt + window)).requestPayload chosen.1)) := by
  obtain ⟨reads, hreadout⟩ := openingReadout_available history view secret signal
    hbound hmarker hsignal
  have hlaw := Publication.accountingSite.controller_first_submission_source_law
    source.fresh compilerInitial 0 (view.application.signalAt + window)
    (application window) openingTransport
    (fun observed => observed.application.accepted.map DisclosureBinding.reference)
    (fun observed => observed.application.done) openingReadout? policy retry history view
    (openingReadStore history view) (openingEnv secret signal) reads
  apply hlaw
  · change view.application.done 5 = false
    simp [PublicState.done, hpublication]
  · change (openingController (view.application.signalAt + window) policy retry).codec.cachedValue
      (application window) history = none
    rw [openingController_codec]
    exact hcache
  · change (openingController (view.application.signalAt + window) policy retry).ready
      view = true
    apply (openingController_ready_iff _ _ _ _).2
    exact ⟨⟨binding, haccepted, hreference⟩, hmarker, by simp [hsignal], hpublication⟩
  · exact hreadout
  · exact openingReadStore_view_agrees history view secret signal hbound hmarker hsignal
  · exact ReadEnv.ofStore?_eq_some_of_ofStoreExec?_eq_some hreadout

/-- Deterministic optional disclosure as a source decision kernel. -/
def pureOpeningDecision (complete : Bool → Bool → Bool) : OpeningDecision :=
  fun (visible : Env simpleExpr.Val (eraseVCtx
      (viewVCtx Publication.accountingSite.data.owner
        Publication.accountingSite.data.context))) =>
    let bound : Bool := visible.get (.there (.there (.there .here)))
    let signal : Bool := visible.get .here
    let opening := if complete bound signal then some bound else none
    FinDist.pure ⟨opening, by
      change (if opening.isNone then true else decide (opening = some bound)) = true
      cases h : complete bound signal <;> simp [opening, h]⟩

theorem opening_source_view (secret signal : Bool) :
    ((openingEnv secret signal).toView (0 : TestPlayer)).eraseEnv =
      Env.cons (x := 3) signal (Env.cons (x := 2) false
        (Env.cons (x := 1) false (Env.cons (x := 0) secret (Env.empty Val)))) := by
  funext name ty binding
  cases binding with
  | here => rfl
  | there binding =>
      cases binding with
      | here => rfl
      | there binding =>
          cases binding with
          | here => rfl
          | there binding =>
              cases binding with
              | here => rfl
              | there binding => cases binding

/-- Concrete command selected once every declared source read is available.
Readiness is checked separately by the generated controller. -/
def pureOpeningCommand (complete : Bool → Bool → Bool)
    (history : List (application window).PlayerEntry)
    (view : (application window).View) : (application window).PlayerCommand :=
  match openingBound? history view, view.application.signal with
  | some bound, some signal =>
      .submit (.publish 5 ((Publication.publicationSite
        (view.application.signalAt + window)).requestPayload
          (if complete bound signal then some bound else none)))
  | _, _ => .wait

/-- The deterministic kernel is the decision at the actual optional-opening
occurrence of the written source profile. -/
theorem pureProfile_opening_decision
    (secret : Bool) (complete : Bool → Bool → Bool)
    (response : Bool → Option Bool → Bool) :
    SourcePolicies.pureProfile [(0, payoff)] secret complete response 0
      Publication.accountingSite.data.decision = pureOpeningDecision complete := rfl

theorem openingPolicy_first_pure (complete : Bool → Bool → Bool)
    (history : List (application window).PlayerEntry) (view : (application window).View)
    (binding : DisclosureBinding) (secret signal : Bool)
    (hcache : openingCommandEncoding.cachedValue (application window) history = none)
    (haccepted : view.application.accepted = some binding)
    (hreference : binding.reference = (0, 0))
    (hbound : openingBound? history view = some secret)
    (hmarker : view.application.markerDone = true)
    (hsignal : view.application.signal = some signal)
    (hpublication : view.application.publication = none) :
    openingPolicy (pureOpeningDecision complete) (fun _ _ => false) history view =
      FinDist.pure (.submit (.publish 5
        ((Publication.publicationSite (view.application.signalAt + window)).requestPayload
          (if complete secret signal then some secret else none)))) := by
  rw [openingPolicy_first_submission (pureOpeningDecision complete) (fun _ _ => false)
    history view binding secret signal hcache haccepted hreference hbound hmarker hsignal
    hpublication]
  simp [pureOpeningDecision, opening_source_view]

/-- Exact deterministic normal form on every history and view. A missing
private preparation therefore remains a wait, while a public default supplies
the bound value without any private-history premise. -/
theorem openingPolicy_pure_eq (complete : Bool → Bool → Bool)
    (history : List (application window).PlayerEntry) (view : (application window).View) :
    let controller := openingController (window := window)
      (view.application.signalAt + window) (pureOpeningDecision complete) (fun _ _ => false)
    openingPolicy (pureOpeningDecision complete) (fun _ _ => false) history view =
      FinDist.pure (if controller.ready view &&
          (openingCommandEncoding.cachedValue (application window) history).isNone then
        pureOpeningCommand complete history view else .wait) := by
  dsimp only
  let controller := openingController (window := window)
    (view.application.signalAt + window) (pureOpeningDecision complete) (fun _ _ => false)
  change controller.policy (application window) history view =
    FinDist.pure (if controller.ready view &&
        (openingCommandEncoding.cachedValue (application window) history).isNone then
      pureOpeningCommand complete history view else .wait)
  cases hresolved : controller.resolved view with
  | true =>
      rw [controller.policy_of_resolved (application window) history view hresolved]
      have hnotReady : controller.ready view = false := by
        cases hready : controller.ready view with
        | false => rfl
        | true =>
            have hflags := (openingController_ready_iff
              (view.application.signalAt + window) (pureOpeningDecision complete)
              (fun _ _ => false) view).mp hready
            change view.application.done 5 = true at hresolved
            simp [PublicState.done, hflags.2.2.2] at hresolved
      rw [hnotReady]
      rfl
  | false =>
      cases hcache : openingCommandEncoding.cachedValue (application window) history with
      | some value =>
          have hcontrollerCache : controller.codec.cachedValue (application window) history =
              some value := by
            simpa [controller] using hcache
          rw [controller.policy_of_cached (application window) history view value
            hresolved hcontrollerCache]
          have hretry : controller.retry history view = false := rfl
          rw [hretry]
          simp
      | none =>
          cases hready : controller.ready view with
          | false =>
              have hcontrollerCache : controller.codec.cachedValue
                  (application window) history = none := by
                simpa [controller] using hcache
              rw [controller.policy_of_uncached_not_ready (application window)
                history view hresolved hcontrollerCache hready]
              simp
          | true =>
              have hflags := (openingController_ready_iff
                (view.application.signalAt + window) (pureOpeningDecision complete)
                (fun _ _ => false) view).mp hready
              obtain ⟨binding, haccepted, hreference⟩ := hflags.1
              obtain ⟨signal, hsignal⟩ := Option.isSome_iff_exists.mp hflags.2.2.1
              cases hbound : openingBound? history view with
              | none =>
                  have hcontrollerCache : controller.codec.cachedValue
                      (application window) history = none := by
                    simpa [controller] using hcache
                  rw [controller.policy_of_uncached_no_readout (application window)
                    history view hresolved hcontrollerCache hready
                    (openingReadout_none_of_bound_none history view hbound)]
                  have hcommand : pureOpeningCommand complete history view = .wait := by
                    simp [pureOpeningCommand, hbound]
                  rw [hcommand]
                  simp
              | some bound =>
                  have hpure := openingPolicy_first_pure complete history view binding bound
                    signal hcache haccepted hreference hbound hflags.2.1 hsignal hflags.2.2.2
                  change controller.policy (application window) history view = _ at hpure
                  rw [hpure]
                  have hcommand : pureOpeningCommand complete history view =
                      .submit (.publish 5 ((Publication.publicationSite
                        (view.application.signalAt + window)).requestPayload
                          (if complete bound signal then some bound else none))) := by
                    simp [pureOpeningCommand, hbound, hsignal]
                  rw [hcommand]
                  simp

/-- A recorded voluntary opening choice is never sampled again when retries
are disabled, including before its inclusion. -/
theorem openingPolicy_recorded (policy : OpeningDecision)
    (history : List (application window).PlayerEntry) (view : (application window).View)
    (value : Option Bool)
    (hcache : openingCommandEncoding.cachedValue (application window) history = some value) :
    openingPolicy policy (fun _ _ => false) history view = FinDist.pure .wait := by
  unfold openingPolicy
  let controller := openingController (window := window)
    (view.application.signalAt + window) policy (fun _ _ => false)
  have hcontrollerCache : controller.codec.cachedValue (application window) history =
      some value := by
    simpa [controller] using hcache
  cases hresolved : controller.resolved view with
  | false =>
      rw [controller.policy_of_cached (application window) history view value
        hresolved hcontrollerCache]
      have hretry : controller.retry history view = false := rfl
      rw [hretry]
      simp
  | true =>
      exact controller.policy_of_resolved (application window) history view hresolved

end VegasTests.OptionalDisclosure.DisclosureState

/--
info: 'VegasTests.OptionalDisclosure.DisclosureState.openingPolicy_first_submission'
depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  VegasTests.OptionalDisclosure.DisclosureState.openingPolicy_first_submission
