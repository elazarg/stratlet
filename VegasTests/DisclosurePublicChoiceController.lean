/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.PublicChoiceController
import VegasTests.DisclosureApplication
import VegasTests.DisclosureSourcePolicies

/-! # Source-generated controller for the public response

The controller reads public application fields and its own submitted commands.
Its full decision readout includes the source signal and optional publication;
the public response guard itself needs no stored values. Source environments
appear in correspondence proofs, not in the native readout.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Vegas EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {window : Nat}

/-- Public completion readout for the generated endpoint. -/
def PublicState.done (view : PublicState) : Nat → Bool
  | 0 => view.accepted.isSome
  | 1 | 2 => view.markerDone
  | 3 => view.signal.isSome
  | 4 | 5 => view.publication.isSome
  | 6 | 7 => view.response.isSome
  | _ => false

theorem observe_done (state : DisclosureState) : state.observe.done = state.done := rfl

/-- The endpoint's wire constructor separates responses from all other calls. -/
def responseCodec : SubmissionCodec Bool Payload where
  encode := .respond
  decode
    | .respond value => some value
    | _ => none
  decode_encode _ := rfl

theorem responseCodec_decode_iff (payload : Payload) (value : Bool) :
    responseCodec.decode payload = some value ↔ payload = .respond value := by
  cases payload <;> simp [responseCodec]

/-- Only the responder's public fields are materialized. The marker is the
forced source constant; neither sealed field is queried. -/
def responseReadStore (view : PublicState) : Store simpleExpr
  | 2 => if view.markerDone then some ⟨.bool, false⟩ else none
  | 3 => view.signal.map (fun value => ⟨.bool, value⟩)
  | 5 => view.publication.map (fun value => ⟨.option .bool, value⟩)
  | _ => none

theorem response_choiceReads : responseGuard.choiceReads =
    {{ field := 5, ty := .option .bool }, { field := 3, ty := .bool },
      { field := 2, ty := .bool }} := rfl

private theorem responseGraphPrerequisites_eq :
    graph.publicationPrerequisites (node 6) (node 7) = [2, 3, 5, 0, 1, 4] := by
  simpa only [responsePrerequisites, responseEndpoint_requires] using
    responsePrerequisites_eq

def responseReadout? (_history : List (application window).PlayerEntry)
    (view : (application window).View) :
    Option (responseOccurrence.ChoiceReads source.fresh responseCompilerInitial) :=
  ReadEnv.ofStoreExec? (responseReadStore view.application) responseGuard.choiceReads

abbrev ResponseDecision :=
  (visible : Env Val (eraseVCtx (viewVCtx (1 : TestPlayer) ResponseContext))) →
    FinDist {value : Bool // evalGuard responseOccurrence.guard value visible = true}

/-- The native response component is an instance of the source compiler. -/
def responseController (policy : ResponseDecision)
    (retry : List (application window).PlayerEntry → (application window).View → Bool) :=
  responseOccurrence.controller source.fresh responseCompilerInitial (application window)
    responseCodec (fun view => view.application.done) responseReadout? policy retry

def pureResponseDecision (response : Bool → Option Bool → Bool) : ResponseDecision :=
  fun visible => FinDist.pure
    ⟨response (visible.get (.there .here)) (visible.get .here), rfl⟩

/-- The supplied deterministic kernel is the decision at the actual occurrence
in the written source profile. -/
theorem pureProfile_response_decision (secret : Bool)
    (complete : Bool → Bool → Bool) (response : Bool → Option Bool → Bool) :
    SourcePolicies.pureProfile [(0, payoff)] secret complete response 1
        responseOccurrence.decision = pureResponseDecision response := rfl

theorem responseReadStore_view_agrees (view : PublicState)
    (secret signal : Bool) (publication : Option Bool)
    (hmarker : view.markerDone = true) (hsignal : view.signal = some signal)
    (hpublication : view.publication = some publication) :
    (responseOccurrence.siteState source.fresh responseCompilerInitial).ViewAgrees
      1 (responseReadStore view) (responseEnv secret signal publication) := by
  intro name ty binding
  cases binding with
  | here =>
      change Store.getAs (responseReadStore view) 5 (.option .bool) = some publication
      simp [Store.getAs, responseReadStore, hpublication, TypedValue.as?]
  | there binding =>
      cases binding with
      | here =>
          change Store.getAs (responseReadStore view) 3 .bool = some signal
          simp [Store.getAs, responseReadStore, hsignal, TypedValue.as?]
      | there binding =>
          cases binding with
          | here =>
              change Store.getAs (responseReadStore view) 2 .bool = some false
              simp [Store.getAs, responseReadStore, hmarker, TypedValue.as?]
          | there binding => cases binding

theorem responseReadout_available (history : List (application window).PlayerEntry)
    (view : (application window).View) (signal : Bool) (publication : Option Bool)
    (hmarker : view.application.markerDone = true)
    (hsignal : view.application.signal = some signal)
    (hpublication : view.application.publication = some publication) :
    ∃ reads, responseReadout? history view = some reads := by
  have available : ∀ ref, ref ∈ responseGuard.choiceReads →
      (Store.getAs (responseReadStore view.application) ref.field ref.ty).isSome := by
    intro ref href
    rw [response_choiceReads] at href
    simp only [Finset.mem_insert, Finset.mem_singleton] at href
    rcases href with rfl | rfl | rfl <;>
      simp [Store.getAs, responseReadStore, hmarker, hsignal, hpublication, TypedValue.as?]
  let reads := ReadEnv.ofStoreChecked
    (responseReadStore view.application) responseGuard.choiceReads available
  refine ⟨reads, ?_⟩
  unfold responseReadout? ReadEnv.ofStoreExec?
  rw [dif_pos available]

/-- First native submission has the actual source decision law. The arbitrary
sealed source value is absent from the runtime readout. -/
theorem responseController_first_submission (policy : ResponseDecision)
    (retry : List (application window).PlayerEntry → (application window).View → Bool)
    (history : List (application window).PlayerEntry) (view : (application window).View)
    (binding : DisclosureBinding) (secret signal : Bool) (publication : Option Bool)
    (hcache : responseCodec.cachedValue (application window) history = none)
    (haccepted : view.application.accepted = some binding)
    (hmarker : view.application.markerDone = true)
    (hsignal : view.application.signal = some signal)
    (hpublication : view.application.publication = some publication)
    (hresponse : view.application.response = none) :
    (responseController policy retry).policy (application window) history view =
      (policy (((responseEnv secret signal publication).toView 1).eraseEnv)).map
        (fun chosen => .submit (.respond chosen.1)) := by
  obtain ⟨reads, hreadout⟩ :=
    responseReadout_available history view signal publication hmarker hsignal hpublication
  apply responseOccurrence.controller_first_submission_source_law source.fresh
    responseCompilerInitial (application window) responseCodec
    (fun observed => observed.application.done) responseReadout? policy retry history view
    (responseReadStore view.application) (responseEnv secret signal publication) reads
  · change view.application.done 7 = false
    simp [PublicState.done, hresponse]
  · exact hcache
  · change responseEndpoint.ready view.application.done = true
    simp [PublicChoice.ready, responseGraphPrerequisites_eq, PublicState.done,
      haccepted, hmarker, hsignal, hpublication, hresponse]
  · exact hreadout
  · exact responseReadStore_view_agrees view.application secret signal publication
      hmarker hsignal hpublication
  · exact ReadEnv.ofStore?_eq_some_of_ofStoreExec?_eq_some hreadout

/--
info: 'VegasTests.OptionalDisclosure.DisclosureState.responseController_first_submission'
depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  VegasTests.OptionalDisclosure.DisclosureState.responseController_first_submission

theorem responseController_first_pure (response : Bool → Option Bool → Bool)
    (history : List (application window).PlayerEntry) (view : (application window).View)
    (binding : DisclosureBinding) (signal : Bool) (publication : Option Bool)
    (hcache : responseCodec.cachedValue (application window) history = none)
    (haccepted : view.application.accepted = some binding)
    (hmarker : view.application.markerDone = true)
    (hsignal : view.application.signal = some signal)
    (hpublication : view.application.publication = some publication)
    (hresponse : view.application.response = none) :
    (responseController (pureResponseDecision response) (fun _ _ => false)).policy
        (application window) history view =
      FinDist.pure (.submit (.respond (response signal publication))) := by
  rw [responseController_first_submission (pureResponseDecision response) (fun _ _ => false)
    history view binding false signal publication hcache haccepted hmarker hsignal
    hpublication hresponse]
  simp [pureResponseDecision, FinDist.map_pure, response_view]

/-- A recorded response is never sampled again, including before inclusion. -/
theorem responseController_recorded (policy : ResponseDecision)
    (history : List (application window).PlayerEntry) (view : (application window).View)
    (value : Bool)
    (hcache : responseCodec.cachedValue (application window) history = some value) :
    (responseController policy (fun _ _ => false)).policy
      (application window) history view = FinDist.pure .wait := by
  unfold ChoiceController.policy
  split
  · rfl
  · simp [responseController, PublicChoiceSite.controller, hcache]

/-- Exact command normal form for a deterministic source decision. Readiness
includes availability of the full public decision view. -/
theorem responseController_pure_eq (response : Bool → Option Bool → Bool)
    (history : List (application window).PlayerEntry) (view : (application window).View) :
    (responseController (pureResponseDecision response) (fun _ _ => false)).policy
        (application window) history view =
      FinDist.pure (if responseEndpoint.ready view.application.done &&
          (responseCodec.cachedValue (application window) history).isNone then
        .submit (.respond (response (view.application.signal.getD false)
          (view.application.publication.getD none))) else .wait) := by
  cases hcache : responseCodec.cachedValue (application window) history with
  | some value =>
      rw [responseController_recorded _ history view value hcache]
      simp
  | none =>
      cases hready : responseEndpoint.ready view.application.done with
      | false =>
          let controller :=
            responseController (window := window) (pureResponseDecision response)
              (fun _ _ => false)
          cases hresolved : controller.resolved view with
          | false =>
              have hcontrollerReady : controller.ready view = false := by
                exact hready
              rw [controller.policy_of_uncached_not_ready (application window)
                history view hresolved hcache hcontrollerReady]
              simp
          | true =>
              rw [controller.policy_of_resolved (application window)
                history view hresolved]
              simp
      | true =>
          have flags := hready
          change (!view.application.response.isSome && !view.application.response.isSome &&
            [2, 3, 5, 0, 1, 4].all view.application.done) = true at flags
          simp only [Bool.and_self, Bool.and_eq_true, Bool.not_eq_true',
            List.all_eq_true] at flags
          have hresponse : view.application.response = none :=
            Option.isNone_iff_eq_none.mp (Option.isSome_eq_false_iff.mp flags.1)
          have hmarker : view.application.markerDone = true := flags.2 2 (by decide)
          obtain ⟨binding, haccepted⟩ :=
            Option.isSome_iff_exists.mp (flags.2 0 (by decide))
          obtain ⟨signal, hsignal⟩ :=
            Option.isSome_iff_exists.mp (flags.2 3 (by decide))
          obtain ⟨publication, hpublication⟩ :=
            Option.isSome_iff_exists.mp (flags.2 5 (by decide))
          rw [responseController_first_pure response history view binding signal publication
            hcache haccepted hmarker hsignal hpublication hresponse]
          simp [hsignal, hpublication]

end VegasTests.OptionalDisclosure.DisclosureState
