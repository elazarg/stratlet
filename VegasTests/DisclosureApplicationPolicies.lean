/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosurePublicChoiceController

/-! # Information-local controllers for the disclosure application -/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Interaction GameTheory.Math.Probability

variable {window : Nat}

private theorem pure_injective {α : Type} {left right : α}
    (h : FinDist.pure left = FinDist.pure right) : left = right := by
  have hmem : left ∈ (FinDist.pure right).support := by
    rw [← h]
    exact FinDist.mem_support_pure.mpr rfl
  exact FinDist.mem_support_pure.mp hmem

def registered (history : List (application window).PlayerEntry) : Bool :=
  history.any fun entry =>
    match entry.command with
    | .privateCommand (0, _) => true
    | _ => false

def bindingSubmitted (history : List (application window).PlayerEntry) : Bool :=
  history.any fun entry =>
    match entry.command with
    | .submit (.bind (0, 0)) => true
    | _ => false

def publicationSubmitted (history : List (application window).PlayerEntry) : Bool :=
  history.any fun entry =>
    match entry.command with
    | .submit (.publish _) => true
    | _ => false

def responseSubmitted (history : List (application window).PlayerEntry) : Bool :=
  history.any fun entry =>
    match entry.command with
    | .submit (.respond _) => true
    | _ => false

theorem response_cache_none_iff (history : List (application window).PlayerEntry) :
    responseCommandEncoding.cachedValue (application window) history = none ↔
      responseSubmitted history = false := by
  induction history with
  | nil => simp [responseSubmitted]
  | cons entry history ih =>
      rcases entry with ⟨view, command⟩
      cases command with
      | submit payload => cases payload <;>
          simp_all [MessageApplication.ChoiceEncoding.cachedValue,
            responseCommandEncoding, responseCodec, responseSubmitted]
      | privateCommand command | replay id | wait =>
          simpa [MessageApplication.ChoiceEncoding.cachedValue,
            responseCommandEncoding, responseSubmitted] using ih

def initialExpirySubmitted (history : List (application window).PlayerEntry) : Bool :=
  history.any fun entry =>
    match entry.command with
    | .submit .expireInitial => true
    | _ => false

def responseExpirySubmitted (history : List (application window).PlayerEntry) : Bool :=
  history.any fun entry =>
    match entry.command with
    | .submit .expireResponse => true
    | _ => false

/-- Pure source rules, with continuation evaluated at the accepted source
value. A public default takes precedence over an unsubmitted private intention.
The owner also drives expiration of an absent responder. -/
def ownerPolicy (secret : Bool) (complete : Bool → Bool → Bool) :
    (application window).PlayerPolicy := fun history view => FinDist.pure <|
  if view.application.response.isSome then .wait else
  match view.application.accepted with
  | none =>
      if !registered history then .privateCommand (0, secret)
      else if bindingSubmitted history then .wait else .submit (.bind (0, 0))
  | some binding =>
      match view.application.signal with
      | none => .wait
      | some signal =>
          match view.application.publication with
          | none =>
              if publicationSubmitted history then .wait else
              let bound := match binding with
                | .commitment _ => secret
                | .publicDefault value => value
              if complete bound signal then .submit (.publish (.opening (0, 0) bound))
              else .submit (.publish .decline)
          | some _ =>
              if view.application.responseAt + window < view.application.clock &&
                  !responseExpirySubmitted history then .submit .expireResponse
              else .wait

/-- The responder drives the owner's initial and disclosure timeouts, and
responds only to the actual resolved publication. Every call uses its own
principal capability; no owner-authored timeout message is synthesized. -/
def responderPolicy (response : ResponseDecision) :
    (application window).PlayerPolicy := fun history view =>
  if view.application.response.isSome then FinDist.pure .wait else
  match view.application.accepted with
  | none =>
      FinDist.pure (if window < view.application.clock && !initialExpirySubmitted history then
        .submit .expireInitial else .wait)
  | some _ =>
      match view.application.signal, view.application.publication with
      | some _, none =>
          FinDist.pure (if view.application.signalAt + window < view.application.clock &&
              !publicationSubmitted history then .submit (.publish .expire) else .wait)
      | some _, some _ =>
          (responseController response (fun _ _ => false)).policy
            (application window) history view
      | _, _ => FinDist.pure .wait

def honestPlayers (secret : Bool) (complete : Bool → Bool → Bool)
    (response : Bool → Option Bool → Bool) : TestPlayer → (application window).PlayerPolicy
  | 0 => ownerPolicy secret complete
  | 1 => responderPolicy (pureResponseDecision response)

/-- A specified inclusion script for the honest-law benchmark. It invokes
the same timeout-capable controllers, but performs no clock advances. -/
def honestEnvironment : (application window).EnvironmentPolicy := fun history _ =>
  FinDist.pure <| match history.length with
  | 0 => .include (0, 0)
  | 1 => .application .marker
  | 2 => .application .sample
  | 3 => .include (0, 1)
  | 4 => .include (1, 0)
  | _ => .wait

def honestSchedule : List (@MessageApplication.Invocation TestPlayer) :=
  [.player 0, .player 0, .environment, .environment, .environment,
    .player 0, .environment, .player 1, .environment]

theorem owner_waits_before_signal (secret : Bool) (complete : Bool → Bool → Bool)
    (history : List (application window).PlayerEntry) (view : (application window).View)
    (binding : DisclosureBinding) (haccepted : view.application.accepted = some binding)
    (hsignal : view.application.signal = none) :
    ownerPolicy secret complete history view = FinDist.pure .wait := by
  simp [ownerPolicy, haccepted, hsignal]

theorem owner_publication_after_signal (secret signal : Bool)
    (complete : Bool → Bool → Bool) (history : List (application window).PlayerEntry)
    (view : (application window).View)
    (haccepted : view.application.accepted = some (.commitment (0, 0)))
    (hsignal : view.application.signal = some signal)
    (hunresolved : view.application.publication = none)
    (hresponse : view.application.response = none)
    (hnotSubmitted : publicationSubmitted history = false) :
    ownerPolicy secret complete history view = FinDist.pure
      (if complete secret signal then .submit (.publish (.opening (0, 0) secret))
       else .submit (.publish .decline)) := by
  simp [ownerPolicy, haccepted, hsignal, hunresolved, hresponse, hnotSubmitted]

/-- Recovery uses the accepted public value, even with different private intent
or an empty local history. It does not prepare or publish another commitment. -/
theorem owner_recovers_public_default (secret value signal : Bool)
    (complete : Bool → Bool → Bool) (history : List (application window).PlayerEntry)
    (view : (application window).View)
    (haccepted : view.application.accepted = some (.publicDefault value))
    (hsignal : view.application.signal = some signal)
    (hunresolved : view.application.publication = none)
    (hresponse : view.application.response = none)
    (hnotSubmitted : publicationSubmitted history = false) :
    ownerPolicy secret complete history view = FinDist.pure
      (if complete value signal then .submit (.publish (.opening (0, 0) value))
       else .submit (.publish .decline)) := by
  simp [ownerPolicy, haccepted, hsignal, hunresolved, hresponse, hnotSubmitted]

theorem owner_expires_response (secret signal : Bool) (complete : Bool → Bool → Bool)
    (history : List (application window).PlayerEntry) (view : (application window).View)
    (binding : DisclosureBinding) (publication : Option Bool)
    (haccepted : view.application.accepted = some binding)
    (hsignal : view.application.signal = some signal)
    (hpublication : view.application.publication = some publication)
    (hresponse : view.application.response = none)
    (hexpired : view.application.responseAt + window < view.application.clock)
    (hnotSubmitted : responseExpirySubmitted history = false) :
    ownerPolicy secret complete history view = FinDist.pure (.submit .expireResponse) := by
  simp [ownerPolicy, haccepted, hsignal, hpublication, hresponse, hexpired, hnotSubmitted]

theorem responder_expires_initial (response : Bool → Option Bool → Bool)
    (history : List (application window).PlayerEntry) (view : (application window).View)
    (haccepted : view.application.accepted = none)
    (hresponse : view.application.response = none)
    (hexpired : window < view.application.clock)
    (hnotSubmitted : initialExpirySubmitted history = false) :
    responderPolicy (pureResponseDecision response) history view =
      FinDist.pure (.submit .expireInitial) := by
  simp [responderPolicy, haccepted, hresponse, hexpired, hnotSubmitted]

theorem responder_expires_publication (response : Bool → Option Bool → Bool)
    (history : List (application window).PlayerEntry) (view : (application window).View)
    (binding : DisclosureBinding) (signal : Bool)
    (haccepted : view.application.accepted = some binding)
    (hsignal : view.application.signal = some signal)
    (hpublication : view.application.publication = none)
    (hresponse : view.application.response = none)
    (hexpired : view.application.signalAt + window < view.application.clock)
    (hnotSubmitted : publicationSubmitted history = false) :
    responderPolicy (pureResponseDecision response) history view =
      FinDist.pure (.submit (.publish .expire)) := by
  simp [responderPolicy, haccepted, hsignal, hpublication, hresponse, hexpired, hnotSubmitted]

theorem responder_submits_after_release (response : Bool → Option Bool → Bool)
    (signal : Bool) (publication : Option Bool)
    (history : List (application window).PlayerEntry) (view : (application window).View)
    (binding : DisclosureBinding) (haccepted : view.application.accepted = some binding)
    (hmarker : view.application.markerDone = true)
    (hsignal : view.application.signal = some signal)
    (hpublication : view.application.publication = some publication)
    (hresponse : view.application.response = none)
    (hnotSubmitted : responseSubmitted history = false) :
    responderPolicy (pureResponseDecision response) history view =
      FinDist.pure (.submit (.respond (response signal publication))) := by
  simp only [responderPolicy, hresponse, Option.isSome_none, Bool.false_eq_true,
    if_false, haccepted, hsignal, hpublication]
  exact responseController_first_pure response history view binding signal publication
    ((response_cache_none_iff history).2 hnotSubmitted) haccepted hmarker hsignal
    hpublication hresponse

/-- Publication is emitted only after the binding and public signal. -/
theorem owner_publish_requires_release (secret : Bool) (complete : Bool → Bool → Bool)
    (history : List (application window).PlayerEntry) (view : (application window).View)
    (request : ConditionalPublication.Payload TestPlayer Bool)
    (hemit : ownerPolicy secret complete history view =
      FinDist.pure (.submit (.publish request))) :
    view.application.accepted.isSome = true ∧
      view.application.signal.isSome = true ∧ view.application.publication = none := by
  unfold ownerPolicy at hemit
  have hcommand := pure_injective hemit
  split at hcommand <;> try contradiction
  split at hcommand
  · split at hcommand <;> try contradiction
    split at hcommand <;> cases hcommand
  · split at hcommand <;> try contradiction
    split at hcommand
    · simp_all
    · split at hcommand <;> cases hcommand

/-- Response packets use only the resolved public inputs, including on views
outside the reachable honest path. Timeout calls have different payloads. -/
theorem responder_submit_requires_release (response : Bool → Option Bool → Bool)
    (history : List (application window).PlayerEntry) (view : (application window).View)
    (value : Bool) (hemit : responderPolicy (pureResponseDecision response) history view =
      FinDist.pure (.submit (.respond value))) :
    view.application.signal.isSome = true ∧
      view.application.publication.isSome = true := by
  unfold responderPolicy at hemit
  split at hemit
  · have hcommand := pure_injective hemit
    cases hcommand
  · split at hemit
    · have hcommand := pure_injective hemit
      split at hcommand <;> cases hcommand
    · split at hemit
      · have hcommand := pure_injective hemit
        split at hcommand <;> cases hcommand
      · simp_all
      · have hcommand := pure_injective hemit
        cases hcommand

end VegasTests.OptionalDisclosure.DisclosureState
