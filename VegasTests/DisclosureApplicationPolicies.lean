/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosureOpeningController

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

def bindingSubmitted (history : List (application window).PlayerEntry) : Bool :=
  history.any fun entry =>
    match entry.command with
    | .submit (.bind (0, 0)) => true
    | _ => false

def openingSubmitted (history : List (application window).PlayerEntry) : Bool :=
  (openingCommandEncoding.cachedValue (application window) history).isSome

def publicationExpirySubmitted (history : List (application window).PlayerEntry) : Bool :=
  history.any fun entry =>
    match entry.command with
    | .submit (.publish endpoint .expire) => endpoint == 5
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

/-- The owner composes source-generated initial and opening choices with an
opaque binding phase and permissionless response expiration. Its initial draw
is recovered from own command history, with accepted public defaults taking
precedence when reconstructing the later source view. -/
def ownerPolicy (initialDecision : InitialDecision) (openingDecision : OpeningDecision) :
    (application window).PlayerPolicy := fun history view =>
  if view.application.response.isSome then FinDist.pure .wait else
  match view.application.accepted with
  | none =>
      match initialCachedValue window history with
      | none => (initialChoiceController window initialDecision).policy
          (application window) history view
      | some _ => FinDist.pure
          (if bindingSubmitted history then .wait else .submit (.bind (0, 0)))
  | some _ =>
      match view.application.signal with
      | none => FinDist.pure .wait
      | some _ =>
          match view.application.publication with
          | none => openingPolicy openingDecision (fun _ _ => false) history view
          | some _ =>
              FinDist.pure (if view.application.responseAt + window < view.application.clock &&
                  !responseExpirySubmitted history then .submit .expireResponse
              else .wait)

/-- Exact pure specialization, including histories outside initialized runs.
The disclosure value is reconstructed from history or an accepted public
default, rather than substituted from the initial policy parameter. -/
theorem ownerPolicy_pure_eq (secret : Bool) (complete : Bool → Bool → Bool)
    (history : List (application window).PlayerEntry) (view : (application window).View) :
    ownerPolicy (pureInitialDecision secret) (pureOpeningDecision complete) history view =
      FinDist.pure (if view.application.response.isSome then .wait else
        match view.application.accepted with
        | none =>
            match initialCachedValue window history with
            | none => .privateCommand (0, secret)
            | some _ => if bindingSubmitted history then .wait else .submit (.bind (0, 0))
        | some _ =>
            match view.application.signal with
            | none => .wait
            | some _ =>
                match view.application.publication with
                | none =>
                    if (openingController (window := window)
                        (view.application.signalAt + window) (pureOpeningDecision complete)
                        (fun _ _ => false)).ready view &&
                        (openingCommandEncoding.cachedValue (application window) history).isNone
                    then pureOpeningCommand complete history view else .wait
                | some _ =>
                    if view.application.responseAt + window < view.application.clock &&
                        !responseExpirySubmitted history then .submit .expireResponse
                    else .wait) := by
  unfold ownerPolicy
  split
  · rfl
  · cases haccepted : view.application.accepted with
    | none =>
        cases hcache : initialCachedValue window history with
        | none =>
            rw [initialChoiceController_first_private window (pureInitialDecision secret)
              history view haccepted hcache]
            simp [pureInitialDecision]
        | some value => rfl
    | some binding =>
        cases view.application.signal with
        | none => rfl
        | some signal =>
            cases view.application.publication with
            | none => exact openingPolicy_pure_eq complete history view
            | some publication => rfl

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
              !publicationExpirySubmitted history then .submit (.publish 5 .expire) else .wait)
      | some _, some _ =>
          (responseController response (fun _ _ => false)).policy
            (application window) history view
      | _, _ => FinDist.pure .wait

def honestPlayers (secret : Bool) (complete : Bool → Bool → Bool)
    (response : Bool → Option Bool → Bool) : TestPlayer → (application window).PlayerPolicy
  | 0 => ownerPolicy (pureInitialDecision secret) (pureOpeningDecision complete)
  | 1 => responderPolicy (pureResponseDecision response)

/-- The pure source response kernel gives a deterministic native command on
every history and view, retaining both timeout branches and generated readiness. -/
theorem responderPolicy_pure_eq (response : Bool → Option Bool → Bool)
    (history : List (application window).PlayerEntry) (view : (application window).View) :
    responderPolicy (pureResponseDecision response) history view =
      FinDist.pure (if view.application.response.isSome then .wait else
        match view.application.accepted with
        | none =>
            if window < view.application.clock && !initialExpirySubmitted history
            then .submit .expireInitial else .wait
        | some _ =>
            match view.application.signal, view.application.publication with
            | some _, none =>
                if view.application.signalAt + window < view.application.clock &&
                    !publicationExpirySubmitted history then .submit (.publish 5 .expire)
                else .wait
            | some _, some _ =>
                if responseEndpoint.ready view.application.done &&
                    (responseCommandEncoding.cachedValue (application window) history).isNone
                then .submit (.respond (response (view.application.signal.getD false)
                  (view.application.publication.getD none))) else .wait
            | _, _ => .wait) := by
  unfold responderPolicy
  split
  · rfl
  · cases view.application.accepted with
    | none => rfl
    | some binding =>
        cases hsignal : view.application.signal with
        | none => rfl
        | some signal =>
            cases hpublication : view.application.publication with
            | none => rfl
            | some publication =>
                simpa only [hsignal, hpublication] using
                  responseController_pure_eq response history view

/-- All native strategic choices are projections of one written source profile.
Protocol control, delivery, and deadline resolution remain native operations. -/
def compiledPlayers (profile : Vegas.SourceBehavioralProfile source.prog) :
    TestPlayer → (application window).PlayerPolicy
  | 0 => ownerPolicy (profile 0 initialSite)
      (profile 0 Publication.publicationCertificate.choice.decision)
  | 1 => responderPolicy (profile 1 responseOccurrence.decision)

theorem compiledPlayers_pure (secret : Bool) (complete : Bool → Bool → Bool)
    (response : Bool → Option Bool → Bool) :
    compiledPlayers (window := window)
        (SourcePolicies.pureProfile [(0, payoff)] secret complete response) =
      honestPlayers secret complete response := by
  funext who
  fin_cases who <;> rfl

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
    ownerPolicy (pureInitialDecision secret) (pureOpeningDecision complete) history view =
      FinDist.pure .wait := by
  simp [ownerPolicy, haccepted, hsignal]

theorem owner_publication_after_signal (secret signal : Bool)
    (complete : Bool → Bool → Bool) (history : List (application window).PlayerEntry)
    (view : (application window).View)
    (haccepted : view.application.accepted = some (.commitment (0, 0)))
    (hcache : initialCachedValue window history = some secret)
    (hmarker : view.application.markerDone = true)
    (hsignal : view.application.signal = some signal)
    (hunresolved : view.application.publication = none)
    (hresponse : view.application.response = none)
    (hnotSubmitted : openingSubmitted history = false) :
    ownerPolicy (pureInitialDecision secret) (pureOpeningDecision complete) history view =
      FinDist.pure
      (if complete secret signal then .submit (.publish 5 (.opening (0, 0) secret))
       else .submit (.publish 5 .decline)) := by
  simp only [ownerPolicy, hresponse, Option.isSome_none, Bool.false_eq_true, if_false,
    haccepted, hsignal, hunresolved]
  have hnone : openingCommandEncoding.cachedValue (application window) history = none := by
    simpa [openingSubmitted] using hnotSubmitted
  have hbound : openingBound? history view = some secret := by
    simpa [openingBound?, haccepted] using hcache
  have hfirst := openingPolicy_first_pure complete history view (.commitment (0, 0)) secret signal
      hnone haccepted rfl hbound hmarker hsignal hunresolved
  cases hchoice : complete secret signal <;>
    simpa [ConditionalPublication.requestPayload, hchoice] using hfirst

/-- Recovery uses the accepted public value, even with different private intent
or an empty local history. It does not prepare or publish another commitment. -/
theorem owner_recovers_public_default (secret value signal : Bool)
    (complete : Bool → Bool → Bool) (history : List (application window).PlayerEntry)
    (view : (application window).View)
    (haccepted : view.application.accepted = some (.publicDefault value))
    (hmarker : view.application.markerDone = true)
    (hsignal : view.application.signal = some signal)
    (hunresolved : view.application.publication = none)
    (hresponse : view.application.response = none)
    (hnotSubmitted : openingSubmitted history = false) :
    ownerPolicy (pureInitialDecision secret) (pureOpeningDecision complete) history view =
      FinDist.pure
      (if complete value signal then .submit (.publish 5 (.opening (0, 0) value))
       else .submit (.publish 5 .decline)) := by
  simp only [ownerPolicy, hresponse, Option.isSome_none, Bool.false_eq_true, if_false,
    haccepted, hsignal, hunresolved]
  have hnone : openingCommandEncoding.cachedValue (application window) history = none := by
    simpa [openingSubmitted] using hnotSubmitted
  have hfirst := openingPolicy_first_pure complete history view (.publicDefault value) value signal
      hnone haccepted rfl (by simp [openingBound?, haccepted]) hmarker hsignal hunresolved
  cases hchoice : complete value signal <;>
    simpa [ConditionalPublication.requestPayload, hchoice] using hfirst

theorem owner_expires_response (secret signal : Bool) (complete : Bool → Bool → Bool)
    (history : List (application window).PlayerEntry) (view : (application window).View)
    (binding : DisclosureBinding) (publication : Option Bool)
    (haccepted : view.application.accepted = some binding)
    (hsignal : view.application.signal = some signal)
    (hpublication : view.application.publication = some publication)
    (hresponse : view.application.response = none)
    (hexpired : view.application.responseAt + window < view.application.clock)
    (hnotSubmitted : responseExpirySubmitted history = false) :
    ownerPolicy (pureInitialDecision secret) (pureOpeningDecision complete) history view =
      FinDist.pure (.submit .expireResponse) := by
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
    (hnotSubmitted : publicationExpirySubmitted history = false) :
    responderPolicy (pureResponseDecision response) history view =
      FinDist.pure (.submit (.publish 5 .expire)) := by
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
    (hemit : ownerPolicy (pureInitialDecision secret) (pureOpeningDecision complete) history view =
      FinDist.pure (.submit (.publish 5 request))) :
    view.application.accepted.isSome = true ∧
      view.application.signal.isSome = true ∧ view.application.publication = none := by
  rw [ownerPolicy_pure_eq] at hemit
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
