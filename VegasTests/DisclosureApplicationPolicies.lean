/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosureApplication

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

def OpeningValid (secret : Bool) (opening : Bool → Option Bool) : Prop :=
  ∀ signal, opening signal = none ∨ opening signal = some secret

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

/-- The owner registers privately, publishes only an opaque binding handle,
and waits for the actual public signal before selecting publication. -/
def ownerPolicy (secret : Bool) (opening : Bool → Option Bool) :
    (application window).PlayerPolicy := fun history view => FinDist.pure <|
  if !registered history then
    .privateCommand (0, secret)
  else if view.application.accepted.isNone then
    if bindingSubmitted history then .wait else .submit (.bind (0, 0))
  else match view.application.signal, view.application.publication with
    | some signal, none =>
        if publicationSubmitted history then .wait
        else match opening signal with
          | none => .submit (.publish .decline)
          | some value => .submit (.publish (.opening (0, 0) value))
    | _, _ => .wait

/-- The responder submits only after both the public signal and the resolved
optional publication are present in its current observation. -/
def responderPolicy (response : Bool → Option Bool → Bool) :
    (application window).PlayerPolicy := fun history view => FinDist.pure <|
  match view.application.signal, view.application.publication with
  | some signal, some publication =>
      if responseSubmitted history then .wait
      else .submit (.respond (response signal publication))
  | _, _ => .wait

def honestPlayers (secret : Bool) (opening : Bool → Option Bool)
    (response : Bool → Option Bool → Bool) : TestPlayer → (application window).PlayerPolicy
  | 0 => ownerPolicy secret opening
  | 1 => responderPolicy response

/-- Environment script indexed only by its own sampled command history. The
sample command triggers the application's fixed fair kernel and carries no
chance result. -/
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

theorem owner_waits_before_signal (secret : Bool) (opening : Bool → Option Bool)
    (history : List (application window).PlayerEntry) (view : (application window).View)
    (hregistered : registered history = true)
    (haccepted : view.application.accepted.isNone = false)
    (hsignal : view.application.signal = none) :
    ownerPolicy secret opening history view = FinDist.pure .wait := by
  simp [ownerPolicy, hregistered, haccepted, hsignal]

theorem owner_publication_after_signal (secret signal : Bool)
    (opening : Bool → Option Bool) (history : List (application window).PlayerEntry)
    (view : (application window).View) (hregistered : registered history = true)
    (haccepted : view.application.accepted.isNone = false)
    (hsignal : view.application.signal = some signal)
    (hunresolved : view.application.publication = none)
    (hnotSubmitted : publicationSubmitted history = false) :
    ownerPolicy secret opening history view = FinDist.pure
      (match opening signal with
       | none => .submit (.publish .decline)
       | some value => .submit (.publish (.opening (0, 0) value))) := by
  simp [ownerPolicy, hregistered, haccepted, hsignal, hunresolved, hnotSubmitted]

/-- Any publication command emitted by the owner controller is causally after
the public binding and signal, and before resolution. -/
theorem owner_publish_requires_release (secret : Bool) (opening : Bool → Option Bool)
    (history : List (application window).PlayerEntry) (view : (application window).View)
    (request : ConditionalPublication.Payload TestPlayer Bool)
    (hemit : ownerPolicy secret opening history view =
      FinDist.pure (.submit (.publish request))) :
    view.application.accepted.isSome = true ∧
      view.application.signal.isSome = true ∧
      view.application.publication = none := by
  by_cases hregistered : registered history <;>
    cases haccepted : view.application.accepted.isNone <;>
    cases hbinding : bindingSubmitted history <;>
    cases hsignal : view.application.signal <;>
    cases hpublication : view.application.publication <;>
    simp_all [ownerPolicy]
  all_goals have hcommand := pure_injective hemit
  all_goals cases hcommand

theorem responder_waits_before_release (response : Bool → Option Bool → Bool)
    (history : List (application window).PlayerEntry) (view : (application window).View)
    (hsignal : view.application.signal = none ∨ view.application.publication = none) :
    responderPolicy response history view = FinDist.pure .wait := by
  rcases hsignal with hsignal | hpublication
  · simp [responderPolicy, hsignal]
  · cases hsignal : view.application.signal <;>
      simp [responderPolicy, hsignal, hpublication]

theorem responder_submits_after_release (response : Bool → Option Bool → Bool)
    (signal : Bool) (publication : Option Bool)
    (history : List (application window).PlayerEntry) (view : (application window).View)
    (hsignal : view.application.signal = some signal)
    (hpublication : view.application.publication = some publication)
    (hnotSubmitted : responseSubmitted history = false) :
    responderPolicy response history view =
      FinDist.pure (.submit (.respond (response signal publication))) := by
  simp [responderPolicy, hsignal, hpublication, hnotSubmitted]

/-- A responder packet is never emitted before both public inputs exist. -/
theorem responder_submit_requires_release (response : Bool → Option Bool → Bool)
    (history : List (application window).PlayerEntry) (view : (application window).View)
    (value : Bool) (hemit : responderPolicy response history view =
      FinDist.pure (.submit (.respond value))) :
    view.application.signal.isSome = true ∧
      view.application.publication.isSome = true := by
  cases hsignal : view.application.signal <;>
    cases hpublication : view.application.publication <;>
    simp_all [responderPolicy]
  all_goals have hcommand := pure_injective hemit
  all_goals simp_all

end VegasTests.OptionalDisclosure.DisclosureState
