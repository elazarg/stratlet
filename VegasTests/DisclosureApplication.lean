/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPolicies
import VegasTests.DisclosurePublication

/-! # Public interaction for the checked disclosure program

This application specializes the checked optional-disclosure source to the
shared message runtime. Operational state contains public progress and an ideal
commitment service, not a graph configuration. Source reconstruction is a
separate proof-facing projection. The publication site and response dependency
gate come from the actual compiled graph.

The environment may execute the forced public marker and trigger the source
chance kernel. Neither operation consults the owner's policy or selects a
chance outcome. A publication window starts when that signal is sampled.
Decline and expiration continue to the source responder decision; initial
withholding and missing responses remain unresolved in this instance.

This is a concrete application specialization, not a general source-to-message
compiler or a strategic equivalence of its atomic two-node operations.
Binding accepts the canonical opaque handle without testing whether it has an
opening. Its private ideal verifier is captured at acceptance: a malformed
binding remains unopenable after later private preparation. Validity affects
opening, not acceptance, observations, or readiness for public chance.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure

open Vegas EventGraph Interaction GameTheory.Math.Probability

structure DisclosureState where
  service : IdealCommitments TestPlayer Nat Bool
  acceptedService : IdealCommitments TestPlayer Nat Bool
  accepted : Option (CommitmentHandle TestPlayer Nat)
  markerDone : Bool
  signal : Option Bool
  signalAt : Nat
  publication : Option (Option Bool)
  response : Option Bool
  clock : Nat

namespace DisclosureState

inductive Payload where
  | bind (handle : CommitmentHandle TestPlayer Nat)
  | publish (request : ConditionalPublication.Payload TestPlayer Bool)
  | respond (value : Bool)
  | cleartext (value : Bool)
  | malformed

inductive EnvironmentCommand where
  | marker
  | sample
  | advance (clock : Nat)

structure PublicState where
  accepted : Option (CommitmentHandle TestPlayer Nat)
  markerDone : Bool
  signal : Option Bool
  signalAt : Nat
  publication : Option (Option Bool)
  response : Option Bool
  clock : Nat

def observe (state : DisclosureState) : PublicState :=
  ⟨state.accepted, state.markerDone, state.signal, state.signalAt,
    state.publication, state.response, state.clock⟩

def empty : DisclosureState :=
  ⟨IdealCommitments.empty, IdealCommitments.empty, none, false, none, 0, none, none, 0⟩

/-- Both members of an atomic source pair have completed together. -/
def done (state : DisclosureState) : Nat → Bool
  | 0 => state.accepted.isSome
  | 1 | 2 => state.markerDone
  | 3 => state.signal.isSome
  | 4 | 5 => state.publication.isSome
  | 6 | 7 => state.response.isSome
  | _ => false

def responsePrerequisites : List Nat :=
  graph.publicationPrerequisites (node 6) (node 7)

def responseReady (state : DisclosureState) : Bool :=
  !state.done 6 && !state.done 7 && responsePrerequisites.all state.done

def privateStep (state : DisclosureState) (who : TestPlayer)
    (command : Nat × Bool) : DisclosureState :=
  { state with service := (state.service.sealValue who command.1 command.2).state }

def environmentStep (state : DisclosureState) : EnvironmentCommand → FinDist DisclosureState
  | .marker =>
      FinDist.pure (if state.accepted.isSome && !state.markerDone then
        { state with markerDone := true } else state)
  | .sample =>
      if state.markerDone && state.signal.isNone then
        fairCoin.denote.map fun signal =>
          { state with signal := some signal, signalAt := state.clock }
      else FinDist.pure state
  | .advance clock => FinDist.pure (if state.clock ≤ clock then { state with clock } else state)

/-- Acceptance freezes the privileged verifier without exposing its result.
Only a subsequent authenticated opening tests the captured commitment. -/
def handle (window : Nat) (state : DisclosureState)
    (message : Message TestPlayer Payload) : Option DisclosureState :=
  match message.payload with
  | .bind handle =>
      if message.sender = 0 ∧ handle = (0, 0) ∧ state.accepted.isNone then
        some { state with
          accepted := some handle
          acceptedService := state.service.freezeAt handle }
      else none
  | .publish request => do
      let result ← (Publication.publicationSite (state.signalAt + window)).resolve? state.clock
        state.acceptedService state.accepted state.done (fun _ => true) ⟨message.id, request⟩
      some { state with publication := some result }
  | .respond value =>
      if message.sender = 1 ∧ state.responseReady then
        some { state with response := some value }
      else none
  | .cleartext _ | .malformed => none

def application (window : Nat) : MessageApplication TestPlayer where
  Application := DisclosureState
  Payload := Payload
  PrivateCommand := Nat × Bool
  EnvironmentCommand := EnvironmentCommand
  PlayerView := PublicState
  EnvironmentView := PublicState
  privateStep := privateStep
  environmentStep := environmentStep
  handle := handle window
  observePlayer state _ := state.observe
  observeEnvironment := observe

def initial (window : Nat) : (application window).State :=
  MessageApplication.State.initial (application window) empty

/-- Proof-facing source reconstruction. A permanently unopenable commitment
uses `false` as a source witness and can resolve only to decline. This convention
does not publish a default, repair the commitment, or settle a pending run. -/
def data (state : DisclosureState) : RunData :=
  ⟨(state.acceptedService.lookup (0, 0)).getD false, state.signal.getD false,
    state.publication.getD none, state.response.getD false⟩

def phase (state : DisclosureState) : Fin 9 :=
  if state.response.isSome then 8 else
  if state.publication.isSome then 6 else
  if state.signal.isSome then 4 else
  if state.markerDone then 3 else
  if state.accepted.isSome then 1 else 0

def decodedConfig (state : DisclosureState) : Config graph := cfg state.data state.phase

/-- Settlement readout is partial. In particular, an unresolved publication
and a resolved source decline have different native meanings. -/
def outcome? (state : DisclosureState) : Option (Bool × Option Bool × Bool) := do
  let signal ← state.signal
  let publication ← state.publication
  let response ← state.response
  some (signal, publication, response)

theorem empty_outcome : empty.outcome? = none := rfl

theorem unresolved_publication (state : DisclosureState) (h : state.publication = none) :
    state.outcome? = none := by
  simp [outcome?, h]

theorem responsePrerequisites_eq :
    responsePrerequisites = [2, 3, 5, 0, 1, 4] := rfl

theorem sample_once (state : DisclosureState) (signal : Bool) :
    environmentStep { state with signal := some signal } .sample =
      FinDist.pure { state with signal := some signal } := by
  simp [environmentStep]

theorem sample_arms_window (state : DisclosureState)
    (hmarker : state.markerDone = true) (hsignal : state.signal = none) :
    environmentStep state .sample = fairCoin.denote.map
      (fun signal => { state with signal := some signal, signalAt := state.clock }) := by
  simp [environmentStep, hmarker, hsignal]

/-- Changing the hidden table alone changes neither application observation.
This does not assert hiding once an opening packet is delivered. -/
theorem observe_service (state : DisclosureState)
    (service : IdealCommitments TestPlayer Nat Bool) :
    observe { state with service } = observe state := rfl

theorem observe_acceptedService (state : DisclosureState)
    (service : IdealCommitments TestPlayer Nat Bool) :
    observe { state with acceptedService := service } = observe state := rfl

/-- Acceptance and its public result do not test whether the submitted handle
has an opening. The same statement applies to a completely empty service. -/
theorem bind_accepts (window : Nat) (state : DisclosureState) (serial : Nat)
    (haccepted : state.accepted = none) :
    handle window state ⟨(0, serial), .bind (0, 0)⟩ =
      some { state with
        accepted := some (0, 0)
        acceptedService := state.service.freezeAt (0, 0) } := by
  simp [handle, Message.sender, haccepted]

theorem bind_public_result (window : Nat) (state : DisclosureState) (serial : Nat)
    (service : IdealCommitments TestPlayer Nat Bool) (haccepted : state.accepted = none) :
    (handle window { state with service } ⟨(0, serial), .bind (0, 0)⟩).map observe =
      some { state.observe with accepted := some (0, 0) } := by
  rw [bind_accepts window { state with service } serial haccepted]
  rfl

/-- Local preparation never modifies the verifier of a binding already
accepted by the application. -/
theorem privateStep_acceptedService (state : DisclosureState) (who : TestPlayer)
    (command : Nat × Bool) :
    (privateStep state who command).acceptedService = state.acceptedService := rfl

/-- Marker progress, chance readiness and law, and clock observations are
independent of both private service tables. This is not hiding of later
opening traffic or of a policy's decision whether to open. -/
theorem environmentStep_public_services (state : DisclosureState)
    (service acceptedService : IdealCommitments TestPlayer Nat Bool)
    (command : EnvironmentCommand) :
    (environmentStep { state with service, acceptedService } command).map observe =
      (environmentStep state command).map observe := by
  cases command <;> simp only [environmentStep]
  all_goals split <;>
    simp [observe, FinDist.map_comp, Function.comp_def]

end DisclosureState
end VegasTests.OptionalDisclosure
