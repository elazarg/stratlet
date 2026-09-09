/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPolicies
import VegasTests.DisclosurePublication
import VegasTests.DisclosurePublicChoice

/-! # Public interaction for the checked disclosure program

This application specializes the checked optional-disclosure source to the
shared message runtime. Operational state contains public progress and an ideal
commitment service, not a graph configuration. Source reconstruction is a
separate proof-facing projection. The publication site comes from the actual
compiled graph. The response handler uses the public-choice endpoint and guard
validator generated from the responder's adjacent source choice and reveal.

The environment may execute the forced public marker and trigger the source
chance kernel. Neither operation consults the owner's policy or selects a
chance outcome. A publication window starts when that signal is sampled.
Decline and expiration continue to the source responder decision. Its own
expiration selects the source rejection action. Initial expiration installs a
public default instead of an owner commitment, leaving private preparation
unchanged. Each expiration requires an included call; none guarantees service.

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

/-- The public disposition of the initial source decision. An installed
default is distinguishable from an owner-submitted opaque commitment. -/
inductive DisclosureBinding where
  | commitment (handle : CommitmentHandle TestPlayer Nat)
  | publicDefault (value : Bool)

namespace DisclosureBinding

def reference : DisclosureBinding → CommitmentHandle TestPlayer Nat
  | .commitment handle => handle
  | .publicDefault _ => (0, 0)

def value? (service : IdealCommitments TestPlayer Nat Bool) : DisclosureBinding → Option Bool
  | .commitment handle => service.lookup handle
  | .publicDefault value => some value

def verify (service : IdealCommitments TestPlayer Nat Bool) (binding : DisclosureBinding)
    (opening : IdealCommitments.Opening
      (Principal := TestPlayer) (Slot := Nat) (Value := Bool)) : Bool :=
  match binding with
  | .commitment handle => opening.handle == handle && service.verify opening
  | .publicDefault value => opening.claimed == value

theorem verify_value (service : IdealCommitments TestPlayer Nat Bool)
    (binding : DisclosureBinding) (opening : IdealCommitments.Opening
      (Principal := TestPlayer) (Slot := Nat) (Value := Bool))
    (hverify : binding.verify service opening = true) :
    binding.value? service = some opening.claimed := by
  cases binding with
  | commitment handle =>
      simp only [verify, Bool.and_eq_true, beq_iff_eq] at hverify
      have hstored := (IdealCommitments.verify_eq_true_iff service opening).mp hverify.2
      simpa only [value?, hverify.1] using hstored
  | publicDefault value =>
      simp only [verify, beq_iff_eq] at hverify
      exact congrArg some hverify.symm

end DisclosureBinding

structure DisclosureState where
  service : IdealCommitments TestPlayer Nat Bool
  acceptedService : IdealCommitments TestPlayer Nat Bool
  accepted : Option DisclosureBinding
  markerDone : Bool
  signal : Option Bool
  signalAt : Nat
  publication : Option (Option Bool)
  responseAt : Nat
  response : Option Bool
  clock : Nat

namespace DisclosureState

inductive Payload where
  | bind (handle : CommitmentHandle TestPlayer Nat)
  | expireInitial
  | publish (endpoint : Nat) (request : ConditionalPublication.Payload TestPlayer Bool)
  | respond (value : Bool)
  | expireResponse
  | cleartext (value : Bool)
  | malformed

inductive EnvironmentCommand where
  | marker
  | sample
  | advance (clock : Nat)

structure PublicState where
  accepted : Option DisclosureBinding
  markerDone : Bool
  signal : Option Bool
  signalAt : Nat
  publication : Option (Option Bool)
  responseAt : Nat
  response : Option Bool
  clock : Nat

def observe (state : DisclosureState) : PublicState :=
  ⟨state.accepted, state.markerDone, state.signal, state.signalAt,
    state.publication, state.responseAt, state.response, state.clock⟩

def empty : DisclosureState :=
  ⟨IdealCommitments.empty, IdealCommitments.empty, none, false, none, 0, none, 0, none, 0⟩

def acceptedReference (state : DisclosureState) : Option (CommitmentHandle TestPlayer Nat) :=
  state.accepted.map DisclosureBinding.reference

def boundValue? (state : DisclosureState) : Option Bool :=
  state.accepted.bind (DisclosureBinding.value? state.acceptedService)

def verifyOpening (state : DisclosureState) (opening : IdealCommitments.Opening
    (Principal := TestPlayer) (Slot := Nat) (Value := Bool)) : Bool :=
  match state.accepted with
  | none => false
  | some binding => binding.verify state.acceptedService opening

theorem verifyOpening_value (state : DisclosureState) (opening : IdealCommitments.Opening
    (Principal := TestPlayer) (Slot := Nat) (Value := Bool))
    (hverify : state.verifyOpening opening = true) :
    state.boundValue? = some opening.claimed := by
  cases haccepted : state.accepted with
  | none => simp [verifyOpening, haccepted] at hverify
  | some binding =>
      simp only [verifyOpening, haccepted] at hverify
      exact (show state.boundValue? = binding.value? state.acceptedService by
        simp [boundValue?, haccepted]).trans
          (binding.verify_value state.acceptedService opening hverify)

/-- Both members of an atomic source pair have completed together. -/
def done (state : DisclosureState) : Nat → Bool
  | 0 => state.accepted.isSome
  | 1 | 2 => state.markerDone
  | 3 => state.signal.isSome
  | 4 | 5 => state.publication.isSome
  | 6 | 7 => state.response.isSome
  | _ => false

def responsePrerequisites : List Nat :=
  responseEndpoint.requires

def responseReady (state : DisclosureState) : Bool :=
  responseEndpoint.ready state.done

/-- Normal form of the generated endpoint's native application effect. -/
@[simp] theorem response_resolve_map {Result : Type}
    (state : DisclosureState) (id : MessageId TestPlayer) (value : Bool)
    (record : Bool → Result) :
    (responseEndpoint.resolve? state.done responseValidator ⟨id, value⟩).map record =
      if id.1 = 1 ∧ state.responseReady then some (record value) else none := by
  simp [PublicChoice.resolve?_map, responseReady, Message.sender]

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

/-- Routing at the source-generated publication address preserves the native
conditional-publication call, including its sender and serial. -/
@[simp] theorem publication_resolve_addressed (deadline now : Nat)
    (verify : IdealCommitments.Opening
      (Principal := TestPlayer) (Slot := Nat) (Value := Bool) → Bool)
    (accepted : Option (CommitmentHandle TestPlayer Nat)) (completed : Nat → Bool)
    (canOpen : Bool → Bool) (id : MessageId TestPlayer)
    (request : ConditionalPublication.Payload TestPlayer Bool) :
    (Publication.publicationSite deadline).resolveAddressed? now verify accepted completed
        canOpen ⟨id, (5, request)⟩ =
      (Publication.publicationSite deadline).resolve? now verify accepted completed
        canOpen ⟨id, request⟩ := rfl

/-- Acceptance freezes the privileged verifier without exposing its result.
Only a subsequent authenticated opening tests the captured commitment. -/
def handle (window : Nat) (state : DisclosureState)
    (message : Message TestPlayer Payload) : Option DisclosureState :=
  match message.payload with
  | .bind handle =>
      if message.sender = 0 ∧ handle = (0, 0) ∧ state.accepted.isNone then
        some { state with
          accepted := some (.commitment handle)
          acceptedService := state.service.freezeAt handle }
      else none
  | .expireInitial =>
      if state.accepted.isNone ∧ window < state.clock then
        some { state with accepted := some (.publicDefault false) }
      else none
  | .publish endpoint request => do
      let result ← (Publication.publicationSite (state.signalAt + window)).resolveAddressed?
        state.clock state.verifyOpening state.acceptedReference state.done (fun _ => true)
          ⟨message.id, (endpoint, request)⟩
      some { state with publication := some result, responseAt := state.clock }
  | .respond value =>
      (responseEndpoint.resolve? state.done responseValidator ⟨message.id, value⟩).map
        (fun chosen => { state with response := some chosen })
  | .expireResponse =>
      if state.responseReady ∧ state.responseAt + window < state.clock then
        some { state with response := some false }
      else none
  | .cleartext _ | .malformed => none

/-- Publication messages are dispatched by the generated source endpoint.
Other addresses remain valid raw traffic but have no application effect. -/
theorem publish_wrong_endpoint (window : Nat) (state : DisclosureState)
    (id : MessageId TestPlayer) (endpoint : Nat)
    (request : ConditionalPublication.Payload TestPlayer Bool) (hne : endpoint ≠ 5) :
    handle window state ⟨id, .publish endpoint request⟩ = none := by
  simp [handle, ConditionalPublication.resolveAddressed?, Message.dispatchEndpoint?,
    Message.routeEndpoint?, Publication.publicationSite_eq, hne]

/-- Acceptance entails the exact generated publication address. -/
theorem publish_endpoint (window : Nat) (state next : DisclosureState)
    (message : Message TestPlayer Payload) (endpoint : Nat)
    (request : ConditionalPublication.Payload TestPlayer Bool)
    (hpayload : message.payload = .publish endpoint request)
    (hhandle : handle window state message = some next) : endpoint = 5 := by
  by_contra hne
  have hreject := publish_wrong_endpoint window state message.id endpoint request hne
  have heq : message = ⟨message.id, .publish endpoint request⟩ := by
    cases message
    simp_all
  rw [heq, hreject] at hhandle
  contradiction

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

/-- Proof-facing source reconstruction uses the accepted commitment or public
default. A permanently unopenable commitment uses `false` as a source witness
and can resolve only to decline. That convention neither installs a public
default nor repairs the commitment or settles a pending run. -/
def data (state : DisclosureState) : RunData :=
  ⟨state.boundValue?.getD false, state.signal.getD false,
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

/-- Initial expiration records a public source default. It leaves every
privately prepared commitment and the captured commitment verifier unchanged. -/
theorem expireInitial_accepts (window : Nat) (state : DisclosureState)
    (caller : TestPlayer) (serial : Nat) (haccepted : state.accepted = none)
    (hexpired : window < state.clock) :
    handle window state ⟨(caller, serial), .expireInitial⟩ =
      some { state with accepted := some (.publicDefault false) } := by
  simp [handle, haccepted, hexpired]

theorem expireInitial_before_deadline (window : Nat) (state : DisclosureState)
    (caller : TestPlayer) (serial : Nat) (hearly : state.clock ≤ window) :
    handle window state ⟨(caller, serial), .expireInitial⟩ = none := by
  simp [handle, Nat.not_lt.mpr hearly]

theorem expireInitial_after_resolution (window : Nat) (state : DisclosureState)
    (caller : TestPlayer) (serial : Nat) (haccepted : state.accepted.isSome = true) :
    handle window state ⟨(caller, serial), .expireInitial⟩ = none := by
  have hnone : state.accepted.isNone = false := by
    cases hbinding : state.accepted <;> simp_all
  simp [handle, hnone]

theorem bind_after_resolution (window : Nat) (state : DisclosureState)
    (id : MessageId TestPlayer) (reference : CommitmentHandle TestPlayer Nat)
    (haccepted : state.accepted.isSome = true) :
    handle window state ⟨id, .bind reference⟩ = none := by
  have hnone : state.accepted.isNone = false := by
    cases hbinding : state.accepted <;> simp_all
  simp [handle, hnone]

/-- A public default uses its recorded public value, independently of a
private commitment that was prepared but never accepted. -/
theorem publicDefault_value (state : DisclosureState) (value : Bool)
    (haccepted : state.accepted = some (.publicDefault value)) :
    state.boundValue? = some value := by
  simp [boundValue?, haccepted, DisclosureBinding.value?]

theorem publicDefault_verification (state : DisclosureState) (value : Bool)
    (haccepted : state.accepted = some (.publicDefault value))
    (opening : IdealCommitments.Opening
      (Principal := TestPlayer) (Slot := Nat) (Value := Bool)) :
    state.verifyOpening opening = (opening.claimed == value) := by
  simp [verifyOpening, haccepted, DisclosureBinding.verify]

theorem responseReady_publication (state : DisclosureState)
    (hready : state.responseReady = true) : state.publication.isSome = true := by
  simp only [responseReady, PublicChoice.ready, Bool.and_eq_true,
    Bool.not_eq_true', List.all_eq_true] at hready
  have hpublicationDone := hready.2 5 (by
    change 5 ∈ responsePrerequisites
    simp [responsePrerequisites_eq])
  simpa [done] using hpublicationDone

/-- The deadline authorizes a permissionless call selecting the existing
source rejection action; it does not synthesize a responder-authored packet. -/
theorem expireResponse_accepts (window : Nat) (state : DisclosureState)
    (caller : TestPlayer) (serial : Nat) (hready : state.responseReady = true)
    (hexpired : state.responseAt + window < state.clock) :
    handle window state ⟨(caller, serial), .expireResponse⟩ =
      some { state with response := some false } := by
  simp [handle, hready, hexpired]

theorem expireResponse_before_deadline (window : Nat) (state : DisclosureState)
    (caller : TestPlayer) (serial : Nat) (hearly : state.clock ≤ state.responseAt + window) :
    handle window state ⟨(caller, serial), .expireResponse⟩ = none := by
  simp [handle, Nat.not_lt.mpr hearly]

theorem expireResponse_completed (window : Nat) (state : DisclosureState)
    (caller : TestPlayer) (serial : Nat) (value : Bool)
    (hresponse : state.response = some value) :
    handle window state ⟨(caller, serial), .expireResponse⟩ = none := by
  simp [handle, responseReady, PublicChoice.ready, done, hresponse]

/-- A completed publication cannot be repeated to re-arm the response clock. -/
theorem publish_after_resolution (window : Nat) (state : DisclosureState)
    (id : MessageId TestPlayer) (endpoint : Nat)
    (request : ConditionalPublication.Payload TestPlayer Bool)
    (result : Option Bool) (hpublication : state.publication = some result) :
    handle window state ⟨id, .publish endpoint request⟩ = none := by
  simp [handle, ConditionalPublication.resolveAddressed?, Message.dispatchEndpoint?,
    Message.routeEndpoint?, ConditionalPublication.resolve?, ConditionalPublication.ready,
    Publication.publicationSite_eq, done, hpublication]

theorem publication_arms_response (window : Nat) (state next : DisclosureState)
    (id : MessageId TestPlayer) (endpoint : Nat)
    (request : ConditionalPublication.Payload TestPlayer Bool)
    (hhandle : handle window state ⟨id, .publish endpoint request⟩ = some next) :
    next.responseAt = state.clock := by
  have hendpoint := publish_endpoint window state next _ endpoint request rfl hhandle
  subst endpoint
  simp only [handle, publication_resolve_addressed] at hhandle
  cases hresolve : (Publication.publicationSite (state.signalAt + window)).resolve?
      state.clock state.verifyOpening state.acceptedReference state.done (fun _ => true)
      ⟨id, request⟩ with
  | none =>
      rw [hresolve] at hhandle
      simp at hhandle
  | some result =>
      rw [hresolve] at hhandle
      cases hhandle
      rfl

/-- The clock only enables calls. Neither publication nor response is resolved
by advancing it, including past both deadlines. -/
theorem advance_no_resolution (state : DisclosureState) (clock : Nat) :
    (environmentStep state (.advance clock)).map
        (fun next => (next.publication, next.response)) =
      FinDist.pure (state.publication, state.response) := by
  simp only [environmentStep]
  split <;> simp

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
        accepted := some (.commitment (0, 0))
        acceptedService := state.service.freezeAt (0, 0) } := by
  simp [handle, Message.sender, haccepted]

theorem bind_public_result (window : Nat) (state : DisclosureState) (serial : Nat)
    (service : IdealCommitments TestPlayer Nat Bool) (haccepted : state.accepted = none) :
    (handle window { state with service } ⟨(0, serial), .bind (0, 0)⟩).map observe =
      some { state.observe with accepted := some (.commitment (0, 0)) } := by
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
