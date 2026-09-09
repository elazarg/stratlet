/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.ChoiceControllerHistory
import VegasTests.DisclosureApplicationPolicies

/-! # Actual responder history for the generated public-choice controller

At a ready response checkpoint, the composite responder policy delegates to
the generated public-choice controller. Its first actual player invocation
therefore records exactly the written source decision law in the responder's
own chronological command history. This is a local invocation fact, not a
settlement or outcome claim.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Vegas EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {window : Nat}

/-- In the resolved-publication phase, the composite responder policy is
exactly its generated public-choice component. -/
theorem responderPolicy_response_component (policy : ResponseDecision)
    (history : List (application window).PlayerEntry)
    (view : (application window).View) (binding : DisclosureBinding)
    (signal : Bool) (publication : Option Bool)
    (haccepted : view.application.accepted = some binding)
    (hsignal : view.application.signal = some signal)
    (hpublication : view.application.publication = some publication)
    (hresponse : view.application.response = none) :
    responderPolicy policy history view =
      (responseController policy (fun _ _ => false)).policy
        (application window) history view := by
  simp [responderPolicy, haccepted, hsignal, hpublication, hresponse]

/-- The first response invocation of the actual composite policy has the
source decision law jointly with the native submission step. -/
theorem responder_invoke_first_source_law
    (policy : ResponseDecision)
    (players : TestPlayer → (application window).PlayerPolicy)
    (environment : (application window).EnvironmentPolicy)
    (execution : (application window).PolicyExecution)
    (binding : DisclosureBinding) (secret signal : Bool)
    (publication : Option Bool)
    (hplayers : players 1 = responderPolicy policy)
    (hcache : responseCodec.cachedValue (application window)
      (execution.principalHistory 1) = none)
    (haccepted : execution.native.application.accepted = some binding)
    (hmarker : execution.native.application.markerDone = true)
    (hsignal : execution.native.application.signal = some signal)
    (hpublication : execution.native.application.publication = some publication)
    (hresponse : execution.native.application.response = none) :
    (application window).invoke players environment execution (.player 1) =
      (policy (((responseEnv secret signal publication).toView 1).eraseEnv)).bind
        (fun chosen => (application window).playerStep 1 execution
          (.submit (.respond chosen.1))) := by
  let view := State.observe (application window) execution.native 1
  have hacceptedView : view.application.accepted = some binding := by
    exact haccepted
  have hmarkerView : view.application.markerDone = true := by
    exact hmarker
  have hsignalView : view.application.signal = some signal := by
    exact hsignal
  have hpublicationView : view.application.publication = some publication := by
    exact hpublication
  have hresponseView : view.application.response = none := by
    exact hresponse
  have hcomponent := responderPolicy_response_component policy
    (execution.principalHistory 1) view binding signal publication hacceptedView
      hsignalView hpublicationView hresponseView
  have hfirst :
      (responseController policy (fun _ _ => false)).policy
          (application window) (execution.principalHistory 1) view =
        (policy (((responseEnv secret signal publication).toView 1).eraseEnv)).map
          (fun chosen => PlayerCommand.submit (Payload.respond chosen.1)) :=
    responseController_first_submission policy (fun _ _ => false)
      (execution.principalHistory 1) view binding secret signal publication hcache
        hacceptedView hmarkerView hsignalView hpublicationView hresponseView
  rw [MessageApplication.invoke, hplayers, hcomponent, hfirst, FinDist.bind_map]

/-- Projecting the actual invocation law to the responder's chronological
cache records exactly the source decision kernel. -/
theorem responder_invoke_first_cached_source_law
    (policy : ResponseDecision)
    (players : TestPlayer → (application window).PlayerPolicy)
    (environment : (application window).EnvironmentPolicy)
    (execution : (application window).PolicyExecution)
    (binding : DisclosureBinding) (secret signal : Bool)
    (publication : Option Bool)
    (hplayers : players 1 = responderPolicy policy)
    (hcache : responseCodec.cachedValue (application window)
      (execution.principalHistory 1) = none)
    (haccepted : execution.native.application.accepted = some binding)
    (hmarker : execution.native.application.markerDone = true)
    (hsignal : execution.native.application.signal = some signal)
    (hpublication : execution.native.application.publication = some publication)
    (hresponse : execution.native.application.response = none) :
    ((application window).invoke players environment execution (.player 1)).map
        (fun next => responseCodec.cachedValue (application window)
          (next.principalHistory 1)) =
      (policy (((responseEnv secret signal publication).toView 1).eraseEnv)).map
        (some ∘ Subtype.val) := by
  rw [responder_invoke_first_source_law policy players environment execution binding
    secret signal publication hplayers hcache haccepted hmarker hsignal hpublication
      hresponse]
  simp only [FinDist.map_bind]
  apply FinDist.bind_congr
  intro chosen _
  simp only [MessageApplication.playerStep, MessageApplication.advance,
    MessageApplication.PlayerCommand.toAction, MessageApplication.step,
    FinDist.pure_bind, FinDist.map_pure, ↓reduceIte]
  have hrecorded := responseCodec.cachedValue_append_encoded_of_none
    (application window) (execution.principalHistory 1)
      (State.observe (application window) execution.native 1) chosen.1 hcache
  exact congrArg FinDist.pure hrecorded

/--
info: 'VegasTests.OptionalDisclosure.DisclosureState.responder_invoke_first_cached_source_law'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  VegasTests.OptionalDisclosure.DisclosureState.responder_invoke_first_cached_source_law

/--
info: 'VegasTests.OptionalDisclosure.DisclosureState.responder_invoke_first_source_law'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  VegasTests.OptionalDisclosure.DisclosureState.responder_invoke_first_source_law

end VegasTests.OptionalDisclosure.DisclosureState
