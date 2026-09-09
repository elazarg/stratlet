/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosureResponderChoice
import VegasTests.DisclosureResponseService

/-! # Timely service of the unchanged responder's selected reply

The initialized command history and empty cycle-boundary queue force a still
unresolved response to be unsubmitted. The next actual arrival phase submits
the selected reply, and inclusion before the deadline preserves that value.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Interaction GameTheory.Math.Probability

variable {window : Nat}

/-- An unchanged responder's timely service cycle accepts its selected reply.
The prefix starts at initialization, including the real command histories and
all retained messages; arbitrary owner traffic and admitted selectors remain
in scope. -/
theorem responder_response_cycle_choice (response : Bool → Option Bool → Bool)
    (signal : Bool) (publication : Option Bool)
    (players : TestPlayer → (application window).PlayerPolicy)
    (hresponder : players 1 = responderPolicy response)
    (selector : (application window).EnvironmentPolicy)
    (hselector : (application window).InclusionService (fun _ => True) selector)
    (cycles : Nat) (execution next : (application window).PolicyExecution)
    (hprefix : execution ∈ ((serviceGame window cycles selector).play players).support)
    (hsignal : execution.native.application.signal = some signal)
    (hpublication : execution.native.application.publication = some publication)
    (hresponse : execution.native.application.response = none)
    (hearly : execution.native.application.clock ≤
      execution.native.application.responseAt + window)
    (hnext : next ∈ ((application window).runPolicies players (serviceEnvironment selector)
      serviceCycle execution).support) :
    next.native.application.response = some (response signal publication) := by
  obtain ⟨_, hhistory, hempty, hinvariant⟩ :=
    service_game_invariants players selector hselector cycles execution hprefix
  have hphase : execution.environmentHistory.length % 13 = 0 := by omega
  have hnotSubmitted : responseSubmitted (execution.principalHistory 1) = false := by
    cases hflag : responseSubmitted (execution.principalHistory 1) with
    | false => rfl
    | true =>
        obtain ⟨entry, hentry, observedSignal, observedPublication, _, _, hcommand⟩ :=
          responder_responseSubmitted_exact response players hresponder
            (serviceEnvironment selector) (serviceSchedule cycles) execution hprefix hflag
        rcases responder_response_submission response (response observedSignal observedPublication)
            players hresponder (serviceEnvironment selector) (serviceSchedule cycles) execution
            hprefix ⟨entry, hentry, hcommand⟩ with hresolved | ⟨_, serial, hpending⟩
        · simp [hresponse] at hresolved
        · simp [hempty] at hpending
  obtain ⟨arrived, drained, harrived, hdrained, htail, hcapacity, hslots, htailPhase⟩ :=
    service_cycle_parts players selector execution next hphase hempty hnext
  have hpublic := (service_arrivals_public players selector execution arrived hphase harrived).1
  have haccepted := hinvariant.2.1 (hinvariant.2.2.1 (by simp [hsignal]))
  obtain ⟨binding, hbinding⟩ := Option.isSome_iff_exists.mp haccepted
  obtain ⟨serial, hpending⟩ := responder_response_arrival response players hresponder selector
    execution arrived hphase binding signal publication hbinding hsignal hpublication
    hresponse hnotSubmitted harrived
  have hsafe := responder_initialized_choice_provenance response players
    hresponder (serviceEnvironment selector) (serviceSchedule cycles) execution hprefix
    signal publication hsignal hpublication
  have hsafeArrived := responder_choice_policy_provenance response signal publication players
    hresponder (serviceEnvironment selector) serviceArrivals execution arrived hsignal
    hpublication hsafe harrived
  have harrivedInvariant := (application window).runPolicies_application_invariant Invariant
    privateStep_invariant (handle_invariant window) environmentStep_invariant
    players (serviceEnvironment selector) serviceArrivals execution arrived hinvariant harrived
  have hresolved := responder_choice_phase_resolves signal publication
    (response signal publication) serial
    players inclusionSlots (serviceEnvironment selector)
    (serviceEnvironment_inclusions selector hselector) 8 arrived drained hslots hcapacity
    harrivedInvariant
    ((congrArg PublicState.signal hpublic).trans hsignal)
    ((congrArg PublicState.publication hpublic).trans hpublication)
    ((congrArg PublicState.response hpublic).trans hresponse)
    (by
      rw [show arrived.native.application.clock = execution.native.application.clock from
        congrArg PublicState.clock hpublic,
        show arrived.native.application.responseAt = execution.native.application.responseAt from
          congrArg PublicState.responseAt hpublic]
      exact hearly)
    hsafeArrived hpending hdrained
  exact (service_tail_preserves_milestones players selector drained next htailPhase htail).2.2.trans
    hresolved

end VegasTests.OptionalDisclosure.DisclosureState
