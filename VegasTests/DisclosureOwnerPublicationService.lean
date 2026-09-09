/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosureOwnerInitialService
import VegasTests.DisclosureOwnerPublicationPolicy

/-! # Initialized preservation of the owner's choices

The first cycle binds the unchanged owner's secret. In the second cycle its
chosen opening or decline reaches inclusion before expiration is eligible.
Pool-wide provenance rules out a conflicting owner packet, including replay
from sent histories or earlier delivery. The opposing player remains arbitrary.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Interaction GameTheory.Math.Probability

variable {window : Nat}

/-- Two actual service cycles preserve the unchanged owner's binding and
optional publication against every responder policy and admitted adaptive
inclusion selector. A positive window protects the first publication opportunity. -/
theorem owner_choice_by_two_cycles (secret : Bool) (complete : Bool → Bool → Bool)
    (hwindow : 1 ≤ window)
    (players : TestPlayer → (application window).PlayerPolicy)
    (howner : players 0 = ownerPolicy (pureInitialDecision secret) (pureOpeningDecision complete))
    (selector : (application window).EnvironmentPolicy)
    (hselector : (application window).InclusionService (fun _ => True) selector)
    (next : (application window).PolicyExecution)
    (hnext : next ∈ ((serviceGame window 2 selector).play players).support) :
    ∃ signal,
      next.native.application.accepted = some (.commitment (0, 0)) ∧
        next.native.application.acceptedService.lookup (0, 0) = some secret ∧
        next.native.application.signal = some signal ∧
        next.native.application.publication =
          some (if complete secret signal then some secret else none) := by
  obtain ⟨before, hbefore, hsecond⟩ :=
    service_game_prefix players selector 2 1 (by decide) next hnext
  have hsecond' : next ∈ ((application window).runPolicies players (serviceEnvironment selector)
      serviceCycle before).support := by
    simpa [serviceSchedule] using hsecond
  obtain ⟨haccepted, hstored, hmarker, hsignalSome, horigin, hclock, hpublication, hresponse,
      hnotSubmitted, hnoPublication, hcache⟩ :=
    owner_initial_cycle secret complete players howner selector hselector before hbefore
  obtain ⟨_, hhistory, hempty, _⟩ :=
    service_game_invariants players selector hselector 1 before hbefore
  have hphase : before.environmentHistory.length % 13 = 0 := by omega
  cases hsignal : before.native.application.signal with
  | none => simp [hsignal] at hsignalSome
  | some signal =>
    let result := if complete secret signal then some secret else none
    have hresult : result = none ∨ result = some secret := by
      dsimp [result]
      split <;> simp
    have hsafe : before.native.pool.Satisfies
        (OwnerPublicationSafe ((Publication.publicationSite 0).requestPayload result)) := by
      apply hnoPublication.mono
      intro message hmessage hsender candidate hcandidate
      exact False.elim (hmessage hsender candidate hcandidate)
    obtain ⟨arrived, drained, harrived, hdrained, htail, hcapacity, hslots, htailPhase⟩ :=
      service_cycle_parts players selector before next hphase hempty hsecond'
    have hpublic := (service_arrivals_public players selector before arrived hphase harrived).1
    obtain ⟨serial, hpending⟩ := owner_publication_arrival secret signal complete players howner
      selector before arrived hphase haccepted hcache hmarker hsignal hpublication hresponse
        hnotSubmitted harrived
    have hsafeArrived := owner_publication_policy_provenance secret signal complete players howner
      (serviceEnvironment selector) serviceArrivals before arrived haccepted hcache hsignal
        hsafe harrived
    have hinvariant : Invariant arrived.native.application := by
      apply (application window).runPolicies_application_invariant Invariant
        privateStep_invariant (handle_invariant window) environmentStep_invariant
        players (serviceEnvironment selector) serviceArrivals before arrived
        (service_game_invariants players selector hselector 1 before hbefore).2.2.2 harrived
    obtain ⟨actions, _, hnative⟩ := (application window).runPolicies_native_support players
      (serviceEnvironment selector) serviceArrivals before arrived harrived
    have hbinding := run_binding window before.native arrived.native actions
      (by simp [haccepted]) hnative
    have hpublished := owner_publication_phase_resolves secret signal result hresult serial
      players inclusionSlots (serviceEnvironment selector)
      (serviceEnvironment_inclusions selector hselector)
      8 arrived drained hslots hcapacity hinvariant
      ((congrArg PublicState.accepted hpublic).trans haccepted)
      (by rw [hbinding.2]; exact hstored)
      ((congrArg PublicState.signal hpublic).trans hsignal)
      ((congrArg PublicState.publication hpublic).trans hpublication)
      (by
        rw [show arrived.native.application.clock = before.native.application.clock from
          congrArg PublicState.clock hpublic,
          show arrived.native.application.signalAt = before.native.application.signalAt from
          congrArg PublicState.signalAt hpublic, horigin, hclock]
        simpa only [Nat.zero_add] using hwindow)
      hsafeArrived (by
        cases hchoice : complete secret signal <;>
          simpa [result, ConditionalPublication.requestPayload, hchoice] using hpending) hdrained
    have hpreserved := service_tail_preserves_milestones players selector drained next
      htailPhase htail
    obtain ⟨wholeActions, _, hwholeNative⟩ :=
      (application window).runPolicies_native_support players
        (serviceEnvironment selector) serviceCycle before next hsecond'
    have hwholeBinding := run_binding window before.native next.native wholeActions
      (by simp [haccepted]) hwholeNative
    have hwholeSignal := runPolicies_signal_origin players (serviceEnvironment selector)
      serviceCycle before next signal hsignal hsecond'
    refine ⟨signal, hwholeBinding.1.trans haccepted, ?_, hwholeSignal.1,
      hpreserved.2.1.trans hpublished⟩
    rw [hwholeBinding.2]
    exact hstored

/-- info: 'VegasTests.OptionalDisclosure.DisclosureState.owner_choice_by_two_cycles'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms owner_choice_by_two_cycles

end VegasTests.OptionalDisclosure.DisclosureState
