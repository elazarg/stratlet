/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosureOwnerPublicationService
import VegasTests.DisclosureOwnerResponseService
import VegasTests.DisclosureResponseTimeOrigins

/-! # Initialized owner guarantees under public service

The unchanged owner's binding and optional publication survive all subsequent
traffic. Its timeout controller also completes an absent responder's decision
under the bounded service, without requiring the responder to submit anything.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Interaction GameTheory.Math.Probability

variable {window : Nat}

/-- After its first two service cycles, the unchanged owner's choices remain
fixed for every later supported execution, regardless of responder behavior. -/
theorem owner_choices_preserved (secret : Bool) (complete : Bool → Bool → Bool)
    (hwindow : 1 ≤ window)
    (players : TestPlayer → (application window).PlayerPolicy)
    (howner : players 0 = ownerPolicy (pureInitialDecision secret) (pureOpeningDecision complete))
    (selector : (application window).EnvironmentPolicy)
    (hselector : (application window).InclusionService (fun _ => True) selector)
    (cycles : Nat) (hcycles : 2 ≤ cycles)
    (next : (application window).PolicyExecution)
    (hnext : next ∈ ((serviceGame window cycles selector).play players).support) :
    ∃ signal,
      next.native.application.accepted = some (.commitment (0, 0)) ∧
        next.native.application.acceptedService.lookup (0, 0) = some secret ∧
        next.native.application.signal = some signal ∧
        next.native.application.publication =
          some (if complete secret signal then some secret else none) := by
  obtain ⟨before, hbefore, htail⟩ :=
    service_game_prefix players selector cycles 2 hcycles next hnext
  obtain ⟨signal, haccepted, hstored, hsignal, hpublication⟩ :=
    owner_choice_by_two_cycles secret complete hwindow players howner selector hselector
      before hbefore
  obtain ⟨actions, _, hnative⟩ := (application window).runPolicies_native_support players
    (serviceEnvironment selector) (serviceSchedule (cycles - 2)) before next htail
  have hbinding := run_binding window before.native next.native actions
    (by simp [haccepted]) hnative
  have hsignalFixed := runPolicies_signal_origin players (serviceEnvironment selector)
    (serviceSchedule (cycles - 2)) before next signal hsignal htail
  have hpublicationFixed := runPolicies_response_origin players (serviceEnvironment selector)
    (serviceSchedule (cycles - 2)) before next _ hpublication htail
  refine ⟨signal, hbinding.1.trans haccepted, ?_, hsignalFixed.1, hpublicationFixed.1⟩
  rw [hbinding.2]
  exact hstored

private theorem owner_response_overdue_by_cycle (secret : Bool) (complete : Bool → Bool → Bool)
    (hwindow : 1 ≤ window)
    (players : TestPlayer → (application window).PlayerPolicy)
    (howner : players 0 = ownerPolicy (pureInitialDecision secret) (pureOpeningDecision complete))
    (selector : (application window).EnvironmentPolicy)
    (hselector : (application window).InclusionService (fun _ => True) selector)
    (cycles : Nat) (hcycles : window + 2 ≤ cycles)
    (next : (application window).PolicyExecution)
    (hnext : next ∈ ((serviceGame window cycles selector).play players).support) :
    next.native.application.publication.isSome = true ∧
      next.native.application.responseAt + window < next.native.application.clock := by
  obtain ⟨published, hpublished, htail⟩ :=
    service_game_prefix players selector cycles 2 (by omega) next hnext
  obtain ⟨signal, _, _, _, hpublication⟩ :=
    owner_choice_by_two_cycles secret complete hwindow players howner selector hselector
      published hpublished
  obtain ⟨before, hbefore, hcycle⟩ :=
    service_game_prefix players selector 2 1 (by decide) published hpublished
  have hcycle' : published ∈ ((application window).runPolicies players (serviceEnvironment selector)
      serviceCycle before).support := by
    simpa [serviceSchedule] using hcycle
  have hbeforeBoundary := service_game_invariants players selector hselector 1 before hbefore
  have hvalid := runPolicies_responseTimeValid players (serviceEnvironment selector)
    (serviceSchedule 1)
    (MessageApplication.PolicyExecution.initial (application window) (initial window)) before
    empty_responseTimeValid hbefore
  have hstrict := service_cycle_responseAt_lt_clock players selector before published
    (by have hh := hbeforeBoundary.2.1; omega) hvalid (by simp [hpublication]) hcycle'
  have hboundary := service_game_invariants players selector hselector 2 published hpublished
  have horigin := runPolicies_response_origin players (serviceEnvironment selector)
    (serviceSchedule (cycles - 2)) published next _ hpublication htail
  have hclock := service_schedule_clock players selector hselector (cycles - 2) published next
    (by have hh := hboundary.2.1; omega) htail
  refine ⟨by simp [horigin.1], ?_⟩
  rw [horigin.2, hclock]
  omega

/-- With a positive window, the unchanged owner guarantees a native outcome
by `window + 3` service cycles against every responder policy and admitted
inclusion selector. Its fixed source choices are described separately by
`owner_choices_preserved`. -/
theorem owner_settles_by_cycle (secret : Bool) (complete : Bool → Bool → Bool)
    (hwindow : 1 ≤ window)
    (players : TestPlayer → (application window).PlayerPolicy)
    (howner : players 0 = ownerPolicy (pureInitialDecision secret) (pureOpeningDecision complete))
    (selector : (application window).EnvironmentPolicy)
    (hselector : (application window).InclusionService (fun _ => True) selector)
    (cycles : Nat) (hcycles : window + 3 ≤ cycles)
    (next : (application window).PolicyExecution)
    (hnext : next ∈ ((serviceGame window cycles selector).play players).support) :
    next.native.application.outcome?.isSome = true := by
  have hfinalInvariant :=
    (service_game_invariants players selector hselector cycles next hnext).2.2.2
  rw [outcome_isSome_iff_response next.native.application hfinalInvariant]
  cases cycles with
  | zero => omega
  | succ cycles =>
      obtain ⟨before, hbefore, htail⟩ :=
        service_game_prefix players selector (cycles + 1) cycles (by omega) next hnext
      have htail' : next ∈ ((application window).runPolicies players (serviceEnvironment selector)
          serviceCycle before).support := by
        simpa [serviceSchedule] using htail
      obtain ⟨_, hhistory, hempty, hinvariant⟩ :=
        service_game_invariants players selector hselector cycles before hbefore
      have hoverdue := owner_response_overdue_by_cycle secret complete hwindow players howner
        selector hselector cycles (by omega) before hbefore
      apply owner_response_expiration_cycle secret complete players howner selector hselector
        before next (by omega) hempty hinvariant hoverdue.1 hoverdue.2 ?_ htail'
      intro hsubmitted
      rcases owner_response_expiration_submission secret complete players howner
          (serviceEnvironment selector) (serviceSchedule cycles) before hbefore
          ((responseExpirySubmitted_iff _).mp hsubmitted) with
        hresponded | ⟨_, hpending⟩
      · exact Or.inl hresponded
      · exact Or.inr hpending

/-- info: 'VegasTests.OptionalDisclosure.DisclosureState.owner_choices_preserved'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms owner_choices_preserved

/-- info: 'VegasTests.OptionalDisclosure.DisclosureState.owner_settles_by_cycle'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms owner_settles_by_cycle

end VegasTests.OptionalDisclosure.DisclosureState
