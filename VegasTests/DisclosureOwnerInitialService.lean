/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosureOwnerArrivals
import VegasTests.DisclosureOwnerProvenance
import VegasTests.DisclosureServiceTimeOrigins

/-! # Exact initialized owner binding under public service

The owner's first serviced cycle binds its selected secret and samples the
source signal. Arbitrary responder traffic cannot substitute an initial
default, and no publication occurs before the next cycle's player invocations.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Interaction GameTheory.Math.Probability

variable {window : Nat}

private theorem publication_none_before_signal (state : DisclosureState)
    (hinvariant : Invariant state) (hsignal : state.signal = none) :
    state.publication = none ∧ state.response = none := by
  have hpublication : state.publication = none := by
    cases hpublished : state.publication with
    | none => rfl
    | some result =>
        have hs := hinvariant.2.2.2.1 (by simp [hpublished])
        simp [hsignal] at hs
  refine ⟨hpublication, ?_⟩
  cases hresponse : state.response with
  | none => rfl
  | some result =>
      have hp := hinvariant.2.2.2.2.2 (by simp [hresponse])
      simp [hpublication] at hp

/-- The first complete service cycle binds the unchanged owner's actual
secret and establishes the public signal. The result holds for every responder
policy and every admitted inclusion selector, even when the window is zero. -/
theorem owner_initial_cycle (secret : Bool) (complete : Bool → Bool → Bool)
    (players : TestPlayer → (application window).PlayerPolicy)
    (howner : players 0 = ownerPolicy (pureInitialDecision secret) (pureOpeningDecision complete))
    (selector : (application window).EnvironmentPolicy)
    (hselector : (application window).InclusionService (fun _ => True) selector)
    (next : (application window).PolicyExecution)
    (hnext : next ∈ ((serviceGame window 1 selector).play players).support) :
    next.native.application.accepted = some (.commitment (0, 0)) ∧
      next.native.application.acceptedService.lookup (0, 0) = some secret ∧
      next.native.application.markerDone = true ∧
      next.native.application.signal.isSome = true ∧
      next.native.application.signalAt = 0 ∧ next.native.application.clock = 1 ∧
      next.native.application.publication = none ∧ next.native.application.response = none ∧
      openingSubmitted (next.principalHistory 0) = false ∧
      next.native.pool.Satisfies OwnerPreSignalMessage ∧
      initialCachedValue window (next.principalHistory 0) = some secret := by
  have hwhole : next ∈ ((application window).runPolicies players (serviceEnvironment selector)
      serviceCycle
      (MessageApplication.PolicyExecution.initial (application window) (initial window))).support :=
    by simpa [serviceGame, MessageApplication.policyGame, serviceSchedule] using hnext
  have hclock := (service_game_invariants players selector hselector 1 next hnext).1
  obtain ⟨arrived, drained, harrived, hdrained, htail, hcapacity, hslots, htailPhase⟩ :=
    service_cycle_parts players selector
      (MessageApplication.PolicyExecution.initial (application window) (initial window)) next
      rfl rfl hwhole
  obtain ⟨hstored, hpending, hpublic, hcache⟩ :=
    owner_initial_arrival secret complete players howner selector arrived harrived
  have hinvariant := policy_invariant window players (serviceEnvironment selector)
    serviceArrivals arrived harrived
  have hprovenance := owner_preSignal_provenance secret complete players howner
    (serviceEnvironment selector) serviceArrivals arrived harrived
    (congrArg PublicState.signal hpublic)
  have hbound := owner_binding_phase_resolves secret 0 players inclusionSlots
    (serviceEnvironment selector) (serviceEnvironment_inclusions selector hselector)
    8 arrived drained hslots hcapacity hstored
    (congrArg PublicState.accepted hpublic) (by
      have hz := congrArg PublicState.clock hpublic
      change arrived.native.application.clock = 0 at hz
      omega) hpending hdrained
  have hbeforeSignal : Invariant drained.native.application ∧
      drained.native.application.signal = none := by
    apply (application window).inclusion_phase_invariant
      (fun state => Invariant state.application ∧ state.application.signal = none)
      (fun state id hstate => ⟨include_native_invariant state id hstate.1,
        (include_signal_fixed state id).1.trans hstate.2⟩)
      players inclusionSlots (serviceEnvironment selector)
      (serviceEnvironment_inclusions selector hselector) 8 arrived drained hslots
      ⟨hinvariant, congrArg PublicState.signal hpublic⟩ hdrained
  have hnone := publication_none_before_signal drained.native.application
    hbeforeSignal.1 hbeforeSignal.2
  have hmilestone := service_tail_establishes_marker_signal players selector drained next
    htailPhase (by simp [hbound.1]) htail
  have hpreserved :=
    service_tail_preserves_milestones players selector drained next htailPhase htail
  obtain ⟨actions, _, hnative⟩ := (application window).runPolicies_native_support players
    (serviceEnvironment selector) (List.replicate 3 .environment) drained next htail
  have hbinding := run_binding window drained.native next.native actions
    (by simp [hbound.1]) hnative
  have horigin := service_cycle_signalAt_lt_clock players selector
    (MessageApplication.PolicyExecution.initial (application window) (initial window)) next
    rfl empty_signalTimeValid hmilestone.2 hwhole
  have henvironment : next ∈ ((application window).runPolicies players
      (serviceEnvironment selector) (List.replicate 11 .environment) arrived).support := by
    change next ∈ ((application window).runPolicies players (serviceEnvironment selector)
      (List.replicate 8 .environment ++ List.replicate 3 .environment) arrived).support
    rw [MessageApplication.runPolicies_append]
    simp only [FinDist.support_bind, Set.mem_iUnion]
    exact ⟨drained, hdrained, htail⟩
  have hhistory := (application window).runPolicies_environment_principalHistory players
    (serviceEnvironment selector) 11 arrived next henvironment
  refine ⟨hbinding.1.trans hbound.1, ?_, hmilestone.1, hmilestone.2, by omega, hclock,
    hpreserved.2.1.trans hnone.1, hpreserved.2.2.trans hnone.2, ?_, ?_, ?_⟩
  · rw [hbinding.2]
    exact hbound.2
  · rw [hhistory]
    exact hprovenance.1
  · exact (application window).runPolicies_environment_pool_satisfies OwnerPreSignalMessage
      players (serviceEnvironment selector) 11 arrived next hprovenance.2 henvironment
  · rw [hhistory]
    exact hcache

/-- info: 'VegasTests.OptionalDisclosure.DisclosureState.owner_initial_cycle'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms owner_initial_cycle

end VegasTests.OptionalDisclosure.DisclosureState
