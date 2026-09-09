/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosureResponderService
import VegasTests.DisclosureFreshPublication
import VegasTests.DisclosureServiceSettlement

/-! # Initialized preservation of the responder's selected reply

At each service-cycle boundary an unresolved published choice has a fresh
response window. The next cycle serves the unchanged responder before any
expiration can select a default. Publication timing is unrestricted within
the admitted service, and the opposing owner's policy is arbitrary.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Interaction GameTheory.Math.Probability

variable {window : Nat}

private theorem responder_fresh_cycle_response_none
    (response : Bool → Option Bool → Bool)
    (players : TestPlayer → (application window).PlayerPolicy)
    (hresponder : players 1 = responderPolicy response)
    (selector : (application window).EnvironmentPolicy)
    (hselector : (application window).InclusionService (fun _ => True) selector)
    (cycles : Nat) (execution next : (application window).PolicyExecution)
    (hprefix : execution ∈ ((serviceGame window cycles selector).play players).support)
    (hpublication : execution.native.application.publication = none)
    (hresponse : execution.native.application.response = none)
    (hnext : next ∈ ((application window).runPolicies players (serviceEnvironment selector)
      serviceCycle execution).support) : next.native.application.response = none := by
  obtain ⟨_, hhistory, hempty, _⟩ :=
    service_game_invariants players selector hselector cycles execution hprefix
  have hphase : execution.environmentHistory.length % 13 = 0 := by omega
  obtain ⟨arrived, drained, harrived, hdrained, htail, _, hslots, htailPhase⟩ :=
    service_cycle_parts players selector execution next hphase hempty hnext
  have hpublic := (service_arrivals_public players selector execution arrived hphase harrived).1
  have harrivedInitialized : arrived ∈ ((application window).runPolicies players
      (serviceEnvironment selector) (serviceSchedule cycles ++ serviceArrivals)
      (MessageApplication.PolicyExecution.initial (application window)
        (initial window))).support := by
    rw [MessageApplication.runPolicies_append]
    simp only [FinDist.support_bind, Set.mem_iUnion]
    exact ⟨execution, hprefix, harrived⟩
  have hsafe := (responder_prePublication_provenance response players hresponder
    (serviceEnvironment selector) (serviceSchedule cycles ++ serviceArrivals) arrived
    harrivedInitialized ((congrArg PublicState.publication hpublic).trans hpublication)).2
  have hresolved := fresh_publication_phase_response_none players inclusionSlots
    (serviceEnvironment selector) (serviceEnvironment_inclusions selector hselector)
    8 arrived drained hslots
    ((congrArg PublicState.publication hpublic).trans hpublication)
    ((congrArg PublicState.response hpublic).trans hresponse) hsafe hdrained
  exact (service_tail_preserves_milestones players selector drained next htailPhase htail).2.2.trans
    hresolved

private def ResponderBoundary (response : Bool → Option Bool → Bool)
    (state : DisclosureState) : Prop :=
  (state.response = none ∨ ∃ signal publication,
    state.signal = some signal ∧ state.publication = some publication ∧
      state.response = some (response signal publication)) ∧
  (state.publication.isSome = true → state.response = none → state.clock ≤ state.responseAt + 1)

private theorem responder_service_boundary (response : Bool → Option Bool → Bool)
    (hwindow : 1 ≤ window)
    (players : TestPlayer → (application window).PlayerPolicy)
    (hresponder : players 1 = responderPolicy response)
    (selector : (application window).EnvironmentPolicy)
    (hselector : (application window).InclusionService (fun _ => True) selector)
    (cycles : Nat) (next : (application window).PolicyExecution)
    (hnext : next ∈ ((serviceGame window cycles selector).play players).support) :
    ResponderBoundary response next.native.application := by
  induction cycles generalizing next with
  | zero =>
      change next ∈ ((application window).runPolicies players (serviceEnvironment selector)
        [] (MessageApplication.PolicyExecution.initial (application window)
          (initial window))).support
        at hnext
      simp only [MessageApplication.runPolicies, FinDist.mem_support_pure] at hnext
      subst next
      simp [ResponderBoundary, MessageApplication.PolicyExecution.initial, initial,
        MessageApplication.State.initial, empty]
  | succ cycles ih =>
      obtain ⟨before, hbefore, htail⟩ :=
        service_game_prefix players selector (cycles + 1) cycles (by omega) next hnext
      have hcycle : next ∈ ((application window).runPolicies players (serviceEnvironment selector)
          serviceCycle before).support := by
        simpa [serviceSchedule] using htail
      have hboundary := ih before hbefore
      obtain ⟨_, hhistory, _, hinvariant⟩ :=
        service_game_invariants players selector hselector cycles before hbefore
      have hphase : before.environmentHistory.length % 13 = 0 := by omega
      cases hresponse : before.native.application.response with
      | some value =>
          rcases hboundary.1 with habsent | ⟨signal, publication, hsignal, hpublication, hchosen⟩
          · simp [hresponse] at habsent
          · have hfixed := runPolicies_response_fixed players (serviceEnvironment selector)
              serviceCycle before next _ hchosen hcycle
            exact ⟨Or.inr ⟨signal, publication,
                (runPolicies_signal_origin players (serviceEnvironment selector)
                  serviceCycle before next signal hsignal hcycle).1,
                (runPolicies_response_origin players (serviceEnvironment selector)
                  serviceCycle before next publication hpublication hcycle).1, hfixed⟩,
              by simp [hfixed]⟩
      | none =>
          cases hpublication : before.native.application.publication with
          | none =>
              have habsent := responder_fresh_cycle_response_none response players hresponder
                selector hselector cycles before next hbefore hpublication hresponse hcycle
              refine ⟨Or.inl habsent, ?_⟩
              intro hpublished _
              exact Nat.le_of_eq (service_cycle_fresh_publication players selector hselector
                before next hphase hpublication hpublished hcycle).symm
          | some publication =>
              have hsignalSome := hinvariant.2.2.2.1 (by simp [hpublication])
              obtain ⟨signal, hsignal⟩ := Option.isSome_iff_exists.mp hsignalSome
              have htimely := hboundary.2 (by simp [hpublication]) hresponse
              have hchosen := responder_response_cycle_choice response signal publication
                players hresponder selector hselector cycles before next hbefore hsignal
                hpublication hresponse (by omega) hcycle
              exact ⟨Or.inr ⟨signal, publication,
                  (runPolicies_signal_origin players (serviceEnvironment selector)
                    serviceCycle before next signal hsignal hcycle).1,
                  (runPolicies_response_origin players (serviceEnvironment selector)
                    serviceCycle before next publication hpublication hcycle).1, hchosen⟩,
                by simp [hchosen]⟩

/-- Every response resolved at an initialized service-cycle boundary is the
unchanged responder's selected reply to the actual public signal and publication.
This is choice preservation on supported runs, not a randomized outcome-law
or strategic backtranslation theorem. -/
theorem responder_choice_preserved (response : Bool → Option Bool → Bool)
    (hwindow : 1 ≤ window)
    (players : TestPlayer → (application window).PlayerPolicy)
    (hresponder : players 1 = responderPolicy response)
    (selector : (application window).EnvironmentPolicy)
    (hselector : (application window).InclusionService (fun _ => True) selector)
    (cycles : Nat) (next : (application window).PolicyExecution)
    (hnext : next ∈ ((serviceGame window cycles selector).play players).support) :
    next.native.application.response = none ∨ ∃ signal publication,
      next.native.application.signal = some signal ∧
        next.native.application.publication = some publication ∧
        next.native.application.response = some (response signal publication) :=
  (responder_service_boundary response hwindow players hresponder selector hselector
    cycles next hnext).1

/-- The unchanged responder reaches its selected reply by a uniform service
bound, from initialization and against every opposing owner policy. -/
theorem responder_settles_to_choice (response : Bool → Option Bool → Bool)
    (hwindow : 1 ≤ window)
    (players : TestPlayer → (application window).PlayerPolicy)
    (hresponder : players 1 = responderPolicy response)
    (selector : (application window).EnvironmentPolicy)
    (hselector : (application window).InclusionService (fun _ => True) selector)
    (cycles : Nat) (hcycles : 2 * window + 4 ≤ cycles)
    (next : (application window).PolicyExecution)
    (hnext : next ∈ ((serviceGame window cycles selector).play players).support) :
    ∃ signal publication,
      next.native.application.signal = some signal ∧
        next.native.application.publication = some publication ∧
        next.native.application.response = some (response signal publication) := by
  have hsettled := responder_settles_by_cycle response players hresponder selector hselector
    cycles hcycles next hnext
  rw [outcome_isSome_iff_response next.native.application
    (service_game_invariants players selector hselector cycles next hnext).2.2.2] at hsettled
  rcases responder_choice_preserved response hwindow players hresponder selector hselector
      cycles next hnext with hnone | hchosen
  · simp [hnone] at hsettled
  · exact hchosen

/-- info: 'VegasTests.OptionalDisclosure.DisclosureState.responder_choice_preserved'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms responder_choice_preserved

/-- info: 'VegasTests.OptionalDisclosure.DisclosureState.responder_settles_to_choice'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms responder_settles_to_choice

end VegasTests.OptionalDisclosure.DisclosureState
