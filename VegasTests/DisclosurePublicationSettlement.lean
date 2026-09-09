/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosurePublicationService
import VegasTests.DisclosureResponderHistory
import VegasTests.DisclosureServiceState
import VegasTests.DisclosureServiceTimeOrigins

/-! # Publication progress under the disclosure service

Once the public signal's deadline is overdue, the unchanged responder's next
service cycle resolves publication. Earlier one-shot submissions must be
accounted for by the native pending-or-resolved invariant.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Interaction GameTheory.Math.Probability

variable {window : Nat}

/-- A full service cycle resolves an overdue publication against arbitrary
owner traffic. The accounting premise is a local request-history obligation,
not an assumption that the cycle itself terminates the application. -/
theorem responder_publication_cycle (response : Bool → Option Bool → Bool)
    (players : TestPlayer → (application window).PlayerPolicy)
    (hresponder : players 1 = responderPolicy (pureResponseDecision response))
    (selector : (application window).EnvironmentPolicy)
    (hselector : (application window).InclusionService (fun _ => True) selector)
    (execution next : (application window).PolicyExecution)
    (hphase : execution.environmentHistory.length % 13 = 0)
    (hempty : execution.native.pool.pending = [])
    (hinvariant : Invariant execution.native.application)
    (hsignal : execution.native.application.signal.isSome = true)
    (hexpired : execution.native.application.signalAt + window < execution.native.application.clock)
    (haccounted : publicationExpirySubmitted (execution.principalHistory 1) = true →
      execution.native.application.publication.isSome = true ∨
        ∃ serial, ⟨(1, serial), Payload.publish 5 .expire⟩ ∈ execution.native.pool.pending)
    (hnext : next ∈ ((application window).runPolicies players (serviceEnvironment selector)
      serviceCycle execution).support) :
    next.native.application.publication.isSome = true := by
  obtain ⟨arrived, drained, harrived, hdrained, htail, hcapacity, hslots, htailPhase⟩ :=
    service_cycle_parts players selector execution next hphase hempty hnext
  have hpublic := service_arrivals_public players selector execution arrived hphase harrived
  have hpublished : drained.native.application.publication.isSome = true := by
    cases hpublication : execution.native.application.publication with
    | some result =>
        apply (application window).inclusion_phase_invariant
          (fun state => state.application.publication.isSome = true)
          include_publication_persists players inclusionSlots (serviceEnvironment selector)
          (serviceEnvironment_inclusions selector hselector)
          8 arrived drained hslots ?_ hdrained
        rw [show arrived.native.application.publication = execution.native.application.publication
          from congrArg PublicState.publication hpublic.1, hpublication]
        rfl
    | none =>
        have hnotSubmitted : publicationExpirySubmitted (execution.principalHistory 1) = false := by
          cases hflag : publicationExpirySubmitted (execution.principalHistory 1) with
          | false => rfl
          | true =>
              rcases haccounted hflag with hpublished | ⟨serial, hpending⟩
              · simp [hpublication] at hpublished
              · simp [hempty] at hpending
        have hresponse : execution.native.application.response = none := by
          cases hr : execution.native.application.response with
          | none => rfl
          | some value =>
              have hp := hinvariant.2.2.2.2.2 (by simp [hr])
              simp [hpublication] at hp
        have hbound := hinvariant.2.1 (hinvariant.2.2.1 hsignal)
        cases haccepted : execution.native.application.accepted with
        | none => simp [haccepted] at hbound
        | some binding =>
          cases hsignalState : execution.native.application.signal with
          | none => simp [hsignalState] at hsignal
          | some signal =>
            obtain ⟨serial, hpending⟩ := responder_publication_arrival response players hresponder
              selector execution arrived hphase binding signal haccepted hsignalState hpublication
              hresponse hexpired hnotSubmitted harrived
            apply publication_expiration_phase_resolves 1 serial players inclusionSlots
              (serviceEnvironment selector) (serviceEnvironment_inclusions selector hselector)
              8 arrived drained hslots hcapacity ?_ ?_ ?_ hpending hdrained
            · exact (application window).runPolicies_application_invariant Invariant
                privateStep_invariant (handle_invariant window) environmentStep_invariant
                players (serviceEnvironment selector) serviceArrivals execution arrived
                hinvariant harrived
            · rw [show arrived.native.application.signal = execution.native.application.signal from
                congrArg PublicState.signal hpublic.1]
              exact hsignal
            · rw [show arrived.native.application.signalAt = execution.native.application.signalAt
                from congrArg PublicState.signalAt hpublic.1,
                show arrived.native.application.clock = execution.native.application.clock from
                congrArg PublicState.clock hpublic.1]
              exact hexpired
  rw [(service_tail_preserves_milestones players selector drained next htailPhase htail).2.1]
  exact hpublished

/-- From actual initialization, an unchanged responder resolves publication
by cycle `2 * window + 3`, against every owner policy and every admitted
adaptive inclusion selector. The result includes earlier one-shot submissions
and does not assume any particular publication value. -/
theorem responder_publication_by_cycle (response : Bool → Option Bool → Bool)
    (players : TestPlayer → (application window).PlayerPolicy)
    (hresponder : players 1 = responderPolicy (pureResponseDecision response))
    (selector : (application window).EnvironmentPolicy)
    (hselector : (application window).InclusionService (fun _ => True) selector)
    (cycles : Nat) (hcycles : 2 * window + 3 ≤ cycles)
    (next : (application window).PolicyExecution)
    (hnext : next ∈ ((serviceGame window cycles selector).play players).support) :
    next.native.application.publication.isSome = true := by
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
      obtain ⟨signal, hsignal, hexpired⟩ := responder_signal_overdue_by_cycle response players
        hresponder selector hselector cycles (by omega) before hbefore
      apply responder_publication_cycle response players hresponder selector hselector before next
        (by omega) hempty hinvariant (by simp [hsignal]) hexpired ?_ htail'
      intro hsubmitted
      have hexact := publicationExpirySubmitted_exact (before.principalHistory 1) hsubmitted
      rcases responder_publication_expiration_submission response players hresponder
          (serviceEnvironment selector) (serviceSchedule cycles) before hbefore hexact with
        hpublished | ⟨_, hpending⟩
      · exact Or.inl hpublished
      · exact Or.inr hpending

/-- info: 'VegasTests.OptionalDisclosure.DisclosureState.responder_publication_by_cycle'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms responder_publication_by_cycle

end VegasTests.OptionalDisclosure.DisclosureState
