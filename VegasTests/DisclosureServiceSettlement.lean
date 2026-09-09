/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosurePublicationSettlement
import VegasTests.DisclosureResponseService

/-! # Initialized settlement under the public disclosure service

The unchanged responder drives the owner's timeout branches and supplies the
final response. Every supported initialized run therefore has an outcome by a
uniform cycle bound, even with an arbitrary owner and payload-sensitive adaptive
inclusion choices. This is termination, not unchanged-choice or outcome-law
preservation.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Interaction GameTheory.Math.Probability

variable {window : Nat}

/-- Every owner deviation settles against the unchanged responder by
`2 * window + 4` complete service cycles. The clock, pending requests, and
controller history all start at the actual initialized game state. No
positive-window premise is needed for this termination statement. -/
theorem responder_settles_by_cycle (response : Bool → Option Bool → Bool)
    (players : TestPlayer → (application window).PlayerPolicy)
    (hresponder : players 1 = responderPolicy response)
    (selector : (application window).EnvironmentPolicy)
    (hselector : (application window).InclusionService (fun _ => True) selector)
    (cycles : Nat) (hcycles : 2 * window + 4 ≤ cycles)
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
      have hpublication := responder_publication_by_cycle response players hresponder selector
        hselector cycles (by omega) before hbefore
      apply responder_response_cycle response players hresponder selector hselector before next
        (by omega) hempty hinvariant hpublication ?_ htail'
      intro hsubmitted
      obtain ⟨entry, hentry, signal, publication, _, _, hcommand⟩ :=
        responder_responseSubmitted_exact response players hresponder (serviceEnvironment selector)
          (serviceSchedule cycles) before hbefore hsubmitted
      have hexact : (application window).SubmittedPayload
          (.respond (response signal publication)) (before.principalHistory 1) :=
        ⟨entry, hentry, hcommand⟩
      rcases responder_response_submission response (response signal publication) players hresponder
          (serviceEnvironment selector) (serviceSchedule cycles) before hbefore hexact with
        hresponded | ⟨_, serial, hpending⟩
      · exact Or.inl hresponded
      · exact Or.inr ⟨response signal publication, serial, hpending⟩

/-- info: 'VegasTests.OptionalDisclosure.DisclosureState.responder_settles_by_cycle'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms responder_settles_by_cycle

end VegasTests.OptionalDisclosure.DisclosureState
