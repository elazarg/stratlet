/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosureServiceArrivals
import VegasTests.DisclosureServiceMilestones
import VegasTests.DisclosureServiceState
import Interaction.MessageApplicationSubmission

/-! # Initial-choice progress under the disclosure service

The unchanged responder submits permissionless expiration after the initial
deadline. Service includes a pending resolver even among arbitrary owner traffic,
and the fixed tail executes the marker and public chance kernel. A history
accounting invariant is needed when the one-shot request was submitted earlier.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Interaction GameTheory.Math.Probability

variable {window : Nat}

theorem environmentStep_clock_mono (state next : DisclosureState)
    (command : EnvironmentCommand)
    (hnext : next ∈ (environmentStep state command).support) : state.clock ≤ next.clock := by
  cases command with
  | marker =>
      simp only [environmentStep, FinDist.mem_support_pure] at hnext
      split at hnext <;> subst next <;> exact Nat.le_refl _
  | sample =>
      simp only [environmentStep] at hnext
      split at hnext
      · simp only [FinDist.support_map, Set.mem_image] at hnext
        obtain ⟨signal, _, rfl⟩ := hnext
        exact Nat.le_refl _
      · simp only [FinDist.mem_support_pure] at hnext
        subst next
        exact Nat.le_refl _
  | advance clock =>
      simp only [environmentStep, FinDist.mem_support_pure] at hnext
      split at hnext
      · subst next
        assumption
      · subst next
        exact Nat.le_refl _

theorem responder_initial_emit_ready (response : Bool → Option Bool → Bool)
    (history : List (application window).PlayerEntry) (view : (application window).View)
    (hemit : .submit Payload.expireInitial ∈ (responderPolicy response history view).support) :
    view.application.accepted = none ∧ window < view.application.clock := by
  unfold responderPolicy at hemit
  simp only [FinDist.mem_support_pure] at hemit
  split at hemit <;> try contradiction
  split at hemit
  · rename_i haccepted
    split at hemit <;> try contradiction
    rename_i hexpired
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hexpired
    exact ⟨haccepted, hexpired.1⟩
  · split at hemit
    · split at hemit <;> cases hemit
    · split at hemit <;> cases hemit
    · cases hemit

theorem initialExpirySubmitted_iff (history : List (application window).PlayerEntry) :
    initialExpirySubmitted history = true ↔
      (application window).SubmittedPayload Payload.expireInitial history := by
  simp only [initialExpirySubmitted, MessageApplication.SubmittedPayload, List.any_eq_true]
  apply exists_congr
  intro entry
  apply and_congr_right
  intro _
  cases hcommand : entry.command with
  | submit payload => cases payload <;> simp
  | privateCommand command | replay id | wait => simp

/-- The unchanged responder's command history accounts for its initial
expiration in every native policy run. No fairness or invocation assumption is
used: after submission, the authored request is pending or binding has resolved. -/
theorem responder_initial_submission (response : Bool → Option Bool → Bool)
    (players : TestPlayer → (application window).PlayerPolicy)
    (hresponder : players 1 = responderPolicy response)
    (environment : (application window).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation TestPlayer))
    (next : (application window).PolicyExecution)
    (hnext : next ∈ ((application window).runPolicies players environment schedule
      (MessageApplication.PolicyExecution.initial (application window) (initial window))).support)
    (hsubmitted : initialExpirySubmitted (next.principalHistory 1) = true) :
    next.native.application.accepted.isSome = true ∨
      ((next.native.application.accepted = none ∧ window < next.native.application.clock) ∧
        ∃ serial, ⟨(1, serial), Payload.expireInitial⟩ ∈ next.native.pool.pending) := by
  apply (application window).runPolicies_submitted_pendingOrResolved
    Invariant (fun state => state.accepted = none ∧ window < state.clock)
    (fun state => state.accepted.isSome = true) 1 Payload.expireInitial players environment
    privateStep_invariant (handle_invariant window) environmentStep_invariant
    (fun _ _ _ hstate => hstate) (fun _ _ _ hstate => Or.inl hstate)
    ?_ ?_ ?_ ?_ ?_ ?_ schedule
    (MessageApplication.PolicyExecution.initial (application window) (initial window)) next
    empty_invariant
    (by simp [MessageApplication.SubmittedPayload, MessageApplication.PolicyExecution.initial])
    hnext ((initialExpirySubmitted_iff _).mp hsubmitted)
  · intro state message final hbound hhandle
    rw [(handle_binding window state message final hbound hhandle).1]
    exact hbound
  · intro state message final hready hhandle
    have hclock := handle_clock state final message hhandle
    cases haccepted : final.accepted with
    | none => exact Or.inl ⟨rfl, by rw [hclock]; exact hready.2⟩
    | some binding => exact Or.inr rfl
  · intro state command final hbound hfinal
    rw [(environmentStep_binding state command final hfinal).1]
    exact hbound
  · intro state command final hready hfinal
    refine Or.inl ⟨(environmentStep_binding state command final hfinal).1.trans hready.1, ?_⟩
    exact hready.2.trans_le (environmentStep_clock_mono state final command hfinal)
  · intro state serial hready
    exact ⟨{ state with accepted := some (.publicDefault false) },
      expireInitial_accepts window state 1 serial hready.1 hready.2, rfl⟩
  · intro execution command _ hcommand hemit
    subst command
    rw [hresponder] at hcommand
    exact responder_initial_emit_ready response (execution.principalHistory 1)
      (MessageApplication.State.observe (application window) execution.native 1) hcommand

private theorem initial_absence_response (state : DisclosureState)
    (hinvariant : Invariant state) (haccepted : state.accepted = none) : state.response = none := by
  cases hresponse : state.response with
  | none => rfl
  | some value =>
      have hbound := hinvariant.2.1 (hinvariant.2.2.1
        (hinvariant.2.2.2.1 (hinvariant.2.2.2.2.2 (by simp [hresponse]))))
      simp [haccepted] at hbound

/-- Once the initial deadline is overdue, one full cycle establishes the
binding and signal if any earlier one-shot expiration remains accounted for.
The owner and the admitted inclusion selector may both be adversarial. -/
theorem responder_initial_cycle (response : Bool → Option Bool → Bool)
    (players : TestPlayer → (application window).PlayerPolicy)
    (hresponder : players 1 = responderPolicy response)
    (selector : (application window).EnvironmentPolicy)
    (hselector : (application window).InclusionService (fun _ => True) selector)
    (execution next : (application window).PolicyExecution)
    (hphase : execution.environmentHistory.length % 13 = 0)
    (hempty : execution.native.pool.pending = [])
    (hinvariant : Invariant execution.native.application)
    (hexpired : window < execution.native.application.clock)
    (haccounted : initialExpirySubmitted (execution.principalHistory 1) = true →
      execution.native.application.accepted.isSome = true ∨
        ∃ serial, ⟨(1, serial), Payload.expireInitial⟩ ∈ execution.native.pool.pending)
    (hnext : next ∈ ((application window).runPolicies players (serviceEnvironment selector)
      serviceCycle execution).support) :
    next.native.application.accepted.isSome = true ∧
      next.native.application.markerDone = true ∧ next.native.application.signal.isSome = true := by
  rw [serviceCycle, MessageApplication.runPolicies_append] at hnext
  simp only [FinDist.support_bind, Set.mem_iUnion] at hnext
  obtain ⟨arrived, harrived, hnext⟩ := hnext
  rw [MessageApplication.runPolicies_append] at hnext
  simp only [FinDist.support_bind, Set.mem_iUnion] at hnext
  obtain ⟨drained, hdrained, hnext⟩ := hnext
  have hpublic := service_arrivals_public players selector execution arrived hphase harrived
  have hcapacity := service_arrival_bound players selector execution arrived hempty harrived
  have harrivalHistory := (application window).runPolicies_environmentHistory_length players
    (serviceEnvironment selector) serviceArrivals execution arrived harrived
  have harrivalCount : serviceArrivals.countP MessageApplication.Invocation.isEnvironment = 2 :=
    by decide
  rw [harrivalCount] at harrivalHistory
  have hslots : ∀ offset < 8, inclusionSlots (arrived.environmentHistory.length + offset) := by
    intro offset hoffset
    dsimp [inclusionSlots]
    omega
  have hbound : drained.native.application.accepted.isSome = true := by
    cases haccepted : execution.native.application.accepted with
    | some binding =>
        apply (application window).inclusion_phase_invariant
          (fun state => state.application.accepted.isSome = true)
          include_binding_persists players inclusionSlots (serviceEnvironment selector)
          (serviceEnvironment_inclusions selector hselector)
          8 arrived drained hslots ?_ hdrained
        rw [show arrived.native.application.accepted = execution.native.application.accepted from
          congrArg PublicState.accepted hpublic.1, haccepted]
        rfl
    | none =>
        have hnotSubmitted : initialExpirySubmitted (execution.principalHistory 1) = false := by
          cases hflag : initialExpirySubmitted (execution.principalHistory 1) with
          | false => rfl
          | true =>
              rcases haccounted hflag with hbound | ⟨serial, hpending⟩
              · simp [haccepted] at hbound
              · simp [hempty] at hpending
        obtain ⟨serial, hpending⟩ := responder_initial_arrival response players hresponder selector
          execution arrived hphase haccepted
          (initial_absence_response execution.native.application hinvariant haccepted)
          hexpired hnotSubmitted harrived
        apply initial_expiration_phase_resolves 1 serial players inclusionSlots
          (serviceEnvironment selector) (serviceEnvironment_inclusions selector hselector)
          8 arrived drained hslots hcapacity ?_ hpending hdrained
        rw [show arrived.native.application.clock = execution.native.application.clock from
          congrArg PublicState.clock hpublic.1]
        exact hexpired
  have hdrainHistory := (application window).runPolicies_environmentHistory_length players
    (serviceEnvironment selector) (List.replicate 8 .environment) arrived drained hdrained
  have hdrainCount :
      (List.replicate 8 (@MessageApplication.Invocation.environment TestPlayer)).countP
        MessageApplication.Invocation.isEnvironment = 8 := by decide
  rw [hdrainCount] at hdrainHistory
  have htailPhase : drained.environmentHistory.length % 13 = 10 := by omega
  have hpreserved :=
    service_tail_preserves_milestones players selector drained next htailPhase hnext
  exact ⟨by rw [hpreserved.1]; exact hbound,
    service_tail_establishes_marker_signal players selector drained next htailPhase hbound hnext⟩

/-- From the actual game initialization, an unchanged responder guarantees
initial binding and the public signal by cycle `window + 2`, against every
owner policy and every admitted adaptive inclusion selector. This is the first
application milestone, not complete disclosure/response settlement. -/
theorem responder_initial_by_cycle (response : Bool → Option Bool → Bool)
    (players : TestPlayer → (application window).PlayerPolicy)
    (hresponder : players 1 = responderPolicy response)
    (selector : (application window).EnvironmentPolicy)
    (hselector : (application window).InclusionService (fun _ => True) selector)
    (cycles : Nat) (hcycles : window + 2 ≤ cycles)
    (next : (application window).PolicyExecution)
    (hnext : next ∈ ((serviceGame window cycles selector).play players).support) :
    next.native.application.accepted.isSome = true ∧
      next.native.application.markerDone = true ∧ next.native.application.signal.isSome = true := by
  cases cycles with
  | zero => omega
  | succ cycles =>
      have hschedule : serviceSchedule (cycles + 1) = serviceSchedule cycles ++ serviceCycle := by
        simp [serviceSchedule, List.replicate_succ']
      change next ∈ ((application window).runPolicies players (serviceEnvironment selector)
        (serviceSchedule (cycles + 1))
        (MessageApplication.PolicyExecution.initial (application window) (initial window))).support
        at hnext
      rw [hschedule, MessageApplication.runPolicies_append] at hnext
      simp only [FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨before, hbefore, hnext⟩ := hnext
      obtain ⟨hclock, hhistory, hempty, hinvariant⟩ :=
        service_game_invariants players selector hselector cycles before hbefore
      apply responder_initial_cycle response players hresponder selector hselector before next
        (by omega) hempty hinvariant (by omega) ?_ hnext
      intro hsubmitted
      rcases responder_initial_submission response players hresponder (serviceEnvironment selector)
          (serviceSchedule cycles) before hbefore hsubmitted with hbound | ⟨_, hpending⟩
      · exact Or.inl hbound
      · exact Or.inr hpending

/-- info: 'VegasTests.OptionalDisclosure.DisclosureState.responder_initial_by_cycle'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.DisclosureState.responder_initial_by_cycle

end VegasTests.OptionalDisclosure.DisclosureState
