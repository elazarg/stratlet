/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosureResponseService
import VegasTests.DisclosureServiceState

/-! # Owner response-expiration accounting -/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Interaction GameTheory.Math.Probability

variable {window : Nat}

private def ResponseExpiryReady (window : Nat) (state : DisclosureState) : Prop :=
  Invariant state ∧ state.publication.isSome = true ∧ state.response = none ∧
    state.responseAt + window < state.clock

private theorem environmentStep_responseAt_fixed_of_publication
    (state next : DisclosureState) (command : EnvironmentCommand)
    (hpublication : state.publication.isSome = true)
    (hnext : next ∈ (environmentStep state command).support) :
    next.responseAt = state.responseAt := by
  cases publicationState : state.publication with
  | none => simp [publicationState] at hpublication
  | some publication =>
      cases command with
      | marker | advance clock =>
          simp only [environmentStep, FinDist.mem_support_pure] at hnext
          split at hnext <;> subst next <;> rfl
      | sample =>
          simp only [environmentStep] at hnext
          split at hnext
          · simp only [FinDist.support_map, Set.mem_image] at hnext
            obtain ⟨signal, _, rfl⟩ := hnext
            rfl
          · simp only [FinDist.mem_support_pure] at hnext
            subst next
            rfl

private theorem environmentStep_response_fixed (state next : DisclosureState)
    (command : EnvironmentCommand)
    (hnext : next ∈ (environmentStep state command).support) :
    next.response = state.response := by
  cases command with
  | marker | advance clock =>
      simp only [environmentStep, FinDist.mem_support_pure] at hnext
      split at hnext <;> subst next <;> rfl
  | sample =>
      simp only [environmentStep] at hnext
      split at hnext
      · simp only [FinDist.support_map, Set.mem_image] at hnext
        obtain ⟨signal, _, rfl⟩ := hnext
        rfl
      · simp only [FinDist.mem_support_pure] at hnext
        subst next
        rfl

private theorem owner_response_expiry_emit_ready (secret : Bool)
    (complete : Bool → Bool → Bool)
    (history : List (application window).PlayerEntry)
    (view : (application window).View)
    (hemit : .submit .expireResponse ∈
      (ownerPolicy secret complete history view).support) :
    view.application.publication.isSome = true ∧
      view.application.response = none ∧
      view.application.responseAt + window < view.application.clock := by
  unfold ownerPolicy at hemit
  simp only [FinDist.mem_support_pure] at hemit
  split at hemit
  · contradiction
  · split at hemit
    · split at hemit
      · contradiction
      · split at hemit <;> simp_all
    · split at hemit
      · contradiction
      · split at hemit
        · split at hemit
          · contradiction
          · split at hemit
            · split at hemit <;> simp_all
            · split at hemit <;> simp_all
        · split at hemit
          · rename_i hexpired
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hexpired
            simp_all
          · contradiction

theorem responseExpirySubmitted_iff (history : List (application window).PlayerEntry) :
    responseExpirySubmitted history = true ↔
      (application window).SubmittedPayload Payload.expireResponse history := by
  simp only [responseExpirySubmitted, MessageApplication.SubmittedPayload, List.any_eq_true]
  apply exists_congr
  intro entry
  apply and_congr_right
  intro _
  cases hcommand : entry.command with
  | submit payload => cases payload <;> simp
  | privateCommand command | replay id | wait => simp

/-- An exact owner-authored response expiration in history is either already
resolved or remains pending at the same overdue response checkpoint. -/
theorem owner_response_expiration_submission (secret : Bool)
    (complete : Bool → Bool → Bool)
    (players : TestPlayer → (application window).PlayerPolicy)
    (howner : players 0 = ownerPolicy secret complete)
    (environment : (application window).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation TestPlayer))
    (next : (application window).PolicyExecution)
    (hnext : next ∈ ((application window).runPolicies players environment schedule
      (MessageApplication.PolicyExecution.initial (application window) (initial window))).support)
    (hsubmitted : (application window).SubmittedPayload .expireResponse
      (next.principalHistory 0)) :
    next.native.application.response.isSome = true ∨
      ((Invariant next.native.application ∧
          next.native.application.publication.isSome = true ∧
          next.native.application.response = none ∧
          next.native.application.responseAt + window < next.native.application.clock) ∧
        ∃ serial, ⟨(0, serial), Payload.expireResponse⟩ ∈ next.native.pool.pending) := by
  apply (application window).runPolicies_submitted_pendingOrResolved
    Invariant (ResponseExpiryReady window) (fun state => state.response.isSome = true)
    0 .expireResponse players environment
    privateStep_invariant (handle_invariant window) environmentStep_invariant
    (fun _ _ _ hstate => hstate)
    (fun state actor command hstate => Or.inl ⟨
      privateStep_invariant state actor command hstate.1,
      by simpa [application, privateStep] using hstate.2⟩)
    ?_ ?_ ?_ ?_ ?_ ?_ schedule
    (MessageApplication.PolicyExecution.initial (application window) (initial window)) next
    empty_invariant
    (by simp [MessageApplication.SubmittedPayload, MessageApplication.PolicyExecution.initial])
    hnext hsubmitted
  · intro state message final hresponded hhandle
    cases responseState : state.response with
    | none => simp [responseState] at hresponded
    | some value =>
        rw [handle_response_fixed state final message value responseState hhandle]
        exact hresponded
  · intro state message final hready hhandle
    change DisclosureState at state final
    have hinvariant := handle_invariant window state message final hready.1 hhandle
    cases responseState : final.response with
    | some value => exact Or.inr (by simp)
    | none =>
        have hfixed := by
          cases publicationState : state.publication with
          | none =>
              have hpublication := hready.2.1
              simp [publicationState] at hpublication
          | some publication =>
              exact handle_publication_fixed window state message final publication
                publicationState hhandle
        refine Or.inl ⟨hinvariant, by rw [hfixed.1]; exact hready.2.1,
          responseState, ?_⟩
        rw [hfixed.2, handle_clock state final message hhandle]
        exact hready.2.2.2
  · intro state command final hresponded hfinal
    change DisclosureState at state final
    rw [environmentStep_response_fixed state final command hfinal]
    exact hresponded
  · intro state command final hready hfinal
    change DisclosureState at state final
    have hinvariant := environmentStep_invariant state command final hready.1 hfinal
    refine Or.inl ⟨hinvariant, ?_, ?_, ?_⟩
    · rw [environmentStep_publication state final command hfinal]
      exact hready.2.1
    · rw [environmentStep_response_fixed state final command hfinal]
      exact hready.2.2.1
    · rw [environmentStep_responseAt_fixed_of_publication state final command
        hready.2.1 hfinal]
      exact hready.2.2.2.trans_le (environmentStep_clock_mono state final command hfinal)
  · intro state serial hready
    change DisclosureState at state
    have hresponseReady := response_ready_of_publication state hready.1
      hready.2.1 hready.2.2.1
    refine ⟨{ state with response := some false }, ?_, by simp⟩
    change handle window state ⟨(0, serial), .expireResponse⟩ =
      some { state with response := some false }
    simp [handle, hresponseReady, hready.2.2.2]
  · intro execution command hinvariant hcommand hemit
    subst command
    rw [howner] at hcommand
    exact ⟨hinvariant, owner_response_expiry_emit_ready secret complete
      (execution.principalHistory 0)
      (MessageApplication.State.observe (application window) execution.native 0) hcommand⟩

private theorem owner_response_expiry_arrival (secret : Bool)
    (complete : Bool → Bool → Bool)
    (players : TestPlayer → (application window).PlayerPolicy)
    (howner : players 0 = ownerPolicy secret complete)
    (selector : (application window).EnvironmentPolicy)
    (execution next : (application window).PolicyExecution)
    (hphase : execution.environmentHistory.length % 13 = 0)
    (hinvariant : Invariant execution.native.application)
    (hpublication : execution.native.application.publication.isSome = true)
    (hresponse : execution.native.application.response = none)
    (hexpired : execution.native.application.responseAt + window <
      execution.native.application.clock)
    (hnotSubmitted : responseExpirySubmitted (execution.principalHistory 0) = false)
    (hnext : next ∈ ((application window).runPolicies players (serviceEnvironment selector)
      serviceArrivals execution).support) :
    ∃ serial, ⟨(0, serial), Payload.expireResponse⟩ ∈ next.native.pool.pending := by
  have hsignal := hinvariant.2.2.2.1 hpublication
  cases acceptedState : execution.native.application.accepted with
  | none =>
      have haccepted := hinvariant.2.1 (hinvariant.2.2.1 hsignal)
      simp [acceptedState] at haccepted
  | some binding =>
    cases signalState : execution.native.application.signal with
    | none => simp [signalState] at hsignal
    | some signal =>
      cases publicationState : execution.native.application.publication with
      | none => simp [publicationState] at hpublication
      | some publication =>
        apply service_owner_arrival .expireResponse players selector execution next hphase ?_ hnext
        rw [howner]
        exact owner_expires_response secret signal complete
          (execution.principalHistory 0)
          (MessageApplication.State.observe (application window) execution.native 0)
          binding publication acceptedState signalState publicationState hresponse
          hexpired hnotSubmitted

/-- An overdue unresolved response is settled by one service cycle when the
owner controller is unchanged and its earlier one-shot expiry is accounted. -/
theorem owner_response_expiration_cycle (secret : Bool)
    (complete : Bool → Bool → Bool)
    (players : TestPlayer → (application window).PlayerPolicy)
    (howner : players 0 = ownerPolicy secret complete)
    (selector : (application window).EnvironmentPolicy)
    (hselector : (application window).InclusionService (fun _ => True) selector)
    (execution next : (application window).PolicyExecution)
    (hphase : execution.environmentHistory.length % 13 = 0)
    (hempty : execution.native.pool.pending = [])
    (hinvariant : Invariant execution.native.application)
    (hpublication : execution.native.application.publication.isSome = true)
    (hexpired : execution.native.application.responseAt + window <
      execution.native.application.clock)
    (haccounted : responseExpirySubmitted (execution.principalHistory 0) = true →
      execution.native.application.response.isSome = true ∨
        ∃ serial, ⟨(0, serial), Payload.expireResponse⟩ ∈ execution.native.pool.pending)
    (hnext : next ∈ ((application window).runPolicies players (serviceEnvironment selector)
      serviceCycle execution).support) :
    next.native.application.response.isSome = true := by
  obtain ⟨arrived, drained, harrived, hdrained, htail, hcapacity, hslots, htailPhase⟩ :=
    service_cycle_parts players selector execution next hphase hempty hnext
  have hpublic := service_arrivals_public players selector execution arrived hphase harrived
  have hresolved : drained.native.application.response.isSome = true := by
    cases responseState : execution.native.application.response with
    | some value =>
        apply (application window).inclusion_phase_invariant
          (fun state => state.application.response.isSome = true)
          include_response_persists players inclusionSlots (serviceEnvironment selector)
          (serviceEnvironment_inclusions selector hselector)
          8 arrived drained hslots ?_ hdrained
        rw [show arrived.native.application.response = execution.native.application.response
          from congrArg PublicState.response hpublic.1, responseState]
        rfl
    | none =>
        have hpending : ∃ serial,
            ⟨(0, serial), Payload.expireResponse⟩ ∈ arrived.native.pool.pending := by
          cases hflag : responseExpirySubmitted (execution.principalHistory 0) with
          | true =>
              rcases haccounted hflag with hresolved | ⟨serial, hpending⟩
              · simp [responseState] at hresolved
              · simp [hempty] at hpending
          | false =>
              exact owner_response_expiry_arrival secret complete players howner
                selector execution arrived hphase hinvariant hpublication responseState
                hexpired hflag harrived
        obtain ⟨serial, hpending⟩ := hpending
        apply response_expiration_phase_resolves 0 serial players inclusionSlots
          (serviceEnvironment selector) (serviceEnvironment_inclusions selector hselector)
          8 arrived drained hslots hcapacity ?_ ?_ ?_ hpending hdrained
        · exact (application window).runPolicies_application_invariant Invariant
            privateStep_invariant (handle_invariant window) environmentStep_invariant
            players (serviceEnvironment selector) serviceArrivals execution arrived
            hinvariant harrived
        · rw [show arrived.native.application.publication =
              execution.native.application.publication from
              congrArg PublicState.publication hpublic.1]
          exact hpublication
        · rw [show arrived.native.application.responseAt = execution.native.application.responseAt
              from congrArg PublicState.responseAt hpublic.1,
              show arrived.native.application.clock = execution.native.application.clock from
              congrArg PublicState.clock hpublic.1]
          exact hexpired
  rw [(service_tail_preserves_milestones players selector drained next htailPhase htail).2.2]
  exact hresolved

end VegasTests.OptionalDisclosure.DisclosureState
