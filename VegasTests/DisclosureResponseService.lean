/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosureInitialService
import VegasTests.DisclosureResponseResolution

/-! # Exact response submission accounting -/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Interaction GameTheory.Math.Probability

variable {window : Nat}

private theorem responder_emits_response_only_when_ready
    (response : Bool → Option Bool → Bool)
    (history : List (application window).PlayerEntry)
    (view : (application window).View) (value : Bool)
    (hemit : .submit (.respond value) ∈
      (responderPolicy (pureResponseDecision response) history view).support) :
    view.application.publication.isSome = true ∧
      view.application.response = none := by
  unfold responderPolicy at hemit
  split at hemit
  · simp at hemit
  · split at hemit
    · simp only [FinDist.mem_support_pure] at hemit
      split at hemit <;> cases hemit
    · split at hemit
      · simp only [FinDist.mem_support_pure] at hemit
        split at hemit <;> cases hemit
      · constructor
        · simp_all
        · cases responseState : view.application.response <;> simp_all
      · simp at hemit

/-- An exact response recorded in the unchanged responder's history is either
resolved or remains as an exact authored pending envelope at a valid response
checkpoint. No delivery or inclusion fairness is assumed. -/
theorem responder_response_submission (response : Bool → Option Bool → Bool)
    (value : Bool)
    (players : TestPlayer → (application window).PlayerPolicy)
    (hresponder : players 1 = responderPolicy (pureResponseDecision response))
    (environment : (application window).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation TestPlayer))
    (next : (application window).PolicyExecution)
    (hnext : next ∈ ((application window).runPolicies players environment schedule
      (MessageApplication.PolicyExecution.initial (application window) (initial window))).support)
    (hsubmitted : (application window).SubmittedPayload (.respond value)
      (next.principalHistory 1)) :
    next.native.application.response.isSome = true ∨
      ((Invariant next.native.application ∧
          next.native.application.publication.isSome = true ∧
          next.native.application.response = none) ∧
        ∃ serial, ⟨(1, serial), Payload.respond value⟩ ∈ next.native.pool.pending) := by
  apply (application window).runPolicies_submitted_pendingOrResolved
    Invariant
    (fun state => Invariant state ∧
      state.publication.isSome = true ∧ state.response = none)
    (fun state => state.response.isSome = true)
    1 (.respond value) players environment
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
    cases hresponse : state.response with
    | none => simp [hresponse] at hresponded
    | some result =>
        rw [handle_response_fixed state final message result hresponse hhandle]
        exact hresponded
  · intro state message final hready hhandle
    have hinvariant := handle_invariant window state message final hready.1 hhandle
    cases hresponse : final.response with
    | some result => exact Or.inr (by simp)
    | none =>
        refine Or.inl ⟨hinvariant, ?_, rfl⟩
        cases hpublication : state.publication with
        | none => simp [hpublication] at hready
        | some result =>
            rw [(handle_publication_fixed window state message final result
              hpublication hhandle).1]
            exact hready.2.1
  · intro state command final hresponded hfinal
    change DisclosureState at state final
    rw [environmentStep_response state final command hfinal]
    exact hresponded
  · intro state command final hready hfinal
    change DisclosureState at state final
    have hinvariant := environmentStep_invariant state command final hready.1 hfinal
    refine Or.inl ⟨hinvariant, ?_, ?_⟩
    · rw [environmentStep_publication state final command hfinal]
      exact hready.2.1
    · rw [environmentStep_response state final command hfinal]
      exact hready.2.2
  · intro state serial hready
    change DisclosureState at state
    have hresponseReady := response_ready_of_publication state hready.1 hready.2.1 hready.2.2
    refine ⟨{ state with response := some value }, ?_, rfl⟩
    change handle window state ⟨(1, serial), .respond value⟩ =
      some { state with response := some value }
    simp [handle, hresponseReady]
  · intro execution command hinvariant hcommand hemit
    subst command
    rw [hresponder] at hcommand
    obtain ⟨hpublication, hresponse⟩ :=
      responder_emits_response_only_when_ready response _ _ value hcommand
    exact ⟨hinvariant, hpublication, hresponse⟩

/-- Once publication is present, one complete service cycle resolves the
responder's choice. Earlier one-shot submissions are supplied by the exact
pending-or-resolved accounting theorem. The actual service schedule supplies
the responder's invocation opportunities; no additional delivery premise is needed. -/
theorem responder_response_cycle (response : Bool → Option Bool → Bool)
    (players : TestPlayer → (application window).PlayerPolicy)
    (hresponder : players 1 = responderPolicy (pureResponseDecision response))
    (selector : (application window).EnvironmentPolicy)
    (hselector : (application window).InclusionService (fun _ => True) selector)
    (execution next : (application window).PolicyExecution)
    (hphase : execution.environmentHistory.length % 13 = 0)
    (hempty : execution.native.pool.pending = [])
    (hinvariant : Invariant execution.native.application)
    (hpublication : execution.native.application.publication.isSome = true)
    (haccounted : responseSubmitted (execution.principalHistory 1) = true →
      execution.native.application.response.isSome = true ∨
        ∃ value serial,
          ⟨(1, serial), Payload.respond value⟩ ∈ execution.native.pool.pending)
    (hnext : next ∈ ((application window).runPolicies players (serviceEnvironment selector)
      serviceCycle execution).support) :
    next.native.application.response.isSome = true := by
  obtain ⟨arrived, drained, harrived, hdrained, htail, hcapacity, hslots, htailPhase⟩ :=
    service_cycle_parts players selector execution next hphase hempty hnext
  have hpublic := service_arrivals_public players selector execution arrived hphase harrived
  have hresolved : drained.native.application.response.isSome = true := by
    cases hresponse : execution.native.application.response with
    | some value =>
        apply (application window).inclusion_phase_invariant
          (fun state => state.application.response.isSome = true)
          include_response_persists players inclusionSlots (serviceEnvironment selector)
          (serviceEnvironment_inclusions selector hselector)
          8 arrived drained hslots ?_ hdrained
        rw [show arrived.native.application.response = execution.native.application.response
          from congrArg PublicState.response hpublic.1, hresponse]
        rfl
    | none =>
        have hpending : ∃ value serial,
            ⟨(1, serial), Payload.respond value⟩ ∈ arrived.native.pool.pending := by
          cases hflag : responseSubmitted (execution.principalHistory 1) with
          | true =>
              rcases haccounted hflag with hresolved | ⟨value, serial, hpending⟩
              · simp [hresponse] at hresolved
              · simp [hempty] at hpending
          | false =>
              have hsignal := hinvariant.2.2.2.1 hpublication
              cases signalState : execution.native.application.signal with
              | none => simp [signalState] at hsignal
              | some signal =>
                cases publicationState : execution.native.application.publication with
                | none => simp [publicationState] at hpublication
                | some publication =>
                  have haccepted := hinvariant.2.1 (hinvariant.2.2.1 hsignal)
                  cases acceptedState : execution.native.application.accepted with
                  | none => simp [acceptedState] at haccepted
                  | some binding =>
                    obtain ⟨serial, hpending⟩ := responder_response_arrival response players
                      hresponder selector execution arrived hphase binding signal publication
                      acceptedState (hinvariant.2.2.1 hsignal) signalState publicationState
                      hresponse hflag harrived
                    exact ⟨response signal publication, serial, hpending⟩
        obtain ⟨value, serial, hpending⟩ := hpending
        apply response_phase_resolves serial value players inclusionSlots
          (serviceEnvironment selector) (serviceEnvironment_inclusions selector hselector)
          8 arrived drained hslots hcapacity ?_ ?_ hpending hdrained
        · exact (application window).runPolicies_application_invariant Invariant
            privateStep_invariant (handle_invariant window) environmentStep_invariant
            players (serviceEnvironment selector) serviceArrivals execution arrived
            hinvariant harrived
        · rw [show arrived.native.application.publication =
              execution.native.application.publication from
              congrArg PublicState.publication hpublic.1]
          exact hpublication
  rw [(service_tail_preserves_milestones players selector drained next htailPhase htail).2.2]
  exact hresolved

end VegasTests.OptionalDisclosure.DisclosureState
