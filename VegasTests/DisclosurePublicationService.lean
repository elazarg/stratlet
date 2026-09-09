/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosureInitialService

/-! # Publication-expiration submission accounting

The unchanged responder submits the exact permissionless publication-expiration
request only after the public signal and deadline.  From actual initialization,
an accounted one-shot submission therefore remains pending and ready, or the
publication milestone has already been established.  No inclusion service or
settlement assumption is used here.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Interaction GameTheory.Math.Probability

variable {window : Nat}

private def PublicationExpiryReady (window : Nat) (state : DisclosureState) : Prop :=
  Invariant state ∧ state.signal.isSome = true ∧ state.publication = none ∧
    state.signalAt + window < state.clock

private theorem environmentStep_signal_fixed_of_some (state next : DisclosureState)
    (command : EnvironmentCommand) (hsignal : state.signal.isSome = true)
    (hnext : next ∈ (environmentStep state command).support) :
    next.signal = state.signal ∧ next.signalAt = state.signalAt := by
  cases hsignalState : state.signal with
  | none => simp [hsignalState] at hsignal
  | some signal =>
      cases command with
      | marker | advance clock =>
          simp only [environmentStep, FinDist.mem_support_pure] at hnext
          split at hnext <;> subst next <;> simp [hsignalState]
      | sample =>
          simp [environmentStep, hsignalState] at hnext
          subst next
          simp [hsignalState]

private theorem responder_publication_emit_ready
    (response : Bool → Option Bool → Bool)
    (history : List (application window).PlayerEntry) (view : (application window).View)
    (hemit : .submit (.publish 5 .expire) ∈
      (responderPolicy (pureResponseDecision response) history view).support) :
    view.application.signal.isSome = true ∧ view.application.publication = none ∧
      view.application.signalAt + window < view.application.clock := by
  unfold responderPolicy at hemit
  split at hemit
  · simp at hemit
  · split at hemit
    · simp only [FinDist.mem_support_pure] at hemit
      split at hemit <;> cases hemit
    · split at hemit
      · simp only [FinDist.mem_support_pure] at hemit
        split at hemit <;> try contradiction
        rename_i hexpired
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hexpired
        simp_all
      · rw [responseController_pure_eq] at hemit
        simp only [FinDist.mem_support_pure] at hemit
        split at hemit <;> cases hemit
      · simp at hemit

/-- In every policy run from the actual empty state, the unchanged responder's
exact publication-expiration history entry is backed by native state: either
publication has resolved, or an exact responder-authored expiration remains
pending while the signal deadline is overdue. -/
theorem responder_publication_expiration_submission
    (response : Bool → Option Bool → Bool)
    (players : TestPlayer → (application window).PlayerPolicy)
    (hresponder : players 1 = responderPolicy (pureResponseDecision response))
    (environment : (application window).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation TestPlayer))
    (next : (application window).PolicyExecution)
    (hnext : next ∈ ((application window).runPolicies players environment schedule
      (MessageApplication.PolicyExecution.initial (application window) (initial window))).support)
    (hsubmitted : (application window).SubmittedPayload (.publish 5 .expire)
      (next.principalHistory 1)) :
    next.native.application.publication.isSome = true ∨
      ((Invariant next.native.application ∧
          next.native.application.signal.isSome = true ∧
          next.native.application.publication = none ∧
          next.native.application.signalAt + window < next.native.application.clock) ∧
        ∃ serial, ⟨(1, serial), Payload.publish 5 .expire⟩ ∈ next.native.pool.pending) := by
  apply (application window).runPolicies_submitted_pendingOrResolved
    Invariant (PublicationExpiryReady window) (fun state => state.publication.isSome = true)
    1 (.publish 5 .expire) players environment
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
  · intro state message final hpublished hhandle
    cases hpublication : state.publication with
    | none => simp [hpublication] at hpublished
    | some result =>
        rw [(handle_publication_fixed window state message final result hpublication hhandle).1]
        exact hpublished
  · intro state message final hready hhandle
    have hinvariant := handle_invariant window state message final hready.1 hhandle
    have hsignal := handle_signal_fixed state final message hhandle
    have hclock := handle_clock state final message hhandle
    cases hpublication : final.publication with
    | none =>
        exact Or.inl ⟨hinvariant, by rw [hsignal.1]; exact hready.2.1,
          hpublication, by rw [hsignal.2, hclock]; exact hready.2.2.2⟩
    | some result => exact Or.inr rfl
  · intro state command final hpublished hfinal
    rw [environmentStep_publication state final command hfinal]
    exact hpublished
  · intro state command final hready hfinal
    have hinvariant := environmentStep_invariant state command final hready.1 hfinal
    have hsignal := environmentStep_signal_fixed_of_some state final command hready.2.1 hfinal
    refine Or.inl ⟨hinvariant, by rw [hsignal.1]; exact hready.2.1,
      (environmentStep_publication state final command hfinal).trans hready.2.2.1, ?_⟩
    rw [hsignal.2]
    exact hready.2.2.2.trans_le (environmentStep_clock_mono state final command hfinal)
  · intro state serial hready
    have hsite := publication_ready_of_signal (window := window) state hready.1
      hready.2.1 hready.2.2.1
    have hhandle : handle window state
        (⟨(1, serial), Payload.publish 5 .expire⟩ : Message TestPlayer Payload) =
        some { state with publication := some none, responseAt := state.clock } := by
      simp only [handle, publication_resolve_addressed,
        ConditionalPublication.resolve?, hsite, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte]
      simp [Publication.publicationSite_eq, hready.2.2.2]
    exact ⟨{ state with publication := some none, responseAt := state.clock }, hhandle, rfl⟩
  · intro execution command hinvariant hcommand hemit
    subst command
    rw [hresponder] at hcommand
    exact ⟨hinvariant, responder_publication_emit_ready response
      (execution.principalHistory 1)
      (MessageApplication.State.observe (application window) execution.native 1) hcommand⟩

/-- info: 'VegasTests.OptionalDisclosure.DisclosureState.responder_publication_expiration_submission'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms responder_publication_expiration_submission

end VegasTests.OptionalDisclosure.DisclosureState
