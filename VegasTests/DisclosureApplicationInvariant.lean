/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPolicyLaws
import VegasTests.DisclosureApplication

/-! # Native invariants of the disclosure application -/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Vegas EventGraph Interaction GameTheory.Math.Probability

def Invariant (state : DisclosureState) : Prop :=
  (state.accepted = none ∨ state.accepted = some (.commitment (0, 0)) ∨
    state.accepted = some (.publicDefault false)) ∧
  (state.markerDone = true → state.accepted.isSome = true) ∧
  (state.signal.isSome = true → state.markerDone = true) ∧
  (state.publication.isSome = true → state.signal.isSome = true) ∧
  (∀ result, state.publication = some result →
    result = none ∨ state.boundValue? = result) ∧
  (state.response.isSome = true → state.publication.isSome = true)

theorem empty_invariant : Invariant empty := by
  simp [Invariant, empty]

theorem data_valid (state : DisclosureState) (hinvariant : Invariant state) :
    state.data.Valid := by
  rcases hinvariant with ⟨_, _, _, _, hresult, _⟩
  cases hpublication : state.publication with
  | none => simp [data, RunData.Valid, hpublication]
  | some result =>
      rcases hresult result hpublication with hnone | hstored
      · simp [data, RunData.Valid, hpublication, hnone]
      · cases result <;> simp [data, RunData.Valid, hpublication, hstored]

theorem response_isSome_iff_phase_terminal (state : DisclosureState) :
    state.response.isSome = true ↔ state.phase = 8 := by
  cases hresponse : state.response with
  | none =>
      constructor
      · simp
      · intro hphase
        have hval := congrArg Fin.val hphase
        simp only [phase, hresponse, Option.isSome_none, Bool.false_eq_true,
          ↓reduceIte] at hval
        split_ifs at hval <;> omega
  | some response => simp [phase, hresponse]

/-- Native completion flags coincide with the prefix represented by the
decoded graph configuration; default values in `data` add no completed node. -/
theorem done_iff_decodedConfig_done (state : DisclosureState)
    (hinvariant : Invariant state) (index : Fin graph.nodeCount) :
    state.done index.val = true ↔ index ∈ state.decodedConfig.done := by
  rcases state with ⟨service, acceptedService, accepted, markerDone, signal, signalAt,
    publication, responseAt, response, clock⟩
  cases accepted <;> cases markerDone <;> cases signal <;>
    cases publication <;> cases response <;> fin_cases index <;>
    simp_all [Invariant, done, decodedConfig, phase, cfg, Config.completeNodes,
      List.finRange, Config.initial, Config.completeNode, node, Fin.ext_iff,
      nodeCount]

theorem outcome_isSome_iff_terminal (state : DisclosureState)
    (hinvariant : Invariant state) :
    state.outcome?.isSome = true ↔ Terminal graph state.decodedConfig := by
  change state.outcome?.isSome = true ↔ Terminal graph (cfg state.data state.phase)
  rw [terminal_iff, ← response_isSome_iff_phase_terminal]
  rcases hinvariant with ⟨_, _, _, hpublication, _, hresponse⟩
  cases hsignal : state.signal <;> cases hpublicationState : state.publication <;>
    cases hresponseState : state.response <;>
    simp_all [outcome?]

/-- A response completes the native outcome; the phase invariant supplies
the signal and publication on which that response depends. -/
theorem outcome_isSome_iff_response (state : DisclosureState) (hinvariant : Invariant state) :
    state.outcome?.isSome = true ↔ state.response.isSome = true := by
  rw [outcome_isSome_iff_terminal state hinvariant]
  change Terminal graph (cfg state.data state.phase) ↔ state.response.isSome = true
  rw [terminal_iff, ← response_isSome_iff_phase_terminal]

theorem privateStep_invariant (state : DisclosureState) (who : TestPlayer)
    (command : Nat × Bool) (hinvariant : Invariant state) :
    Invariant (privateStep state who command) := by
  exact hinvariant

theorem handle_invariant (window : Nat) (state : DisclosureState)
    (message : Message TestPlayer Payload) (next : DisclosureState)
    (hinvariant : Invariant state)
    (hhandle : handle window state message = some next) : Invariant next := by
  rcases hinvariant with ⟨haccepted, hmarker, hsignal, hpublication,
    hresult, hresponse⟩
  cases hpayload : message.payload with
  | bind boundHandle =>
      simp only [handle, hpayload] at hhandle
      split at hhandle <;> try contradiction
      rename_i hbind
      cases hhandle
      rcases hbind with ⟨_, rfl, hunbound⟩
      refine ⟨Or.inr (Or.inl rfl), fun _ => rfl, hsignal, hpublication, ?_, hresponse⟩
      intro result hresultState
      change state.publication = some result at hresultState
      have hsome : state.publication.isSome = true := by rw [hresultState]; rfl
      have hacceptedSome := hmarker (hsignal (hpublication hsome))
      simp_all
  | expireInitial =>
      simp only [handle, hpayload] at hhandle
      split at hhandle <;> try contradiction
      rename_i hexpired
      cases hhandle
      refine ⟨Or.inr (Or.inr rfl), fun _ => rfl, hsignal, hpublication, ?_, hresponse⟩
      intro result hresultState
      change state.publication = some result at hresultState
      have hsome : state.publication.isSome = true := by rw [hresultState]; rfl
      have hacceptedSome := hmarker (hsignal (hpublication hsome))
      simp_all
  | publish request =>
      simp only [handle, hpayload] at hhandle
      cases hresolve : (Publication.publicationSite (state.signalAt + window)).resolve?
          state.clock state.verifyOpening state.acceptedReference state.done (fun _ => true)
          ⟨message.id, request⟩ with
      | none =>
        rw [hresolve] at hhandle
        simp at hhandle
      | some result =>
        rw [hresolve] at hhandle
        cases hhandle
        have hready :=
          (Publication.publicationSite (state.signalAt + window)).resolve_success_inversion
            state.clock state.verifyOpening state.acceptedReference state.done (fun _ => true)
            ⟨message.id, request⟩ result hresolve
        have hsignalSome : state.signal.isSome = true := by
          simp only [ConditionalPublication.ready, Publication.publicationSite_eq,
            Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hready
          have hdone := List.all_eq_true.mp hready.2 3 (by decide)
          simpa [done] using hdone
        refine ⟨haccepted, hmarker, hsignal, ?_, ?_, ?_⟩
        · intro _
          exact hsignalSome
        · intro choice hchoice
          cases hchoice
          cases result with
          | none => exact Or.inl rfl
          | some value =>
              exact Or.inr (verifyOpening_value state ⟨(0, 0), value⟩
                ((Publication.publicationSite (state.signalAt + window)).resolve_some_verified
                  state.clock state.verifyOpening state.acceptedReference state.done (fun _ => true)
                  ⟨message.id, request⟩ value hresolve))
        · intro hresponseSome
          rfl
  | respond value =>
      simp only [handle, hpayload] at hhandle
      split at hhandle <;> try contradiction
      rename_i hrespond
      cases hhandle
      refine ⟨haccepted, hmarker, hsignal, hpublication, hresult, ?_⟩
      intro _
      exact responseReady_publication state hrespond.2
  | expireResponse =>
      simp only [handle, hpayload] at hhandle
      split at hhandle <;> try contradiction
      rename_i hexpired
      cases hhandle
      exact ⟨haccepted, hmarker, hsignal, hpublication, hresult,
        fun _ => responseReady_publication state hexpired.1⟩
  | cleartext value => simp [handle, hpayload] at hhandle
  | malformed => simp [handle, hpayload] at hhandle

theorem environmentStep_invariant (state : DisclosureState)
    (command : EnvironmentCommand) (next : DisclosureState) (hinvariant : Invariant state)
    (hnext : next ∈ (environmentStep state command).support) : Invariant next := by
  cases command with
  | marker =>
      simp only [environmentStep, FinDist.mem_support_pure] at hnext
      subst next
      split <;> simp_all [Invariant, boundValue?]
  | sample =>
      simp only [environmentStep] at hnext
      split at hnext
      · simp only [FinDist.support_map, Set.mem_image] at hnext
        rcases hnext with ⟨signal, _, rfl⟩
        simp_all [Invariant, boundValue?]
      · simp only [FinDist.mem_support_pure] at hnext
        subst next
        exact hinvariant
  | advance clock =>
      simp only [environmentStep, FinDist.mem_support_pure] at hnext
      subst next
      split <;> simpa [Invariant, boundValue?] using hinvariant

theorem policy_invariant (window : Nat)
    (players : TestPlayer → (application window).PlayerPolicy)
    (environment : (application window).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation TestPlayer))
    (next : (application window).PolicyExecution)
    (hnext : next ∈ ((application window).runPolicies players environment schedule
      (MessageApplication.PolicyExecution.initial (application window)
        (initial window))).support) :
    Invariant next.native.application := by
  exact (application window).runPolicies_initial_application_invariant Invariant
    privateStep_invariant (handle_invariant window) environmentStep_invariant
    players environment schedule (initial window) next empty_invariant hnext

theorem handle_binding (window : Nat) (state : DisclosureState)
    (message : Message TestPlayer Payload) (next : DisclosureState)
    (hbound : state.accepted.isSome = true)
    (hhandle : handle window state message = some next) :
    next.accepted = state.accepted ∧ next.acceptedService = state.acceptedService := by
  cases hpayload : message.payload with
  | bind boundHandle =>
      have hnone : state.accepted.isNone = false := by
        cases haccepted : state.accepted <;> simp_all
      simp [handle, hpayload, hnone] at hhandle
  | expireInitial =>
      have hnone : state.accepted.isNone = false := by
        cases haccepted : state.accepted <;> simp_all
      simp [handle, hpayload, hnone] at hhandle
  | publish request =>
      simp only [handle, hpayload] at hhandle
      cases hresolve : (Publication.publicationSite (state.signalAt + window)).resolve?
          state.clock state.verifyOpening state.acceptedReference state.done (fun _ => true)
          ⟨message.id, request⟩ with
      | none =>
          rw [hresolve] at hhandle
          simp at hhandle
      | some result =>
          rw [hresolve] at hhandle
          cases hhandle
          exact ⟨rfl, rfl⟩
  | respond value =>
      simp only [handle, hpayload] at hhandle
      split at hhandle <;> try contradiction
      cases hhandle
      exact ⟨rfl, rfl⟩
  | expireResponse =>
      simp only [handle, hpayload] at hhandle
      split at hhandle <;> try contradiction
      cases hhandle
      exact ⟨rfl, rfl⟩
  | cleartext value => simp [handle, hpayload] at hhandle
  | malformed => simp [handle, hpayload] at hhandle

theorem environmentStep_binding (state : DisclosureState) (command : EnvironmentCommand)
    (next : DisclosureState) (hnext : next ∈ (environmentStep state command).support) :
    next.accepted = state.accepted ∧ next.acceptedService = state.acceptedService := by
  cases command with
  | marker =>
      simp only [environmentStep, FinDist.mem_support_pure] at hnext
      subst next
      split <;> exact ⟨rfl, rfl⟩
  | sample =>
      simp only [environmentStep] at hnext
      split at hnext
      · simp only [FinDist.support_map, Set.mem_image] at hnext
        obtain ⟨signal, _, rfl⟩ := hnext
        exact ⟨rfl, rfl⟩
      · simp only [FinDist.mem_support_pure] at hnext
        subst next
        exact ⟨rfl, rfl⟩
  | advance clock =>
      simp only [environmentStep, FinDist.mem_support_pure] at hnext
      subst next
      split <;> exact ⟨rfl, rfl⟩

/-- Environment work does not resolve or change a publication. -/
theorem environmentStep_publication (state next : DisclosureState)
    (command : EnvironmentCommand)
    (hnext : next ∈ (environmentStep state command).support) :
    next.publication = state.publication := by
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

/-- Once publication resolves, accepted calls preserve both its value and the
response window's origin. Repeated or failed traffic cannot restart that window. -/
theorem handle_publication_fixed (window : Nat) (state : DisclosureState)
    (message : Message TestPlayer Payload) (next : DisclosureState) (result : Option Bool)
    (hpublication : state.publication = some result)
    (hhandle : handle window state message = some next) :
    next.publication = state.publication ∧ next.responseAt = state.responseAt := by
  cases hpayload : message.payload
  case publish request =>
    cases message with
    | mk id payload =>
        cases hpayload
        rw [publish_after_resolution window state id request result hpublication] at hhandle
        cases hhandle
  all_goals
    simp only [handle, hpayload] at hhandle
    first
    | contradiction
    | split at hhandle <;> try contradiction
      cases hhandle
      exact ⟨rfl, rfl⟩

/-- Once accepted, both the public binding and its private verifier survive
every finite native continuation, including late preparation and rebinding. -/
theorem run_binding (window : Nat) (state next : (application window).State)
    (actions : List (application window).Action)
    (hbound : state.application.accepted.isSome = true)
    (hnext : next ∈ ((application window).run actions state).support) :
    next.application.accepted = state.application.accepted ∧
      next.application.acceptedService = state.application.acceptedService := by
  apply (application window).run_application_invariant
    (fun current => current.accepted = state.application.accepted ∧
      current.acceptedService = state.application.acceptedService)
    ?_ ?_ ?_ state next actions ⟨rfl, rfl⟩ hnext
  · intro current who command hcurrent
    exact hcurrent
  · intro current message final hcurrent hhandle
    have hsome : current.accepted.isSome = true := by rw [hcurrent.1]; exact hbound
    have hpreserved := handle_binding window current message final hsome hhandle
    exact ⟨hpreserved.1.trans hcurrent.1, hpreserved.2.trans hcurrent.2⟩
  · intro current command final hcurrent hfinal
    have hpreserved := environmentStep_binding current command final hfinal
    exact ⟨hpreserved.1.trans hcurrent.1, hpreserved.2.trans hcurrent.2⟩

/-- Resolution of an unopenable accepted binding can only publish decline.
This statement does not imply that a resolution event ever occurs. -/
theorem unopenable_publication (state : DisclosureState) (hinvariant : Invariant state)
    (hempty : state.boundValue? = none)
    (result : Option Bool) (hresult : state.publication = some result) : result = none := by
  rcases hinvariant.2.2.2.2.1 result hresult with hnone | hstored
  · exact hnone
  · exact hstored.symm.trans hempty

/-- Every supported continuation of an accepted unopenable binding that
resolves publication selects decline, regardless of all subsequent actions. -/
theorem run_unopenable_publication (window : Nat) (state next : (application window).State)
    (actions : List (application window).Action) (hinvariant : Invariant state.application)
    (hbound : state.application.accepted.isSome = true)
    (hempty : state.application.boundValue? = none)
    (hnext : next ∈ ((application window).run actions state).support)
    (result : Option Bool) (hresult : next.application.publication = some result) :
    result = none := by
  have hpreserved := run_binding window state next actions hbound hnext
  have hfinal := (application window).run_application_invariant Invariant
    privateStep_invariant (handle_invariant window) environmentStep_invariant
    state next actions hinvariant hnext
  have hvalue : next.application.boundValue? = state.application.boundValue? := by
    simp only [boundValue?, hpreserved.1, hpreserved.2]
  exact unopenable_publication next.application hfinal (hvalue.trans hempty) result hresult

/--
info: 'VegasTests.OptionalDisclosure.DisclosureState.run_unopenable_publication' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.DisclosureState.run_unopenable_publication

end VegasTests.OptionalDisclosure.DisclosureState
