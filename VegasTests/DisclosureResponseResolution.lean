/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosureServiceResolution

/-! # Response resolution under public inclusion service

A pending responder choice or permissionless overdue expiration resolves the
actual response phase. Competing raw messages may resolve it first. Timely
controller submission and preservation of the chosen value require additional
whole-cycle and race-exclusion proofs.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Interaction GameTheory.Math.Probability

variable {window : Nat}

theorem handle_response_fixed (state next : DisclosureState)
    (message : Message TestPlayer Payload) (value : Bool) (hresponse : state.response = some value)
    (hhandle : handle window state message = some next) : next.response = state.response := by
  cases hpayload : message.payload
  case respond reply => simp [handle, hpayload, responseReady, done, hresponse] at hhandle
  case expireResponse => simp [handle, hpayload, responseReady, done, hresponse] at hhandle
  case publish request =>
    simp only [handle, hpayload] at hhandle
    cases hresolve : (Publication.publicationSite (state.signalAt + window)).resolve?
        state.clock state.verifyOpening state.acceptedReference state.done (fun _ => true)
        ⟨message.id, request⟩ with
    | none =>
        rw [hresolve] at hhandle
        cases hhandle
    | some result =>
        rw [hresolve] at hhandle
        cases hhandle
        rfl
  all_goals
    simp only [handle, hpayload] at hhandle
    first
    | contradiction
    | split at hhandle <;> try contradiction
      cases hhandle
      rfl

theorem environmentStep_response (state next : DisclosureState)
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

/-- A resolved response survives every policy-driven continuation exactly. -/
theorem runPolicies_response_fixed
    (players : TestPlayer → (application window).PlayerPolicy)
    (environment : (application window).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation TestPlayer))
    (execution next : (application window).PolicyExecution) (value : Bool)
    (hresponse : execution.native.application.response = some value)
    (hnext : next ∈ ((application window).runPolicies players environment schedule
      execution).support) : next.native.application.response = some value := by
  apply (application window).runPolicies_application_invariant
    (fun state => state.response = some value) ?_ ?_ ?_
    players environment schedule execution next hresponse hnext
  · intro _ _ _ hstate
    exact hstate
  · intro state message final hstate hhandle
    exact (handle_response_fixed state final message value hstate hhandle).trans hstate
  · intro state command final hstate hfinal
    exact (environmentStep_response state final command hfinal).trans hstate

theorem include_response_persists (state : (application window).State)
    (id : MessageId TestPlayer) (hresponse : state.application.response.isSome = true) :
    ((application window).includePending state id).application.response.isSome = true := by
  apply (application window).includePending_application_invariant
    (fun current => current.response.isSome = true) ?_ state id hresponse
  intro current message next hcurrent hhandle
  cases hresponded : current.response with
  | none => simp [hresponded] at hcurrent
  | some value =>
      rw [handle_response_fixed current next message value hresponded hhandle]
      exact hcurrent

theorem include_response_origin_fixed (state : (application window).State)
    (id : MessageId TestPlayer) (result : Option Bool)
    (hpublication : state.application.publication = some result) :
    ((application window).includePending state id).application.publication =
        state.application.publication ∧
      ((application window).includePending state id).application.responseAt =
        state.application.responseAt := by
  apply (application window).includePending_application_invariant
    (fun current => current.publication = state.application.publication ∧
      current.responseAt = state.application.responseAt) ?_ state id ⟨rfl, rfl⟩
  intro current message next hcurrent hhandle
  have hfixed := handle_publication_fixed window current message next result
    (hcurrent.1.trans hpublication) hhandle
  exact ⟨hfixed.1.trans hcurrent.1, hfixed.2.trans hcurrent.2⟩

theorem response_ready_of_publication (state : DisclosureState) (hinvariant : Invariant state)
    (hpublication : state.publication.isSome = true) (hresponse : state.response = none) :
    state.responseReady = true := by
  have hsignal := hinvariant.2.2.2.1 hpublication
  have hmarker := hinvariant.2.2.1 hsignal
  have haccepted := hinvariant.2.1 hmarker
  simp [responseReady, responsePrerequisites_eq, done,
    hresponse, hpublication, hsignal, hmarker, haccepted]

theorem include_response_resolves (state : (application window).State)
    (id : MessageId TestPlayer) (serial : Nat) (value : Bool)
    (hinvariant : Invariant state.application)
    (hpublication : state.application.publication.isSome = true)
    (hlookup : state.pool.lookup id = some ⟨(1, serial), Payload.respond value⟩) :
    ((application window).includePending state id).application.response.isSome = true := by
  cases hresponse : state.application.response with
  | none =>
      have hready := response_ready_of_publication
        state.application hinvariant hpublication hresponse
      have hhandle : handle window state.application ⟨(1, serial), .respond value⟩ =
          some { state.application with response := some value } := by
        simp [handle, Message.sender, hready]
      rw [(application window).includePending_accept state id _ _ hlookup hhandle]
      rfl
  | some response => exact include_response_persists state id (by simp [hresponse])

theorem response_phase_resolves (serial : Nat) (value : Bool)
    (players : TestPlayer → (application window).PlayerPolicy) (during : Nat → Prop)
    (environment : (application window).EnvironmentPolicy)
    (hservice : (application window).InclusionService during environment)
    (count : Nat) (execution next : (application window).PolicyExecution)
    (hslots : ∀ offset < count, during (execution.environmentHistory.length + offset))
    (hcapacity : execution.native.pool.pending.length ≤ count)
    (hinvariant : Invariant execution.native.application)
    (hpublication : execution.native.application.publication.isSome = true)
    (hpending : ⟨(1, serial), Payload.respond value⟩ ∈ execution.native.pool.pending)
    (hnext : next ∈ ((application window).runPolicies players environment
      (List.replicate count .environment) execution).support) :
    next.native.application.response.isSome = true := by
  apply (application window).inclusion_phase_resolves
    (fun state => Invariant state.application ∧ state.application.publication.isSome = true)
    (fun state => state.application.response.isSome = true)
    ⟨(1, serial), .respond value⟩ include_response_persists ?_
    (fun state id hready hlookup => include_response_resolves state id serial value
      hready.1 hready.2 hlookup)
    players during environment hservice count execution next hslots hcapacity
    ⟨hinvariant, hpublication⟩ hpending hnext
  intro state id hready
  exact Or.inl ⟨include_native_invariant state id hready.1,
    include_publication_persists state id hready.2⟩

theorem include_response_expiration_resolves (state : (application window).State)
    (id : MessageId TestPlayer) (caller : TestPlayer) (serial : Nat)
    (hinvariant : Invariant state.application)
    (hpublication : state.application.publication.isSome = true)
    (hexpired : state.application.responseAt + window < state.application.clock)
    (hlookup : state.pool.lookup id = some ⟨(caller, serial), Payload.expireResponse⟩) :
    ((application window).includePending state id).application.response.isSome = true := by
  cases hresponse : state.application.response with
  | none =>
      have hready := response_ready_of_publication
        state.application hinvariant hpublication hresponse
      rw [(application window).includePending_accept state id _ _ hlookup
        (expireResponse_accepts window state.application caller serial hready hexpired)]
      rfl
  | some response => exact include_response_persists state id (by simp [hresponse])

theorem response_expiration_phase_resolves (caller : TestPlayer) (serial : Nat)
    (players : TestPlayer → (application window).PlayerPolicy) (during : Nat → Prop)
    (environment : (application window).EnvironmentPolicy)
    (hservice : (application window).InclusionService during environment)
    (count : Nat) (execution next : (application window).PolicyExecution)
    (hslots : ∀ offset < count, during (execution.environmentHistory.length + offset))
    (hcapacity : execution.native.pool.pending.length ≤ count)
    (hinvariant : Invariant execution.native.application)
    (hpublication : execution.native.application.publication.isSome = true)
    (hexpired : execution.native.application.responseAt + window <
      execution.native.application.clock)
    (hpending : ⟨(caller, serial), Payload.expireResponse⟩ ∈ execution.native.pool.pending)
    (hnext : next ∈ ((application window).runPolicies players environment
      (List.replicate count .environment) execution).support) :
    next.native.application.response.isSome = true := by
  apply (application window).inclusion_phase_resolves
    (fun state => Invariant state.application ∧ state.application.publication.isSome = true ∧
      state.application.responseAt + window < state.application.clock)
    (fun state => state.application.response.isSome = true)
    ⟨(caller, serial), .expireResponse⟩ include_response_persists ?_
    (fun state id hready hlookup => include_response_expiration_resolves state id caller serial
      hready.1 hready.2.1 hready.2.2 hlookup)
    players during environment hservice count execution next hslots hcapacity
    ⟨hinvariant, hpublication, hexpired⟩ hpending hnext
  intro state id hready
  refine Or.inl ⟨include_native_invariant state id hready.1,
    include_publication_persists state id hready.2.1, ?_⟩
  cases hpublished : state.application.publication with
  | none => simp [hpublished] at hready
  | some result =>
      rw [(include_response_origin_fixed state id result hpublished).2, includePending_clock]
      exact hready.2.2

/-- info: 'VegasTests.OptionalDisclosure.DisclosureState.response_phase_resolves'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.DisclosureState.response_phase_resolves

/-- info: 'VegasTests.OptionalDisclosure.DisclosureState.response_expiration_phase_resolves'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.DisclosureState.response_expiration_phase_resolves

end VegasTests.OptionalDisclosure.DisclosureState
