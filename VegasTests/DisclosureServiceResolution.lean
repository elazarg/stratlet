/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationProgress
import VegasTests.DisclosureApplicationInvariant
import VegasTests.DisclosureServiceClock

/-! # Application resolution under the disclosure inclusion service

These proofs instantiate stable-resolver progress with the actual handlers.
They begin with a concrete pending envelope, allow arbitrary competing raw
messages, and establish resolution after a sufficiently serviced inclusion
phase. They do not yet prove that a controller submits that envelope by a
particular cycle or that an unchanged source choice wins a timeout race.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Interaction GameTheory.Math.Probability

variable {window : Nat}

theorem include_binding_persists (state : (application window).State)
    (id : MessageId TestPlayer) (hbound : state.application.accepted.isSome = true) :
    ((application window).includePending state id).application.accepted.isSome = true := by
  have hrun : (application window).includePending state id ∈
      ((application window).run [.include id] state).support := by
    simp [MessageApplication.run, MessageApplication.step]
  have hbinding := run_binding window state ((application window).includePending state id)
    [.include id] hbound hrun
  rw [hbinding.1]
  exact hbound

theorem include_binding_resolves (state : (application window).State)
    (id : MessageId TestPlayer) (serial : Nat)
    (hlookup : state.pool.lookup id = some ⟨(0, serial), Payload.bind (0, 0)⟩) :
    ((application window).includePending state id).application.accepted.isSome = true := by
  cases haccepted : state.application.accepted with
  | none =>
      have hhandle : handle window state.application ⟨(0, serial), .bind (0, 0)⟩ =
          some { state.application with
            accepted := some (.commitment (0, 0))
            acceptedService := state.application.service.freezeAt (0, 0) } := by
        simp [handle, Message.sender, haccepted]
      rw [(application window).includePending_accept state id _ _ hlookup hhandle]
      rfl
  | some binding =>
      exact include_binding_persists state id (by simp [haccepted])

/-- A pending canonical owner binding resolves the initial decision despite
arbitrary competing includes. An earlier competing expiration may resolve it
first; this theorem therefore does not assert the selected source value. -/
theorem binding_phase_resolves (serial : Nat)
    (players : TestPlayer → (application window).PlayerPolicy) (during : Nat → Prop)
    (environment : (application window).EnvironmentPolicy)
    (hservice : (application window).InclusionService during environment)
    (count : Nat) (execution next : (application window).PolicyExecution)
    (hslots : ∀ offset < count, during (execution.environmentHistory.length + offset))
    (hcapacity : execution.native.pool.pending.length ≤ count)
    (hpending : ⟨(0, serial), Payload.bind (0, 0)⟩ ∈ execution.native.pool.pending)
    (hnext : next ∈ ((application window).runPolicies players environment
      (List.replicate count .environment) execution).support) :
    next.native.application.accepted.isSome = true :=
  (application window).inclusion_phase_resolves (fun _ => True)
    (fun state => state.application.accepted.isSome = true) ⟨(0, serial), .bind (0, 0)⟩
    include_binding_persists (fun _ _ _ => Or.inl trivial)
    (fun state id _ hlookup => include_binding_resolves state id serial hlookup)
    players during environment hservice count execution next hslots hcapacity trivial hpending hnext

theorem include_initial_expiration_resolves (state : (application window).State)
    (id : MessageId TestPlayer) (caller : TestPlayer) (serial : Nat)
    (hexpired : window < state.application.clock)
    (hlookup : state.pool.lookup id = some ⟨(caller, serial), Payload.expireInitial⟩) :
    ((application window).includePending state id).application.accepted.isSome = true := by
  cases haccepted : state.application.accepted with
  | none =>
      rw [(application window).includePending_accept state id _ _ hlookup
        (expireInitial_accepts window state.application caller serial haccepted hexpired)]
      rfl
  | some binding =>
      exact include_binding_persists state id (by simp [haccepted])

/-- A pending overdue initial expiration resolves the initial decision within
the serviced phase. The call may be authored by either principal; inclusion
does not synthesize an owner action or modify unsubmitted preparation. -/
theorem initial_expiration_phase_resolves (caller : TestPlayer) (serial : Nat)
    (players : TestPlayer → (application window).PlayerPolicy) (during : Nat → Prop)
    (environment : (application window).EnvironmentPolicy)
    (hservice : (application window).InclusionService during environment)
    (count : Nat) (execution next : (application window).PolicyExecution)
    (hslots : ∀ offset < count, during (execution.environmentHistory.length + offset))
    (hcapacity : execution.native.pool.pending.length ≤ count)
    (hexpired : window < execution.native.application.clock)
    (hpending : ⟨(caller, serial), Payload.expireInitial⟩ ∈ execution.native.pool.pending)
    (hnext : next ∈ ((application window).runPolicies players environment
      (List.replicate count .environment) execution).support) :
    next.native.application.accepted.isSome = true := by
  apply (application window).inclusion_phase_resolves
    (fun state => window < state.application.clock)
    (fun state => state.application.accepted.isSome = true)
    ⟨(caller, serial), .expireInitial⟩ include_binding_persists ?_
    (fun state id hready hlookup =>
      include_initial_expiration_resolves state id caller serial hready hlookup)
    players during environment hservice count execution next hslots hcapacity
    hexpired hpending hnext
  intro state id hready
  exact Or.inl (by simpa only [includePending_clock] using hready)

theorem handle_signal_fixed (state next : DisclosureState)
    (message : Message TestPlayer Payload)
    (hhandle : handle window state message = some next) :
    next.signal = state.signal ∧ next.signalAt = state.signalAt := by
  cases hpayload : message.payload
  case publish endpoint request =>
    have hendpoint := publish_endpoint window state next message endpoint request hpayload hhandle
    subst endpoint
    simp only [handle, hpayload, publication_resolve_addressed] at hhandle
    cases hresolve : (Publication.publicationSite (state.signalAt + window)).resolve?
        state.clock state.verifyOpening state.acceptedReference state.done (fun _ => true)
        ⟨message.id, request⟩ with
    | none =>
        rw [hresolve] at hhandle
        cases hhandle
    | some result =>
        rw [hresolve] at hhandle
        cases hhandle
        exact ⟨rfl, rfl⟩
  all_goals
    simp only [handle, hpayload, response_resolve_map] at hhandle
    first
    | contradiction
    | split at hhandle <;> try contradiction
      cases hhandle
      exact ⟨rfl, rfl⟩

theorem include_signal_fixed (state : (application window).State) (id : MessageId TestPlayer) :
    ((application window).includePending state id).application.signal = state.application.signal ∧
      ((application window).includePending state id).application.signalAt =
        state.application.signalAt := by
  apply (application window).includePending_application_invariant
    (fun current => current.signal = state.application.signal ∧
      current.signalAt = state.application.signalAt) ?_ state id ⟨rfl, rfl⟩
  intro current message next hcurrent hhandle
  have hfixed := handle_signal_fixed current next message hhandle
  exact ⟨hfixed.1.trans hcurrent.1, hfixed.2.trans hcurrent.2⟩

theorem include_native_invariant (state : (application window).State)
    (id : MessageId TestPlayer) (hinvariant : Invariant state.application) :
    Invariant ((application window).includePending state id).application :=
  (application window).includePending_application_invariant Invariant
    (handle_invariant window) state id hinvariant

theorem include_publication_persists (state : (application window).State)
    (id : MessageId TestPlayer) (hpublication : state.application.publication.isSome = true) :
    ((application window).includePending state id).application.publication.isSome = true := by
  apply (application window).includePending_application_invariant
    (fun current => current.publication.isSome = true) ?_ state id hpublication
  intro current message next hcurrent hhandle
  cases hpublished : current.publication with
  | none => simp [hpublished] at hcurrent
  | some result =>
      rw [(handle_publication_fixed window current message next result hpublished hhandle).1]
      exact hcurrent

theorem publication_ready_of_signal (state : DisclosureState) (hinvariant : Invariant state)
    (hsignal : state.signal.isSome = true) (hpublication : state.publication = none) :
    (Publication.publicationSite (state.signalAt + window)).ready
      state.acceptedReference state.done = true := by
  have hmarker := hinvariant.2.2.1 hsignal
  have hbound := hinvariant.2.1 hmarker
  rcases hinvariant.1 with hnone | hcommit | hdefault
  · simp [hnone] at hbound
  · simp [ConditionalPublication.ready, Publication.publicationSite_eq,
      acceptedReference, hcommit, DisclosureBinding.reference, done, hmarker, hsignal, hpublication]
  · simp [ConditionalPublication.ready, Publication.publicationSite_eq,
      acceptedReference, hdefault, DisclosureBinding.reference,
      done, hmarker, hsignal, hpublication]

theorem include_publication_expiration_resolves (state : (application window).State)
    (id : MessageId TestPlayer) (caller : TestPlayer) (serial : Nat)
    (hinvariant : Invariant state.application)
    (hsignal : state.application.signal.isSome = true)
    (hexpired : state.application.signalAt + window < state.application.clock)
    (hlookup : state.pool.lookup id = some ⟨(caller, serial), Payload.publish 5 .expire⟩) :
    ((application window).includePending state id).application.publication.isSome = true := by
  cases hpublication : state.application.publication with
  | none =>
      have hready := publication_ready_of_signal (window := window)
        state.application hinvariant hsignal hpublication
      have hhandle : handle window state.application ⟨(caller, serial), .publish 5 .expire⟩ =
          some { state.application with
            publication := some none, responseAt := state.application.clock } := by
        simp only [handle, publication_resolve_addressed,
          ConditionalPublication.resolve?, hready, Bool.not_true,
          Bool.false_eq_true, ↓reduceIte]
        simp [Publication.publicationSite_eq, hexpired]
      rw [(application window).includePending_accept state id _ _ hlookup hhandle]
      rfl
  | some result =>
      exact include_publication_persists state id (by simp [hpublication])

/-- An overdue pending publication-expiration call reaches the source's
publication decision under service, even if competing traffic resolves it
first. The source continuation is not replaced by global termination. -/
theorem publication_expiration_phase_resolves (caller : TestPlayer) (serial : Nat)
    (players : TestPlayer → (application window).PlayerPolicy) (during : Nat → Prop)
    (environment : (application window).EnvironmentPolicy)
    (hservice : (application window).InclusionService during environment)
    (count : Nat) (execution next : (application window).PolicyExecution)
    (hslots : ∀ offset < count, during (execution.environmentHistory.length + offset))
    (hcapacity : execution.native.pool.pending.length ≤ count)
    (hinvariant : Invariant execution.native.application)
    (hsignal : execution.native.application.signal.isSome = true)
    (hexpired : execution.native.application.signalAt + window < execution.native.application.clock)
    (hpending : ⟨(caller, serial), Payload.publish 5 .expire⟩ ∈ execution.native.pool.pending)
    (hnext : next ∈ ((application window).runPolicies players environment
      (List.replicate count .environment) execution).support) :
    next.native.application.publication.isSome = true := by
  apply (application window).inclusion_phase_resolves
    (fun state => Invariant state.application ∧ state.application.signal.isSome = true ∧
      state.application.signalAt + window < state.application.clock)
    (fun state => state.application.publication.isSome = true)
    ⟨(caller, serial), .publish 5 .expire⟩ include_publication_persists ?_
    (fun state id hready hlookup => include_publication_expiration_resolves state id caller serial
      hready.1 hready.2.1 hready.2.2 hlookup)
    players during environment hservice count execution next hslots hcapacity
    ⟨hinvariant, hsignal, hexpired⟩ hpending hnext
  intro state id hready
  refine Or.inl ⟨include_native_invariant state id hready.1, ?_, ?_⟩
  · rw [(include_signal_fixed state id).1]
    exact hready.2.1
  · rw [(include_signal_fixed state id).2, includePending_clock]
    exact hready.2.2

/-- info: 'VegasTests.OptionalDisclosure.DisclosureState.binding_phase_resolves'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.DisclosureState.binding_phase_resolves

/-- info: 'VegasTests.OptionalDisclosure.DisclosureState.initial_expiration_phase_resolves'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.DisclosureState.initial_expiration_phase_resolves

/-- info: 'VegasTests.OptionalDisclosure.DisclosureState.publication_expiration_phase_resolves'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.DisclosureState.publication_expiration_phase_resolves

end VegasTests.OptionalDisclosure.DisclosureState
