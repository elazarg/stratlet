/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosureServiceResolution

/-! # Exact owner binding settlement

Before the initial deadline, a stored owner secret and a pending canonical
binding settle to the matching commitment snapshot under the admitted
inclusion service. Competing expiration calls cannot select the public default.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Interaction GameTheory.Math.Probability

variable {window : Nat}

/-- The live commitment service has permanently occupied the owner's source
slot with the selected secret. -/
def OwnerSecretStored (secret : Bool) (state : DisclosureState) : Prop :=
  state.service.lookup (0, 0) = some secret

/-- Before binding resolution, the source is either unresolved or has the
unique commitment snapshot containing the already stored secret. -/
def OwnerBindingInvariant (secret : Bool) (state : DisclosureState) : Prop :=
  OwnerSecretStored secret state ∧
    (state.accepted = none ∨
      state.accepted = some (.commitment (0, 0)) ∧
        state.acceptedService.lookup (0, 0) = some secret)

theorem privateStep_ownerSecretStored (secret : Bool) (state : DisclosureState)
    (who : TestPlayer) (command : Nat × Bool) (hstored : OwnerSecretStored secret state) :
    OwnerSecretStored secret (privateStep state who command) := by
  exact IdealCommitments.lookup_sealValue_of_eq_some state.service who command.1 command.2
    (0, 0) secret hstored

private theorem handle_service (state next : DisclosureState)
    (message : Message TestPlayer Payload)
    (hhandle : handle window state message = some next) : next.service = state.service := by
  cases message with
  | mk id payload =>
      cases payload with
      | bind reference | expireInitial | expireResponse =>
          simp only [handle] at hhandle
          split at hhandle <;> cases hhandle
          rfl
      | respond value =>
          simp only [handle, response_resolve_map] at hhandle
          split at hhandle <;> cases hhandle
          rfl
      | publish endpoint request =>
          have hendpoint := publish_endpoint window state next
            ⟨id, .publish endpoint request⟩ endpoint request rfl hhandle
          subst endpoint
          cases hresolve : (Publication.publicationSite (state.signalAt + window)).resolve?
              state.clock state.verifyOpening state.acceptedReference state.done (fun _ => true)
              ⟨id, request⟩ with
          | none =>
              simp only [handle, publication_resolve_addressed, hresolve,
                Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hhandle
          | some result =>
              simp only [handle, publication_resolve_addressed, hresolve,
                Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hhandle
              cases hhandle
              rfl
      | cleartext value | malformed => simp [handle] at hhandle

theorem handle_ownerSecretStored (secret : Bool) (state next : DisclosureState)
    (message : Message TestPlayer Payload) (hstored : OwnerSecretStored secret state)
    (hhandle : handle window state message = some next) : OwnerSecretStored secret next := by
  rw [OwnerSecretStored, handle_service state next message hhandle]
  exact hstored

theorem environmentStep_ownerSecretStored (secret : Bool) (state next : DisclosureState)
    (command : EnvironmentCommand) (hstored : OwnerSecretStored secret state)
    (hnext : next ∈ (environmentStep state command).support) : OwnerSecretStored secret next := by
  cases command with
  | marker | advance clock =>
      simp only [environmentStep, FinDist.mem_support_pure] at hnext
      split at hnext <;> subst next <;> exact hstored
  | sample =>
      simp only [environmentStep] at hnext
      split at hnext
      · simp only [FinDist.support_map, Set.mem_image] at hnext
        obtain ⟨signal, _, rfl⟩ := hnext
        exact hstored
      · simp only [FinDist.mem_support_pure] at hnext
        subst next
        exact hstored

theorem privateStep_ownerBindingInvariant (secret : Bool) (state : DisclosureState)
    (who : TestPlayer) (command : Nat × Bool)
    (hinvariant : OwnerBindingInvariant secret state) :
    OwnerBindingInvariant secret (privateStep state who command) := by
  exact ⟨privateStep_ownerSecretStored secret state who command hinvariant.1,
    by simpa [privateStep] using hinvariant.2⟩

theorem environmentStep_ownerBindingInvariant (secret : Bool) (state next : DisclosureState)
    (command : EnvironmentCommand) (hinvariant : OwnerBindingInvariant secret state)
    (hnext : next ∈ (environmentStep state command).support) :
    OwnerBindingInvariant secret next := by
  refine ⟨environmentStep_ownerSecretStored secret state next command hinvariant.1 hnext, ?_⟩
  have hbinding := environmentStep_binding state command next hnext
  rcases hinvariant.2 with hunresolved | hresolved
  · exact Or.inl (hbinding.1.trans hunresolved)
  · exact Or.inr ⟨hbinding.1.trans hresolved.1,
      by rw [hbinding.2]; exact hresolved.2⟩

theorem handle_ownerBindingInvariant (secret : Bool) (state next : DisclosureState)
    (message : Message TestPlayer Payload) (hinvariant : OwnerBindingInvariant secret state)
    (hearly : state.clock ≤ window) (hhandle : handle window state message = some next) :
    OwnerBindingInvariant secret next := by
  refine ⟨handle_ownerSecretStored secret state next message hinvariant.1 hhandle, ?_⟩
  rcases hinvariant.2 with hunresolved | hresolved
  · cases message with
    | mk id payload =>
        cases payload with
        | bind reference =>
            simp only [handle] at hhandle
            split at hhandle <;> try contradiction
            rename_i hbind
            cases hhandle
            rcases hbind with ⟨_, rfl, _⟩
            exact Or.inr ⟨rfl, by simpa [OwnerSecretStored] using hinvariant.1⟩
        | expireInitial =>
            rw [expireInitial_before_deadline window state id.1 id.2 hearly] at hhandle
            contradiction
        | publish endpoint request =>
            have hendpoint := publish_endpoint window state next
              ⟨id, .publish endpoint request⟩ endpoint request rfl hhandle
            subst endpoint
            cases hresolve : (Publication.publicationSite (state.signalAt + window)).resolve?
                state.clock state.verifyOpening state.acceptedReference state.done (fun _ => true)
                ⟨id, request⟩ with
            | none =>
                simp only [handle, publication_resolve_addressed, hresolve,
                  Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hhandle
            | some result =>
                simp only [handle, publication_resolve_addressed, hresolve,
                  Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hhandle
                cases hhandle
                exact Or.inl hunresolved
        | respond value =>
            simp only [handle, response_resolve_map] at hhandle
            split at hhandle <;> try contradiction
            cases hhandle
            exact Or.inl hunresolved
        | expireResponse =>
            simp only [handle] at hhandle
            split at hhandle <;> try contradiction
            cases hhandle
            exact Or.inl hunresolved
        | cleartext value | malformed => simp [handle] at hhandle
  · have hpreserved := handle_binding window state message next (by simp [hresolved.1]) hhandle
    exact Or.inr ⟨hpreserved.1.trans hresolved.1,
      by rw [hpreserved.2]; exact hresolved.2⟩

private def OwnerBindingReady (window : Nat) (secret : Bool)
    (state : (application window).State) : Prop :=
  OwnerBindingInvariant secret state.application ∧
    state.application.accepted = none ∧ state.application.clock ≤ window

private def OwnerBindingResolved (secret : Bool)
    (state : (application window).State) : Prop :=
  state.application.accepted = some (.commitment (0, 0)) ∧
    state.application.acceptedService.lookup (0, 0) = some secret

/-- A predeadline canonical owner binding wins its serviced inclusion phase
and freezes the already stored secret, despite arbitrary competing traffic. -/
theorem owner_binding_phase_resolves (secret : Bool) (serial : Nat)
    (players : TestPlayer → (application window).PlayerPolicy) (during : Nat → Prop)
    (environment : (application window).EnvironmentPolicy)
    (hservice : (application window).InclusionService during environment)
    (count : Nat) (execution next : (application window).PolicyExecution)
    (hslots : ∀ offset < count, during (execution.environmentHistory.length + offset))
    (hcapacity : execution.native.pool.pending.length ≤ count)
    (hstored : OwnerSecretStored secret execution.native.application)
    (hunresolved : execution.native.application.accepted = none)
    (hearly : execution.native.application.clock ≤ window)
    (hpending : ⟨(0, serial), Payload.bind (0, 0)⟩ ∈ execution.native.pool.pending)
    (hnext : next ∈ ((application window).runPolicies players environment
      (List.replicate count .environment) execution).support) :
    next.native.application.accepted = some (.commitment (0, 0)) ∧
      next.native.application.acceptedService.lookup (0, 0) = some secret := by
  apply (application window).inclusion_phase_resolves
    (OwnerBindingReady window secret) (OwnerBindingResolved secret)
    ⟨(0, serial), Payload.bind (0, 0)⟩ ?_ ?_ ?_ players during environment hservice count
    execution next hslots hcapacity ⟨⟨hstored, Or.inl hunresolved⟩, hunresolved, hearly⟩
    hpending hnext
  · intro state id hresolved
    apply (application window).includePending_application_invariant
      (fun application => application.accepted = some (.commitment (0, 0)) ∧
        application.acceptedService.lookup (0, 0) = some secret) ?_ state id hresolved
    intro current message final hcurrent hhandle
    have hpreserved := handle_binding window current message final (by simp [hcurrent.1]) hhandle
    exact ⟨hpreserved.1.trans hcurrent.1, by rw [hpreserved.2]; exact hcurrent.2⟩
  · intro state id hready
    have hphase : OwnerBindingInvariant secret
          ((application window).includePending state id).application ∧
        ((application window).includePending state id).application.clock ≤ window := by
      apply (application window).includePending_application_invariant
        (fun application => OwnerBindingInvariant secret application ∧
          application.clock ≤ window) ?_ state id ⟨hready.1, hready.2.2⟩
      intro current message final hcurrent hhandle
      exact ⟨handle_ownerBindingInvariant secret current final message hcurrent.1
          hcurrent.2 hhandle,
        by rw [handle_clock current final message hhandle]; exact hcurrent.2⟩
    cases haccepted : ((application window).includePending state id).application.accepted with
    | none =>
        exact Or.inl ⟨hphase.1, haccepted, hphase.2⟩
    | some binding =>
        rcases hphase.1.2 with hunresolved' | hresolved
        · simp [haccepted] at hunresolved'
        · exact Or.inr hresolved
  · intro state id hready hlookup
    have hhandle := bind_accepts window state.application serial hready.2.1
    rw [(application window).includePending_accept state id _ _ hlookup hhandle]
    exact ⟨rfl, by simpa [OwnerBindingInvariant, OwnerSecretStored] using hready.1.1⟩

end VegasTests.OptionalDisclosure.DisclosureState
