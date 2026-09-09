/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageInvariant
import VegasTests.DisclosureOwnerBinding

/-! # Exact owner publication settlement

An authenticated owner request settles to its selected result before the
publication deadline. Full pool provenance excludes stale conflicting owner
requests while permitting arbitrary responder traffic and replay.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Interaction GameTheory.Math.Probability

variable {window : Nat}

/-- Every owner-authored publication packet carries the fixed request. Other
payloads and responder-authored packets are unrestricted. -/
def OwnerPublicationSafe (request : ConditionalPublication.Payload TestPlayer Bool)
    (message : Message TestPlayer Payload) : Prop :=
  message.sender = 0 →
    ∀ candidate, message.payload = .publish 5 candidate → candidate = request

private theorem owner_request_resolves (secret signal : Bool) (result : Option Bool)
    (hresult : result = none ∨ result = some secret) (state : DisclosureState)
    (serial : Nat) (hinvariant : Invariant state)
    (haccepted : state.accepted = some (.commitment (0, 0)))
    (hstored : state.acceptedService.lookup (0, 0) = some secret)
    (hsignal : state.signal = some signal) (hpublication : state.publication = none) :
    handle window state ⟨(0, serial),
        .publish 5 ((Publication.publicationSite 0).requestPayload result)⟩ =
      some { state with publication := some result, responseAt := state.clock } := by
  have hready := publication_ready_of_signal (window := window) state hinvariant
    (by simp [hsignal]) hpublication
  have hverify : state.verifyOpening ⟨(0, 0), secret⟩ = true := by
    simp [verifyOpening, haccepted, DisclosureBinding.verify, IdealCommitments.verify, hstored]
  have hresolve : (Publication.publicationSite (state.signalAt + window)).resolve?
      state.clock state.verifyOpening state.acceptedReference state.done (fun _ => true)
      ⟨(0, serial), (Publication.publicationSite 0).requestPayload result⟩ = some result := by
    have hrequest : (Publication.publicationSite 0).requestPayload result =
        (Publication.publicationSite (state.signalAt + window)).requestPayload result := by
      cases result <;> rfl
    rw [hrequest]
    apply ((Publication.publicationSite (state.signalAt + window)).resolve_requestPayload
      state.clock state.verifyOpening state.acceptedReference state.done (fun _ => true)
      hready serial result).2
    rcases hresult with rfl | rfl
    · trivial
    · exact ⟨hverify, rfl⟩
  simp only [handle, publication_resolve_addressed, hresolve,
    Option.bind_eq_bind, Option.bind_some]

private theorem handle_publication_none_or_owner_result (result : Option Bool)
    (state next : DisclosureState) (message : Message TestPlayer Payload)
    (hpublication : state.publication = none)
    (hearly : state.clock ≤ state.signalAt + window)
    (hsafe : OwnerPublicationSafe
      ((Publication.publicationSite 0).requestPayload result) message)
    (hhandle : handle window state message = some next) :
    next.publication = none ∨ next.publication = some result := by
  cases message with
  | mk id payload =>
      cases payload with
      | bind reference | expireInitial | expireResponse =>
          simp only [handle] at hhandle
          split at hhandle <;> try contradiction
          cases hhandle
          exact Or.inl hpublication
      | respond value =>
          simp only [handle, response_resolve_map] at hhandle
          split at hhandle <;> try contradiction
          cases hhandle
          exact Or.inl hpublication
      | publish endpoint request =>
          have hendpoint := publish_endpoint window state next
            ⟨id, .publish endpoint request⟩ endpoint request rfl hhandle
          subst endpoint
          cases request with
          | opening reference claimed =>
              simp only [handle, publication_resolve_addressed,
                ConditionalPublication.resolve?] at hhandle
              split at hhandle <;> try contradiction
              split at hhandle <;> try contradiction
              rename_i hopen
              have hrequest := hsafe hopen.1 (.opening reference claimed) (by rfl)
              cases hresultState : result with
              | none =>
                  rw [hresultState] at hrequest
                  simp [ConditionalPublication.requestPayload] at hrequest
              | some expected =>
                  rw [hresultState] at hrequest
                  simp only [ConditionalPublication.requestPayload] at hrequest
                  injection hrequest with _ hclaimed
                  simp only [Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hhandle
                  cases hhandle
                  exact Or.inr (by simp [hclaimed])
          | decline =>
              simp only [handle, publication_resolve_addressed,
                ConditionalPublication.resolve?] at hhandle
              split at hhandle <;> try contradiction
              split at hhandle <;> try contradiction
              rename_i howner
              have hrequest := hsafe howner .decline (by rfl)
              cases hresultState : result with
              | none =>
                  simp only [Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hhandle
                  cases hhandle
                  exact Or.inr (by simp)
              | some expected =>
                  rw [hresultState] at hrequest
                  simp [ConditionalPublication.requestPayload] at hrequest
          | expire =>
              simp only [handle, publication_resolve_addressed] at hhandle
              simp [ConditionalPublication.resolve?, Nat.not_lt.mpr hearly] at hhandle
          | cleartext value | malformed =>
              simp only [handle, publication_resolve_addressed] at hhandle
              simp [ConditionalPublication.resolve?] at hhandle
      | cleartext value | malformed => simp [handle] at hhandle

private def OwnerPublicationReady (window : Nat) (secret signal : Bool)
    (result : Option Bool) (state : (application window).State) : Prop :=
  Invariant state.application ∧
    state.application.accepted = some (.commitment (0, 0)) ∧
    state.application.acceptedService.lookup (0, 0) = some secret ∧
    state.application.signal = some signal ∧
    state.application.publication = none ∧
    state.application.clock ≤ state.application.signalAt + window ∧
    MessagePool.Satisfies
      (OwnerPublicationSafe ((Publication.publicationSite 0).requestPayload result)) state.pool

private def OwnerPublicationResolved (result : Option Bool)
    (state : (application window).State) : Prop :=
  state.application.publication = some result

/-- A canonical owner opening or decline wins its predeadline serviced
inclusion phase and records exactly the selected result. -/
theorem owner_publication_phase_resolves (secret signal : Bool) (result : Option Bool)
    (hresult : result = none ∨ result = some secret) (serial : Nat)
    (players : TestPlayer → (application window).PlayerPolicy) (during : Nat → Prop)
    (environment : (application window).EnvironmentPolicy)
    (hservice : (application window).InclusionService during environment)
    (count : Nat) (execution next : (application window).PolicyExecution)
    (hslots : ∀ offset < count, during (execution.environmentHistory.length + offset))
    (hcapacity : execution.native.pool.pending.length ≤ count)
    (hinvariant : Invariant execution.native.application)
    (haccepted : execution.native.application.accepted = some (.commitment (0, 0)))
    (hstored : execution.native.application.acceptedService.lookup (0, 0) = some secret)
    (hsignal : execution.native.application.signal = some signal)
    (hpublication : execution.native.application.publication = none)
    (hearly : execution.native.application.clock ≤
      execution.native.application.signalAt + window)
    (hsafe : MessagePool.Satisfies
      (OwnerPublicationSafe ((Publication.publicationSite 0).requestPayload result))
        execution.native.pool)
    (hpending : ⟨(0, serial),
        Payload.publish 5 ((Publication.publicationSite 0).requestPayload result)⟩ ∈
      execution.native.pool.pending)
    (hnext : next ∈ ((application window).runPolicies players environment
      (List.replicate count .environment) execution).support) :
    next.native.application.publication = some result := by
  apply (application window).inclusion_phase_resolves
    (OwnerPublicationReady window secret signal result) (OwnerPublicationResolved result)
    ⟨(0, serial), Payload.publish 5 ((Publication.publicationSite 0).requestPayload result)⟩
    ?_ ?_ ?_
    players during environment hservice count execution next hslots hcapacity
    ⟨hinvariant, haccepted, hstored, hsignal, hpublication, hearly, hsafe⟩ hpending hnext
  · intro state id hresolved
    apply (application window).includePending_application_invariant
      (fun application => application.publication = some result) ?_ state id hresolved
    intro current message final hcurrent hhandle
    exact (handle_publication_fixed window current message final result hcurrent hhandle).1.trans
      hcurrent
  · intro state id hready
    have hsafety := MessagePool.Satisfies.includePending hready.2.2.2.2.2.2 id
    cases hlookup : state.pool.lookup id with
    | none =>
        rw [(application window).includePending_missing state id hlookup]
        exact Or.inl hready
    | some message =>
        have hmessage : message ∈ state.pool.pending := List.mem_of_find?_eq_some hlookup
        have hmessageSafe := hready.2.2.2.2.2.2.1 message hmessage
        cases hhandle : handle window state.application message with
        | none =>
            rw [(application window).includePending_reject state id message hlookup hhandle]
            exact Or.inl ⟨hready.1, hready.2.1, hready.2.2.1,
              hready.2.2.2.1, hready.2.2.2.2.1, hready.2.2.2.2.2.1, hsafety⟩
        | some final =>
            rw [(application window).includePending_accept state id message final hlookup hhandle]
            rcases handle_publication_none_or_owner_result result state.application final message
                hready.2.2.2.2.1 hready.2.2.2.2.2.1 hmessageSafe hhandle with
              hunresolved | hresolved
            · have hbinding := handle_binding window state.application message final
                  (by simp [hready.2.1]) hhandle
              have hsignalFixed := handle_signal_fixed state.application final message hhandle
              exact Or.inl ⟨handle_invariant window state.application message final hready.1
                  hhandle, hbinding.1.trans hready.2.1,
                by rw [hbinding.2]; exact hready.2.2.1,
                hsignalFixed.1.trans hready.2.2.2.1, hunresolved,
                by rw [handle_clock state.application final message hhandle, hsignalFixed.2]
                   exact hready.2.2.2.2.2.1,
                hsafety⟩
            · exact Or.inr hresolved
  · intro state id hready hlookup
    have hhandle := owner_request_resolves (window := window) secret signal result hresult
      state.application serial hready.1 hready.2.1 hready.2.2.1 hready.2.2.2.1
      hready.2.2.2.2.1
    rw [(application window).includePending_accept state id _ _ hlookup hhandle]
    exact rfl

end VegasTests.OptionalDisclosure.DisclosureState
