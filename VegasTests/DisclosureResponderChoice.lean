/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageInvariant
import VegasTests.DisclosureResponseResolution
import VegasTests.DisclosureResponderProvenance

/-! # Exact responder choice settlement

A timely authenticated responder request settles to its selected value. Pool
provenance excludes stale conflicting responder choices while permitting
arbitrary owner traffic, malformed packets, and replay.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Interaction GameTheory.Math.Probability

variable {window : Nat}

/-- Before the response deadline, processing one provenance-safe packet either
leaves the response unresolved or records exactly the expected choice. -/
theorem handle_response_none_or_expected (expected : Bool)
    (state next : DisclosureState) (message : Message TestPlayer Payload)
    (hresponse : state.response = none)
    (hearly : state.clock ≤ state.responseAt + window)
    (hsafe : ResponderChoiceSafe expected message)
    (hhandle : handle window state message = some next) :
    next.response = none ∨ next.response = some expected := by
  cases message with
  | mk id payload =>
      cases payload with
      | respond value =>
          simp only [handle, response_resolve_map] at hhandle
          split at hhandle <;> try contradiction
          rename_i hrequest
          have hvalue := hsafe hrequest.1 value rfl
          cases hhandle
          exact Or.inr (by simp [hvalue])
      | expireResponse =>
          simp [handle, Nat.not_lt.mpr hearly] at hhandle
      | publish request =>
          simp only [handle] at hhandle
          cases hresolve : (Publication.publicationSite (state.signalAt + window)).resolve?
              state.clock state.verifyOpening state.acceptedReference state.done
              (fun _ => true) ⟨id, request⟩ with
          | none =>
              rw [hresolve] at hhandle
              cases hhandle
          | some result =>
              rw [hresolve] at hhandle
              cases hhandle
              exact Or.inl hresponse
      | bind reference | expireInitial =>
          simp only [handle] at hhandle
          split at hhandle <;> try contradiction
          cases hhandle
          exact Or.inl hresponse
      | cleartext value | malformed => simp [handle] at hhandle

private def ResponderChoiceReady (window : Nat) (signal : Bool)
    (publication : Option Bool) (expected : Bool)
    (state : (application window).State) : Prop :=
  Invariant state.application ∧
    state.application.signal = some signal ∧
    state.application.publication = some publication ∧
    state.application.response = none ∧
    state.application.clock ≤ state.application.responseAt + window ∧
    MessagePool.Satisfies (ResponderChoiceSafe expected) state.pool

private def ResponderChoiceResolved (expected : Bool)
    (state : (application window).State) : Prop :=
  state.application.response = some expected

/-- A canonical responder choice wins its timely serviced inclusion phase and
records exactly the selected value. -/
theorem responder_choice_phase_resolves (signal : Bool) (publication : Option Bool)
    (expected : Bool) (serial : Nat)
    (players : TestPlayer → (application window).PlayerPolicy) (during : Nat → Prop)
    (environment : (application window).EnvironmentPolicy)
    (hservice : (application window).InclusionService during environment)
    (count : Nat) (execution next : (application window).PolicyExecution)
    (hslots : ∀ offset < count,
      during (execution.environmentHistory.length + offset))
    (hcapacity : execution.native.pool.pending.length ≤ count)
    (hinvariant : Invariant execution.native.application)
    (hsignal : execution.native.application.signal = some signal)
    (hpublication : execution.native.application.publication = some publication)
    (hresponse : execution.native.application.response = none)
    (hearly : execution.native.application.clock ≤
      execution.native.application.responseAt + window)
    (hsafe : MessagePool.Satisfies (ResponderChoiceSafe expected)
      execution.native.pool)
    (hpending : Message.mk (1, serial) (Payload.respond expected) ∈
      execution.native.pool.pending)
    (hnext : next ∈ ((application window).runPolicies players environment
      (List.replicate count .environment) execution).support) :
    next.native.application.response = some expected := by
  apply (application window).inclusion_phase_resolves
    (ResponderChoiceReady window signal publication expected)
    (ResponderChoiceResolved expected) (Message.mk (1, serial) (.respond expected))
    ?_ ?_ ?_ players during environment hservice count execution next hslots hcapacity
    ⟨hinvariant, hsignal, hpublication, hresponse, hearly, hsafe⟩ hpending hnext
  · intro state id hresolved
    apply (application window).includePending_application_invariant
      (fun application => application.response = some expected) ?_ state id hresolved
    intro current message final hcurrent hhandle
    exact (handle_response_fixed current final message expected hcurrent hhandle).trans hcurrent
  · intro state id hready
    have hsafety := MessagePool.Satisfies.includePending hready.2.2.2.2.2 id
    cases hlookup : state.pool.lookup id with
    | none =>
        rw [(application window).includePending_missing state id hlookup]
        exact Or.inl hready
    | some message =>
        have hmessage : message ∈ state.pool.pending := List.mem_of_find?_eq_some hlookup
        have hmessageSafe := hready.2.2.2.2.2.1 message hmessage
        cases hhandle : handle window state.application message with
        | none =>
            rw [(application window).includePending_reject state id message hlookup hhandle]
            exact Or.inl <| And.intro hready.1 <| And.intro hready.2.1 <|
              And.intro hready.2.2.1 <| And.intro hready.2.2.2.1 <|
              And.intro hready.2.2.2.2.1 hsafety
        | some final =>
            rw [(application window).includePending_accept state id message final hlookup hhandle]
            rcases handle_response_none_or_expected expected state.application final message
                hready.2.2.2.1 hready.2.2.2.2.1 hmessageSafe hhandle with
              hunresolved | hresolved
            · have hsignalFixed := handle_signal_fixed state.application final message hhandle
              have hpublicationFixed := handle_publication_fixed window state.application message
                final publication hready.2.2.1 hhandle
              exact Or.inl <| And.intro
                (handle_invariant window state.application message final hready.1 hhandle) <|
                And.intro (hsignalFixed.1.trans hready.2.1) <|
                And.intro (hpublicationFixed.1.trans hready.2.2.1) <|
                And.intro hunresolved <| And.intro (by
                  rw [handle_clock state.application final message hhandle,
                    hpublicationFixed.2]
                  exact hready.2.2.2.2.1) hsafety
            · exact Or.inr hresolved
  · intro state id hready hlookup
    have hreadyResponse := response_ready_of_publication state.application hready.1
      (by simp [hready.2.2.1]) hready.2.2.2.1
    have hhandle : handle window state.application
        (Message.mk (1, serial) (Payload.respond expected)) =
        some { state.application with response := some expected } := by
      simp [handle, hreadyResponse]
    rw [(application window).includePending_accept state id _ _ hlookup hhandle]
    rfl

end VegasTests.OptionalDisclosure.DisclosureState
