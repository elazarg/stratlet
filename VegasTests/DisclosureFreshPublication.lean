/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosureResponderProvenance
import VegasTests.DisclosureResponseTimeOrigins

/-! # Fresh publication time at service-cycle boundaries -/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Interaction GameTheory.Math.Probability

variable {window : Nat}

/-- During a clock-fixed inclusion phase, publication is either absent or its
response origin is exactly the phase's entry clock. -/
def ResponseFirstArm (origin : Nat) (state : DisclosureState) : Prop :=
  state.clock = origin ∧ (state.publication = none ∨ state.responseAt = origin)

private theorem handle_firstArm (origin : Nat) (state : DisclosureState)
    (message : Message TestPlayer Payload) (next : DisclosureState)
    (hstate : ResponseFirstArm origin state)
    (hhandle : handle window state message = some next) : ResponseFirstArm origin next := by
  constructor
  · rw [handle_clock state next message hhandle]
    exact hstate.1
  cases statePublication : state.publication with
  | some result =>
      rcases hstate.2 with habsent | horigin
      · simp [statePublication] at habsent
      · exact Or.inr ((handle_publication_fixed window state message next result
          statePublication hhandle).2.trans horigin)
  | none =>
      cases nextPublication : next.publication with
      | none => exact Or.inl rfl
      | some result =>
          right
          cases message with
          | mk id payload =>
            cases payload with
            | publish request =>
                rw [publication_arms_response window state next id request hhandle]
                exact hstate.1
            | bind binding =>
                simp only [handle, Fin.isValue, Option.isNone_iff_eq_none,
                  Option.ite_none_right_eq_some, Option.some.injEq] at hhandle
                rcases hhandle with ⟨_, rfl⟩
                simp [statePublication] at nextPublication
            | expireInitial =>
                simp only [handle, Option.isNone_iff_eq_none,
                  Option.ite_none_right_eq_some, Option.some.injEq] at hhandle
                rcases hhandle with ⟨_, rfl⟩
                simp [statePublication] at nextPublication
            | respond value =>
                simp only [handle, response_resolve_map] at hhandle
                split at hhandle <;> try contradiction
                cases hhandle
                simp [statePublication] at nextPublication
            | expireResponse =>
                simp only [handle, Option.ite_none_right_eq_some,
                  Option.some.injEq] at hhandle
                rcases hhandle with ⟨_, rfl⟩
                simp [statePublication] at nextPublication
            | cleartext value => simp [handle] at hhandle nextPublication
            | malformed => simp [handle] at hhandle nextPublication

theorem include_firstArm (origin : Nat) (state : (application window).State)
    (id : MessageId TestPlayer) (hstate : ResponseFirstArm origin state.application) :
    ResponseFirstArm origin ((application window).includePending state id).application := by
  exact (application window).includePending_application_invariant (ResponseFirstArm origin)
    (handle_firstArm (window := window) origin) state id hstate

private theorem handle_response_none_of_prePublicationSafe (origin : Nat)
    (state next : DisclosureState) (message : Message TestPlayer Payload)
    (harm : ResponseFirstArm origin state) (hresponse : state.response = none)
    (hsafe : ResponderPrePublicationMessage message)
    (hhandle : handle window state message = some next) : next.response = none := by
  cases message with
  | mk id payload =>
    cases payload with
    | respond value =>
        simp only [handle, response_resolve_map] at hhandle
        split at hhandle <;> try contradiction
        rename_i hrespond
        cases hhandle
        exfalso
        exact hsafe hrespond.1 value rfl
    | expireResponse =>
        simp only [handle, Option.ite_none_right_eq_some, Option.some.injEq] at hhandle
        rcases hhandle with ⟨hready, rfl⟩
        rcases harm.2 with hpublication | horigin
        · have hnode : 4 ∈ responseEndpoint.requires := by decide
          have hready' := hready.1
          simp only [responseReady, PublicChoice.ready, Bool.and_eq_true,
            Bool.not_eq_true', List.all_eq_true] at hready'
          have hdone := hready'.2 4 hnode
          simp [done, hpublication] at hdone
        · have hclock := harm.1
          omega
    | publish request =>
        simp only [handle] at hhandle
        cases hresolve : (Publication.publicationSite (state.signalAt + window)).resolve?
            state.clock state.verifyOpening state.acceptedReference state.done (fun _ => true)
            ⟨id, request⟩ with
        | none =>
            rw [hresolve] at hhandle
            contradiction
        | some result =>
            rw [hresolve] at hhandle
            cases hhandle
            exact hresponse
    | bind binding | expireInitial | cleartext value | malformed =>
        simp only [handle] at hhandle
        first
        | contradiction
        | split at hhandle <;> try contradiction
          cases hhandle
          exact hresponse

/-- A response-free, pre-publication-safe pool cannot resolve the response
during a reserved inclusion phase. Publication may become armed during the
phase, but its fresh deadline makes an expiration packet ineffective. -/
theorem fresh_publication_phase_response_none
    (players : TestPlayer → (application window).PlayerPolicy)
    (during : Nat → Prop)
    (environment : (application window).EnvironmentPolicy)
    (hservice : (application window).InclusionService during environment)
    (count : Nat) (execution next : (application window).PolicyExecution)
    (hslots : ∀ offset < count,
      during (execution.environmentHistory.length + offset))
    (hpublication : execution.native.application.publication = none)
    (hresponse : execution.native.application.response = none)
    (hsafe : execution.native.pool.Satisfies ResponderPrePublicationMessage)
    (hnext : next ∈ ((application window).runPolicies players environment
      (List.replicate count .environment) execution).support) :
    next.native.application.response = none := by
  let origin := execution.native.application.clock
  let Stable (state : (application window).State) : Prop :=
    ResponseFirstArm origin state.application ∧
      state.pool.Satisfies ResponderPrePublicationMessage ∧
      state.application.response = none
  have hinitial : Stable execution.native :=
    ⟨⟨rfl, Or.inl hpublication⟩, hsafe, hresponse⟩
  have hstable : ∀ state id, Stable state →
      Stable ((application window).includePending state id) := by
    intro state id hstate
    refine ⟨include_firstArm origin state id hstate.1, ?_, ?_⟩
    · simpa only [MessageApplication.includePending_pool] using
        hstate.2.1.includePending id
    cases hlookup : state.pool.lookup id with
    | none =>
        rw [(application window).includePending_missing state id hlookup]
        exact hstate.2.2
    | some message =>
        have hsafeMessage := hstate.2.1.1 message (List.mem_of_find?_eq_some hlookup)
        cases hresult : handle window state.application message with
        | none =>
            rw [(application window).includePending_reject state id message hlookup hresult]
            exact hstate.2.2
        | some result =>
            rw [(application window).includePending_accept state id message result hlookup hresult]
            exact handle_response_none_of_prePublicationSafe origin state.application result
              message hstate.1 hstate.2.2 hsafeMessage hresult
  exact ((application window).inclusion_phase_invariant Stable hstable players
    during environment hservice count execution next hslots hinitial hnext).2.2

/-- If publication is first armed during a service cycle, its response origin
is the entry clock and the cycle's final advance puts the boundary clock one
tick later. -/
theorem service_cycle_fresh_publication (players : TestPlayer →
    (application window).PlayerPolicy)
    (selector : (application window).EnvironmentPolicy)
    (hselector : (application window).InclusionService (fun _ => True) selector)
    (execution next : (application window).PolicyExecution)
    (hphase : execution.environmentHistory.length % 13 = 0)
    (hpublication : execution.native.application.publication = none)
    (hnextPublication : next.native.application.publication.isSome = true)
    (hnext : next ∈ ((application window).runPolicies players (serviceEnvironment selector)
      serviceCycle execution).support) :
    next.native.application.responseAt + 1 = next.native.application.clock := by
  have hcycleSupport := hnext
  rw [serviceCycle, MessageApplication.runPolicies_append] at hnext
  simp only [FinDist.support_bind, Set.mem_iUnion] at hnext
  obtain ⟨arrived, harrived, hnext⟩ := hnext
  rw [MessageApplication.runPolicies_append] at hnext
  simp only [FinDist.support_bind, Set.mem_iUnion] at hnext
  obtain ⟨drained, hdrained, htail⟩ := hnext
  have hpublic := service_arrivals_public players selector execution arrived hphase harrived
  have harrivalHistory := (application window).runPolicies_environmentHistory_length players
    (serviceEnvironment selector) serviceArrivals execution arrived harrived
  have harrivalCount : serviceArrivals.countP MessageApplication.Invocation.isEnvironment = 2 :=
    by decide
  rw [harrivalCount] at harrivalHistory
  have hslots : ∀ offset < 8, inclusionSlots (arrived.environmentHistory.length + offset) := by
    intro offset hoffset
    dsimp [inclusionSlots]
    omega
  have harrivedArm : ResponseFirstArm execution.native.application.clock
      arrived.native.application := by
    exact ⟨congrArg PublicState.clock hpublic.1,
      Or.inl ((congrArg PublicState.publication hpublic.1).trans hpublication)⟩
  have hdrainedArm := (application window).inclusion_phase_invariant
    (fun state => ResponseFirstArm execution.native.application.clock state.application)
    (fun state id hstate => include_firstArm execution.native.application.clock state id hstate)
    players inclusionSlots (serviceEnvironment selector)
    (serviceEnvironment_inclusions selector hselector) 8 arrived drained hslots
    harrivedArm hdrained
  have htailMilestones := service_tail_preserves_milestones players selector drained next (by
    have hdrainHistory := (application window).runPolicies_environmentHistory_length players
      (serviceEnvironment selector) (List.replicate 8 .environment) arrived drained hdrained
    have hdrainCount :
        (List.replicate 8 (@MessageApplication.Invocation.environment TestPlayer)).countP
          MessageApplication.Invocation.isEnvironment = 8 := by decide
    rw [hdrainCount] at hdrainHistory
    omega) htail
  have hdrainedPublication : drained.native.application.publication.isSome = true := by
    simpa only [← htailMilestones.2.1] using hnextPublication
  have hdrainedOrigin := hdrainedArm.2.resolve_left (by
    intro hnone
    rw [hnone] at hdrainedPublication
    contradiction)
  cases drainedPublication : drained.native.application.publication with
  | none => simp [drainedPublication] at hdrainedPublication
  | some result =>
      have horigin := runPolicies_response_origin players (serviceEnvironment selector)
        (List.replicate 3 .environment) drained next result drainedPublication htail
      rw [horigin.2, hdrainedOrigin,
        service_cycle_clock players selector hselector execution next hphase hcycleSupport]

end VegasTests.OptionalDisclosure.DisclosureState
