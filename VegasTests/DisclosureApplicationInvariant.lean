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
  (state.accepted = none ∨
    state.accepted = some (0, 0) ∧ ∃ secret, state.service.lookup (0, 0) = some secret) ∧
  (state.markerDone = true → state.accepted.isSome = true) ∧
  (state.signal.isSome = true → state.markerDone = true) ∧
  (state.publication.isSome = true → state.signal.isSome = true) ∧
  (∀ result, state.publication = some result →
    ∃ secret, state.service.lookup (0, 0) = some secret ∧
      (result = none ∨ result = some secret)) ∧
  (state.response.isSome = true → state.publication.isSome = true)

theorem empty_invariant : Invariant empty := by
  simp [Invariant, empty]

theorem data_valid (state : DisclosureState) (hinvariant : Invariant state) :
    state.data.Valid := by
  rcases hinvariant with ⟨_, _, _, _, hresult, _⟩
  cases hpublication : state.publication with
  | none => simp [data, RunData.Valid, hpublication]
  | some result =>
      rcases hresult result hpublication with ⟨secret, hstored, hchoice⟩
      simp only [data, RunData.Valid, hpublication, Option.getD_some]
      simpa [hstored] using hchoice

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
  rcases state with ⟨service, accepted, markerDone, signal, signalAt,
    publication, response, clock⟩
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

theorem privateStep_invariant (state : DisclosureState) (who : TestPlayer)
    (command : Nat × Bool) (hinvariant : Invariant state) :
    Invariant (privateStep state who command) := by
  rcases hinvariant with ⟨haccepted, hmarker, hsignal, hpublication,
    hresult, hresponse⟩
  refine ⟨?_, hmarker, hsignal, hpublication, ?_, hresponse⟩
  · rcases haccepted with hnone | ⟨hcanonical, secret, hstored⟩
    · exact Or.inl hnone
    · exact Or.inr ⟨hcanonical, secret,
        IdealCommitments.lookup_sealValue_of_eq_some _ _ _ _ _ _ hstored⟩
  · intro result hresultState
    rcases hresult result hresultState with ⟨secret, hstored, hchoice⟩
    exact ⟨secret,
      IdealCommitments.lookup_sealValue_of_eq_some _ _ _ _ _ _ hstored, hchoice⟩

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
      rcases hbind with ⟨_, rfl, _, hoccupied⟩
      refine ⟨Or.inr ⟨rfl, ?_⟩, ?_, hsignal, hpublication, hresult, hresponse⟩
      · simpa only [Option.isSome_iff_exists] using hoccupied
      · intro _
        rfl
  | publish request =>
      simp only [handle, hpayload] at hhandle
      cases hresolve : (Publication.publicationSite (state.signalAt + window)).resolve?
          state.clock state.service state.accepted state.done (fun _ => true)
          ⟨message.id, request⟩ with
      | none =>
        rw [hresolve] at hhandle
        simp at hhandle
      | some result =>
        rw [hresolve] at hhandle
        cases hhandle
        have hready :=
          (Publication.publicationSite (state.signalAt + window)).resolve_success_inversion
            state.clock state.service state.accepted state.done (fun _ => true)
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
          rcases haccepted with hnone | ⟨_, secret, hstored⟩
          · simp [ConditionalPublication.ready, hnone] at hready
          · exact ⟨secret, hstored,
              (Publication.publicationSite (state.signalAt + window)).resolve_value
                state.clock state.service state.accepted state.done (fun _ => true)
                ⟨message.id, request⟩ secret (by simpa using hstored) result hresolve⟩
        · intro hresponseSome
          rfl
  | respond value =>
      simp only [handle, hpayload] at hhandle
      split at hhandle <;> try contradiction
      rename_i hrespond
      cases hhandle
      refine ⟨haccepted, hmarker, hsignal, hpublication, hresult, ?_⟩
      intro _
      rcases hrespond with ⟨_, hready⟩
      simp only [responseReady, Bool.and_eq_true, Bool.not_eq_true',
        List.all_eq_true] at hready
      have hpublicationDone := hready.2 5 (by simp [responsePrerequisites_eq])
      simpa [done] using hpublicationDone
  | cleartext value => simp [handle, hpayload] at hhandle
  | malformed => simp [handle, hpayload] at hhandle

theorem environmentStep_invariant (state : DisclosureState)
    (command : EnvironmentCommand) (next : DisclosureState) (hinvariant : Invariant state)
    (hnext : next ∈ (environmentStep state command).support) : Invariant next := by
  cases command with
  | marker =>
      simp only [environmentStep, FinDist.mem_support_pure] at hnext
      subst next
      split <;> simp_all [Invariant]
  | sample =>
      simp only [environmentStep] at hnext
      split at hnext
      · simp only [FinDist.support_map, Set.mem_image] at hnext
        rcases hnext with ⟨signal, _, rfl⟩
        simp_all [Invariant]
      · simp only [FinDist.mem_support_pure] at hnext
        subst next
        exact hinvariant
  | advance clock =>
      simp only [environmentStep, FinDist.mem_support_pure] at hnext
      subst next
      split <;> simpa [Invariant] using hinvariant

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

end VegasTests.OptionalDisclosure.DisclosureState
