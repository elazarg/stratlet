/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosureServiceTimeOrigins

/-! # Response-window time origins under the disclosure service -/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Interaction GameTheory.Math.Probability

variable {window : Nat}

def ResponseTimeValid (state : DisclosureState) : Prop :=
  state.publication.isSome = true → state.responseAt ≤ state.clock

theorem empty_responseTimeValid : ResponseTimeValid empty := by
  simp [ResponseTimeValid, empty]

private theorem handle_responseTimeValid (state : DisclosureState)
    (message : Message TestPlayer Payload) (next : DisclosureState)
    (hstate : ResponseTimeValid state)
    (hhandle : handle window state message = some next) : ResponseTimeValid next := by
  intro hpublication
  cases statePublication : state.publication with
  | some result =>
      have hfixed := handle_publication_fixed window state message next result
        statePublication hhandle
      rw [hfixed.2, handle_clock state next message hhandle]
      exact hstate (by simp [statePublication])
  | none =>
      cases message with
      | mk id payload =>
        cases payload with
        | publish request =>
            rw [publication_arms_response window state next id request hhandle,
              handle_clock state next ⟨id, .publish request⟩ hhandle]
        | bind binding =>
            simp only [handle, Fin.isValue, Option.isNone_iff_eq_none,
              Option.ite_none_right_eq_some, Option.some.injEq] at hhandle
            rcases hhandle with ⟨_, rfl⟩
            simp [statePublication] at hpublication
        | expireInitial =>
            simp only [handle, Option.isNone_iff_eq_none, Option.ite_none_right_eq_some,
              Option.some.injEq] at hhandle
            rcases hhandle with ⟨_, rfl⟩
            simp [statePublication] at hpublication
        | respond value =>
            simp only [handle, Fin.isValue, Option.ite_none_right_eq_some,
              Option.some.injEq] at hhandle
            rcases hhandle with ⟨_, rfl⟩
            simp [statePublication] at hpublication
        | expireResponse =>
            simp only [handle, Option.ite_none_right_eq_some, Option.some.injEq] at hhandle
            rcases hhandle with ⟨_, rfl⟩
            simp [statePublication] at hpublication
        | cleartext value =>
            simp [handle] at hhandle
        | malformed =>
            simp [handle] at hhandle

private theorem environmentStep_responseTimeValid (state : DisclosureState)
    (command : EnvironmentCommand) (next : DisclosureState)
    (hstate : ResponseTimeValid state)
    (hnext : next ∈ (environmentStep state command).support) : ResponseTimeValid next := by
  cases command with
  | marker =>
      simp only [environmentStep, FinDist.mem_support_pure] at hnext
      split at hnext <;> subst next <;> exact hstate
  | sample =>
      simp only [environmentStep] at hnext
      split at hnext
      · simp only [FinDist.support_map, Set.mem_image] at hnext
        obtain ⟨signal, _, rfl⟩ := hnext
        exact hstate
      · simp only [FinDist.mem_support_pure] at hnext
        subst next
        exact hstate
  | advance clock =>
      simp only [environmentStep, FinDist.mem_support_pure] at hnext
      split at hnext
      · rename_i hclock
        subst next
        intro hpublication
        exact (hstate hpublication).trans hclock
      · subst next
        exact hstate

theorem run_responseTimeValid (state next : (application window).State)
    (actions : List (application window).Action)
    (hstate : ResponseTimeValid state.application)
    (hnext : next ∈ ((application window).run actions state).support) :
    ResponseTimeValid next.application := by
  exact (application window).run_application_invariant ResponseTimeValid
    (fun _ _ _ hvalid => hvalid) (handle_responseTimeValid (window := window))
    environmentStep_responseTimeValid state next actions hstate hnext

theorem runPolicies_responseTimeValid
    (players : TestPlayer → (application window).PlayerPolicy)
    (environment : (application window).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation TestPlayer))
    (execution next : (application window).PolicyExecution)
    (hstate : ResponseTimeValid execution.native.application)
    (hnext : next ∈ ((application window).runPolicies players environment schedule
      execution).support) : ResponseTimeValid next.native.application := by
  exact (application window).runPolicies_application_invariant ResponseTimeValid
    (fun _ _ _ hvalid => hvalid) (handle_responseTimeValid (window := window))
    environmentStep_responseTimeValid players environment schedule execution next hstate hnext

private theorem environmentStep_response_origin (state : DisclosureState)
    (command : EnvironmentCommand) (next : DisclosureState) (result : Option Bool)
    (hstate : state.publication = some result)
    (hnext : next ∈ (environmentStep state command).support) :
    next.publication = some result ∧ next.responseAt = state.responseAt := by
  cases command with
  | marker | advance clock =>
      simp only [environmentStep, FinDist.mem_support_pure] at hnext
      split at hnext <;> subst next <;> exact ⟨hstate, rfl⟩
  | sample =>
      simp only [environmentStep] at hnext
      split at hnext
      · simp only [FinDist.support_map, Set.mem_image] at hnext
        obtain ⟨signal, _, rfl⟩ := hnext
        exact ⟨hstate, rfl⟩
      · simp only [FinDist.mem_support_pure] at hnext
        subst next
        exact ⟨hstate, rfl⟩

theorem runPolicies_response_origin
    (players : TestPlayer → (application window).PlayerPolicy)
    (environment : (application window).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation TestPlayer))
    (execution next : (application window).PolicyExecution) (result : Option Bool)
    (hpublication : execution.native.application.publication = some result)
    (hnext : next ∈ ((application window).runPolicies players environment schedule
      execution).support) :
    next.native.application.publication = some result ∧
      next.native.application.responseAt = execution.native.application.responseAt := by
  apply (application window).runPolicies_application_invariant
    (fun current => current.publication = some result ∧
      current.responseAt = execution.native.application.responseAt)
    ?_ ?_ ?_ players environment schedule execution next ⟨hpublication, rfl⟩ hnext
  · intro _ _ _ hcurrent
    exact hcurrent
  · intro current message final hcurrent hhandle
    have hfixed := handle_publication_fixed window current message final result
      hcurrent.1 hhandle
    exact ⟨hfixed.1.trans hcurrent.1, hfixed.2.trans hcurrent.2⟩
  · intro current command final hcurrent hfinal
    have hfixed := environmentStep_response_origin current command final result
      hcurrent.1 hfinal
    exact ⟨hfixed.1, hfixed.2.trans hcurrent.2⟩

/-- At a complete service-cycle boundary, an already armed response window
has an origin strictly before the boundary clock. -/
theorem service_tail_responseAt_lt_clock
    (players : TestPlayer → (application window).PlayerPolicy)
    (selector : (application window).EnvironmentPolicy)
    (execution next : (application window).PolicyExecution)
    (hphase : execution.environmentHistory.length % 13 = 10)
    (hvalid : ResponseTimeValid execution.native.application)
    (hpublication : next.native.application.publication.isSome = true)
    (hnext : next ∈ ((application window).runPolicies players (serviceEnvironment selector)
      (List.replicate 3 .environment) execution).support) :
    next.native.application.responseAt < next.native.application.clock := by
  obtain ⟨marked, sampled, hmarked, hsampled, hadvanced⟩ :=
    service_tail_steps players selector execution next hphase hnext
  obtain ⟨markedApplication, hmarkedApplication, hmarkedState⟩ :=
    environmentPolicyStep_application_support execution marked .marker hmarked
  obtain ⟨sampledApplication, hsampledApplication, hsampledState⟩ :=
    environmentPolicyStep_application_support marked sampled .sample hsampled
  obtain ⟨nextApplication, hnextApplication, hnextState⟩ :=
    environmentPolicyStep_application_support sampled next
      (.advance (sampled.native.application.clock + 1)) hadvanced
  have hmarkedValid : ResponseTimeValid marked.native.application := by
    rw [hmarkedState]
    exact environmentStep_responseTimeValid execution.native.application .marker
      markedApplication hvalid hmarkedApplication
  have hmarkedApplicationValid : ResponseTimeValid markedApplication := by
    rw [← hmarkedState]
    exact hmarkedValid
  have hsampledApplication' := hsampledApplication
  rw [hmarkedState] at hsampledApplication'
  have hsampledApplicationValid : ResponseTimeValid sampledApplication :=
    environmentStep_responseTimeValid markedApplication .sample sampledApplication
      hmarkedApplicationValid hsampledApplication'
  have hsampledValid : ResponseTimeValid sampled.native.application := by
    rw [hsampledState]
    exact hsampledApplicationValid
  have hnextExact : nextApplication =
      { sampled.native.application with clock := sampled.native.application.clock + 1 } := by
    simp only [environmentStep, FinDist.mem_support_pure] at hnextApplication
    simpa using hnextApplication
  have hstateExact : next.native.application =
      { sampled.native.application with clock := sampled.native.application.clock + 1 } := by
    rw [hnextState, hnextExact]
  have hsampledPublication : sampled.native.application.publication.isSome = true := by
    simpa [hstateExact] using hpublication
  have hle := hsampledValid hsampledPublication
  rw [hstateExact]
  simp only
  omega

/-- At the end of a complete service cycle, every armed response window has
a strictly earlier origin. -/
theorem service_cycle_responseAt_lt_clock
    (players : TestPlayer → (application window).PlayerPolicy)
    (selector : (application window).EnvironmentPolicy)
    (execution next : (application window).PolicyExecution)
    (hphase : execution.environmentHistory.length % 13 = 0)
    (hvalid : ResponseTimeValid execution.native.application)
    (hpublication : next.native.application.publication.isSome = true)
    (hnext : next ∈ ((application window).runPolicies players (serviceEnvironment selector)
      serviceCycle execution).support) :
    next.native.application.responseAt < next.native.application.clock := by
  let prelude := serviceArrivals ++ List.replicate 8 .environment
  have hcycle : serviceCycle = prelude ++ List.replicate 3 .environment := by
    simp [serviceCycle, prelude]
  rw [hcycle, MessageApplication.runPolicies_append] at hnext
  simp only [FinDist.support_bind, Set.mem_iUnion] at hnext
  obtain ⟨middle, hmiddle, hnext⟩ := hnext
  have hmiddleValid := runPolicies_responseTimeValid players (serviceEnvironment selector)
    prelude execution middle hvalid hmiddle
  have hhistory := (application window).runPolicies_environmentHistory_length players
    (serviceEnvironment selector) prelude execution middle hmiddle
  have hcount : prelude.countP MessageApplication.Invocation.isEnvironment = 10 := by
    decide
  rw [hcount] at hhistory
  exact service_tail_responseAt_lt_clock players selector middle next (by omega)
    hmiddleValid hpublication hnext

end VegasTests.OptionalDisclosure.DisclosureState
