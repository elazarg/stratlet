/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosureApplicationInvariant
import VegasTests.DisclosureServiceClock

/-! # Service-game prefixes and boundary invariants

The clock, environment invocation count, pending capacity, and native invariant
hold at every complete-cycle boundary, under arbitrary player policies. These
facts support the controller-specific progress proofs without assuming progress.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Interaction GameTheory.Math.Probability

variable {window : Nat}

theorem serviceSchedule_add (first second : Nat) :
    serviceSchedule (first + second) = serviceSchedule first ++ serviceSchedule second := by
  simp only [serviceSchedule, List.replicate_add, List.flatten_append]

/-- A supported service cycle decomposes into its actual arrival, inclusion,
and fixed-tail executions, with the capacity and phase facts needed by local
application proofs. No application-resolution premise is included. -/
theorem service_cycle_parts (players : TestPlayer → (application window).PlayerPolicy)
    (selector : (application window).EnvironmentPolicy)
    (execution next : (application window).PolicyExecution)
    (hphase : execution.environmentHistory.length % 13 = 0)
    (hempty : execution.native.pool.pending = [])
    (hnext : next ∈ ((application window).runPolicies players (serviceEnvironment selector)
      serviceCycle execution).support) :
    ∃ arrived drained,
      arrived ∈ ((application window).runPolicies players (serviceEnvironment selector)
        serviceArrivals execution).support ∧
      drained ∈ ((application window).runPolicies players (serviceEnvironment selector)
        (List.replicate 8 .environment) arrived).support ∧
      next ∈ ((application window).runPolicies players (serviceEnvironment selector)
        (List.replicate 3 .environment) drained).support ∧
      arrived.native.pool.pending.length ≤ 8 ∧
      (∀ offset < 8, inclusionSlots (arrived.environmentHistory.length + offset)) ∧
      drained.environmentHistory.length % 13 = 10 := by
  rw [serviceCycle, MessageApplication.runPolicies_append] at hnext
  simp only [FinDist.support_bind, Set.mem_iUnion] at hnext
  obtain ⟨arrived, harrived, hnext⟩ := hnext
  rw [MessageApplication.runPolicies_append] at hnext
  simp only [FinDist.support_bind, Set.mem_iUnion] at hnext
  obtain ⟨drained, hdrained, hnext⟩ := hnext
  have harrivalHistory := (application window).runPolicies_environmentHistory_length players
    (serviceEnvironment selector) serviceArrivals execution arrived harrived
  have harrivalCount : serviceArrivals.countP MessageApplication.Invocation.isEnvironment = 2 :=
    by decide
  rw [harrivalCount] at harrivalHistory
  have hdrainHistory := (application window).runPolicies_environmentHistory_length players
    (serviceEnvironment selector) (List.replicate 8 .environment) arrived drained hdrained
  have hdrainCount :
      (List.replicate 8 (@MessageApplication.Invocation.environment TestPlayer)).countP
        MessageApplication.Invocation.isEnvironment = 8 := by decide
  rw [hdrainCount] at hdrainHistory
  refine ⟨arrived, drained, harrived, hdrained, hnext,
    service_arrival_bound players selector execution arrived hempty harrived, ?_, by omega⟩
  intro offset hoffset
  dsimp [inclusionSlots]
  omega

/-- Every supported complete run has a supported prefix at the selected cycle
boundary and a continuation from that very policy execution, including its
native state and all principal and environment histories. -/
theorem service_game_prefix (players : TestPlayer → (application window).PlayerPolicy)
    (selector : (application window).EnvironmentPolicy) (cycles cut : Nat)
    (hle : cut ≤ cycles) (next : (application window).PolicyExecution)
    (hnext : next ∈ ((serviceGame window cycles selector).play players).support) :
    ∃ middle, middle ∈ ((serviceGame window cut selector).play players).support ∧
      next ∈ ((application window).runPolicies players (serviceEnvironment selector)
        (serviceSchedule (cycles - cut)) middle).support := by
  change next ∈ ((application window).runPolicies players (serviceEnvironment selector)
    (serviceSchedule cycles)
    (MessageApplication.PolicyExecution.initial (application window) (initial window))).support
    at hnext
  have hsplit : serviceSchedule cycles =
      serviceSchedule cut ++ serviceSchedule (cycles - cut) := by
    rw [← serviceSchedule_add, Nat.add_sub_of_le hle]
  rw [hsplit, MessageApplication.runPolicies_append] at hnext
  simp only [FinDist.support_bind, Set.mem_iUnion] at hnext
  obtain ⟨middle, hmiddle, htail⟩ := hnext
  exact ⟨middle, hmiddle, htail⟩

/-- Boundary facts for the actual initialized service game. None of the
conclusions assert that a source decision has resolved. -/
theorem service_game_invariants (players : TestPlayer → (application window).PlayerPolicy)
    (selector : (application window).EnvironmentPolicy)
    (hselector : (application window).InclusionService (fun _ => True) selector)
    (cycles : Nat) (next : (application window).PolicyExecution)
    (hnext : next ∈ ((serviceGame window cycles selector).play players).support) :
    next.native.application.clock = cycles ∧
      next.environmentHistory.length = cycles * 13 ∧
      next.native.pool.pending = [] ∧ Invariant next.native.application := by
  have hclock := service_schedule_clock players selector hselector cycles
    (MessageApplication.PolicyExecution.initial (application window) (initial window)) next
    rfl hnext
  have hhistory := (application window).runPolicies_environmentHistory_length players
    (serviceEnvironment selector) (serviceSchedule cycles)
    (MessageApplication.PolicyExecution.initial (application window) (initial window)) next hnext
  have hcount : (serviceSchedule cycles).countP
      MessageApplication.Invocation.isEnvironment = cycles * 13 := by
    simp [serviceSchedule, serviceCycle, serviceArrivals,
      MessageApplication.Invocation.isEnvironment]
  rw [hcount] at hhistory
  refine ⟨?_, ?_, service_schedule_empty players selector hselector cycles
    (MessageApplication.PolicyExecution.initial (application window) (initial window)) next
    rfl rfl hnext, policy_invariant window players (serviceEnvironment selector)
      (serviceSchedule cycles) next hnext⟩
  · simpa [MessageApplication.PolicyExecution.initial, initial,
      MessageApplication.State.initial, empty] using hclock
  · simpa only [MessageApplication.PolicyExecution.initial, List.length_nil, Nat.zero_add]
      using hhistory

end VegasTests.OptionalDisclosure.DisclosureState
