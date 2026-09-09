/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationService
import VegasTests.DisclosureApplicationPolicies

/-! # A slotted service instance for public disclosure

Each cycle gives two invocations to each player, two delivery opportunities,
two further invocations to each player before any inclusion, eight reserved
inclusion opportunities, fixed marker/chance triggers, and one
public clock increment. An inclusion selector may inspect the native public
environment view and choose any existing pending identifier. The supplied
service predicate, rather than player honesty, justifies draining the queue.

This defines one environment policy and one invocation list for the existing
policy game. Queue bounds do not yet prove settlement, timely opportunity for
each source choice, or strategic comparison. These are additional obligations.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Interaction GameTheory.Math.Probability

variable {window : Nat}

def inclusionSlots (index : Nat) : Prop := 2 ≤ index % 13 ∧ index % 13 < 10

def serviceEnvironment (selector : (application window).EnvironmentPolicy) :
    (application window).EnvironmentPolicy := fun history view =>
  match history.length % 13 with
  | 0 => FinDist.pure <| match view.pool.pending with
      | [] => .wait
      | message :: _ => .deliver 0 message.id
  | 1 => FinDist.pure <| match view.pool.pending with
      | [] => .wait
      | message :: _ => .deliver 1 message.id
  | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => selector history view
  | 10 => FinDist.pure (.application .marker)
  | 11 => FinDist.pure (.application .sample)
  | _ => FinDist.pure (.application (.advance (view.application.clock + 1)))

/-- Recipients can react to a delivered packet while it remains pending.
The inclusion service must reserve capacity for both rounds of player traffic. -/
def serviceArrivals : List (@MessageApplication.Invocation TestPlayer) :=
  [.player 0, .player 0, .player 1, .player 1, .environment, .environment,
    .player 0, .player 0, .player 1, .player 1]

def serviceCycle : List (@MessageApplication.Invocation TestPlayer) :=
  serviceArrivals ++ (List.replicate 8 .environment ++ List.replicate 3 .environment)

def serviceSchedule (cycles : Nat) : List (@MessageApplication.Invocation TestPlayer) :=
  (List.replicate cycles serviceCycle).flatten

def serviceGame (window cycles : Nat) (selector : (application window).EnvironmentPolicy) :=
  (application window).policyGame (serviceEnvironment selector) (serviceSchedule cycles)
    (initial window)

theorem serviceEnvironment_inclusions (selector : (application window).EnvironmentPolicy)
    (hselector : (application window).InclusionService (fun _ => True) selector) :
    (application window).InclusionService inclusionSlots (serviceEnvironment selector) := by
  intro history view command hslot hcommand
  have hindex : history.length % 13 = 2 ∨ history.length % 13 = 3 ∨
      history.length % 13 = 4 ∨ history.length % 13 = 5 ∨
      history.length % 13 = 6 ∨ history.length % 13 = 7 ∨
      history.length % 13 = 8 ∨ history.length % 13 = 9 := by
    dsimp [inclusionSlots] at hslot
    omega
  apply hselector history view command trivial
  rcases hindex with hindex | hindex | hindex | hindex | hindex | hindex | hindex | hindex <;>
    simpa [serviceEnvironment, hindex] using hcommand

/-- This service phase drains any queue of at most eight messages, for every
admitted adaptive selector and every policy execution entering that phase.
Malformed and duplicate traffic is included and consumes capacity normally. -/
theorem service_drain_empty (players : TestPlayer → (application window).PlayerPolicy)
    (selector : (application window).EnvironmentPolicy)
    (hselector : (application window).InclusionService (fun _ => True) selector)
    (execution next : (application window).PolicyExecution)
    (hphase : execution.environmentHistory.length % 13 = 2)
    (hcapacity : execution.native.pool.pending.length ≤ 8)
    (hnext : next ∈ ((application window).runPolicies players (serviceEnvironment selector)
      (List.replicate 8 .environment) execution).support) :
    next.native.pool.pending = [] := by
  apply (application window).inclusion_phase_empty players inclusionSlots
    (serviceEnvironment selector) (serviceEnvironment_inclusions selector hselector)
    8 execution next ?_ hcapacity hnext
  intro offset hoffset
  dsimp [inclusionSlots]
  omega

/-- Both player phases add at most eight pending copies, including reactions
to delivered messages and arbitrary replay or malformed traffic. -/
theorem service_arrival_bound (players : TestPlayer → (application window).PlayerPolicy)
    (selector : (application window).EnvironmentPolicy)
    (execution next : (application window).PolicyExecution)
    (hempty : execution.native.pool.pending = [])
    (hnext : next ∈ ((application window).runPolicies players (serviceEnvironment selector)
      serviceArrivals execution).support) :
    next.native.pool.pending.length ≤ 8 := by
  have hbound := (application window).runPolicies_pending_bound players
    (serviceEnvironment selector) serviceArrivals execution next hnext
  simpa [serviceArrivals, MessageApplication.Invocation.isEnvironment, hempty] using hbound

/-- Every complete service cycle restores the empty pending pool, for all
player policies and all admitted adaptive inclusion selectors. This is a
capacity result; it does not assert application acceptance or settlement. -/
theorem service_cycle_empty (players : TestPlayer → (application window).PlayerPolicy)
    (selector : (application window).EnvironmentPolicy)
    (hselector : (application window).InclusionService (fun _ => True) selector)
    (execution next : (application window).PolicyExecution)
    (hphase : execution.environmentHistory.length % 13 = 0)
    (hempty : execution.native.pool.pending = [])
    (hnext : next ∈ ((application window).runPolicies players (serviceEnvironment selector)
      serviceCycle execution).support) :
    next.native.pool.pending = [] := by
  rw [serviceCycle, MessageApplication.runPolicies_append] at hnext
  simp only [GameTheory.Math.Probability.FinDist.support_bind, Set.mem_iUnion] at hnext
  obtain ⟨arrived, harrived, hnext⟩ := hnext
  rw [MessageApplication.runPolicies_append] at hnext
  simp only [GameTheory.Math.Probability.FinDist.support_bind, Set.mem_iUnion] at hnext
  obtain ⟨drained, hdrained, hnext⟩ := hnext
  have hcapacity := service_arrival_bound players selector execution arrived hempty harrived
  have hhistory := (application window).runPolicies_environmentHistory_length players
    (serviceEnvironment selector) serviceArrivals execution arrived harrived
  simp only [serviceArrivals, List.countP_cons, List.countP_nil,
    MessageApplication.Invocation.isEnvironment, Bool.false_eq_true, ↓reduceIte,
    Nat.reduceAdd] at hhistory
  have hstart : arrived.environmentHistory.length % 13 = 2 := by omega
  have hcleared := service_drain_empty players selector hselector arrived drained
    hstart hcapacity hdrained
  have htail := (application window).runPolicies_pending_bound players
    (serviceEnvironment selector) (List.replicate 3 .environment) drained next hnext
  simpa [List.replicate_succ, MessageApplication.Invocation.isEnvironment, hcleared] using htail

/-- The capacity invariant composes across any number of complete cycles.
It holds for arbitrary player policies, not only unilateral replacements. -/
theorem service_schedule_empty (players : TestPlayer → (application window).PlayerPolicy)
    (selector : (application window).EnvironmentPolicy)
    (hselector : (application window).InclusionService (fun _ => True) selector)
    (cycles : Nat) (execution next : (application window).PolicyExecution)
    (hphase : execution.environmentHistory.length % 13 = 0)
    (hempty : execution.native.pool.pending = [])
    (hnext : next ∈ ((application window).runPolicies players (serviceEnvironment selector)
      (serviceSchedule cycles) execution).support) :
    next.native.pool.pending = [] := by
  induction cycles generalizing execution with
  | zero =>
      simp only [serviceSchedule, List.replicate_zero, List.flatten_nil,
        MessageApplication.runPolicies, FinDist.mem_support_pure] at hnext
      subst next
      exact hempty
  | succ cycles ih =>
      have hschedule : serviceSchedule (cycles + 1) = serviceCycle ++ serviceSchedule cycles := by
        simp [serviceSchedule, List.replicate_succ]
      rw [hschedule, MessageApplication.runPolicies_append] at hnext
      simp only [FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨middle, hmiddle, hnext⟩ := hnext
      have hcleared := service_cycle_empty players selector hselector execution middle
        hphase hempty hmiddle
      have hhistory := (application window).runPolicies_environmentHistory_length players
        (serviceEnvironment selector) serviceCycle execution middle hmiddle
      have hcount : serviceCycle.countP MessageApplication.Invocation.isEnvironment = 13 := by
        decide
      rw [hcount] at hhistory
      exact ih middle (by omega) hcleared hnext

/-- From the game's actual initial state, every supported completed service
schedule leaves no pending messages. Application nontermination is separate. -/
theorem service_game_empty (window cycles : Nat)
    (players : TestPlayer → (application window).PlayerPolicy)
    (selector : (application window).EnvironmentPolicy)
    (hselector : (application window).InclusionService (fun _ => True) selector)
    (next : (application window).PolicyExecution)
    (hnext : next ∈ ((serviceGame window cycles selector).play players).support) :
    next.native.pool.pending = [] :=
  service_schedule_empty players selector hselector cycles
    (MessageApplication.PolicyExecution.initial _ (initial window)) next rfl rfl hnext

/-- FIFO supplies the service obligation concretely; service is not an
uninstantiated assumption on a scheduler record. -/
theorem fifo_inclusions : (application window).InclusionService inclusionSlots
    (serviceEnvironment (application window).includeFirst) :=
  serviceEnvironment_inclusions _ ((application window).includeFirst_service (fun _ => True))

/-- info: 'VegasTests.OptionalDisclosure.DisclosureState.service_game_empty' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.DisclosureState.service_game_empty

end VegasTests.OptionalDisclosure.DisclosureState
