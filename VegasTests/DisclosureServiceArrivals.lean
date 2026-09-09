/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationArrival
import VegasTests.DisclosureServiceResolution

/-! # Controller opportunities before disclosure inclusion

Delivery and arbitrary player traffic preserve the public application state.
A ready unchanged responder actually submits its initial-expiration request
at its first invocation, and the rest of the communication phase retains it.
Relating a prior one-shot submission to a current pending request is a separate
history invariant.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Interaction GameTheory.Math.Probability

variable {window : Nat}

theorem serviceEnvironment_deliveries (selector : (application window).EnvironmentPolicy) :
    (application window).DeliveryOnly (fun index => index % 13 < 2)
      (serviceEnvironment selector) := by
  intro history view command hphase hcommand
  have hindex : history.length % 13 = 0 ∨ history.length % 13 = 1 := by omega
  rcases hindex with hindex | hindex
  all_goals
    unfold serviceEnvironment at hcommand
    rw [hindex] at hcommand
    cases hpending : view.pool.pending with
    | nil =>
        simp only [hpending, FinDist.mem_support_pure] at hcommand
        exact Or.inl hcommand
    | cons message rest =>
        simp only [hpending, FinDist.mem_support_pure] at hcommand
        exact Or.inr ⟨_, message.id, hcommand⟩

theorem service_communication_phase
    (players : TestPlayer → (application window).PlayerPolicy)
    (selector : (application window).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation TestPlayer))
    (execution next : (application window).PolicyExecution)
    (hslots : ∀ offset < schedule.countP MessageApplication.Invocation.isEnvironment,
      (execution.environmentHistory.length + offset) % 13 < 2)
    (hnext : next ∈ ((application window).runPolicies players (serviceEnvironment selector)
      schedule execution).support) :
    next.native.application.observe = execution.native.application.observe ∧
      execution.native.pool.pending.Sublist next.native.pool.pending := by
  apply (application window).arrival_phase
    (fun state => state.observe = execution.native.application.observe)
    (fun _ _ _ hstate => hstate) players (fun index => index % 13 < 2)
    (serviceEnvironment selector) (serviceEnvironment_deliveries selector)
    schedule execution next hslots rfl hnext

theorem service_arrivals_public
    (players : TestPlayer → (application window).PlayerPolicy)
    (selector : (application window).EnvironmentPolicy)
    (execution next : (application window).PolicyExecution)
    (hphase : execution.environmentHistory.length % 13 = 0)
    (hnext : next ∈ ((application window).runPolicies players (serviceEnvironment selector)
      serviceArrivals execution).support) :
    next.native.application.observe = execution.native.application.observe ∧
      execution.native.pool.pending.Sublist next.native.pool.pending := by
  apply service_communication_phase players selector serviceArrivals execution next ?_ hnext
  intro offset hoffset
  have hcount : serviceArrivals.countP MessageApplication.Invocation.isEnvironment = 2 := by decide
  rw [hcount] at hoffset
  omega

/-- A request emitted by the owner at the first invocation of the service
arrival phase remains pending through the phase's later player traffic and
delivery-only environment work. -/
theorem service_owner_arrival (payload : Payload)
    (players : TestPlayer → (application window).PlayerPolicy)
    (selector : (application window).EnvironmentPolicy)
    (execution next : (application window).PolicyExecution)
    (hphase : execution.environmentHistory.length % 13 = 0)
    (hrequest : players 0 (execution.principalHistory 0)
      (MessageApplication.State.observe (application window) execution.native 0) =
        FinDist.pure (.submit payload))
    (hnext : next ∈ ((application window).runPolicies players (serviceEnvironment selector)
      serviceArrivals execution).support) :
    ∃ serial, ⟨(0, serial), payload⟩ ∈ next.native.pool.pending := by
  let rest : List (@MessageApplication.Invocation TestPlayer) := serviceArrivals.drop 1
  have hschedule : serviceArrivals = .player 0 :: rest := rfl
  rw [hschedule] at hnext
  simp only [MessageApplication.runPolicies, FinDist.support_bind, Set.mem_iUnion] at hnext
  obtain ⟨after, hafter, hnext⟩ := hnext
  simp only [MessageApplication.invoke, hrequest, FinDist.pure_bind] at hafter
  have hpending : ⟨(0, execution.native.pool.nextSerial 0), payload⟩ ∈
      after.native.pool.pending := by
    have hnative : after.native ∈
        (((application window).playerStep 0 execution (.submit payload)).map
          MessageApplication.PolicyExecution.native).support := by
      rw [FinDist.support_map]
      exact ⟨after, hafter, rfl⟩
    rw [MessageApplication.playerStep_native] at hnative
    simp only [MessageApplication.PlayerCommand.toAction, MessageApplication.step,
      FinDist.mem_support_pure] at hnative
    rw [hnative]
    simp [MessagePool.submit]
  have htail := service_communication_phase players selector rest after next (by
    intro offset hoffset
    have hhistory := (application window).playerStep_environmentHistory 0 execution
      (.submit payload) after hafter
    rw [hhistory]
    simp [rest, serviceArrivals, MessageApplication.Invocation.isEnvironment] at hoffset ⊢
    omega) hnext
  exact ⟨execution.native.pool.nextSerial 0, htail.2.subset hpending⟩

private theorem owner_pair_preserves_responder_history
    (players : TestPlayer → (application window).PlayerPolicy)
    (environment : (application window).EnvironmentPolicy)
    (execution next : (application window).PolicyExecution)
    (hnext : next ∈ ((application window).runPolicies players environment
      [.player 0, .player 0] execution).support) :
    next.principalHistory 1 = execution.principalHistory 1 := by
  simp only [MessageApplication.runPolicies, FinDist.support_bind, Set.mem_iUnion,
    FinDist.mem_support_pure] at hnext
  obtain ⟨middle, hmiddle, final, hfinal, rfl⟩ := hnext
  simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle hfinal
  obtain ⟨first, _, hfirst⟩ := hmiddle
  obtain ⟨second, _, hsecond⟩ := hfinal
  exact ((application window).playerStep_other_history 0 1 (by decide)
    middle second next hsecond).trans
      ((application window).playerStep_other_history 0 1 (by decide)
        execution first middle hfirst)

/-- A responder whose next command is determined by the unchanged public
application state submits at its first invocation in this communication phase.
Arbitrary owner traffic and delivery cannot remove the resulting envelope. -/
theorem service_responder_arrival (payload : Payload)
    (players : TestPlayer → (application window).PlayerPolicy)
    (selector : (application window).EnvironmentPolicy)
    (execution next : (application window).PolicyExecution)
    (hphase : execution.environmentHistory.length % 13 = 0)
    (hrequest : ∀ view : (application window).View,
      view.application = execution.native.application.observe →
      players 1 (execution.principalHistory 1) view = FinDist.pure (.submit payload))
    (hnext : next ∈ ((application window).runPolicies players (serviceEnvironment selector)
      serviceArrivals execution).support) :
    ∃ serial, ⟨(1, serial), payload⟩ ∈ next.native.pool.pending := by
  let rest : List (@MessageApplication.Invocation TestPlayer) :=
    [.player 1, .environment, .environment, .player 0, .player 0, .player 1, .player 1]
  have hschedule : serviceArrivals = [.player 0, .player 0] ++ .player 1 :: rest := rfl
  rw [hschedule, MessageApplication.runPolicies_append] at hnext
  simp only [FinDist.support_bind, Set.mem_iUnion] at hnext
  obtain ⟨before, hbefore, hnext⟩ := hnext
  have hpublic := (service_communication_phase players selector [.player 0, .player 0]
    execution before (by simp [MessageApplication.Invocation.isEnvironment]) hbefore).1
  have hhistory := owner_pair_preserves_responder_history players
    (serviceEnvironment selector) execution before hbefore
  have henv := (application window).runPolicies_environmentHistory_length players
    (serviceEnvironment selector) [.player 0, .player 0] execution before hbefore
  have henv' : before.environmentHistory.length = execution.environmentHistory.length := by
    simpa [MessageApplication.Invocation.isEnvironment] using henv
  have hemit : players 1 (before.principalHistory 1)
      (MessageApplication.State.observe (application window) before.native 1) =
        FinDist.pure (.submit payload) := by
    rw [hhistory]
    exact hrequest _ hpublic
  simp only [MessageApplication.runPolicies, MessageApplication.invoke,
    hemit, FinDist.pure_bind, FinDist.support_bind, Set.mem_iUnion] at hnext
  obtain ⟨submitted, hsubmitted, hnext⟩ := hnext
  have hpending : ⟨(1, before.native.pool.nextSerial 1), payload⟩ ∈
      submitted.native.pool.pending := by
    have hnative : submitted.native ∈ (((application window).playerStep 1 before
        (.submit payload)).map
          MessageApplication.PolicyExecution.native).support := by
      rw [FinDist.support_map]
      exact ⟨submitted, hsubmitted, rfl⟩
    rw [MessageApplication.playerStep_native] at hnative
    simp only [MessageApplication.PlayerCommand.toAction, MessageApplication.step,
      FinDist.mem_support_pure] at hnative
    rw [hnative]
    simp [MessagePool.submit]
  have hsubmittedHistory := (application window).playerStep_environmentHistory 1 before
    (.submit payload) submitted hsubmitted
  have htail := service_communication_phase players selector rest submitted next (by
    intro offset hoffset
    have hcount : rest.countP MessageApplication.Invocation.isEnvironment = 2 := by decide
    rw [hcount] at hoffset
    rw [hsubmittedHistory, henv']
    omega) hnext
  exact ⟨before.native.pool.nextSerial 1, htail.2.subset hpending⟩

/-- The actual unchanged responder submits its initial timeout once the
deadline is overdue, provided it has not already emitted that one-shot call. -/
theorem responder_initial_arrival (response : Bool → Option Bool → Bool)
    (players : TestPlayer → (application window).PlayerPolicy)
    (hresponder : players 1 = responderPolicy (pureResponseDecision response))
    (selector : (application window).EnvironmentPolicy)
    (execution next : (application window).PolicyExecution)
    (hphase : execution.environmentHistory.length % 13 = 0)
    (haccepted : execution.native.application.accepted = none)
    (hresponse : execution.native.application.response = none)
    (hexpired : window < execution.native.application.clock)
    (hnotSubmitted : initialExpirySubmitted (execution.principalHistory 1) = false)
    (hnext : next ∈ ((application window).runPolicies players (serviceEnvironment selector)
      serviceArrivals execution).support) :
    ∃ serial, ⟨(1, serial), Payload.expireInitial⟩ ∈ next.native.pool.pending := by
  apply service_responder_arrival Payload.expireInitial players selector execution next
    hphase ?_ hnext
  intro view hview
  rw [hresponder]
  apply responder_expires_initial response _ view
    ((congrArg PublicState.accepted hview).trans haccepted)
    ((congrArg PublicState.response hview).trans hresponse) ?_ hnotSubmitted
  rw [show view.application.clock = execution.native.application.clock from
    congrArg PublicState.clock hview]
  exact hexpired

theorem responder_publication_arrival (response : Bool → Option Bool → Bool)
    (players : TestPlayer → (application window).PlayerPolicy)
    (hresponder : players 1 = responderPolicy (pureResponseDecision response))
    (selector : (application window).EnvironmentPolicy)
    (execution next : (application window).PolicyExecution)
    (hphase : execution.environmentHistory.length % 13 = 0)
    (binding : DisclosureBinding) (signal : Bool)
    (haccepted : execution.native.application.accepted = some binding)
    (hsignal : execution.native.application.signal = some signal)
    (hpublication : execution.native.application.publication = none)
    (hresponse : execution.native.application.response = none)
    (hexpired : execution.native.application.signalAt + window < execution.native.application.clock)
    (hnotSubmitted : publicationExpirySubmitted (execution.principalHistory 1) = false)
    (hnext : next ∈ ((application window).runPolicies players (serviceEnvironment selector)
      serviceArrivals execution).support) :
    ∃ serial, ⟨(1, serial), Payload.publish 5 .expire⟩ ∈ next.native.pool.pending := by
  apply service_responder_arrival (.publish 5 .expire) players selector execution next
    hphase ?_ hnext
  intro view hview
  rw [hresponder]
  apply responder_expires_publication response _ view binding signal
    ((congrArg PublicState.accepted hview).trans haccepted)
    ((congrArg PublicState.signal hview).trans hsignal)
    ((congrArg PublicState.publication hview).trans hpublication)
    ((congrArg PublicState.response hview).trans hresponse) ?_ hnotSubmitted
  rw [show view.application.clock = execution.native.application.clock from
    congrArg PublicState.clock hview,
    show view.application.signalAt = execution.native.application.signalAt from
      congrArg PublicState.signalAt hview]
  exact hexpired

theorem responder_response_arrival (response : Bool → Option Bool → Bool)
    (players : TestPlayer → (application window).PlayerPolicy)
    (hresponder : players 1 = responderPolicy (pureResponseDecision response))
    (selector : (application window).EnvironmentPolicy)
    (execution next : (application window).PolicyExecution)
    (hphase : execution.environmentHistory.length % 13 = 0)
    (binding : DisclosureBinding) (signal : Bool) (publication : Option Bool)
    (haccepted : execution.native.application.accepted = some binding)
    (hmarker : execution.native.application.markerDone = true)
    (hsignal : execution.native.application.signal = some signal)
    (hpublication : execution.native.application.publication = some publication)
    (hresponse : execution.native.application.response = none)
    (hnotSubmitted : responseSubmitted (execution.principalHistory 1) = false)
    (hnext : next ∈ ((application window).runPolicies players (serviceEnvironment selector)
      serviceArrivals execution).support) :
    ∃ serial, ⟨(1, serial), Payload.respond (response signal publication)⟩ ∈
      next.native.pool.pending := by
  apply service_responder_arrival (.respond (response signal publication)) players selector
    execution next hphase ?_ hnext
  intro view hview
  rw [hresponder]
  exact responder_submits_after_release response signal publication _ view binding
    ((congrArg PublicState.accepted hview).trans haccepted)
    ((congrArg PublicState.markerDone hview).trans hmarker)
    ((congrArg PublicState.signal hview).trans hsignal)
    ((congrArg PublicState.publication hview).trans hpublication)
    ((congrArg PublicState.response hview).trans hresponse) hnotSubmitted

end VegasTests.OptionalDisclosure.DisclosureState
