/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPolicyInvariant
import VegasTests.DisclosureServiceResolution

/-! # Owner publication provenance before the public signal

From the actual empty initialization, an unchanged owner cannot have authored
a publication while the signal remains absent.  The statement covers both the
owner's policy history and every location retained by the message pool, so a
later replay cannot manufacture stale owner publication traffic.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Interaction GameTheory.Math.Probability

variable {window : Nat}

/-- Owner-authored pool messages before the signal are not publication requests. -/
def OwnerPreSignalMessage (message : Message TestPlayer Payload) : Prop :=
  message.sender = 0 → ∀ request, message.payload ≠ .publish request

private theorem owner_command_before_signal (secret : Bool)
    (complete : Bool → Bool → Bool)
    (execution : (application window).PolicyExecution)
    (command : (application window).PlayerCommand)
    (hsignal : execution.native.application.signal = none)
    (hcommand : command ∈ (ownerPolicy secret complete
      (execution.principalHistory 0)
      (MessageApplication.State.observe (application window) execution.native 0)).support) :
    ∀ request, command ≠ .submit (.publish request) := by
  intro request heq
  subst command
  have hemit : ownerPolicy secret complete (execution.principalHistory 0)
      (MessageApplication.State.observe (application window) execution.native 0) =
      FinDist.pure (.submit (.publish request)) := by
    unfold ownerPolicy at hcommand ⊢
    simp only [FinDist.mem_support_pure] at hcommand
    rw [← hcommand]
  have hrelease := owner_publish_requires_release secret complete
    (execution.principalHistory 0)
    (MessageApplication.State.observe (application window) execution.native 0) request hemit
  simpa [MessageApplication.State.observe, application, observe, hsignal] using hrelease.2.1

private theorem playerStep_signal (who : TestPlayer)
    (execution next : (application window).PolicyExecution)
    (command : (application window).PlayerCommand)
    (hnext : next ∈ ((application window).playerStep who execution command).support) :
    next.native.application.signal = execution.native.application.signal := by
  have hnative : next.native ∈
      (((application window).playerStep who execution command).map
        MessageApplication.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  rw [MessageApplication.playerStep_native] at hnative
  cases command with
  | privateCommand command =>
      simp only [MessageApplication.PlayerCommand.toAction, MessageApplication.step,
        FinDist.mem_support_pure] at hnative
      rw [hnative]
      rfl
  | submit payload | replay id | wait =>
      simp only [MessageApplication.PlayerCommand.toAction, MessageApplication.step,
        FinDist.mem_support_pure] at hnative
      rw [hnative]

private theorem environmentStep_signal_none_before (state next : DisclosureState)
    (command : EnvironmentCommand)
    (hnext : next ∈ (environmentStep state command).support)
    (hnextSignal : next.signal = none) : state.signal = none := by
  cases hsignal : state.signal with
  | none => rfl
  | some signal =>
      cases command with
      | marker | advance clock =>
          simp only [environmentStep, FinDist.mem_support_pure] at hnext
          split at hnext <;> subst next <;> simp [hsignal] at hnextSignal
      | sample =>
          simp only [environmentStep, hsignal, Option.isNone_some, Bool.and_false,
            Bool.false_eq_true, if_false, FinDist.mem_support_pure] at hnext
          subst next
          simp [hsignal] at hnextSignal

private theorem environmentPolicyStep_signal_none_before
    (execution next : (application window).PolicyExecution)
    (command : (application window).EnvironmentPolicyCommand)
    (hnext : next ∈ ((application window).environmentPolicyStep execution command).support)
    (hnextSignal : next.native.application.signal = none) :
    execution.native.application.signal = none := by
  have hnative : next.native ∈
      (((application window).environmentPolicyStep execution command).map
        MessageApplication.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  rw [MessageApplication.environmentStep_native] at hnative
  cases command with
  | deliver observer id | wait =>
      simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
        MessageApplication.step, FinDist.mem_support_pure] at hnative
      rwa [hnative] at hnextSignal
  | «include» id =>
      simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
        MessageApplication.step, FinDist.mem_support_pure] at hnative
      rw [hnative] at hnextSignal
      rw [(include_signal_fixed execution.native id).1] at hnextSignal
      exact hnextSignal
  | application applicationCommand =>
      simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
        MessageApplication.step, FinDist.support_map, Set.mem_image] at hnative
      obtain ⟨applicationNext, happlication, hstate⟩ := hnative
      rw [← hstate] at hnextSignal
      exact environmentStep_signal_none_before execution.native.application applicationNext
        applicationCommand happlication hnextSignal

private theorem publicationSubmitted_append_nonpublication
    (history : List (application window).PlayerEntry)
    (view : (application window).View) (command : (application window).PlayerCommand)
    (hhistory : publicationSubmitted history = false)
    (hcommand : ∀ request, command ≠ .submit (.publish request)) :
    publicationSubmitted (history ++ [⟨view, command⟩]) = false := by
  unfold publicationSubmitted at hhistory ⊢
  rw [List.any_append, hhistory]
  cases command with
  | privateCommand command | replay id | wait =>
      simp
  | submit payload =>
      cases payload with
      | publish request => exact (hcommand request rfl).elim
      | bind handle | expireInitial | respond value | expireResponse | cleartext value |
          malformed =>
          simp

/-- From actual initialization, absence of the public signal certifies that no
owner publication was recorded in policy history or anywhere in the message
pool. The responder and environment policies are arbitrary. -/
theorem owner_preSignal_provenance (secret : Bool) (complete : Bool → Bool → Bool)
    (players : TestPlayer → (application window).PlayerPolicy)
    (howner : players 0 = ownerPolicy secret complete)
    (environment : (application window).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation TestPlayer))
    (next : (application window).PolicyExecution)
    (hnext : next ∈ ((application window).runPolicies players environment schedule
      (MessageApplication.PolicyExecution.initial (application window) (initial window))).support)
    (hsignal : next.native.application.signal = none) :
    publicationSubmitted (next.principalHistory 0) = false ∧
      next.native.pool.Satisfies OwnerPreSignalMessage := by
  let Provenance := fun execution : (application window).PolicyExecution =>
    execution.native.application.signal = none →
      publicationSubmitted (execution.principalHistory 0) = false ∧
        execution.native.pool.Satisfies OwnerPreSignalMessage
  apply (application window).runPolicies_execution_invariant Provenance players environment
    ?_ ?_ schedule
    (MessageApplication.PolicyExecution.initial (application window) (initial window))
    next ?_ hnext hsignal
  · intro execution who command final hexecution hcommand hfinal hfinalSignal
    have hexecutionSignal := playerStep_signal who execution final command hfinal
    rw [hexecutionSignal] at hfinalSignal
    have hcurrent := hexecution hfinalSignal
    constructor
    · by_cases hwho : who = 0
      · subst who
        have hcommandSafe := owner_command_before_signal secret complete execution command
          hfinalSignal (by rw [← howner]; exact hcommand)
        rw [MessageApplication.playerStep_history_self (application window) 0 execution
          command final hfinal]
        exact publicationSubmitted_append_nonpublication (execution.principalHistory 0)
          (MessageApplication.State.observe (application window) execution.native 0)
          command hcurrent.1 hcommandSafe
      · rw [MessageApplication.playerStep_other_history (application window) who 0 (Ne.symm hwho)
          execution command final hfinal]
        exact hcurrent.1
    · apply (application window).playerStep_pool_satisfies OwnerPreSignalMessage who
        execution final command hcurrent.2 ?_ hfinal
      intro payload hsubmitPayload
      subst command
      intro hsender request hpayload
      change who = 0 at hsender
      subst who
      change payload = .publish request at hpayload
      have hcommandSafe := owner_command_before_signal secret complete execution
        (.submit payload) hfinalSignal (by rw [← howner]; exact hcommand)
      apply hcommandSafe request
      rw [hpayload]
  · intro execution command final hexecution _ hfinal hfinalSignal
    have hexecutionSignal := environmentPolicyStep_signal_none_before execution final command
      hfinal hfinalSignal
    have hcurrent := hexecution hexecutionSignal
    constructor
    · rw [MessageApplication.environmentStep_principalHistory (application window)
        execution command final hfinal]
      exact hcurrent.1
    · exact (application window).environmentPolicyStep_pool_satisfies
        OwnerPreSignalMessage execution final command hcurrent.2 hfinal
  · intro _
    constructor
    · rfl
    · exact MessagePool.Satisfies.empty

end VegasTests.OptionalDisclosure.DisclosureState
