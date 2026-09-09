/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPolicyInvariant
import VegasTests.DisclosureOwnerPublication
import VegasTests.DisclosureServiceTimeOrigins

/-! # Owner publication provenance under policy continuations

Once the owner's commitment and the public signal are fixed, every publication
packet subsequently emitted by the unchanged owner carries the unique request
selected by its completion rule.  Arbitrary other-player traffic and arbitrary
environment actions preserve this provenance through delivery, inclusion, and
replay.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Interaction GameTheory.Math.Probability

variable {window : Nat}

private theorem owner_emitted_publication_eq (secret signal : Bool)
    (complete : Bool → Bool → Bool)
    (history : List (application window).PlayerEntry) (view : (application window).View)
    (request : ConditionalPublication.Payload TestPlayer Bool)
    (haccepted : view.application.accepted = some (.commitment (0, 0)))
    (hsignal : view.application.signal = some signal)
    (hemit : .submit (.publish request) ∈
      (ownerPolicy secret complete history view).support) :
    request = (Publication.publicationSite 0).requestPayload
      (if complete secret signal then some secret else none) := by
  unfold ownerPolicy at hemit
  simp only [FinDist.mem_support_pure] at hemit
  cases hresponse : view.application.response with
  | some response =>
      rw [hresponse] at hemit
      simp only [Option.isSome_some, if_true] at hemit
      cases hemit
  | none =>
      rw [hresponse] at hemit
      simp only [Option.isSome_none, Bool.false_eq_true, if_false] at hemit
      simp only [haccepted, hsignal] at hemit
      cases hpublication : view.application.publication with
      | some publication =>
          simp only [hpublication] at hemit
          split at hemit <;> cases hemit
      | none =>
          simp only [hpublication] at hemit
          cases hsubmitted : publicationSubmitted history with
          | true =>
              rw [hsubmitted] at hemit
              simp only [if_true] at hemit
              cases hemit
          | false =>
              rw [hsubmitted] at hemit
              simp only [Bool.false_eq_true, if_false] at hemit
              cases hchoice : complete secret signal with
              | false =>
                  rw [hchoice] at hemit
                  simp only [Bool.false_eq_true, if_false] at hemit
                  simp only [Bool.false_eq_true, if_false,
                    ConditionalPublication.requestPayload]
                  exact Payload.publish.inj
                    (MessageApplication.PlayerCommand.submit.inj hemit)
              | true =>
                  rw [hchoice] at hemit
                  simp only [if_true] at hemit
                  simp only [if_true, ConditionalPublication.requestPayload]
                  simpa [Publication.publicationSite_eq] using Payload.publish.inj
                    (MessageApplication.PlayerCommand.submit.inj hemit)

private theorem playerStep_binding_signal
    (who : TestPlayer) (execution next : (application window).PolicyExecution)
    (command : (application window).PlayerCommand)
    (signal : Bool)
    (haccepted : execution.native.application.accepted = some (.commitment (0, 0)))
    (hsignal : execution.native.application.signal = some signal)
    (hnext : next ∈ ((application window).playerStep who execution command).support) :
    next.native.application.accepted = some (.commitment (0, 0)) ∧
      next.native.application.signal = some signal := by
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
      exact ⟨haccepted, hsignal⟩
  | submit payload | replay id | wait =>
      simp only [MessageApplication.PlayerCommand.toAction, MessageApplication.step,
        FinDist.mem_support_pure] at hnative
      rw [hnative]
      exact ⟨haccepted, hsignal⟩

private theorem environmentStep_signal_of_some (state next : DisclosureState)
    (command : EnvironmentCommand) (signal : Bool) (hsignal : state.signal = some signal)
    (hnext : next ∈ (environmentStep state command).support) :
    next.signal = some signal := by
  cases command with
  | marker | advance clock =>
      simp only [environmentStep, FinDist.mem_support_pure] at hnext
      split at hnext <;> subst next <;> exact hsignal
  | sample =>
      simp only [environmentStep, hsignal, Option.isNone_some, Bool.and_false,
        Bool.false_eq_true, if_false, FinDist.mem_support_pure] at hnext
      subst next
      exact hsignal

private theorem includePending_accepted_fixed
    (state : (application window).State) (id : MessageId TestPlayer)
    (haccepted : state.application.accepted = some (.commitment (0, 0))) :
    ((application window).includePending state id).application.accepted =
      some (.commitment (0, 0)) := by
  apply (application window).includePending_application_invariant
    (fun current => current.accepted = some (.commitment (0, 0))) ?_ state id haccepted
  intro current message next hcurrent hhandle
  have hfixed := handle_binding window current message next (by simp [hcurrent]) hhandle
  exact hfixed.1.trans hcurrent

private theorem environmentPolicyStep_binding_signal
    (execution next : (application window).PolicyExecution)
    (command : (application window).EnvironmentPolicyCommand)
    (signal : Bool)
    (haccepted : execution.native.application.accepted = some (.commitment (0, 0)))
    (hsignal : execution.native.application.signal = some signal)
    (hnext : next ∈ ((application window).environmentPolicyStep execution command).support) :
    next.native.application.accepted = some (.commitment (0, 0)) ∧
      next.native.application.signal = some signal := by
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
      rw [hnative]
      exact ⟨haccepted, hsignal⟩
  | «include» id =>
      simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
        MessageApplication.step, FinDist.mem_support_pure] at hnative
      rw [hnative]
      exact ⟨includePending_accepted_fixed execution.native id haccepted,
        by rw [(include_signal_fixed execution.native id).1]; exact hsignal⟩
  | application applicationCommand =>
      simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
        MessageApplication.step, FinDist.support_map, Set.mem_image] at hnative
      obtain ⟨applicationNext, happlication, hstate⟩ := hnative
      rw [← hstate]
      exact ⟨(environmentStep_binding execution.native.application applicationCommand
          applicationNext happlication).1.trans haccepted,
        environmentStep_signal_of_some execution.native.application applicationNext
          applicationCommand signal hsignal happlication⟩

/-- With a fixed accepted owner commitment and signal, the unchanged owner can
only add the canonical publication request selected by `complete`; arbitrary
other-player and environment behavior preserves the same pool provenance. -/
theorem owner_publication_policy_provenance (secret signal : Bool)
    (complete : Bool → Bool → Bool)
    (players : TestPlayer → (application window).PlayerPolicy)
    (howner : players 0 = ownerPolicy secret complete)
    (environment : (application window).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation TestPlayer))
    (execution next : (application window).PolicyExecution)
    (haccepted : execution.native.application.accepted = some (.commitment (0, 0)))
    (hsignal : execution.native.application.signal = some signal)
    (hsafe : execution.native.pool.Satisfies
      (OwnerPublicationSafe ((Publication.publicationSite 0).requestPayload
        (if complete secret signal then some secret else none))))
    (hnext : next ∈ ((application window).runPolicies players environment schedule
      execution).support) :
    next.native.pool.Satisfies
      (OwnerPublicationSafe ((Publication.publicationSite 0).requestPayload
        (if complete secret signal then some secret else none))) := by
  let request := (Publication.publicationSite 0).requestPayload
    (if complete secret signal then some secret else none)
  let Provenance := fun current : (application window).PolicyExecution =>
    current.native.application.accepted = some (.commitment (0, 0)) ∧
      current.native.application.signal = some signal ∧
      current.native.pool.Satisfies (OwnerPublicationSafe request)
  have hinitial : Provenance execution := ⟨haccepted, hsignal, hsafe⟩
  have hfinal := (application window).runPolicies_execution_invariant Provenance
    players environment ?_ ?_ schedule execution next hinitial hnext
  · exact hfinal.2.2
  · intro current who command final hcurrent hcommand hstep
    have hfixed := playerStep_binding_signal who current final command signal hcurrent.1
      hcurrent.2.1 hstep
    refine ⟨hfixed.1, hfixed.2, ?_⟩
    apply (application window).playerStep_pool_satisfies
      (OwnerPublicationSafe request) who current final command hcurrent.2.2 ?_ hstep
    intro payload hsubmit
    subst command
    by_cases hwho : who = 0
    · subst who
      intro _ candidate hpayload
      change payload = .publish candidate at hpayload
      rw [hpayload] at hcommand
      have hrequest := owner_emitted_publication_eq secret signal complete
        (current.principalHistory 0)
        (MessageApplication.State.observe (application window) current.native 0)
        candidate hcurrent.1 hcurrent.2.1 ?_
      · exact hrequest
      · rw [← howner]
        exact hcommand
    · intro hsender
      simp [Message.sender, hwho] at hsender
  · intro current command final hcurrent _ hstep
    have hfixed := environmentPolicyStep_binding_signal current final command signal hcurrent.1
      hcurrent.2.1 hstep
    exact ⟨hfixed.1, hfixed.2,
      (application window).environmentPolicyStep_pool_satisfies
        (OwnerPublicationSafe request) current final command hcurrent.2.2 hstep⟩

end VegasTests.OptionalDisclosure.DisclosureState
