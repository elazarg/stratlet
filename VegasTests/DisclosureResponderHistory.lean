/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPolicyHistory
import VegasTests.DisclosurePublicationService

/-! # Responder policy-history provenance

Every command recorded for the unchanged responder came from its policy at the
recorded public view. Thus its coarse one-shot flags can be refined to the exact
payloads needed by service progress proofs, independently of scheduling or
fairness.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Interaction GameTheory.Math.Probability

variable {window : Nat}

private def ResponderCommandLaw (response : Bool → Option Bool → Bool)
    (view : (application window).View) (command : (application window).PlayerCommand) : Prop :=
  (∀ request, command = .submit (.publish request) → request = .expire) ∧
    (∀ value, command = .submit (.respond value) →
      ∃ signal publication,
        view.application.signal = some signal ∧
          view.application.publication = some publication ∧
          value = response signal publication)

private def ResponderHistoryLaw (response : Bool → Option Bool → Bool)
    (history : List (application window).PlayerEntry) : Prop :=
  ∀ entry ∈ history, ResponderCommandLaw response entry.beforeView entry.command

private theorem responder_command_law (response : Bool → Option Bool → Bool)
    (history : List (application window).PlayerEntry) (view : (application window).View)
    (command : (application window).PlayerCommand)
    (hcommand : command ∈ (responderPolicy response history view).support) :
    ResponderCommandLaw response view command := by
  cases hresponse : view.application.response with
  | some value =>
      simp [responderPolicy, hresponse] at hcommand
      subst command
      simp [ResponderCommandLaw]
  | none =>
    cases haccepted : view.application.accepted with
    | none =>
        simp only [responderPolicy, hresponse, Option.isSome_none, Bool.false_eq_true,
          if_false, haccepted,
          FinDist.mem_support_pure] at hcommand
        split at hcommand <;> subst command <;> simp [ResponderCommandLaw]
    | some binding =>
        cases hsignal : view.application.signal with
        | none =>
            simp [responderPolicy, hresponse, haccepted, hsignal] at hcommand
            subst command
            simp [ResponderCommandLaw]
        | some signal =>
            cases hpublication : view.application.publication with
            | none =>
                simp only [responderPolicy, hresponse, Option.isSome_none,
                  Bool.false_eq_true, if_false, haccepted, hsignal, hpublication,
                  FinDist.mem_support_pure] at hcommand
                split at hcommand
                · subst command
                  constructor
                  · intro request hrequest
                    injection hrequest with hpayload
                    injection hpayload with hrequest
                    exact hrequest.symm
                  · intro value hvalue
                    cases hvalue
                · subst command
                  simp [ResponderCommandLaw]
            | some publication =>
                simp only [responderPolicy, hresponse, Option.isSome_none,
                  Bool.false_eq_true, if_false, haccepted, hsignal, hpublication,
                  FinDist.mem_support_pure] at hcommand
                split at hcommand
                · subst command
                  simp [ResponderCommandLaw]
                · subst command
                  constructor
                  · intro request hrequest
                    cases hrequest
                  · intro value hvalue
                    refine ⟨signal, publication, hsignal, hpublication, ?_⟩
                    injection hvalue with hpayload
                    injection hpayload with hvalue
                    exact hvalue.symm

private theorem responder_history_law
    (response : Bool → Option Bool → Bool)
    (players : TestPlayer → (application window).PlayerPolicy)
    (hresponder : players 1 = responderPolicy response)
    (environment : (application window).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation TestPlayer))
    (next : (application window).PolicyExecution)
    (hnext : next ∈ ((application window).runPolicies players environment schedule
      (MessageApplication.PolicyExecution.initial (application window) (initial window))).support) :
    ResponderHistoryLaw response (next.principalHistory 1) := by
  apply (application window).runPolicies_principalHistory_forall 1
    (ResponderCommandLaw response) players environment ?_ schedule
    (MessageApplication.PolicyExecution.initial (application window) (initial window)) next
    (by simp [MessageApplication.PolicyExecution.initial]) hnext
  intro history view command hcommand
  rw [hresponder] at hcommand
  exact responder_command_law response history view command hcommand

/-- Along every supported run from initialization, the responder's coarse
publication flag denotes an exact publication-expiration submission. -/
theorem responder_publicationSubmitted_exact
    (response : Bool → Option Bool → Bool)
    (players : TestPlayer → (application window).PlayerPolicy)
    (hresponder : players 1 = responderPolicy response)
    (environment : (application window).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation TestPlayer))
    (next : (application window).PolicyExecution)
    (hnext : next ∈ ((application window).runPolicies players environment schedule
      (MessageApplication.PolicyExecution.initial (application window) (initial window))).support)
    (hsubmitted : publicationSubmitted (next.principalHistory 1) = true) :
    (application window).SubmittedPayload (.publish .expire) (next.principalHistory 1) := by
  have hlaw := responder_history_law response players hresponder environment schedule next hnext
  simp only [publicationSubmitted, List.any_eq_true] at hsubmitted
  obtain ⟨entry, hentry, hpublication⟩ := hsubmitted
  cases hcommand : entry.command with
  | privateCommand command | replay id | wait => simp [hcommand] at hpublication
  | submit payload =>
      cases payload with
      | publish request =>
          have hrequest := (hlaw entry hentry).1 request hcommand
          subst request
          exact ⟨entry, hentry, hcommand⟩
      | bind handle | expireInitial | respond value | expireResponse | cleartext value |
          malformed => simp [hcommand] at hpublication

/-- A recorded responder response is exactly the fixed controller's value at
the public signal and publication stored in that history entry's view. -/
theorem responder_responseSubmitted_exact
    (response : Bool → Option Bool → Bool)
    (players : TestPlayer → (application window).PlayerPolicy)
    (hresponder : players 1 = responderPolicy response)
    (environment : (application window).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation TestPlayer))
    (next : (application window).PolicyExecution)
    (hnext : next ∈ ((application window).runPolicies players environment schedule
      (MessageApplication.PolicyExecution.initial (application window) (initial window))).support)
    (hsubmitted : responseSubmitted (next.principalHistory 1) = true) :
    ∃ entry ∈ next.principalHistory 1, ∃ signal publication,
      entry.beforeView.application.signal = some signal ∧
        entry.beforeView.application.publication = some publication ∧
        entry.command = .submit (.respond (response signal publication)) := by
  have hlaw := responder_history_law response players hresponder environment schedule next hnext
  simp only [responseSubmitted, List.any_eq_true] at hsubmitted
  obtain ⟨entry, hentry, hresponse⟩ := hsubmitted
  cases hcommand : entry.command with
  | privateCommand command | replay id | wait => simp [hcommand] at hresponse
  | submit payload =>
      cases payload with
      | respond value =>
          obtain ⟨signal, publication, hsignal, hpublication, hvalue⟩ :=
            (hlaw entry hentry).2 value hcommand
          refine ⟨entry, hentry, signal, publication, hsignal, hpublication, ?_⟩
          rw [hcommand, hvalue]
      | bind handle | expireInitial | publish request | expireResponse | cleartext value |
          malformed => simp [hcommand] at hresponse

end VegasTests.OptionalDisclosure.DisclosureState
