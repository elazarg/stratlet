/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPolicyInvariant
import VegasTests.DisclosureResponderHistory
import VegasTests.DisclosureServiceTimeOrigins

/-! # Responder choice provenance

Before publication, the unchanged responder cannot author a response packet.
After the public signal and publication are fixed, every responder-authored
response packet carries the controller's unique value on those public inputs.
Both statements cover the full message pool and survive arbitrary traffic,
delivery, inclusion, and replay.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Interaction GameTheory.Math.Probability

variable {window : Nat}

def ResponderPrePublicationMessage (message : Message TestPlayer Payload) : Prop :=
  message.sender = 1 → ∀ value, message.payload ≠ .respond value

def ResponderChoiceSafe (expected : Bool) (message : Message TestPlayer Payload) : Prop :=
  message.sender = 1 → ∀ value, message.payload = .respond value → value = expected

private theorem responder_command_before_publication
    (response : Bool → Option Bool → Bool)
    (history : List (application window).PlayerEntry) (view : (application window).View)
    (command : (application window).PlayerCommand)
    (hpublication : view.application.publication = none)
    (hcommand : command ∈ (responderPolicy (pureResponseDecision response) history view).support) :
    ∀ value, command ≠ .submit (.respond value) := by
  intro value heq
  subst command
  obtain ⟨_, _, _, hpublished, _⟩ :=
    responder_response_support response history view value hcommand
  rw [hpublication] at hpublished
  cases hpublished

private theorem responder_emitted_response_eq
    (response : Bool → Option Bool → Bool)
    (history : List (application window).PlayerEntry) (view : (application window).View)
    (signal : Bool) (publication : Option Bool) (value : Bool)
    (hsignal : view.application.signal = some signal)
    (hpublication : view.application.publication = some publication)
    (hemit : .submit (.respond value) ∈
      (responderPolicy (pureResponseDecision response) history view).support) :
    value = response signal publication := by
  obtain ⟨actualSignal, actualPublication, hsignal', hpublication', hvalue⟩ :=
    responder_response_support response history view value hemit
  have hsignalEq := Option.some.inj (hsignal'.symm.trans hsignal)
  have hpublicationEq := Option.some.inj (hpublication'.symm.trans hpublication)
  simpa only [hsignalEq, hpublicationEq] using hvalue

private theorem playerStep_signal_publication
    (who : TestPlayer) (execution next : (application window).PolicyExecution)
    (command : (application window).PlayerCommand)
    (hnext : next ∈ ((application window).playerStep who execution command).support) :
    next.native.application.signal = execution.native.application.signal ∧
      next.native.application.publication = execution.native.application.publication := by
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
      exact ⟨rfl, rfl⟩
  | submit payload | replay id | wait =>
      simp only [MessageApplication.PlayerCommand.toAction, MessageApplication.step,
        FinDist.mem_support_pure] at hnative
      rw [hnative]
      exact ⟨rfl, rfl⟩

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

private theorem includePending_publication_fixed
    (state : (application window).State) (id : MessageId TestPlayer)
    (publication : Option Bool) (hpublication : state.application.publication = some publication) :
    ((application window).includePending state id).application.publication = some publication := by
  apply (application window).includePending_application_invariant
    (fun current => current.publication = some publication) ?_ state id hpublication
  intro current message next hcurrent hhandle
  exact (handle_publication_fixed window current message next publication hcurrent hhandle).1.trans
    hcurrent

private theorem environmentPolicyStep_signal_publication
    (execution next : (application window).PolicyExecution)
    (command : (application window).EnvironmentPolicyCommand)
    (signal : Bool) (publication : Option Bool)
    (hsignal : execution.native.application.signal = some signal)
    (hpublication : execution.native.application.publication = some publication)
    (hnext : next ∈ ((application window).environmentPolicyStep execution command).support) :
    next.native.application.signal = some signal ∧
      next.native.application.publication = some publication := by
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
      exact ⟨hsignal, hpublication⟩
  | «include» id =>
      simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
        MessageApplication.step, FinDist.mem_support_pure] at hnative
      rw [hnative]
      exact ⟨by rw [(include_signal_fixed execution.native id).1]; exact hsignal,
        includePending_publication_fixed execution.native id publication hpublication⟩
  | application applicationCommand =>
      simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
        MessageApplication.step, FinDist.support_map, Set.mem_image] at hnative
      obtain ⟨applicationNext, happlication, hstate⟩ := hnative
      rw [← hstate]
      exact ⟨environmentStep_signal_of_some execution.native.application applicationNext
          applicationCommand signal hsignal happlication,
        (environmentStep_publication execution.native.application applicationNext
          applicationCommand happlication).trans hpublication⟩

private theorem environmentPolicyStep_publication_none_before
    (execution next : (application window).PolicyExecution)
    (command : (application window).EnvironmentPolicyCommand)
    (hnext : next ∈ ((application window).environmentPolicyStep execution command).support)
    (hnextPublication : next.native.application.publication = none) :
    execution.native.application.publication = none := by
  cases hpublication : execution.native.application.publication with
  | none => rfl
  | some publication =>
      have hfixed : next.native.application.publication = some publication := by
        cases hsignal : execution.native.application.signal with
        | some signal =>
            exact (environmentPolicyStep_signal_publication execution next command signal
              publication hsignal hpublication hnext).2
        | none =>
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
                rwa [hnative]
            | «include» id =>
                simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
                  MessageApplication.step, FinDist.mem_support_pure] at hnative
                rw [hnative]
                exact includePending_publication_fixed execution.native id publication hpublication
            | application applicationCommand =>
                simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
                  MessageApplication.step, FinDist.support_map, Set.mem_image] at hnative
                obtain ⟨applicationNext, happlication, hstate⟩ := hnative
                rw [← hstate]
                exact (environmentStep_publication execution.native.application applicationNext
                  applicationCommand happlication).trans hpublication
      rw [hfixed] at hnextPublication
      cases hnextPublication

private theorem responseSubmitted_append_nonresponse
    (history : List (application window).PlayerEntry)
    (view : (application window).View) (command : (application window).PlayerCommand)
    (hhistory : responseSubmitted history = false)
    (hcommand : ∀ value, command ≠ .submit (.respond value)) :
    responseSubmitted (history ++ [⟨view, command⟩]) = false := by
  unfold responseSubmitted at hhistory ⊢
  rw [List.any_append, hhistory]
  cases command with
  | privateCommand command | replay id | wait => simp
  | submit payload =>
      cases payload with
      | respond value => exact (hcommand value rfl).elim
      | bind handle | expireInitial | publish request | expireResponse | cleartext value |
          malformed => simp

/-- From initialization, an absent publication rules out responder response
submissions both in responder history and throughout the full message pool. -/
theorem responder_prePublication_provenance
    (response : Bool → Option Bool → Bool)
    (players : TestPlayer → (application window).PlayerPolicy)
    (hresponder : players 1 = responderPolicy (pureResponseDecision response))
    (environment : (application window).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation TestPlayer))
    (next : (application window).PolicyExecution)
    (hnext : next ∈ ((application window).runPolicies players environment schedule
      (MessageApplication.PolicyExecution.initial (application window) (initial window))).support)
    (hpublication : next.native.application.publication = none) :
    responseSubmitted (next.principalHistory 1) = false ∧
      next.native.pool.Satisfies ResponderPrePublicationMessage := by
  let Provenance := fun execution : (application window).PolicyExecution =>
    execution.native.application.publication = none →
      responseSubmitted (execution.principalHistory 1) = false ∧
        execution.native.pool.Satisfies ResponderPrePublicationMessage
  apply (application window).runPolicies_execution_invariant Provenance players environment
    ?_ ?_ schedule
    (MessageApplication.PolicyExecution.initial (application window) (initial window))
    next ?_ hnext hpublication
  · intro execution who command final hexecution hcommand hstep hfinalPublication
    have hfields := playerStep_signal_publication who execution final command hstep
    have hcurrentPublication : execution.native.application.publication = none :=
      hfields.2.symm.trans hfinalPublication
    have hcurrent := hexecution hcurrentPublication
    constructor
    · by_cases hwho : who = 1
      · subst who
        have hcommandSafe := responder_command_before_publication response
          (execution.principalHistory 1)
          (MessageApplication.State.observe (application window) execution.native 1)
          command (by
            simpa [MessageApplication.State.observe, application, observe] using
              hcurrentPublication)
          (by rw [← hresponder]; exact hcommand)
        rw [MessageApplication.playerStep_history_self (application window) 1 execution
          command final hstep]
        exact responseSubmitted_append_nonresponse (execution.principalHistory 1)
          (MessageApplication.State.observe (application window) execution.native 1)
          command hcurrent.1 hcommandSafe
      · rw [MessageApplication.playerStep_other_history (application window) who 1
          (Ne.symm hwho) execution command final hstep]
        exact hcurrent.1
    · apply (application window).playerStep_pool_satisfies
        ResponderPrePublicationMessage who execution final command hcurrent.2 ?_ hstep
      intro payload hsubmit
      subst command
      intro hsender value hpayload
      change who = 1 at hsender
      subst who
      change payload = .respond value at hpayload
      have hcommandSafe := responder_command_before_publication response
        (execution.principalHistory 1)
        (MessageApplication.State.observe (application window) execution.native 1)
        (.submit payload) hcurrentPublication
        (by rw [← hresponder]; exact hcommand)
      apply hcommandSafe value
      rw [hpayload]
  · intro execution command final hexecution _ hstep hfinalPublication
    have hcurrentPublication := environmentPolicyStep_publication_none_before execution final
      command hstep hfinalPublication
    have hcurrent := hexecution hcurrentPublication
    constructor
    · rw [MessageApplication.environmentStep_principalHistory (application window)
        execution command final hstep]
      exact hcurrent.1
    · exact (application window).environmentPolicyStep_pool_satisfies
        ResponderPrePublicationMessage execution final command hcurrent.2 hstep
  · intro _
    exact ⟨rfl, MessagePool.Satisfies.empty⟩

/-- Once signal and publication are fixed, every responder-authored response
packet in the full pool equals the unchanged responder's public-input choice. -/
theorem responder_choice_policy_provenance
    (response : Bool → Option Bool → Bool) (signal : Bool) (publication : Option Bool)
    (players : TestPlayer → (application window).PlayerPolicy)
    (hresponder : players 1 = responderPolicy (pureResponseDecision response))
    (environment : (application window).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation TestPlayer))
    (execution next : (application window).PolicyExecution)
    (hsignal : execution.native.application.signal = some signal)
    (hpublication : execution.native.application.publication = some publication)
    (hsafe : execution.native.pool.Satisfies
      (ResponderChoiceSafe (response signal publication)))
    (hnext : next ∈ ((application window).runPolicies players environment schedule
      execution).support) :
    next.native.pool.Satisfies (ResponderChoiceSafe (response signal publication)) := by
  let Provenance := fun current : (application window).PolicyExecution =>
    current.native.application.signal = some signal ∧
      current.native.application.publication = some publication ∧
      current.native.pool.Satisfies (ResponderChoiceSafe (response signal publication))
  have hinitial : Provenance execution := ⟨hsignal, hpublication, hsafe⟩
  have hfinal := (application window).runPolicies_execution_invariant Provenance
    players environment ?_ ?_ schedule execution next hinitial hnext
  · exact hfinal.2.2
  · intro current who command final hcurrent hcommand hstep
    have hfields := playerStep_signal_publication who current final command hstep
    refine ⟨hfields.1.trans hcurrent.1, hfields.2.trans hcurrent.2.1, ?_⟩
    apply (application window).playerStep_pool_satisfies
      (ResponderChoiceSafe (response signal publication)) who current final command
      hcurrent.2.2 ?_ hstep
    intro payload hsubmit
    subst command
    by_cases hwho : who = 1
    · subst who
      intro _ value hpayload
      change payload = .respond value at hpayload
      rw [hpayload] at hcommand
      apply responder_emitted_response_eq response (current.principalHistory 1)
        (MessageApplication.State.observe (application window) current.native 1)
        signal publication value
      · exact hcurrent.1
      · exact hcurrent.2.1
      · rw [← hresponder]
        exact hcommand
    · intro hsender
      simp [Message.sender, hwho] at hsender
  · intro current command final hcurrent _ hstep
    have hfields := environmentPolicyStep_signal_publication current final command signal
      publication hcurrent.1 hcurrent.2.1 hstep
    exact ⟨hfields.1, hfields.2,
      (application window).environmentPolicyStep_pool_satisfies
        (ResponderChoiceSafe (response signal publication)) current final command
        hcurrent.2.2 hstep⟩

private theorem playerStep_invariant
    (who : TestPlayer) (execution next : (application window).PolicyExecution)
    (command : (application window).PlayerCommand)
    (hinvariant : Invariant execution.native.application)
    (hnext : next ∈ ((application window).playerStep who execution command).support) :
    Invariant next.native.application := by
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
      exact privateStep_invariant execution.native.application who command hinvariant
  | submit payload | replay id | wait =>
      simp only [MessageApplication.PlayerCommand.toAction, MessageApplication.step,
        FinDist.mem_support_pure] at hnative
      rw [hnative]
      exact hinvariant

private theorem environmentPolicyStep_invariant
    (execution next : (application window).PolicyExecution)
    (command : (application window).EnvironmentPolicyCommand)
    (hinvariant : Invariant execution.native.application)
    (hnext : next ∈ ((application window).environmentPolicyStep execution command).support) :
    Invariant next.native.application := by
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
      exact hinvariant
  | «include» id =>
      simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
        MessageApplication.step, FinDist.mem_support_pure] at hnative
      rw [hnative]
      exact include_native_invariant execution.native id hinvariant
  | application applicationCommand =>
      simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
        MessageApplication.step, FinDist.support_map, Set.mem_image] at hnative
      obtain ⟨applicationNext, happlication, hstate⟩ := hnative
      rw [← hstate]
      exact environmentStep_invariant execution.native.application applicationCommand
        applicationNext hinvariant happlication

private def DynamicResponderProvenance (response : Bool → Option Bool → Bool)
    (execution : (application window).PolicyExecution) : Prop :=
  Invariant execution.native.application ∧
    (execution.native.application.publication = none →
      execution.native.pool.Satisfies ResponderPrePublicationMessage) ∧
    ∀ signal publication,
      execution.native.application.signal = some signal →
      execution.native.application.publication = some publication →
      execution.native.pool.Satisfies (ResponderChoiceSafe (response signal publication))

private theorem prePublication_implies_choice (expected : Bool)
    (message : Message TestPlayer Payload)
    (hsafe : ResponderPrePublicationMessage message) : ResponderChoiceSafe expected message := by
  intro hsender value hpayload
  exact (hsafe hsender value hpayload).elim

/-- From actual initialization, a fixed final signal and publication determine
every responder-authored response packet anywhere in the pool, including
packets moved by replay, delivery, or inclusion. -/
theorem responder_initialized_choice_provenance
    (response : Bool → Option Bool → Bool)
    (players : TestPlayer → (application window).PlayerPolicy)
    (hresponder : players 1 = responderPolicy (pureResponseDecision response))
    (environment : (application window).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation TestPlayer))
    (next : (application window).PolicyExecution)
    (hnext : next ∈ ((application window).runPolicies players environment schedule
      (MessageApplication.PolicyExecution.initial (application window) (initial window))).support)
    (signal : Bool) (publication : Option Bool)
    (hsignal : next.native.application.signal = some signal)
    (hpublication : next.native.application.publication = some publication) :
    next.native.pool.Satisfies (ResponderChoiceSafe (response signal publication)) := by
  have hdynamic := (application window).runPolicies_execution_invariant
    (DynamicResponderProvenance response) players environment ?_ ?_ schedule
    (MessageApplication.PolicyExecution.initial (application window) (initial window)) next
    ?_ hnext
  · exact hdynamic.2.2 signal publication hsignal hpublication
  · intro execution who command final hcurrent hcommand hstep
    have hfields := playerStep_signal_publication who execution final command hstep
    refine ⟨playerStep_invariant who execution final command hcurrent.1 hstep, ?_, ?_⟩
    · intro hfinalPublication
      have hcurrentPublication : execution.native.application.publication = none :=
        hfields.2.symm.trans hfinalPublication
      have hsafe := hcurrent.2.1 hcurrentPublication
      apply (application window).playerStep_pool_satisfies
        ResponderPrePublicationMessage who execution final command hsafe ?_ hstep
      intro payload hsubmit
      subst command
      intro hsender value hpayload
      change who = 1 at hsender
      subst who
      change payload = .respond value at hpayload
      have hcommandSafe := responder_command_before_publication response
        (execution.principalHistory 1)
        (MessageApplication.State.observe (application window) execution.native 1)
        (.submit payload) hcurrentPublication (by rw [← hresponder]; exact hcommand)
      apply hcommandSafe value
      rw [hpayload]
    · intro finalSignal finalPublication hfinalSignal hfinalPublication
      have hcurrentSignal : execution.native.application.signal = some finalSignal :=
        hfields.1.symm.trans hfinalSignal
      have hcurrentPublication : execution.native.application.publication =
          some finalPublication := hfields.2.symm.trans hfinalPublication
      have hsafe := hcurrent.2.2 finalSignal finalPublication hcurrentSignal
        hcurrentPublication
      apply (application window).playerStep_pool_satisfies
        (ResponderChoiceSafe (response finalSignal finalPublication)) who execution final
        command hsafe ?_ hstep
      intro payload hsubmit
      subst command
      by_cases hwho : who = 1
      · subst who
        intro _ value hpayload
        change payload = .respond value at hpayload
        rw [hpayload] at hcommand
        apply responder_emitted_response_eq response (execution.principalHistory 1)
          (MessageApplication.State.observe (application window) execution.native 1)
          finalSignal finalPublication value hcurrentSignal hcurrentPublication
        rw [← hresponder]
        exact hcommand
      · intro hsender
        simp [Message.sender, hwho] at hsender
  · intro execution command final hcurrent _ hstep
    refine ⟨environmentPolicyStep_invariant execution final command hcurrent.1 hstep, ?_, ?_⟩
    · intro hfinalPublication
      have hcurrentPublication := environmentPolicyStep_publication_none_before execution final
        command hstep hfinalPublication
      exact (application window).environmentPolicyStep_pool_satisfies
        ResponderPrePublicationMessage execution final command
        (hcurrent.2.1 hcurrentPublication) hstep
    · intro finalSignal finalPublication hfinalSignal hfinalPublication
      cases hcurrentPublication : execution.native.application.publication with
      | none =>
          have hpre := (application window).environmentPolicyStep_pool_satisfies
            ResponderPrePublicationMessage execution final command
            (hcurrent.2.1 hcurrentPublication) hstep
          exact hpre.mono (prePublication_implies_choice (response finalSignal finalPublication))
      | some currentPublication =>
          have hsome := hcurrent.1.2.2.2.1 (by simp [hcurrentPublication])
          cases hcurrentSignal : execution.native.application.signal with
          | none => simp [hcurrentSignal] at hsome
          | some currentSignal =>
              have hfixed := environmentPolicyStep_signal_publication execution final command
                currentSignal currentPublication hcurrentSignal hcurrentPublication hstep
              have hsignalEq : currentSignal = finalSignal := by
                rw [hfixed.1] at hfinalSignal
                exact Option.some.inj hfinalSignal
              have hpublicationEq : currentPublication = finalPublication := by
                rw [hfixed.2] at hfinalPublication
                exact Option.some.inj hfinalPublication
              subst currentSignal
              subst currentPublication
              exact (application window).environmentPolicyStep_pool_satisfies
                (ResponderChoiceSafe (response finalSignal finalPublication)) execution final
                command (hcurrent.2.2 finalSignal finalPublication hcurrentSignal
                  hcurrentPublication) hstep
  · refine ⟨empty_invariant, ?_, ?_⟩
    · intro _
      exact MessagePool.Satisfies.empty
    · intro signal publication hsignal _
      simp [MessageApplication.PolicyExecution.initial, initial,
        MessageApplication.State.initial, empty] at hsignal

end VegasTests.OptionalDisclosure.DisclosureState
