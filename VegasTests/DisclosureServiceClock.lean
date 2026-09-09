/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosureService

/-! # Clock progress of the slotted disclosure service

The service's first twelve environment invocations preserve the public
application clock.  Its thirteenth invocation advances that clock by exactly
one.  These facts are independent of player policies and of the admitted
inclusion selector's choices.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Interaction GameTheory.Math.Probability

variable {window : Nat}

private theorem privateStep_clock (state : DisclosureState) (who : TestPlayer)
    (command : Nat × Bool) :
    (privateStep state who command).clock = state.clock := rfl

theorem handle_clock (state next : DisclosureState)
    (message : Message TestPlayer Payload)
    (hhandle : handle window state message = some next) :
    next.clock = state.clock := by
  cases message with
  | mk id payload =>
      cases payload with
      | bind reference | expireInitial | expireResponse =>
          simp only [handle] at hhandle
          split at hhandle <;> cases hhandle
          rfl
      | respond value =>
          simp only [handle, response_resolve_map] at hhandle
          split at hhandle <;> cases hhandle
          rfl
      | publish endpoint request =>
          have hendpoint := publish_endpoint window state next
            ⟨id, .publish endpoint request⟩ endpoint request rfl hhandle
          subst endpoint
          cases hresolve : (Publication.publicationSite (state.signalAt + window)).resolve?
              state.clock state.verifyOpening state.acceptedReference state.done (fun _ => true)
              ⟨id, request⟩ with
          | none =>
              simp only [handle, publication_resolve_addressed, hresolve] at hhandle
              simp only [Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hhandle
          | some result =>
              simp only [handle, publication_resolve_addressed, hresolve] at hhandle
              simp only [Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hhandle
              cases hhandle
              rfl
      | cleartext value | malformed => simp [handle] at hhandle

theorem includePending_clock
    (state : (application window).State) (id : MessageId TestPlayer) :
    ((application window).includePending state id).application.clock =
      state.application.clock := by
  change (state.pool.includeApplication state.application id (handle window)).application.clock =
    state.application.clock
  cases hlookup : state.pool.lookup id with
  | none =>
      rw [MessagePool.includeApplication_missing _ _ _ _ hlookup]
  | some message =>
      cases hhandle : handle window state.application message with
      | none =>
          rw [MessagePool.includeApplication_reject _ _ _ _ _ hlookup hhandle]
      | some next =>
          rw [MessagePool.includeApplication_accept _ _ _ _ _ _ hlookup hhandle]
          exact handle_clock state.application next message hhandle

private theorem playerStep_clock
    (who : TestPlayer) (execution next : (application window).PolicyExecution)
    (command : (application window).PlayerCommand)
    (hnext : next ∈ ((application window).playerStep who execution command).support) :
    next.native.application.clock = execution.native.application.clock := by
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
      exact privateStep_clock execution.native.application who command
  | submit payload | replay id =>
      simp only [MessageApplication.PlayerCommand.toAction, MessageApplication.step,
        FinDist.mem_support_pure] at hnative
      rw [hnative]
  | wait =>
      simp only [MessageApplication.PlayerCommand.toAction, FinDist.mem_support_pure] at hnative
      rw [hnative]

private theorem marker_clock (state next : DisclosureState)
    (hnext : next ∈ (environmentStep state .marker).support) :
    next.clock = state.clock := by
  simp only [environmentStep, FinDist.mem_support_pure] at hnext
  split at hnext <;> rw [hnext]

private theorem sample_clock (state next : DisclosureState)
    (hnext : next ∈ (environmentStep state .sample).support) :
    next.clock = state.clock := by
  simp only [environmentStep] at hnext
  split at hnext
  · simp only [FinDist.support_map, Set.mem_image] at hnext
    obtain ⟨signal, _, rfl⟩ := hnext
    rfl
  · simp only [FinDist.mem_support_pure] at hnext
    rw [hnext]

private theorem environmentStep_clock_of_command
    (execution next : (application window).PolicyExecution)
    (command : (application window).EnvironmentPolicyCommand)
    (hcommand : command = .wait ∨ (∃ observer id, command = .deliver observer id) ∨
      (∃ id, command = .include id) ∨ command = .application .marker ∨
      command = .application .sample)
    (hnext : next ∈ ((application window).environmentPolicyStep execution command).support) :
    next.native.application.clock = execution.native.application.clock := by
  have hnative : next.native ∈
      (((application window).environmentPolicyStep execution command).map
        MessageApplication.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  rw [MessageApplication.environmentStep_native] at hnative
  rcases hcommand with rfl | ⟨observer, id, rfl⟩ | ⟨id, rfl⟩ | rfl | rfl
  · simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
      FinDist.mem_support_pure] at hnative
    rw [hnative]
  · simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
      MessageApplication.step, FinDist.mem_support_pure] at hnative
    rw [hnative]
  · simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
      MessageApplication.step, FinDist.mem_support_pure] at hnative
    rw [hnative]
    exact includePending_clock execution.native id
  · simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
      MessageApplication.step, FinDist.support_map, Set.mem_image] at hnative
    obtain ⟨applicationNext, happlication, hstate⟩ := hnative
    rw [← hstate]
    exact marker_clock execution.native.application applicationNext happlication
  · simp only [MessageApplication.EnvironmentPolicyCommand.toAction,
      MessageApplication.step, FinDist.support_map, Set.mem_image] at hnative
    obtain ⟨applicationNext, happlication, hstate⟩ := hnative
    rw [← hstate]
    exact sample_clock execution.native.application applicationNext happlication

private theorem invoke_clock_before_advance
    (players : TestPlayer → (application window).PlayerPolicy)
    (selector : (application window).EnvironmentPolicy)
    (hselector : (application window).InclusionService (fun _ => True) selector)
    (execution next : (application window).PolicyExecution)
    (invocation : @MessageApplication.Invocation TestPlayer)
    (hphase : execution.environmentHistory.length % 13 ≠ 12)
    (hnext : next ∈ ((application window).invoke players (serviceEnvironment selector)
      execution invocation).support) :
    next.native.application.clock = execution.native.application.clock := by
  cases invocation with
  | player who =>
      simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨command, _, hstep⟩ := hnext
      exact playerStep_clock who execution next command hstep
  | environment =>
      simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨command, hcommand, hstep⟩ := hnext
      cases command with
      | deliver observer id =>
          exact environmentStep_clock_of_command execution next _
            (Or.inr (Or.inl ⟨observer, id, rfl⟩)) hstep
      | «include» id =>
          exact environmentStep_clock_of_command execution next _
            (Or.inr (Or.inr (Or.inl ⟨id, rfl⟩))) hstep
      | wait =>
          exact environmentStep_clock_of_command execution next _ (Or.inl rfl) hstep
      | application appCommand =>
          change EnvironmentCommand at appCommand
          cases appCommand with
          | marker =>
              exact environmentStep_clock_of_command execution next _
                (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hstep
          | sample =>
              exact environmentStep_clock_of_command execution next _
                (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hstep
          | advance clock =>
              have hindex : execution.environmentHistory.length % 13 = 0 ∨
                  execution.environmentHistory.length % 13 = 1 ∨
                  execution.environmentHistory.length % 13 = 2 ∨
                  execution.environmentHistory.length % 13 = 3 ∨
                  execution.environmentHistory.length % 13 = 4 ∨
                  execution.environmentHistory.length % 13 = 5 ∨
                  execution.environmentHistory.length % 13 = 6 ∨
                  execution.environmentHistory.length % 13 = 7 ∨
                  execution.environmentHistory.length % 13 = 8 ∨
                  execution.environmentHistory.length % 13 = 9 ∨
                  execution.environmentHistory.length % 13 = 10 ∨
                  execution.environmentHistory.length % 13 = 11 := by omega
              rcases hindex with hindex | hindex | hindex | hindex | hindex | hindex |
                  hindex | hindex | hindex | hindex | hindex | hindex
              · have hpolicy : serviceEnvironment selector execution.environmentHistory
                    execution.native.environmentView = FinDist.pure
                      (match execution.native.pool.pending with
                      | [] => .wait
                      | message :: _ => .deliver 0 message.id) := by
                    unfold serviceEnvironment
                    rw [hindex]
                    rfl
                rw [hpolicy] at hcommand
                cases hpending : execution.native.pool.pending <;>
                  simp [hpending] at hcommand
              · have hpolicy : serviceEnvironment selector execution.environmentHistory
                    execution.native.environmentView = FinDist.pure
                      (match execution.native.pool.pending with
                      | [] => .wait
                      | message :: _ => .deliver 1 message.id) := by
                    unfold serviceEnvironment
                    rw [hindex]
                    rfl
                rw [hpolicy] at hcommand
                cases hpending : execution.native.pool.pending <;>
                  simp [hpending] at hcommand
              all_goals first
                | have hallowed := serviceEnvironment_inclusions selector hselector
                    execution.environmentHistory execution.native.environmentView _
                    (show inclusionSlots execution.environmentHistory.length by
                      simp only [inclusionSlots]
                      omega) hcommand
                  cases hpending : execution.native.pool.pending with
                  | nil =>
                      simp only [MessageApplication.State.environmentView, hpending] at hallowed
                      contradiction
                  | cons message rest =>
                      simp only [MessageApplication.State.environmentView, hpending] at hallowed
                      obtain ⟨id, message, hlookup, hfalse⟩ := hallowed
                      cases hfalse
                | have hpolicy : serviceEnvironment selector execution.environmentHistory
                      execution.native.environmentView =
                      FinDist.pure (.application .marker) := by
                    unfold serviceEnvironment
                    rw [hindex]
                    rfl
                  rw [hpolicy] at hcommand
                  simp at hcommand
                | have hpolicy : serviceEnvironment selector execution.environmentHistory
                      execution.native.environmentView =
                      FinDist.pure (.application .sample) := by
                    unfold serviceEnvironment
                    rw [hindex]
                    rfl
                  rw [hpolicy] at hcommand
                  simp at hcommand

private theorem advance_clock (state next : DisclosureState)
    (hnext : next ∈ (environmentStep state (.advance (state.clock + 1))).support) :
    next.clock = state.clock + 1 := by
  simp only [environmentStep, FinDist.mem_support_pure] at hnext
  rw [hnext]
  split
  · rfl
  · omega

private theorem environmentPolicyStep_advance_clock
    (execution next : (application window).PolicyExecution)
    (hnext : next ∈ ((application window).environmentPolicyStep execution
      (.application (.advance (execution.native.application.clock + 1)))).support) :
    next.native.application.clock = execution.native.application.clock + 1 := by
  change (show DisclosureState from next.native.application).clock =
    (show DisclosureState from execution.native.application).clock + 1
  have hnative : next.native ∈
      (((application window).environmentPolicyStep execution
        (.application (.advance (execution.native.application.clock + 1)))).map
          MessageApplication.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  rw [MessageApplication.environmentStep_native] at hnative
  simp only [MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
    FinDist.support_map, Set.mem_image] at hnative
  obtain ⟨applicationNext, happlication, hstate⟩ := hnative
  rw [← hstate]
  exact advance_clock execution.native.application applicationNext happlication

private theorem invoke_advance_clock
    (players : TestPlayer → (application window).PlayerPolicy)
    (selector : (application window).EnvironmentPolicy)
    (execution next : (application window).PolicyExecution)
    (hphase : execution.environmentHistory.length % 13 = 12)
    (hnext : next ∈ ((application window).invoke players (serviceEnvironment selector)
      execution .environment).support) :
    next.native.application.clock = execution.native.application.clock + 1 := by
  simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at hnext
  obtain ⟨command, hcommand, hstep⟩ := hnext
  have hpolicy : serviceEnvironment selector execution.environmentHistory
      execution.native.environmentView = FinDist.pure
        (.application (.advance (execution.native.application.clock + 1))) := by
    unfold serviceEnvironment
    rw [hphase]
    rfl
  rw [hpolicy] at hcommand
  simp only [FinDist.mem_support_pure] at hcommand
  subst command
  change (show DisclosureState from next.native.application).clock =
    (show DisclosureState from execution.native.application).clock + 1
  exact environmentPolicyStep_advance_clock execution next hstep

private theorem runPolicies_clock_before_advance
    (players : TestPlayer → (application window).PlayerPolicy)
    (selector : (application window).EnvironmentPolicy)
    (hselector : (application window).InclusionService (fun _ => True) selector)
    (schedule : List (@MessageApplication.Invocation TestPlayer))
    (execution next : (application window).PolicyExecution)
    (hslots : ∀ offset < schedule.countP MessageApplication.Invocation.isEnvironment,
      (execution.environmentHistory.length + offset) % 13 ≠ 12)
    (hnext : next ∈ ((application window).runPolicies players (serviceEnvironment selector)
      schedule execution).support) :
    next.native.application.clock = execution.native.application.clock := by
  induction schedule generalizing execution with
  | nil =>
      simp only [MessageApplication.runPolicies, FinDist.mem_support_pure] at hnext
      subst next
      rfl
  | cons invocation rest ih =>
      simp only [MessageApplication.runPolicies, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨middle, hmiddle, hnext⟩ := hnext
      cases invocation with
      | player who =>
          simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
          obtain ⟨command, _, hstep⟩ := hmiddle
          have hclock := playerStep_clock who execution middle command hstep
          have hhistory := (application window).playerStep_environmentHistory
            who execution command middle hstep
          have htail := ih middle (by
            intro offset hoffset
            rw [hhistory]
            apply hslots offset
            simpa [MessageApplication.Invocation.isEnvironment] using hoffset) hnext
          exact htail.trans hclock
      | environment =>
          have hphase : execution.environmentHistory.length % 13 ≠ 12 := by
            simpa using hslots 0 (by
              simp [MessageApplication.Invocation.isEnvironment])
          have hclock := invoke_clock_before_advance players selector hselector
            execution middle .environment hphase hmiddle
          simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
          obtain ⟨command, _, hstep⟩ := hmiddle
          have hhistory := (application window).environmentStep_history_length
            execution command middle hstep
          have htail := ih middle (by
            intro offset hoffset
            rw [hhistory]
            have hslot := hslots (offset + 1) (by
              simp only [List.countP_cons, MessageApplication.Invocation.isEnvironment,
                ↓reduceIte]
              omega)
            omega) hnext
          exact htail.trans hclock

/-- One supported service cycle advances the public application clock exactly
once, independently of all player choices and all admitted inclusion choices. -/
theorem service_cycle_clock (players : TestPlayer → (application window).PlayerPolicy)
    (selector : (application window).EnvironmentPolicy)
    (hselector : (application window).InclusionService (fun _ => True) selector)
    (execution next : (application window).PolicyExecution)
    (hphase : execution.environmentHistory.length % 13 = 0)
    (hnext : next ∈ ((application window).runPolicies players (serviceEnvironment selector)
      serviceCycle execution).support) :
    next.native.application.clock = execution.native.application.clock + 1 := by
  let prelude := serviceArrivals ++
    (List.replicate 8 .environment ++ List.replicate 2 .environment)
  have hcycle : serviceCycle = prelude ++ [.environment] := by
    simp [serviceCycle, prelude, List.replicate_succ]
  rw [hcycle, MessageApplication.runPolicies_append] at hnext
  simp only [FinDist.support_bind, Set.mem_iUnion] at hnext
  obtain ⟨middle, hmiddle, hnext⟩ := hnext
  have hcount : prelude.countP MessageApplication.Invocation.isEnvironment = 12 := by
    decide
  have hprelude := runPolicies_clock_before_advance players selector hselector prelude
    execution middle (by
      intro offset hoffset
      rw [hcount] at hoffset
      omega) hmiddle
  have hhistory := (application window).runPolicies_environmentHistory_length players
    (serviceEnvironment selector) prelude execution middle hmiddle
  rw [hcount] at hhistory
  have hmiddlePhase : middle.environmentHistory.length % 13 = 12 := by omega
  simp only [MessageApplication.runPolicies, FinDist.support_bind, Set.mem_iUnion,
    FinDist.mem_support_pure] at hnext
  obtain ⟨advanced, hadvanced, hfinal⟩ := hnext
  subst next
  have hadvance := invoke_advance_clock players selector middle advanced hmiddlePhase hadvanced
  omega

/-- Any number of complete supported service cycles advances the public clock
by exactly the number of cycles. -/
theorem service_schedule_clock (players : TestPlayer → (application window).PlayerPolicy)
    (selector : (application window).EnvironmentPolicy)
    (hselector : (application window).InclusionService (fun _ => True) selector)
    (cycles : Nat) (execution next : (application window).PolicyExecution)
    (hphase : execution.environmentHistory.length % 13 = 0)
    (hnext : next ∈ ((application window).runPolicies players (serviceEnvironment selector)
      (serviceSchedule cycles) execution).support) :
    next.native.application.clock = execution.native.application.clock + cycles := by
  induction cycles generalizing execution with
  | zero =>
      simp only [serviceSchedule, List.replicate_zero, List.flatten_nil,
        MessageApplication.runPolicies, FinDist.mem_support_pure] at hnext
      subst next
      simp
  | succ cycles ih =>
      have hschedule : serviceSchedule (cycles + 1) =
          serviceCycle ++ serviceSchedule cycles := by
        simp [serviceSchedule, List.replicate_succ]
      rw [hschedule, MessageApplication.runPolicies_append] at hnext
      simp only [FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨middle, hmiddle, hnext⟩ := hnext
      have hcycle := service_cycle_clock players selector hselector execution middle
        hphase hmiddle
      have hhistory := (application window).runPolicies_environmentHistory_length players
        (serviceEnvironment selector) serviceCycle execution middle hmiddle
      have hcount : serviceCycle.countP MessageApplication.Invocation.isEnvironment = 13 := by
        decide
      rw [hcount] at hhistory
      have htail := ih middle (by omega) hnext
      omega

/-- info: 'VegasTests.OptionalDisclosure.DisclosureState.service_schedule_clock'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.DisclosureState.service_schedule_clock

end VegasTests.OptionalDisclosure.DisclosureState
