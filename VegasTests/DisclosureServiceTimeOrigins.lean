/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosureInitialService
import VegasTests.DisclosureServiceState

/-! # Signal time origins under the disclosure service

The public signal records the clock at which it was sampled.  Once present,
both the signal and that time origin survive every native or policy-driven
continuation.  Combined with exact service-clock progress, this makes the
publication deadline strictly overdue by cycle `2 * window + 2`, without
asserting that any publication request is submitted or included.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Interaction GameTheory.Math.Probability

variable {window : Nat}

/-- A present public signal cannot have been sampled after the current clock. -/
def SignalTimeValid (state : DisclosureState) : Prop :=
  state.signal.isSome = true → state.signalAt ≤ state.clock

theorem empty_signalTimeValid : SignalTimeValid empty := by
  simp [SignalTimeValid, empty]

private theorem privateStep_signalTimeValid (state : DisclosureState) (who : TestPlayer)
    (command : Nat × Bool) (hstate : SignalTimeValid state) :
    SignalTimeValid (privateStep state who command) := by
  exact hstate

private theorem handle_signalTimeValid (state : DisclosureState)
    (message : Message TestPlayer Payload) (next : DisclosureState)
    (hstate : SignalTimeValid state)
    (hhandle : handle window state message = some next) : SignalTimeValid next := by
  have hsignal := handle_signal_fixed state next message hhandle
  have hclock := handle_clock state next message hhandle
  intro hpresent
  rw [hsignal.2, hclock]
  apply hstate
  rwa [hsignal.1] at hpresent

private theorem environmentStep_signalTimeValid (state : DisclosureState)
    (command : EnvironmentCommand) (next : DisclosureState) (hstate : SignalTimeValid state)
    (hnext : next ∈ (environmentStep state command).support) : SignalTimeValid next := by
  cases command with
  | marker =>
      simp only [environmentStep, FinDist.mem_support_pure] at hnext
      split at hnext <;> subst next <;> exact hstate
  | sample =>
      simp only [environmentStep] at hnext
      split at hnext
      · simp only [FinDist.support_map, Set.mem_image] at hnext
        obtain ⟨signal, _, rfl⟩ := hnext
        simp [SignalTimeValid]
      · simp only [FinDist.mem_support_pure] at hnext
        subst next
        exact hstate
  | advance clock =>
      simp only [environmentStep, FinDist.mem_support_pure] at hnext
      split at hnext
      · rename_i hclock
        subst next
        intro hpresent
        exact (hstate hpresent).trans hclock
      · subst next
        exact hstate

/-- `signalAt ≤ clock` is a native invariant of every supported continuation. -/
theorem run_signalTimeValid (state next : (application window).State)
    (actions : List (application window).Action) (hstate : SignalTimeValid state.application)
    (hnext : next ∈ ((application window).run actions state).support) :
    SignalTimeValid next.application := by
  exact (application window).run_application_invariant SignalTimeValid
    privateStep_signalTimeValid (handle_signalTimeValid (window := window))
    environmentStep_signalTimeValid
    state next actions hstate hnext

/-- `signalAt ≤ clock` is preserved by arbitrary players, environments, and schedules. -/
theorem runPolicies_signalTimeValid
    (players : TestPlayer → (application window).PlayerPolicy)
    (environment : (application window).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation TestPlayer))
    (execution next : (application window).PolicyExecution)
    (hstate : SignalTimeValid execution.native.application)
    (hnext : next ∈ ((application window).runPolicies players environment schedule
      execution).support) : SignalTimeValid next.native.application := by
  exact (application window).runPolicies_application_invariant SignalTimeValid
    privateStep_signalTimeValid (handle_signalTimeValid (window := window))
    environmentStep_signalTimeValid
    players environment schedule execution next hstate hnext

private theorem environmentStep_signal_origin (state : DisclosureState)
    (command : EnvironmentCommand) (next : DisclosureState) (signal : Bool) (origin : Nat)
    (hstate : state.signal = some signal ∧ state.signalAt = origin)
    (hnext : next ∈ (environmentStep state command).support) :
    next.signal = some signal ∧ next.signalAt = origin := by
  cases command with
  | marker =>
      simp only [environmentStep, FinDist.mem_support_pure] at hnext
      split at hnext <;> subst next <;> exact hstate
  | sample =>
      have hsample : environmentStep state .sample = FinDist.pure state := by
        simp [environmentStep, hstate.1]
      rw [hsample] at hnext
      simp only [FinDist.mem_support_pure] at hnext
      subst next
      exact hstate
  | advance clock =>
      simp only [environmentStep, FinDist.mem_support_pure] at hnext
      split at hnext <;> subst next <;> exact hstate

/-- Once sampled, the signal and its exact sampling clock survive every native run. -/
theorem run_signal_origin (state next : (application window).State)
    (actions : List (application window).Action) (signal : Bool)
    (hsignal : state.application.signal = some signal)
    (hnext : next ∈ ((application window).run actions state).support) :
    next.application.signal = some signal ∧
      next.application.signalAt = state.application.signalAt := by
  apply (application window).run_application_invariant
    (fun current => current.signal = some signal ∧
      current.signalAt = state.application.signalAt)
    ?_ ?_ ?_ state next actions ⟨hsignal, rfl⟩ hnext
  · intro current who command hcurrent
    exact hcurrent
  · intro current message final hcurrent hhandle
    have hfixed := handle_signal_fixed current final message hhandle
    exact ⟨hfixed.1.trans hcurrent.1, hfixed.2.trans hcurrent.2⟩
  · intro current command final hcurrent hfinal
    exact environmentStep_signal_origin current command final signal
      state.application.signalAt hcurrent hfinal

/-- Once sampled, the signal and its exact sampling clock survive arbitrary
policy-driven continuations. -/
theorem runPolicies_signal_origin
    (players : TestPlayer → (application window).PlayerPolicy)
    (environment : (application window).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation TestPlayer))
    (execution next : (application window).PolicyExecution) (signal : Bool)
    (hsignal : execution.native.application.signal = some signal)
    (hnext : next ∈ ((application window).runPolicies players environment schedule
      execution).support) :
    next.native.application.signal = some signal ∧
      next.native.application.signalAt = execution.native.application.signalAt := by
  apply (application window).runPolicies_application_invariant
    (fun current => current.signal = some signal ∧
      current.signalAt = execution.native.application.signalAt)
    ?_ ?_ ?_ players environment schedule execution next ⟨hsignal, rfl⟩ hnext
  · intro current who command hcurrent
    exact hcurrent
  · intro current message final hcurrent hhandle
    have hfixed := handle_signal_fixed current final message hhandle
    exact ⟨hfixed.1.trans hcurrent.1, hfixed.2.trans hcurrent.2⟩
  · intro current command final hcurrent hfinal
    exact environmentStep_signal_origin current command final signal
      execution.native.application.signalAt hcurrent hfinal

/-- A present signal at the end of the fixed service tail was sampled strictly
before the clock value at that cycle boundary. -/
theorem service_tail_signalAt_lt_clock
    (players : TestPlayer → (application window).PlayerPolicy)
    (selector : (application window).EnvironmentPolicy)
    (execution next : (application window).PolicyExecution)
    (hphase : execution.environmentHistory.length % 13 = 10)
    (hvalid : SignalTimeValid execution.native.application)
    (hsignal : next.native.application.signal.isSome = true)
    (hnext : next ∈ ((application window).runPolicies players (serviceEnvironment selector)
      (List.replicate 3 .environment) execution).support) :
    next.native.application.signalAt < next.native.application.clock := by
  obtain ⟨marked, sampled, hmarked, hsampled, hadvanced⟩ :=
    service_tail_steps players selector execution next hphase hnext
  obtain ⟨markedApplication, hmarkedApplication, hmarkedState⟩ :=
    environmentPolicyStep_application_support execution marked .marker hmarked
  obtain ⟨sampledApplication, hsampledApplication, hsampledState⟩ :=
    environmentPolicyStep_application_support marked sampled .sample hsampled
  obtain ⟨nextApplication, hnextApplication, hnextState⟩ :=
    environmentPolicyStep_application_support sampled next
      (.advance (sampled.native.application.clock + 1)) hadvanced
  have hmarkedValid : SignalTimeValid marked.native.application := by
    rw [hmarkedState]
    exact environmentStep_signalTimeValid execution.native.application .marker
      markedApplication hvalid hmarkedApplication
  have hmarkedApplicationValid : SignalTimeValid markedApplication := by
    rw [← hmarkedState]
    exact hmarkedValid
  have hsampledApplication' : sampledApplication ∈
      (environmentStep markedApplication .sample).support := by
    rw [← hmarkedState]
    exact hsampledApplication
  have hsampledApplicationValid : SignalTimeValid sampledApplication :=
    environmentStep_signalTimeValid markedApplication .sample sampledApplication
      hmarkedApplicationValid hsampledApplication'
  have hsampledValid : SignalTimeValid sampled.native.application := by
    rw [hsampledState]
    exact hsampledApplicationValid
  have hnextExact : nextApplication =
      { sampled.native.application with clock := sampled.native.application.clock + 1 } := by
    simp only [environmentStep, FinDist.mem_support_pure] at hnextApplication
    simpa using hnextApplication
  have hstateExact : next.native.application =
      { sampled.native.application with clock := sampled.native.application.clock + 1 } := by
    rw [hnextState, hnextExact]
  have hsampledSignal : sampled.native.application.signal.isSome = true := by
    simpa [hstateExact] using hsignal
  have hle := hsampledValid hsampledSignal
  rw [hstateExact]
  simp only
  omega

/-- At a complete service-cycle boundary, every present signal has a strictly
earlier time origin. -/
theorem service_cycle_signalAt_lt_clock
    (players : TestPlayer → (application window).PlayerPolicy)
    (selector : (application window).EnvironmentPolicy)
    (execution next : (application window).PolicyExecution)
    (hphase : execution.environmentHistory.length % 13 = 0)
    (hvalid : SignalTimeValid execution.native.application)
    (hsignal : next.native.application.signal.isSome = true)
    (hnext : next ∈ ((application window).runPolicies players (serviceEnvironment selector)
      serviceCycle execution).support) :
    next.native.application.signalAt < next.native.application.clock := by
  let prelude := serviceArrivals ++ List.replicate 8 .environment
  have hcycle : serviceCycle = prelude ++ List.replicate 3 .environment := by
    simp [serviceCycle, prelude]
  rw [hcycle, MessageApplication.runPolicies_append] at hnext
  simp only [FinDist.support_bind, Set.mem_iUnion] at hnext
  obtain ⟨middle, hmiddle, hnext⟩ := hnext
  have hmiddleValid := runPolicies_signalTimeValid players (serviceEnvironment selector)
    prelude execution middle hvalid hmiddle
  have hhistory := (application window).runPolicies_environmentHistory_length players
    (serviceEnvironment selector) prelude execution middle hmiddle
  have hcount : prelude.countP MessageApplication.Invocation.isEnvironment = 10 := by
    decide
  rw [hcount] at hhistory
  exact service_tail_signalAt_lt_clock players selector middle next (by omega)
    hmiddleValid hsignal hnext

/-- After any positive number of complete service cycles, every present signal
has a strictly earlier time origin. -/
theorem service_schedule_signalAt_lt_clock
    (players : TestPlayer → (application window).PlayerPolicy)
    (selector : (application window).EnvironmentPolicy)
    (cycles : Nat) (hcycles : 0 < cycles)
    (execution next : (application window).PolicyExecution)
    (hphase : execution.environmentHistory.length % 13 = 0)
    (hvalid : SignalTimeValid execution.native.application)
    (hsignal : next.native.application.signal.isSome = true)
    (hnext : next ∈ ((application window).runPolicies players (serviceEnvironment selector)
      (serviceSchedule cycles) execution).support) :
    next.native.application.signalAt < next.native.application.clock := by
  obtain ⟨priorCycles, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : cycles ≠ 0)
  have hschedule : serviceSchedule (priorCycles + 1) =
      serviceSchedule priorCycles ++ serviceCycle := by
    simp [serviceSchedule, List.replicate_succ']
  rw [hschedule, MessageApplication.runPolicies_append] at hnext
  simp only [FinDist.support_bind, Set.mem_iUnion] at hnext
  obtain ⟨middle, hmiddle, hnext⟩ := hnext
  have hmiddleValid := runPolicies_signalTimeValid players (serviceEnvironment selector)
    (serviceSchedule priorCycles) execution middle hvalid hmiddle
  have hhistory := (application window).runPolicies_environmentHistory_length players
    (serviceEnvironment selector) (serviceSchedule priorCycles) execution middle hmiddle
  have hcount : (serviceSchedule priorCycles).countP
      MessageApplication.Invocation.isEnvironment = priorCycles * 13 := by
    simp [serviceSchedule, serviceCycle, serviceArrivals,
      MessageApplication.Invocation.isEnvironment]
  rw [hcount] at hhistory
  exact service_cycle_signalAt_lt_clock players selector middle next (by omega)
    hmiddleValid hsignal hnext

/-- From the canonical service game, the signal exists and its publication
deadline is strictly overdue at every cycle at or after `2 * window + 2`.
This is a timing fact only: it does not assert submission or inclusion of a
publication resolver. -/
theorem responder_signal_overdue_by_cycle
    (response : Bool → Option Bool → Bool)
    (players : TestPlayer → (application window).PlayerPolicy)
    (hresponder : players 1 = responderPolicy (pureResponseDecision response))
    (selector : (application window).EnvironmentPolicy)
    (hselector : (application window).InclusionService (fun _ => True) selector)
    (cycles : Nat) (hcycles : 2 * window + 2 ≤ cycles)
    (next : (application window).PolicyExecution)
    (hnext : next ∈ ((serviceGame window cycles selector).play players).support) :
    ∃ signal, next.native.application.signal = some signal ∧
      next.native.application.signalAt + window < next.native.application.clock := by
  let prefixCycles := window + 2
  let suffixCycles := cycles - prefixCycles
  have hprefix : prefixCycles ≤ cycles := by
    dsimp [prefixCycles]
    omega
  obtain ⟨middle, hmiddle, hnext⟩ :=
    service_game_prefix players selector cycles prefixCycles hprefix next hnext
  have hboundary := service_game_invariants players selector hselector prefixCycles middle hmiddle
  have hmilestone := responder_initial_by_cycle response players hresponder selector hselector
    prefixCycles (by simp [prefixCycles]) middle hmiddle
  cases hsignal : middle.native.application.signal with
  | none => simp [hsignal] at hmilestone
  | some signal =>
      refine ⟨signal, ?_⟩
      have hphase : middle.environmentHistory.length % 13 = 0 := by
        rw [hboundary.2.1]
        omega
      have hstrict := service_schedule_signalAt_lt_clock players selector prefixCycles
        (by simp [prefixCycles])
        (MessageApplication.PolicyExecution.initial (application window) (initial window))
        middle rfl empty_signalTimeValid (by simp [hsignal]) hmiddle
      have hsuffix : window ≤ suffixCycles := by
        dsimp [suffixCycles, prefixCycles]
        omega
      have horigin := runPolicies_signal_origin players (serviceEnvironment selector)
        (serviceSchedule suffixCycles) middle next signal hsignal hnext
      have hclock := service_schedule_clock players selector hselector suffixCycles middle next
        hphase hnext
      refine ⟨horigin.1, ?_⟩
      rw [horigin.2, hclock]
      omega

end VegasTests.OptionalDisclosure.DisclosureState
