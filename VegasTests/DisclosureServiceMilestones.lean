/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosureService

/-! # Milestones established by the fixed service tail

The last three environment invocations of each service cycle run the marker,
sample, and clock-advance commands.  This file records their effect on the
disclosure milestones without assuming settlement or global liveness.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure.DisclosureState

open Interaction GameTheory.Math.Probability

variable {window : Nat}

theorem environmentPolicyStep_application_support
    (execution next : (application window).PolicyExecution)
    (command : EnvironmentCommand)
    (hnext : next ∈ ((application window).environmentPolicyStep execution
      (.application command)).support) :
    ∃ applicationNext,
      applicationNext ∈ (environmentStep execution.native.application command).support ∧
      next.native.application = applicationNext := by
  have hnative : next.native ∈
      (((application window).environmentPolicyStep execution
        (.application command)).map MessageApplication.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  rw [MessageApplication.environmentStep_native] at hnative
  simp only [MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
    FinDist.support_map, Set.mem_image] at hnative
  obtain ⟨applicationNext, happlication, hstate⟩ := hnative
  exact ⟨applicationNext, happlication,
    (congrArg MessageApplication.State.application hstate).symm⟩

private theorem marker_milestones (state next : DisclosureState)
    (hnext : next ∈ (environmentStep state .marker).support) :
    next.accepted = state.accepted ∧ next.publication = state.publication ∧
      next.response = state.response := by
  simp only [environmentStep, FinDist.mem_support_pure] at hnext
  split at hnext <;> subst next <;> simp

private theorem marker_progress (state next : DisclosureState)
    (haccepted : state.accepted.isSome = true)
    (hnext : next ∈ (environmentStep state .marker).support) :
    next.markerDone = true := by
  simp only [environmentStep, FinDist.mem_support_pure] at hnext
  split at hnext
  · subst next
    rfl
  · rename_i hnot
    subst next
    simpa [haccepted] using hnot

private theorem sample_milestones (state next : DisclosureState)
    (hnext : next ∈ (environmentStep state .sample).support) :
    next.accepted = state.accepted ∧ next.publication = state.publication ∧
      next.response = state.response := by
  simp only [environmentStep] at hnext
  split at hnext
  · simp only [FinDist.support_map, Set.mem_image] at hnext
    obtain ⟨signal, _, rfl⟩ := hnext
    simp
  · simp only [FinDist.mem_support_pure] at hnext
    subst next
    simp

private theorem sample_progress (state next : DisclosureState)
    (hmarker : state.markerDone = true)
    (hnext : next ∈ (environmentStep state .sample).support) :
    next.markerDone = true ∧ next.signal.isSome = true := by
  cases hsignal : state.signal with
  | none =>
      simp only [environmentStep, hmarker, hsignal, Option.isNone_none,
        Bool.true_and, if_true, FinDist.support_map, Set.mem_image] at hnext
      obtain ⟨signal, _, rfl⟩ := hnext
      simp
  | some signal =>
      simp only [environmentStep, hmarker, hsignal, Option.isNone_some,
        Bool.and_false, Bool.false_eq_true, if_false, FinDist.mem_support_pure] at hnext
      subst next
      simp [hmarker, hsignal]

private theorem advance_milestones (state next : DisclosureState) (clock : Nat)
    (hnext : next ∈ (environmentStep state (.advance clock)).support) :
    next.accepted = state.accepted ∧ next.markerDone = state.markerDone ∧
      next.signal = state.signal ∧ next.publication = state.publication ∧
      next.response = state.response := by
  simp only [environmentStep, FinDist.mem_support_pure] at hnext
  split at hnext <;> subst next <;> simp

theorem service_tail_steps
    (players : TestPlayer → (application window).PlayerPolicy)
    (selector : (application window).EnvironmentPolicy)
    (execution next : (application window).PolicyExecution)
    (hphase : execution.environmentHistory.length % 13 = 10)
    (hnext : next ∈ ((application window).runPolicies players (serviceEnvironment selector)
      (List.replicate 3 .environment) execution).support) :
    ∃ marked sampled,
      marked ∈ ((application window).environmentPolicyStep execution
        (.application .marker)).support ∧
      sampled ∈ ((application window).environmentPolicyStep marked
        (.application .sample)).support ∧
      next ∈ ((application window).environmentPolicyStep sampled
        (.application (.advance (sampled.native.application.clock + 1)))).support := by
  simp only [List.replicate_succ, List.replicate_zero, MessageApplication.runPolicies,
    FinDist.support_bind, Set.mem_iUnion, FinDist.mem_support_pure] at hnext
  obtain ⟨marked, hmarked, sampled, hsampled, advanced, hadvanced, hfinal⟩ := hnext
  subst next
  have hmarkerPolicy : serviceEnvironment selector execution.environmentHistory
      execution.native.environmentView = FinDist.pure (.application .marker) := by
    unfold serviceEnvironment
    rw [hphase]
    rfl
  simp only [MessageApplication.invoke, hmarkerPolicy, FinDist.pure_bind] at hmarked
  have hmarkedHistory := (application window).environmentStep_history_length execution
    (.application .marker) marked hmarked
  have hsamplePhase : marked.environmentHistory.length % 13 = 11 := by omega
  have hsamplePolicy : serviceEnvironment selector marked.environmentHistory
      marked.native.environmentView = FinDist.pure (.application .sample) := by
    unfold serviceEnvironment
    rw [hsamplePhase]
    rfl
  simp only [MessageApplication.invoke, hsamplePolicy, FinDist.pure_bind] at hsampled
  have hsampledHistory := (application window).environmentStep_history_length marked
    (.application .sample) sampled hsampled
  have hadvancePhase : sampled.environmentHistory.length % 13 = 12 := by omega
  have hadvancePolicy : serviceEnvironment selector sampled.environmentHistory
      sampled.native.environmentView = FinDist.pure
        (.application (.advance (sampled.native.application.clock + 1))) := by
    unfold serviceEnvironment
    rw [hadvancePhase]
    rfl
  simp only [MessageApplication.invoke, hadvancePolicy, FinDist.pure_bind] at hadvanced
  exact ⟨marked, sampled, hmarked, hsampled, hadvanced⟩

/-- The fixed marker/sample/advance tail preserves every previously reached
binding, publication, and response milestone. -/
theorem service_tail_preserves_milestones
    (players : TestPlayer → (application window).PlayerPolicy)
    (selector : (application window).EnvironmentPolicy)
    (execution next : (application window).PolicyExecution)
    (hphase : execution.environmentHistory.length % 13 = 10)
    (hnext : next ∈ ((application window).runPolicies players (serviceEnvironment selector)
      (List.replicate 3 .environment) execution).support) :
    next.native.application.accepted = execution.native.application.accepted ∧
      next.native.application.publication = execution.native.application.publication ∧
      next.native.application.response = execution.native.application.response := by
  obtain ⟨marked, sampled, hmarked, hsampled, hadvanced⟩ :=
    service_tail_steps players selector execution next hphase hnext
  obtain ⟨markedApplication, hmarkedApplication, hmarkedNative⟩ :=
    environmentPolicyStep_application_support execution marked .marker hmarked
  obtain ⟨sampledApplication, hsampledApplication, hsampledNative⟩ :=
    environmentPolicyStep_application_support marked sampled .sample hsampled
  obtain ⟨advancedApplication, hadvancedApplication, hadvancedNative⟩ :=
    environmentPolicyStep_application_support sampled next
      (.advance (sampled.native.application.clock + 1)) hadvanced
  have hm := marker_milestones execution.native.application markedApplication hmarkedApplication
  have hs := sample_milestones marked.native.application sampledApplication hsampledApplication
  have ha := advance_milestones sampled.native.application advancedApplication _
    hadvancedApplication
  rw [hmarkedNative] at hs
  rw [hsampledNative] at ha
  rw [hadvancedNative]
  exact ⟨ha.1.trans (hs.1.trans hm.1),
    ha.2.2.2.1.trans (hs.2.1.trans hm.2.1),
    ha.2.2.2.2.trans (hs.2.2.trans hm.2.2)⟩

/-- If a binding exists on entry, the same fixed tail completes the marker
and samples a signal.  No inclusion or settlement assumption is used. -/
theorem service_tail_establishes_marker_signal
    (players : TestPlayer → (application window).PlayerPolicy)
    (selector : (application window).EnvironmentPolicy)
    (execution next : (application window).PolicyExecution)
    (hphase : execution.environmentHistory.length % 13 = 10)
    (haccepted : execution.native.application.accepted.isSome = true)
    (hnext : next ∈ ((application window).runPolicies players (serviceEnvironment selector)
      (List.replicate 3 .environment) execution).support) :
    next.native.application.markerDone = true ∧
      next.native.application.signal.isSome = true := by
  obtain ⟨marked, sampled, hmarked, hsampled, hadvanced⟩ :=
    service_tail_steps players selector execution next hphase hnext
  obtain ⟨markedApplication, hmarkedApplication, hmarkedNative⟩ :=
    environmentPolicyStep_application_support execution marked .marker hmarked
  obtain ⟨sampledApplication, hsampledApplication, hsampledNative⟩ :=
    environmentPolicyStep_application_support marked sampled .sample hsampled
  obtain ⟨advancedApplication, hadvancedApplication, hadvancedNative⟩ :=
    environmentPolicyStep_application_support sampled next
      (.advance (sampled.native.application.clock + 1)) hadvanced
  have hmarker := marker_progress execution.native.application markedApplication
    haccepted hmarkedApplication
  rw [← hmarkedNative] at hmarker
  have hsample := sample_progress marked.native.application sampledApplication
    hmarker hsampledApplication
  rw [← hsampledNative] at hsample
  have hadvanceMilestones := advance_milestones sampled.native.application
    advancedApplication _ hadvancedApplication
  change (show DisclosureState from next.native.application).markerDone = true ∧
    (show DisclosureState from next.native.application).signal.isSome = true
  rw [hadvancedNative]
  exact ⟨hadvanceMilestones.2.1.trans hsample.1,
    congrArg Option.isSome hadvanceMilestones.2.2.1 |>.trans hsample.2⟩

end VegasTests.OptionalDisclosure.DisclosureState
