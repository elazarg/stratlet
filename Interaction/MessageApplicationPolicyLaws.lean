/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPolicies
import Interaction.MessageApplicationLaws

/-! # Native support refinement for message-application policies -/

noncomputable section

namespace Interaction.MessageApplication

open GameTheory.Math.Probability

universe uPrincipal

variable {Principal : Type uPrincipal} (app : MessageApplication Principal)

private theorem advance_support [DecidableEq Principal]
    (execution : app.PolicyExecution) (action : Option app.Action)
    (advanced : app.State × List app.Action)
    (hadvanced : advanced ∈ (app.advance execution action).support) :
    ∃ suffix, advanced.2 = execution.nativeTrace ++ suffix ∧
      advanced.1 ∈ (app.run suffix execution.native).support := by
  cases action with
  | none =>
      simp only [advance, FinDist.mem_support_pure] at hadvanced
      subst advanced
      exact ⟨[], by simp⟩
  | some action =>
      simp only [advance, FinDist.support_bind, Set.mem_iUnion] at hadvanced
      rcases hadvanced with ⟨next, hnext, hadvanced⟩
      simp only [FinDist.mem_support_pure] at hadvanced
      subst advanced
      refine ⟨[action], rfl, ?_⟩
      simp only [run_cons, run_nil, FinDist.support_bind, Set.mem_iUnion]
      exact ⟨next, hnext, FinDist.mem_support_pure.mpr rfl⟩

private theorem playerStep_support [DecidableEq Principal]
    (who : Principal) (execution : app.PolicyExecution) (command : app.PlayerCommand)
    (next : app.PolicyExecution)
    (hnext : next ∈ (app.playerStep who execution command).support) :
    ∃ suffix, next.nativeTrace = execution.nativeTrace ++ suffix ∧
      next.native ∈ (app.run suffix execution.native).support := by
  simp only [playerStep, FinDist.support_bind, Set.mem_iUnion] at hnext
  rcases hnext with ⟨advanced, hadvanced, hnext⟩
  simp only [FinDist.mem_support_pure] at hnext
  subst next
  exact advance_support app execution _ advanced hadvanced

private theorem environmentStep_support [DecidableEq Principal]
    (execution : app.PolicyExecution) (command : app.EnvironmentPolicyCommand)
    (next : app.PolicyExecution)
    (hnext : next ∈ (app.environmentPolicyStep execution command).support) :
    ∃ suffix, next.nativeTrace = execution.nativeTrace ++ suffix ∧
      next.native ∈ (app.run suffix execution.native).support := by
  simp only [environmentPolicyStep, FinDist.support_bind, Set.mem_iUnion] at hnext
  rcases hnext with ⟨advanced, hadvanced, hnext⟩
  simp only [FinDist.mem_support_pure] at hnext
  subst next
  exact advance_support app execution _ advanced hadvanced

private theorem invoke_support [DecidableEq Principal]
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (execution next : app.PolicyExecution) (invocation : @Invocation Principal)
    (hnext : next ∈ (app.invoke players environment execution invocation).support) :
    ∃ suffix, next.nativeTrace = execution.nativeTrace ++ suffix ∧
      next.native ∈ (app.run suffix execution.native).support := by
  cases invocation with
  | player who =>
      simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at hnext
      rcases hnext with ⟨command, _, hstep⟩
      exact playerStep_support app who execution command next hstep
  | environment =>
      simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at hnext
      rcases hnext with ⟨command, _, hstep⟩
      exact environmentStep_support app execution command next hstep

/-- Every supported policy outcome is supported by native execution of exactly
the action suffix appended to its proof-facing trace. -/
theorem runPolicies_native_support [DecidableEq Principal]
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (schedule : List (@Invocation Principal)) (execution next : app.PolicyExecution)
    (hnext : next ∈ (app.runPolicies players environment schedule execution).support) :
    ∃ suffix, next.nativeTrace = execution.nativeTrace ++ suffix ∧
      next.native ∈ (app.run suffix execution.native).support := by
  induction schedule generalizing execution with
  | nil =>
      simp only [runPolicies, FinDist.mem_support_pure] at hnext
      subst next
      exact ⟨[], by simp⟩
  | cons invocation rest ih =>
      simp only [runPolicies, FinDist.support_bind, Set.mem_iUnion] at hnext
      rcases hnext with ⟨middle, hmiddle, hnext⟩
      rcases invoke_support app players environment execution middle invocation hmiddle with
        ⟨first, hfirstTrace, hfirstRun⟩
      rcases ih middle hnext with ⟨second, hsecondTrace, hsecondRun⟩
      refine ⟨first ++ second, ?_, ?_⟩
      · rw [hsecondTrace, hfirstTrace, List.append_assoc]
      · rw [app.run_append, FinDist.support_bind]
        simp only [Set.mem_iUnion]
        exact ⟨middle.native, hfirstRun, hsecondRun⟩

/-- From the canonical empty policy execution, the recorded native trace is
itself a native execution witnessing every supported outcome. -/
theorem runPolicies_initial_native_support [DecidableEq Principal]
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (schedule : List (@Invocation Principal)) (initial : app.State)
    (next : app.PolicyExecution)
    (hnext : next ∈ (app.runPolicies players environment schedule
      (PolicyExecution.initial app initial)).support) :
    next.native ∈ (app.run next.nativeTrace initial).support := by
  rcases runPolicies_native_support app players environment schedule
      (PolicyExecution.initial app initial) next hnext with ⟨suffix, htrace, hrun⟩
  simp only [PolicyExecution.initial, List.nil_append] at htrace
  rwa [htrace]

/-- Any application invariant preserved by the native hooks holds throughout
every supported policy run from an invariant initial application state. -/
theorem runPolicies_initial_application_invariant [DecidableEq Principal]
    (invariant : app.Application → Prop)
    (hprivate : ∀ application who command, invariant application →
      invariant (app.privateStep application who command))
    (hhandler : ∀ application message next, invariant application →
      app.handle application message = some next → invariant next)
    (henvironment : ∀ application command next, invariant application →
      next ∈ (app.environmentStep application command).support → invariant next)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (schedule : List (@Invocation Principal)) (initial : app.State)
    (next : app.PolicyExecution) (hinitial : invariant initial.application)
    (hnext : next ∈ (app.runPolicies players environment schedule
      (PolicyExecution.initial app initial)).support) :
    invariant next.native.application := by
  exact app.run_application_invariant invariant hprivate hhandler henvironment
    initial next.native next.nativeTrace hinitial
    (runPolicies_initial_native_support app players environment schedule initial next hnext)

end Interaction.MessageApplication
