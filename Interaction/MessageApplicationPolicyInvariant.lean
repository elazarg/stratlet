/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPolicyLaws
import Interaction.MessageInvariant

/-! # Execution invariants for message-application policies

Unlike application-only invariants, these predicates may inspect the complete
policy execution: native state, principal histories, environment history, and
the proof-facing native trace.  The local preservation premises receive the
actual command selected by the corresponding policy.
-/

noncomputable section

namespace Interaction.MessageApplication

open GameTheory.Math.Probability

universe uPrincipal

variable {Principal : Type uPrincipal} (app : MessageApplication Principal)

/-- An execution predicate preserved by every locally supported policy command
is preserved by the complete supported policy run. -/
theorem runPolicies_execution_invariant [DecidableEq Principal]
    (invariant : app.PolicyExecution → Prop)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (hplayer : ∀ execution who command next, invariant execution →
      command ∈ (players who (execution.principalHistory who)
        (State.observe app execution.native who)).support →
      next ∈ (app.playerStep who execution command).support → invariant next)
    (henvironment : ∀ execution command next, invariant execution →
      command ∈ (environment execution.environmentHistory
        (State.environmentView app execution.native)).support →
      next ∈ (app.environmentPolicyStep execution command).support → invariant next)
    (schedule : List (@Invocation Principal)) (execution next : app.PolicyExecution)
    (hexecution : invariant execution)
    (hnext : next ∈ (app.runPolicies players environment schedule execution).support) :
    invariant next := by
  induction schedule generalizing execution with
  | nil =>
      simp only [runPolicies, FinDist.mem_support_pure] at hnext
      subst next
      exact hexecution
  | cons invocation rest ih =>
      simp only [runPolicies, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨middle, hmiddle, hnext⟩ := hnext
      apply ih middle ?_ hnext
      cases invocation with
      | player who =>
          simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
          obtain ⟨command, hcommand, hstep⟩ := hmiddle
          exact hplayer execution who command middle hexecution hcommand hstep
      | environment =>
          simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
          obtain ⟨command, hcommand, hstep⟩ := hmiddle
          exact henvironment execution command middle hexecution hcommand hstep

theorem playerStep_pool_satisfies [DecidableEq Principal]
    (safe : Message Principal app.Payload → Prop)
    (who : Principal) (execution next : app.PolicyExecution)
    (command : app.PlayerCommand)
    (hsafe : execution.native.pool.Satisfies safe)
    (hsubmit : ∀ payload, command = .submit payload →
      safe ⟨(who, execution.native.pool.nextSerial who), payload⟩)
    (hnext : next ∈ (app.playerStep who execution command).support) :
    next.native.pool.Satisfies safe := by
  have hnative : next.native ∈
      ((app.playerStep who execution command).map PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  rw [app.playerStep_native] at hnative
  cases command with
  | privateCommand privateCommand =>
      simp only [PlayerCommand.toAction, step, FinDist.mem_support_pure] at hnative
      rw [hnative]
      exact hsafe
  | submit payload =>
      simp only [PlayerCommand.toAction, step, FinDist.mem_support_pure] at hnative
      rw [hnative]
      exact hsafe.submit who payload (hsubmit payload rfl)
  | replay id =>
      simp only [PlayerCommand.toAction, step, FinDist.mem_support_pure] at hnative
      rw [hnative]
      exact hsafe.replay who id
  | wait =>
      simp only [PlayerCommand.toAction, FinDist.mem_support_pure] at hnative
      rw [hnative]
      exact hsafe

theorem environmentPolicyStep_pool_satisfies [DecidableEq Principal]
    (safe : Message Principal app.Payload → Prop)
    (execution next : app.PolicyExecution) (command : app.EnvironmentPolicyCommand)
    (hsafe : execution.native.pool.Satisfies safe)
    (hnext : next ∈ (app.environmentPolicyStep execution command).support) :
    next.native.pool.Satisfies safe := by
  have hnative : next.native ∈
      ((app.environmentPolicyStep execution command).map PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  rw [app.environmentStep_native] at hnative
  cases command with
  | deliver observer id =>
      simp only [EnvironmentPolicyCommand.toAction, step, FinDist.mem_support_pure] at hnative
      rw [hnative]
      exact hsafe.deliver observer id
  | «include» id =>
      simp only [EnvironmentPolicyCommand.toAction, step, FinDist.mem_support_pure] at hnative
      rw [hnative, includePending_pool]
      exact hsafe.includePending id
  | application applicationCommand =>
      simp only [EnvironmentPolicyCommand.toAction, step, FinDist.support_map,
        Set.mem_image] at hnative
      obtain ⟨applicationNext, _, hnative⟩ := hnative
      rw [← hnative]
      exact hsafe
  | wait =>
      simp only [EnvironmentPolicyCommand.toAction, FinDist.mem_support_pure] at hnative
      rw [hnative]
      exact hsafe

/-- Environment-only phases preserve message provenance without any premise
on player policies, since those policies are not invoked in the phase. -/
theorem runPolicies_environment_pool_satisfies [DecidableEq Principal]
    (safe : Message Principal app.Payload → Prop)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (count : Nat) (execution next : app.PolicyExecution)
    (hsafe : execution.native.pool.Satisfies safe)
    (hnext : next ∈ (app.runPolicies players environment
      (List.replicate count .environment) execution).support) :
    next.native.pool.Satisfies safe := by
  induction count generalizing execution with
  | zero =>
      simp only [List.replicate_zero, runPolicies, FinDist.mem_support_pure] at hnext
      subst next
      exact hsafe
  | succ count ih =>
      simp only [List.replicate_succ, runPolicies, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨middle, hmiddle, htail⟩ := hnext
      simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
      obtain ⟨command, _, hstep⟩ := hmiddle
      exact ih middle (app.environmentPolicyStep_pool_satisfies safe execution middle
        command hsafe hstep) htail

/-- If every submitted payload selected by a player policy is safe at every
possible serial, then all messages retained by the pool remain safe throughout
the policy run. Delivery, replay, and inclusion require no extra premise. -/
theorem runPolicies_pool_satisfies [DecidableEq Principal]
    (safe : Message Principal app.Payload → Prop)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (hsubmit : ∀ (execution : app.PolicyExecution) (who : Principal)
      (payload : app.Payload),
      .submit payload ∈ (players who (execution.principalHistory who)
        (State.observe app execution.native who)).support →
      ∀ serial, safe ⟨(who, serial), payload⟩)
    (schedule : List (@Invocation Principal)) (execution next : app.PolicyExecution)
    (hsafe : execution.native.pool.Satisfies safe)
    (hnext : next ∈ (app.runPolicies players environment schedule execution).support) :
    next.native.pool.Satisfies safe := by
  apply app.runPolicies_execution_invariant
    (fun current => current.native.pool.Satisfies safe) players environment
    ?_ ?_ schedule execution next hsafe hnext
  · intro current who command final hcurrent hcommand hfinal
    apply playerStep_pool_satisfies app safe who current final command hcurrent ?_ hfinal
    intro payload hsubmitCommand
    subst command
    exact hsubmit current who payload hcommand (current.native.pool.nextSerial who)
  · intro current command final hcurrent _ hfinal
    exact environmentPolicyStep_pool_satisfies app safe current final command hcurrent hfinal

end Interaction.MessageApplication
