/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPolicies

/-! # Communication phases before application inclusion

Players can prepare, submit, replay, and wait while the environment delivers
pending packets or waits. During such a phase, existing pending envelopes are
retained. Application invariants need preservation only by private preparation;
the environment does not execute application transactions in this phase.
-/

noncomputable section

namespace Interaction.MessageApplication

open GameTheory.Math.Probability

universe uPrincipal

variable {Principal : Type uPrincipal} [DecidableEq Principal]
variable (app : MessageApplication Principal)

/-- This phase permits delivery and waiting, with no inclusion or application
trigger. It is a restriction on commands, not a promise of successful delivery. -/
def DeliveryOnly (during : Nat → Prop) (environment : app.EnvironmentPolicy) : Prop :=
  ∀ history view command, during history.length →
    command ∈ (environment history view).support →
    command = .wait ∨ ∃ observer id, command = .deliver observer id

theorem playerStep_arrival (invariant : app.Application → Prop)
    (hprivate : ∀ state who command, invariant state →
      invariant (app.privateStep state who command))
    (who : Principal) (execution next : app.PolicyExecution) (command : app.PlayerCommand)
    (hinvariant : invariant execution.native.application)
    (hnext : next ∈ (app.playerStep who execution command).support) :
    invariant next.native.application ∧
      execution.native.pool.pending.Sublist next.native.pool.pending := by
  have hnative : next.native ∈ ((app.playerStep who execution command).map
      PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  rw [playerStep_native] at hnative
  cases command with
  | privateCommand command =>
      simp only [PlayerCommand.toAction, step, FinDist.mem_support_pure] at hnative
      rw [hnative]
      exact ⟨hprivate _ who command hinvariant, List.Sublist.refl _⟩
  | submit payload =>
      simp only [PlayerCommand.toAction, step, FinDist.mem_support_pure] at hnative
      rw [hnative]
      exact ⟨hinvariant, List.sublist_append_left _ _⟩
  | replay id =>
      simp only [PlayerCommand.toAction, step, FinDist.mem_support_pure] at hnative
      rw [hnative]
      refine ⟨hinvariant, ?_⟩
      unfold MessagePool.replay
      split
      · exact List.sublist_append_left _ _
      · exact List.Sublist.refl _
  | wait =>
      simp only [PlayerCommand.toAction, FinDist.mem_support_pure] at hnative
      rw [hnative]
      exact ⟨hinvariant, List.Sublist.refl _⟩

theorem environmentStep_deliveryOnly (execution next : app.PolicyExecution)
    (command : app.EnvironmentPolicyCommand)
    (hcommand : command = .wait ∨ ∃ observer id, command = .deliver observer id)
    (hnext : next ∈ (app.environmentPolicyStep execution command).support) :
    next.native.application = execution.native.application ∧
      next.native.pool.pending = execution.native.pool.pending := by
  have hnative : next.native ∈ ((app.environmentPolicyStep execution command).map
      PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  rw [environmentStep_native] at hnative
  rcases hcommand with rfl | ⟨observer, id, rfl⟩
  · simp only [EnvironmentPolicyCommand.toAction, FinDist.mem_support_pure] at hnative
    rw [hnative]
    exact ⟨rfl, rfl⟩
  · simp only [EnvironmentPolicyCommand.toAction, step, FinDist.mem_support_pure] at hnative
    rw [hnative]
    refine ⟨rfl, ?_⟩
    unfold MessagePool.deliver
    split <;> rfl

/-- Arbitrary interleaved player traffic and delivery retain every pending
envelope and every application invariant preserved by private preparation.
The schedule may include randomized reactions to delivered content. -/
theorem arrival_phase (invariant : app.Application → Prop)
    (hprivate : ∀ state who command, invariant state →
      invariant (app.privateStep state who command))
    (players : Principal → app.PlayerPolicy) (during : Nat → Prop)
    (environment : app.EnvironmentPolicy) (hdelivery : app.DeliveryOnly during environment)
    (schedule : List (@Invocation Principal)) (execution next : app.PolicyExecution)
    (hslots : ∀ offset < schedule.countP Invocation.isEnvironment,
      during (execution.environmentHistory.length + offset))
    (hinvariant : invariant execution.native.application)
    (hnext : next ∈ (app.runPolicies players environment schedule execution).support) :
    invariant next.native.application ∧
      execution.native.pool.pending.Sublist next.native.pool.pending := by
  induction schedule generalizing execution with
  | nil =>
      simp only [runPolicies, FinDist.mem_support_pure] at hnext
      subst next
      exact ⟨hinvariant, List.Sublist.refl _⟩
  | cons invocation rest ih =>
      simp only [runPolicies, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨middle, hmiddle, hnext⟩ := hnext
      cases invocation with
      | player who =>
          simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
          obtain ⟨command, _, hstep⟩ := hmiddle
          have hstate := app.playerStep_arrival invariant hprivate
            who execution middle command hinvariant hstep
          have hhistory := app.playerStep_environmentHistory who execution command middle hstep
          have htail := ih middle (by
            intro offset hoffset
            rw [hhistory]
            apply hslots offset
            simpa [Invocation.isEnvironment] using hoffset) hstate.1 hnext
          exact ⟨htail.1, hstate.2.trans htail.2⟩
      | environment =>
          simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
          obtain ⟨command, hcommand, hstep⟩ := hmiddle
          have hslot : during execution.environmentHistory.length := by
            simpa using hslots 0 (by simp [Invocation.isEnvironment])
          have hstate := app.environmentStep_deliveryOnly execution middle command
            (hdelivery _ _ command hslot hcommand) hstep
          have hhistory := app.environmentStep_history_length execution command middle hstep
          have htail := ih middle (by
            intro offset hoffset
            rw [hhistory]
            convert hslots (offset + 1) (by
              simp only [List.countP_cons, Invocation.isEnvironment, ↓reduceIte]
              omega) using 1
            omega) (by rw [hstate.1]; exact hinvariant) hnext
          exact ⟨htail.1, by rw [← hstate.2]; exact htail.2⟩

end Interaction.MessageApplication
