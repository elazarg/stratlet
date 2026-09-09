/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPolicyLaws

/-! # Bounded inclusion service for message applications

An inclusion service picks an existing pending identifier whenever the pool
is nonempty and waits otherwise. It may inspect the entire environment view
and its local history. The shared policy runner executes its selected native
inclusion; no sender callback is invoked. This is a service phase, not a
complete clock, delivery, or settlement discipline.
-/

noncomputable section

namespace Interaction.MessageApplication

open GameTheory.Math.Probability

universe uPrincipal

variable {Principal : Type uPrincipal} [DecidableEq Principal]
variable (app : MessageApplication Principal)

/-- A local operational service obligation, independent of application
acceptance and strategic correctness. It excludes censoring a nonempty pool
by waiting during a reserved inclusion opportunity. -/
def InclusionService (during : Nat → Prop) (environment : app.EnvironmentPolicy) : Prop :=
  ∀ history view command, during history.length →
    command ∈ (environment history view).support →
    match view.pool.pending with
    | [] => command = .wait
    | _ :: _ => ∃ id message, view.pool.lookup id = some message ∧ command = .include id

/-- FIFO is one service instance; the predicate also permits other orders,
including choices depending on public payloads and previous observations. -/
def includeFirst : app.EnvironmentPolicy := fun _ view => FinDist.pure <|
  match view.pool.pending with
  | [] => .wait
  | message :: _ => .include message.id

theorem includeFirst_service (during : Nat → Prop) :
    app.InclusionService during app.includeFirst := by
  intro history view command _ hcommand
  simp only [includeFirst, FinDist.mem_support_pure] at hcommand
  subst command
  cases hpending : view.pool.pending with
  | nil => rfl
  | cons message rest =>
      refine ⟨message.id, message, ?_, rfl⟩
      simp [MessagePool.lookup, hpending]

/-- One reserved service invocation consumes one pending copy, or preserves
the empty pool. Application success, malformed traffic, and duplicate IDs
do not affect this count. -/
theorem inclusion_step_length (players : Principal → app.PlayerPolicy)
    (during : Nat → Prop) (environment : app.EnvironmentPolicy)
    (hservice : app.InclusionService during environment)
    (execution next : app.PolicyExecution)
    (hslot : during execution.environmentHistory.length)
    (hnext : next ∈ (app.invoke players environment execution .environment).support) :
    next.native.pool.pending.length = execution.native.pool.pending.length - 1 ∧
      next.environmentHistory.length = execution.environmentHistory.length + 1 := by
  simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at hnext
  obtain ⟨command, hcommand, hnext⟩ := hnext
  refine ⟨?_, app.environmentStep_history_length execution command next hnext⟩
  have hallowed := hservice execution.environmentHistory execution.native.environmentView
    command hslot hcommand
  cases hpending : execution.native.pool.pending with
  | nil =>
      simp only [State.environmentView, hpending] at hallowed
      subst command
      rw [environmentStep_wait] at hnext
      simp only [FinDist.mem_support_pure] at hnext
      subst next
      simp [hpending]
  | cons first rest =>
      simp only [State.environmentView, hpending] at hallowed
      obtain ⟨id, message, hlookup, rfl⟩ := hallowed
      simp only [environmentPolicyStep, advance, EnvironmentPolicyCommand.toAction,
        step, FinDist.pure_bind, FinDist.mem_support_pure] at hnext
      subst next
      have hlength := MessagePool.include_pending_length execution.native.pool id message hlookup
      rw [includePending_pool]
      simp only [hpending] at hlength ⊢
      omega

/-- A bounded inclusion phase empties any queue within its initial size.
Players receive no invocation during this phase; arrivals before or between
phases require their own resource/opportunity bounds. -/
theorem inclusion_phase_length (players : Principal → app.PlayerPolicy)
    (during : Nat → Prop) (environment : app.EnvironmentPolicy)
    (hservice : app.InclusionService during environment)
    (count : Nat) (execution next : app.PolicyExecution)
    (hslots : ∀ offset < count, during (execution.environmentHistory.length + offset))
    (hnext : next ∈ (app.runPolicies players environment
      (List.replicate count .environment) execution).support) :
    next.native.pool.pending.length = execution.native.pool.pending.length - count := by
  induction count generalizing execution with
  | zero =>
      simp only [List.replicate_zero, runPolicies, FinDist.mem_support_pure] at hnext
      subst next
      simp
  | succ count ih =>
      simp only [List.replicate_succ, runPolicies, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨middle, hmiddle, hnext⟩ := hnext
      have hslot : during execution.environmentHistory.length := by
        simpa using hslots 0 (by omega)
      have hstep := app.inclusion_step_length players during environment hservice
        execution middle hslot hmiddle
      have hremaining : ∀ offset < count, during (middle.environmentHistory.length + offset) := by
        intro offset hoffset
        rw [hstep.2]
        convert hslots (offset + 1) (by omega) using 1
        omega
      have htail := ih middle hremaining hnext
      omega

theorem inclusion_phase_empty (players : Principal → app.PlayerPolicy)
    (during : Nat → Prop) (environment : app.EnvironmentPolicy)
    (hservice : app.InclusionService during environment)
    (count : Nat) (execution next : app.PolicyExecution)
    (hslots : ∀ offset < count, during (execution.environmentHistory.length + offset))
    (hcapacity : execution.native.pool.pending.length ≤ count)
    (hnext : next ∈ (app.runPolicies players environment
      (List.replicate count .environment) execution).support) :
    next.native.pool.pending = [] := by
  have hlength := app.inclusion_phase_length players during environment hservice
    count execution next hslots hnext
  cases hlist : next.native.pool.pending with
  | nil => rfl
  | cons message rest => simp [hlist] at hlength; omega

/-- Each principal invocation adds at most one pending message, even when
the sampled command is an arbitrary replay or malformed submission. -/
theorem player_step_pending_bound (who : Principal) (execution next : app.PolicyExecution)
    (command : app.PlayerCommand)
    (hnext : next ∈ (app.playerStep who execution command).support) :
    next.native.pool.pending.length ≤ execution.native.pool.pending.length + 1 := by
  have hmem : next.native ∈ ((app.playerStep who execution command).map
      PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  rw [playerStep_native] at hmem
  cases command with
  | privateCommand command =>
      simp only [PlayerCommand.toAction, step, FinDist.mem_support_pure] at hmem
      rw [hmem]
      simp
  | submit payload =>
      simp only [PlayerCommand.toAction, step, FinDist.mem_support_pure] at hmem
      rw [hmem]
      simp [MessagePool.submit]
  | replay id =>
      simp only [PlayerCommand.toAction, step, FinDist.mem_support_pure] at hmem
      rw [hmem]
      exact MessagePool.replay_pending_length_le execution.native.pool who id
  | wait =>
      simp only [PlayerCommand.toAction, FinDist.mem_support_pure] at hmem
      rw [hmem]
      simp

/-- Environment commands may publish, deliver, or update the application,
but cannot add pending messages. This includes rejected and missing includes. -/
theorem environment_step_pending_bound (execution next : app.PolicyExecution)
    (command : app.EnvironmentPolicyCommand)
    (hnext : next ∈ (app.environmentPolicyStep execution command).support) :
    next.native.pool.pending.length ≤ execution.native.pool.pending.length := by
  have hmem : next.native ∈ ((app.environmentPolicyStep execution command).map
      PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  rw [environmentStep_native] at hmem
  cases command with
  | deliver who id =>
      simp only [EnvironmentPolicyCommand.toAction, step, FinDist.mem_support_pure] at hmem
      rw [hmem, MessagePool.deliver_preserves_pending]
  | «include» id =>
      simp only [EnvironmentPolicyCommand.toAction, step, FinDist.mem_support_pure] at hmem
      rw [hmem, includePending_pool]
      cases hlookup : execution.native.pool.lookup id with
      | none => simp [MessagePool.includePending, hlookup, MessagePool.Result.invalid]
      | some message =>
          have hlength := MessagePool.include_pending_length
            execution.native.pool id message hlookup
          omega
  | application command =>
      simp only [EnvironmentPolicyCommand.toAction, step, FinDist.support_map,
        Set.mem_image] at hmem
      obtain ⟨application, _, hstate⟩ := hmem
      rw [← hstate]
  | wait =>
      simp only [EnvironmentPolicyCommand.toAction, FinDist.mem_support_pure] at hmem
      rw [hmem]

/-- Arrival capacity for an arbitrary interleaving, counting every player
invocation rather than only honest submissions. Delivery may occur before a
player reacts; the bound imposes no restriction on that reaction. -/
theorem runPolicies_pending_bound (players : Principal → app.PlayerPolicy)
    (environment : app.EnvironmentPolicy) (schedule : List (@Invocation Principal))
    (execution next : app.PolicyExecution)
    (hnext : next ∈ (app.runPolicies players environment schedule execution).support) :
    next.native.pool.pending.length ≤ execution.native.pool.pending.length +
      schedule.countP (fun invocation => !invocation.isEnvironment) := by
  induction schedule generalizing execution with
  | nil =>
      simp only [runPolicies, FinDist.mem_support_pure] at hnext
      subst next
      simp
  | cons invocation rest ih =>
      simp only [runPolicies, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨middle, hmiddle, hnext⟩ := hnext
      have htail := ih middle hnext
      simp only [Invocation.isEnvironment] at htail
      cases invocation with
      | player who =>
          simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
          obtain ⟨command, _, hstep⟩ := hmiddle
          have hbound := app.player_step_pending_bound who execution middle command hstep
          simp only [List.countP_cons, Invocation.isEnvironment, Bool.not_false, ↓reduceIte]
          omega
      | environment =>
          simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
          obtain ⟨command, _, hstep⟩ := hmiddle
          have hbound := app.environment_step_pending_bound execution middle command hstep
          simp only [List.countP_cons, Invocation.isEnvironment, Bool.not_true,
            Bool.false_eq_true, ↓reduceIte]
          omega

end Interaction.MessageApplication
