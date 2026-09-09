/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPolicies

/-! # Message-application policy history laws

Local laws of a fixed principal's supported policy commands hold for every
entry recorded in that principal's history, independently of the other
policies and the invocation schedule.
-/

noncomputable section

namespace Interaction.MessageApplication

open GameTheory.Math.Probability

universe uPrincipal

variable {Principal : Type uPrincipal} (app : MessageApplication Principal)

/-- A law satisfied by every command supported by one principal's policy is
satisfied by every entry appended to that principal's history. Existing
entries need only satisfy the same law at the start of the run. -/
theorem runPolicies_principalHistory_forall [DecidableEq Principal]
    (who : Principal) (entryLaw : app.View → app.PlayerCommand → Prop)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (hpolicy : ∀ history view command,
      command ∈ (players who history view).support → entryLaw view command)
    (schedule : List (@Invocation Principal)) (execution next : app.PolicyExecution)
    (hinitial : ∀ entry ∈ execution.principalHistory who,
      entryLaw entry.beforeView entry.command)
    (hnext : next ∈ (app.runPolicies players environment schedule execution).support) :
    ∀ entry ∈ next.principalHistory who, entryLaw entry.beforeView entry.command := by
  induction schedule generalizing execution with
  | nil =>
      simp only [runPolicies, FinDist.mem_support_pure] at hnext
      subst next
      exact hinitial
  | cons invocation rest ih =>
      simp only [runPolicies, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨middle, hmiddle, hnext⟩ := hnext
      apply ih middle ?_ hnext
      cases invocation with
      | player actor =>
          simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
          obtain ⟨command, hcommand, hstep⟩ := hmiddle
          by_cases hactor : actor = who
          · subst actor
            rw [playerStep_history_self app who execution command middle hstep]
            intro entry hentry
            simp only [List.mem_append, List.mem_singleton] at hentry
            rcases hentry with hentry | rfl
            · exact hinitial entry hentry
            · exact hpolicy (execution.principalHistory who)
                (State.observe app execution.native who) command hcommand
          · rw [app.playerStep_other_history actor who (Ne.symm hactor)
                execution command middle hstep]
            exact hinitial
      | environment =>
          simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
          obtain ⟨command, _, hstep⟩ := hmiddle
          rw [congrFun (app.environmentStep_principalHistory execution command middle hstep) who]
          exact hinitial

end Interaction.MessageApplication
