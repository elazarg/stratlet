/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPolicyLaws
import Interaction.MessagePoolCounters

/-! # Message counters through application execution

The sender-local counter invariant is preserved by every native application
action and by the existing policy runner.  No policy, scheduling, handler, or
service restriction is required: only submission advances a counter, while
all other message operations retain existing envelopes.
-/

noncomputable section

namespace Interaction.MessageApplication

open GameTheory.Math.Probability

universe uPrincipal

variable {Principal : Type uPrincipal} [DecidableEq Principal]
variable (app : MessageApplication Principal)

/-- Every supported native action preserves the retained-envelope counter
invariant. -/
theorem step_serialsBeforeNext
    (state next : app.State) (action : app.Action)
    (hserials : state.pool.SerialsBeforeNext)
    (hnext : next ∈ (app.step state action).support) :
    next.pool.SerialsBeforeNext := by
  cases action with
  | privateCommand who command =>
      simp only [step, FinDist.mem_support_pure] at hnext
      subst next
      exact hserials
  | submit who payload =>
      simp only [step, FinDist.mem_support_pure] at hnext
      subst next
      exact hserials.submit who payload
  | replay who id =>
      simp only [step, FinDist.mem_support_pure] at hnext
      subst next
      exact hserials.replay who id
  | deliver who id =>
      simp only [step, FinDist.mem_support_pure] at hnext
      subst next
      exact hserials.deliver who id
  | «include» id =>
      simp only [step, FinDist.mem_support_pure] at hnext
      subst next
      rw [app.includePending_pool]
      exact hserials.includePending id
  | environment command =>
      simp only [step, FinDist.support_map, Set.mem_image] at hnext
      obtain ⟨application, _hsupported, rfl⟩ := hnext
      exact hserials

/-- The counter invariant is preserved through an actual native action list. -/
theorem run_serialsBeforeNext
    (state final : app.State) (actions : List app.Action)
    (hserials : state.pool.SerialsBeforeNext)
    (hfinal : final ∈ (app.run actions state).support) :
    final.pool.SerialsBeforeNext := by
  induction actions generalizing state with
  | nil =>
      simp only [run, FinDist.mem_support_pure] at hfinal
      subst final
      exact hserials
  | cons action rest ih =>
      simp only [run, FinDist.support_bind, Set.mem_iUnion] at hfinal
      obtain ⟨next, hnext, hfinal⟩ := hfinal
      exact ih next (app.step_serialsBeforeNext state next action hserials hnext) hfinal

/-- Arbitrary behavioral policies and invocation schedules preserve the
native pool's sender-local counter invariant. -/
theorem runPolicies_serialsBeforeNext
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (schedule : List (@Invocation Principal))
    (execution next : app.PolicyExecution)
    (hserials : execution.native.pool.SerialsBeforeNext)
    (hnext : next ∈
      (app.runPolicies players environment schedule execution).support) :
    next.native.pool.SerialsBeforeNext := by
  obtain ⟨suffix, _htrace, hnative⟩ :=
    app.runPolicies_native_support players environment schedule execution next hnext
  exact app.run_serialsBeforeNext execution.native next.native suffix hserials hnative

/-- Every supported policy execution from canonical message-state
initialization has a well-counted native pool. -/
theorem runPolicies_initial_serialsBeforeNext
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (schedule : List (@Invocation Principal)) (application : app.Application)
    (next : app.PolicyExecution)
    (hnext : next ∈
      (app.runPolicies players environment schedule
        (PolicyExecution.initial app (State.initial app application))).support) :
    next.native.pool.SerialsBeforeNext := by
  apply app.runPolicies_serialsBeforeNext players environment schedule
    (PolicyExecution.initial app (State.initial app application)) next
  · exact MessagePool.SerialsBeforeNext.empty
  · exact hnext

/-- Therefore the sender's current next serial is absent from pending lookup
at every supported initialized policy execution. -/
theorem runPolicies_initial_lookup_nextSerial_eq_none
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (schedule : List (@Invocation Principal)) (application : app.Application)
    (next : app.PolicyExecution)
    (hnext : next ∈
      (app.runPolicies players environment schedule
        (PolicyExecution.initial app (State.initial app application))).support)
    (who : Principal) :
    next.native.pool.lookup (who, next.native.pool.nextSerial who) = none :=
  (app.runPolicies_initial_serialsBeforeNext players environment schedule application
    next hnext).lookup_nextSerial_eq_none who

end Interaction.MessageApplication

/-- info: 'Interaction.MessageApplication.runPolicies_initial_lookup_nextSerial_eq_none'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.MessageApplication.runPolicies_initial_lookup_nextSerial_eq_none
