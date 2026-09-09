/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.ChoiceController

/-! # Actual-run history laws for sample-once choice controllers

These laws connect the controller's list-level cache to the real
`MessageApplication` policy runner.  The first ready invocation records exactly
one draw from the supplied kernel, while every later continuation retains the
earliest recorded value.
-/

noncomputable section

namespace Interaction.MessageApplication

open GameTheory.Math.Probability

universe uPrincipal uValue uInput

variable {Principal : Type uPrincipal} (app : MessageApplication Principal)
variable {Value : Type uValue} {Input : Type uInput}

namespace ChoiceController

/-- The complete first-invocation law samples the decision kernel and runs the
actual encoded command. Native state, traffic, and both kinds of local history
remain in the outcome; this is not just a cached-value marginal. -/
theorem invoke_uncached_ready [DecidableEq Principal]
    (controller : ChoiceController app Value Input) (who : Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (execution : app.PolicyExecution) (input : Input)
    (hpolicy : players who (execution.principalHistory who)
      (State.observe app execution.native who) =
        controller.policy app (execution.principalHistory who)
          (State.observe app execution.native who))
    (hresolved : controller.resolved (State.observe app execution.native who) = false)
    (hcache : controller.codec.cachedValue app
      (execution.principalHistory who) = none)
    (hready : controller.ready (State.observe app execution.native who) = true)
    (hreadout : controller.readout? (execution.principalHistory who)
      (State.observe app execution.native who) = some input) :
    app.invoke players environment execution (.player who) =
      (controller.kernel input).bind fun value =>
        app.playerStep who execution (controller.codec.encode value) := by
  rw [invoke, hpolicy, controller.policy_of_uncached_ready app
    (execution.principalHistory who) (State.observe app execution.native who)
    input hresolved hcache hready hreadout, FinDist.bind_map]

/-- A ready, unresolved invocation with no cached command records exactly
the source-kernel draw in the principal's actual command history.  Application
state effects of the command cannot alter this projected law. -/
theorem invoke_uncached_ready_cachedValue [DecidableEq Principal]
    (controller : ChoiceController app Value Input) (who : Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (execution : app.PolicyExecution) (input : Input)
    (hpolicy : players who (execution.principalHistory who)
      (State.observe app execution.native who) =
        controller.policy app (execution.principalHistory who)
          (State.observe app execution.native who))
    (hresolved : controller.resolved (State.observe app execution.native who) = false)
    (hcache : controller.codec.cachedValue app
      (execution.principalHistory who) = none)
    (hready : controller.ready (State.observe app execution.native who) = true)
    (hreadout : controller.readout? (execution.principalHistory who)
      (State.observe app execution.native who) = some input) :
    (app.invoke players environment execution (.player who)).map
        (fun next => controller.codec.cachedValue app
          (next.principalHistory who)) =
      (controller.kernel input).map some := by
  rw [controller.invoke_uncached_ready app who players environment execution input
    hpolicy hresolved hcache hready hreadout, FinDist.map_bind]
  apply FinDist.bind_congr
  intro value _
  cases hcommand : controller.codec.encode value
  all_goals
    have hrecorded := controller.codec.cachedValue_append_encoded_of_none
      app (execution.principalHistory who)
        (State.observe app execution.native who) value hcache
    rw [hcommand] at hrecorded
    simpa [playerStep, advance, PlayerCommand.toAction, step] using
      congrArg FinDist.pure hrecorded

/-- info: 'Interaction.MessageApplication.ChoiceController.invoke_uncached_ready_cachedValue'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms invoke_uncached_ready_cachedValue

end ChoiceController

namespace ChoiceEncoding

/-- Once an endpoint value occurs in a principal's actual history, recording
any further player command preserves that earliest value. -/
theorem playerStep_cachedValue_of_some [DecidableEq Principal]
    (encoding : ChoiceEncoding Value app.PlayerCommand) (who : Principal)
    (execution next : app.PolicyExecution) (command : app.PlayerCommand)
    (value : Value)
    (hcache : encoding.cachedValue app
      (execution.principalHistory who) = some value)
    (hnext : next ∈ (app.playerStep who execution command).support) :
    encoding.cachedValue app (next.principalHistory who) = some value := by
  rw [playerStep_history_self app who execution command next hnext]
  exact encoding.cachedValue_append_of_some app _ _ value hcache

/-- Arbitrary later player and environment invocations cannot replace an
endpoint's earliest cached value.  No settlement or liveness premise is used. -/
theorem runPolicies_cachedValue_of_some [DecidableEq Principal]
    (encoding : ChoiceEncoding Value app.PlayerCommand) (who : Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (schedule : List (@Invocation Principal)) (execution next : app.PolicyExecution)
    (value : Value)
    (hcache : encoding.cachedValue app
      (execution.principalHistory who) = some value)
    (hnext : next ∈
      (app.runPolicies players environment schedule execution).support) :
    encoding.cachedValue app (next.principalHistory who) = some value := by
  induction schedule generalizing execution with
  | nil =>
      simp only [runPolicies, FinDist.mem_support_pure] at hnext
      subst next
      exact hcache
  | cons invocation rest ih =>
      simp only [runPolicies, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨middle, hmiddle, hnext⟩ := hnext
      apply ih middle ?_ hnext
      cases invocation with
      | player actor =>
          simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
          obtain ⟨command, _, hstep⟩ := hmiddle
          by_cases hactor : actor = who
          · subst actor
            exact encoding.playerStep_cachedValue_of_some app who execution
              middle command value hcache hstep
          · rw [app.playerStep_other_history actor who (Ne.symm hactor)
                execution command middle hstep]
            exact hcache
      | environment =>
          simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
          obtain ⟨command, _, hstep⟩ := hmiddle
          rw [congrFun
            (app.environmentStep_principalHistory execution command middle hstep) who]
          exact hcache

/-- info: 'Interaction.MessageApplication.ChoiceEncoding.runPolicies_cachedValue_of_some'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runPolicies_cachedValue_of_some

end ChoiceEncoding

end Interaction.MessageApplication
