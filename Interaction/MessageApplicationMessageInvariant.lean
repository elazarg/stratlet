/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPolicyInvariant

/-! # Application invariants guarded by retained-message safety

An application handler may preserve an invariant only for a selected class of
messages.  This module composes that local fact with the carrier invariant for
all pending, included, delivered, and sent messages.  The result concerns the
existing policy runner and does not restrict unrelated policy behavior beyond
the stated safety of messages that a supported submission creates.
-/

noncomputable section

namespace Interaction.MessageApplication

open GameTheory.Math.Probability

universe uPrincipal

variable {Principal : Type uPrincipal} (app : MessageApplication Principal)

private theorem includePending_application_invariant_of_satisfies
    [DecidableEq Principal]
    (safe : Message Principal app.Payload → Prop)
    (invariant : app.Application → Prop)
    (hhandler : ∀ application message next, invariant application → safe message →
      app.handle application message = some next → invariant next)
    (state : app.State) (id : MessageId Principal)
    (hsafe : state.pool.Satisfies safe) (hinvariant : invariant state.application) :
    invariant (app.includePending state id).application := by
  cases hlookup : state.pool.lookup id with
  | none =>
      rw [app.includePending_missing state id hlookup]
      exact hinvariant
  | some message =>
      have hmessage : safe message :=
        hsafe.1 message (List.mem_of_find?_eq_some hlookup)
      cases hresult : app.handle state.application message with
      | none =>
          rw [app.includePending_reject state id message hlookup hresult]
          exact hinvariant
      | some result =>
          rw [app.includePending_accept state id message result hlookup hresult]
          exact hhandler _ _ _ hinvariant hmessage hresult

/-- Message safety and an application invariant are preserved together by an
actual supported policy run.  Submission safety is required only for commands
that the player policy supports at the execution where they are selected. -/
theorem runPolicies_message_application_invariant [DecidableEq Principal]
    (safe : Message Principal app.Payload → Prop)
    (invariant : app.Application → Prop)
    (hprivate : ∀ application who command, invariant application →
      invariant (app.privateStep application who command))
    (hhandler : ∀ application message next, invariant application → safe message →
      app.handle application message = some next → invariant next)
    (henvironment : ∀ application command next, invariant application →
      next ∈ (app.environmentStep application command).support → invariant next)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (hsubmit : ∀ (execution : app.PolicyExecution) (who : Principal)
      (payload : app.Payload),
      .submit payload ∈ (players who (execution.principalHistory who)
        (State.observe app execution.native who)).support →
      ∀ serial, safe ⟨(who, serial), payload⟩)
    (schedule : List (@Invocation Principal)) (execution next : app.PolicyExecution)
    (hsafe : execution.native.pool.Satisfies safe)
    (hinvariant : invariant execution.native.application)
    (hnext : next ∈ (app.runPolicies players environment schedule execution).support) :
    next.native.pool.Satisfies safe ∧ invariant next.native.application := by
  apply app.runPolicies_execution_invariant
    (fun current => current.native.pool.Satisfies safe ∧
      invariant current.native.application)
    players environment ?_ ?_ schedule execution next ⟨hsafe, hinvariant⟩ hnext
  · intro current who command final hcurrent hcommand hfinal
    have hpool := app.playerStep_pool_satisfies safe who current final command
      hcurrent.1 (by
        intro payload hcommandSubmit
        subst command
        exact hsubmit current who payload hcommand
          (current.native.pool.nextSerial who)) hfinal
    have hnative : final.native ∈
        ((app.playerStep who current command).map PolicyExecution.native).support := by
      rw [FinDist.support_map]
      exact ⟨final, hfinal, rfl⟩
    rw [app.playerStep_native] at hnative
    refine ⟨hpool, ?_⟩
    cases command with
    | privateCommand privateCommand =>
        simp only [PlayerCommand.toAction, step, FinDist.mem_support_pure] at hnative
        rw [hnative]
        exact hprivate _ _ _ hcurrent.2
    | submit payload | replay id | wait =>
        simp only [PlayerCommand.toAction, step, FinDist.mem_support_pure] at hnative
        rw [hnative]
        exact hcurrent.2
  · intro current command final hcurrent _ hfinal
    have hpool := app.environmentPolicyStep_pool_satisfies safe current final command
      hcurrent.1 hfinal
    have hnative : final.native ∈
        ((app.environmentPolicyStep current command).map PolicyExecution.native).support := by
      rw [FinDist.support_map]
      exact ⟨final, hfinal, rfl⟩
    rw [app.environmentStep_native] at hnative
    refine ⟨hpool, ?_⟩
    cases command with
    | deliver observer id =>
        simp only [EnvironmentPolicyCommand.toAction, step,
          FinDist.mem_support_pure] at hnative
        rw [hnative]
        exact hcurrent.2
    | «include» id =>
        simp only [EnvironmentPolicyCommand.toAction, step, FinDist.mem_support_pure] at hnative
        rw [hnative]
        exact includePending_application_invariant_of_satisfies app safe invariant hhandler
          current.native id hcurrent.1 hcurrent.2
    | application applicationCommand =>
        simp only [EnvironmentPolicyCommand.toAction, step, FinDist.support_map,
          Set.mem_image] at hnative
        obtain ⟨applicationNext, hsupported, hnative⟩ := hnative
        rw [← hnative]
        exact henvironment _ _ _ hcurrent.2 hsupported
    | wait =>
        simp only [EnvironmentPolicyCommand.toAction, FinDist.mem_support_pure] at hnative
        rw [hnative]
        exact hcurrent.2

end Interaction.MessageApplication

/-- info: 'Interaction.MessageApplication.runPolicies_message_application_invariant' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.MessageApplication.runPolicies_message_application_invariant
