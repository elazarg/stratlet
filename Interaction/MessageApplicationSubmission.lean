/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationProgress

/-! # One-shot submission progress

A policy's local command history can justify waiting after one submission only
when the submitted envelope is still pending or the application milestone has
already occurred.  This module proves that bridge for one principal and one
exact payload.  Other policies and environment commands remain arbitrary; the
hypotheses concern only preservation of readiness and the milestone by the
application kernels.
-/

noncomputable section

namespace Interaction.MessageApplication

open GameTheory.Math.Probability

universe uPrincipal

variable {Principal : Type uPrincipal} [DecidableEq Principal]
variable (app : MessageApplication Principal)

/-- The principal has sampled an exact submission command at least once. -/
def SubmittedPayload (payload : app.Payload) (history : List app.PlayerEntry) : Prop :=
  ∃ entry ∈ history, entry.command = .submit payload

/-- A pending envelope authored by the named principal carries the exact
payload.  The serial is the one allocated by the native submission step. -/
def AuthoredPending (who : Principal) (payload : app.Payload) (state : app.State) : Prop :=
  ∃ serial, ({ id := (who, serial), payload } : Message Principal app.Payload) ∈
    state.pool.pending

/-- The proof state supporting a one-shot controller after submission. -/
def PendingOrResolved (ready milestone : app.Application → Prop)
    (who : Principal) (payload : app.Payload) (state : app.State) : Prop :=
  milestone state.application ∨
    (ready state.application ∧ app.AuthoredPending who payload state)

private theorem include_milestone
    (milestone : app.Application → Prop)
    (hhandler : ∀ application message next, milestone application →
      app.handle application message = some next → milestone next)
    (state : app.State) (id : MessageId Principal)
    (hstate : milestone state.application) :
    milestone (app.includePending state id).application :=
  app.includePending_application_invariant milestone hhandler state id hstate

private theorem include_ready_or_milestone
    (ready milestone : app.Application → Prop)
    (hhandler : ∀ application message next, ready application →
      app.handle application message = some next →
        ready next ∨ milestone next)
    (state : app.State) (id : MessageId Principal)
    (hstate : ready state.application) :
    ready (app.includePending state id).application ∨
      milestone (app.includePending state id).application := by
  cases hlookup : state.pool.lookup id with
  | none =>
      rw [app.includePending_missing state id hlookup]
      exact Or.inl hstate
  | some message =>
      cases hresult : app.handle state.application message with
      | none =>
          rw [app.includePending_reject state id message hlookup hresult]
          exact Or.inl hstate
      | some next =>
          rw [app.includePending_accept state id message next hlookup hresult]
          exact hhandler state.application message next hstate hresult

private theorem include_matching_resolves
    (ready milestone : app.Application → Prop)
    (who : Principal) (payload : app.Payload)
    (hresolve : ∀ application serial, ready application →
      ∃ next, app.handle application
        ({ id := (who, serial), payload } : Message Principal app.Payload) = some next ∧
          milestone next)
    (target : Message Principal app.Payload)
    (htarget : ∃ serial, target = { id := (who, serial), payload })
    (state : app.State) (id : MessageId Principal)
    (hready : ready state.application) (hlookup : state.pool.lookup id = some target) :
    milestone (app.includePending state id).application := by
  obtain ⟨serial, rfl⟩ := htarget
  obtain ⟨next, hhandle, hnext⟩ := hresolve state.application serial hready
  rw [app.includePending_accept state id _ next hlookup hhandle]
  exact hnext

private theorem step_pendingOrResolved
    (ready milestone : app.Application → Prop)
    (who : Principal) (payload : app.Payload)
    (hprivateMilestone : ∀ application actor command, milestone application →
      milestone (app.privateStep application actor command))
    (hprivateReady : ∀ application actor command, ready application →
      ready (app.privateStep application actor command) ∨
        milestone (app.privateStep application actor command))
    (hhandlerMilestone : ∀ application message next, milestone application →
      app.handle application message = some next → milestone next)
    (hhandlerReady : ∀ application message next, ready application →
      app.handle application message = some next → ready next ∨ milestone next)
    (henvironmentMilestone : ∀ application command next, milestone application →
      next ∈ (app.environmentStep application command).support → milestone next)
    (henvironmentReady : ∀ application command next, ready application →
      next ∈ (app.environmentStep application command).support →
        ready next ∨ milestone next)
    (hresolve : ∀ application serial, ready application →
      ∃ next, app.handle application
        ({ id := (who, serial), payload } : Message Principal app.Payload) = some next ∧
          milestone next)
    (state next : app.State) (action : app.Action)
    (hstate : app.PendingOrResolved ready milestone who payload state)
    (hnext : next ∈ (app.step state action).support) :
    app.PendingOrResolved ready milestone who payload next := by
  rcases hstate with hdone | ⟨hready, serial, hpending⟩
  · left
    cases action with
    | privateCommand actor command =>
        simp only [step, FinDist.mem_support_pure] at hnext
        subst next
        exact hprivateMilestone _ actor command hdone
    | submit actor sent | replay actor id | deliver actor id =>
        simp only [step, FinDist.mem_support_pure] at hnext
        subst next
        exact hdone
    | «include» id =>
        simp only [step, FinDist.mem_support_pure] at hnext
        subst next
        exact include_milestone app milestone hhandlerMilestone state id hdone
    | environment command =>
        simp only [step, FinDist.support_map, Set.mem_image] at hnext
        obtain ⟨application, hsupported, rfl⟩ := hnext
        exact henvironmentMilestone _ command application hdone hsupported
  · cases action with
    | privateCommand actor command =>
        simp only [step, FinDist.mem_support_pure] at hnext
        subst next
        rcases hprivateReady _ actor command hready with hready' | hdone
        · exact Or.inr ⟨hready', serial, hpending⟩
        · exact Or.inl hdone
    | submit actor sent =>
        simp only [step, FinDist.mem_support_pure] at hnext
        subst next
        refine Or.inr ⟨hready, serial, ?_⟩
        change ({ id := (who, serial), payload } : Message Principal app.Payload) ∈
          state.pool.pending ++ [_]
        exact List.mem_append_left _ hpending
    | replay actor id =>
        simp only [step, FinDist.mem_support_pure] at hnext
        subst next
        refine Or.inr ⟨hready, serial, ?_⟩
        unfold MessagePool.replay
        split
        · exact List.mem_append_left _ hpending
        · exact hpending
    | deliver actor id =>
        simp only [step, FinDist.mem_support_pure] at hnext
        subst next
        refine Or.inr ⟨hready, serial, ?_⟩
        unfold MessagePool.deliver
        split <;> exact hpending
    | «include» id =>
        simp only [step, FinDist.mem_support_pure] at hnext
        subst next
        have hprogress := app.include_pending_or_resolved
          (fun current => ready current.application)
          (fun current => milestone current.application)
          ({ id := (who, serial), payload } : Message Principal app.Payload)
          (fun current selected hdone =>
            include_milestone app milestone hhandlerMilestone current selected hdone)
          (fun current selected hready =>
            include_ready_or_milestone app ready milestone hhandlerReady
              current selected hready)
          (fun current selected hready hlookup =>
            include_matching_resolves app ready milestone who payload hresolve _
              ⟨serial, rfl⟩ current selected hready hlookup)
          state id (Or.inr ⟨hready, hpending⟩)
        rcases hprogress with hdone | ⟨hready', hpending'⟩
        · exact Or.inl hdone
        · exact Or.inr ⟨hready', serial, hpending'⟩
    | environment command =>
        simp only [step, FinDist.support_map, Set.mem_image] at hnext
        obtain ⟨application, hsupported, rfl⟩ := hnext
        rcases henvironmentReady _ command application hready hsupported with hready' | hdone
        · exact Or.inr ⟨hready', serial, hpending⟩
        · exact Or.inl hdone

private theorem run_pendingOrResolved
    (ready milestone : app.Application → Prop)
    (who : Principal) (payload : app.Payload)
    (hprivateMilestone : ∀ application actor command, milestone application →
      milestone (app.privateStep application actor command))
    (hprivateReady : ∀ application actor command, ready application →
      ready (app.privateStep application actor command) ∨
        milestone (app.privateStep application actor command))
    (hhandlerMilestone : ∀ application message next, milestone application →
      app.handle application message = some next → milestone next)
    (hhandlerReady : ∀ application message next, ready application →
      app.handle application message = some next → ready next ∨ milestone next)
    (henvironmentMilestone : ∀ application command next, milestone application →
      next ∈ (app.environmentStep application command).support → milestone next)
    (henvironmentReady : ∀ application command next, ready application →
      next ∈ (app.environmentStep application command).support →
        ready next ∨ milestone next)
    (hresolve : ∀ application serial, ready application →
      ∃ next, app.handle application
        ({ id := (who, serial), payload } : Message Principal app.Payload) = some next ∧
          milestone next)
    (state next : app.State) (actions : List app.Action)
    (hstate : app.PendingOrResolved ready milestone who payload state)
    (hnext : next ∈ (app.run actions state).support) :
    app.PendingOrResolved ready milestone who payload next := by
  induction actions generalizing state with
  | nil =>
      simp only [run_nil, FinDist.mem_support_pure] at hnext
      subst next
      exact hstate
  | cons action rest ih =>
      simp only [run_cons, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨middle, hmiddle, hnext⟩ := hnext
      exact ih middle
        (step_pendingOrResolved app ready milestone who payload
          hprivateMilestone hprivateReady hhandlerMilestone hhandlerReady
          henvironmentMilestone henvironmentReady hresolve state middle action hstate hmiddle)
        hnext

/-- Starting before this principal has submitted the exact payload, every
supported policy execution satisfies the one-shot bridge: a matching history
entry implies that the milestone holds, or an exact natively authored envelope
remains pending while the request is ready.

The environment and all other player policies are unrestricted.  No service,
settlement, or invocation opportunity is assumed. -/
theorem runPolicies_submitted_pendingOrResolved
    (invariant ready milestone : app.Application → Prop)
    (who : Principal) (payload : app.Payload)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (hinvariantPrivate : ∀ application actor command, invariant application →
      invariant (app.privateStep application actor command))
    (hinvariantHandler : ∀ application message next, invariant application →
      app.handle application message = some next → invariant next)
    (hinvariantEnvironment : ∀ application command next, invariant application →
      next ∈ (app.environmentStep application command).support → invariant next)
    (hprivateMilestone : ∀ application actor command, milestone application →
      milestone (app.privateStep application actor command))
    (hprivateReady : ∀ application actor command, ready application →
      ready (app.privateStep application actor command) ∨
        milestone (app.privateStep application actor command))
    (hhandlerMilestone : ∀ application message next, milestone application →
      app.handle application message = some next → milestone next)
    (hhandlerReady : ∀ application message next, ready application →
      app.handle application message = some next → ready next ∨ milestone next)
    (henvironmentMilestone : ∀ application command next, milestone application →
      next ∈ (app.environmentStep application command).support → milestone next)
    (henvironmentReady : ∀ application command next, ready application →
      next ∈ (app.environmentStep application command).support →
        ready next ∨ milestone next)
    (hresolve : ∀ application serial, ready application →
      ∃ next, app.handle application
        ({ id := (who, serial), payload } : Message Principal app.Payload) = some next ∧
          milestone next)
    (hemit : ∀ (execution : app.PolicyExecution) (command : app.PlayerCommand),
      invariant execution.native.application →
      command ∈ (players who (execution.principalHistory who)
        (State.observe app execution.native who)).support →
      command = .submit payload → ready execution.native.application)
    (schedule : List (@Invocation Principal)) (execution next : app.PolicyExecution)
    (hinvariant : invariant execution.native.application)
    (hbefore : ¬ app.SubmittedPayload payload (execution.principalHistory who))
    (hnext : next ∈ (app.runPolicies players environment schedule execution).support) :
    app.SubmittedPayload payload (next.principalHistory who) →
      app.PendingOrResolved ready milestone who payload next.native := by
  induction schedule generalizing execution with
  | nil =>
      simp only [runPolicies, FinDist.mem_support_pure] at hnext
      subst next
      exact fun hsubmitted => (hbefore hsubmitted).elim
  | cons invocation rest ih =>
      simp only [runPolicies, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨middle, hmiddle, hnext⟩ := hnext
      have hsingle : middle ∈
          (app.runPolicies players environment [invocation] execution).support := by
        simp only [runPolicies, FinDist.support_bind, Set.mem_iUnion]
        exact ⟨middle, hmiddle, FinDist.mem_support_pure.mpr rfl⟩
      obtain ⟨actions, _, hrun⟩ :=
        app.runPolicies_native_support players environment [invocation] execution middle hsingle
      have hinvariantMiddle : invariant middle.native.application :=
        app.run_application_invariant invariant hinvariantPrivate hinvariantHandler
          hinvariantEnvironment execution.native middle.native actions hinvariant hrun
      cases invocation with
      | player actor =>
          simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
          obtain ⟨command, hcommand, hstep⟩ := hmiddle
          by_cases hactor : actor = who
          · subst actor
            have hhistory := playerStep_history_self app who execution command middle hstep
            by_cases hmatch : command = .submit payload
            · have hready := hemit execution command hinvariant hcommand hmatch
              have hnative : middle.native ∈ ((app.playerStep who execution command).map
                  PolicyExecution.native).support := by
                rw [FinDist.support_map]
                exact ⟨middle, hstep, rfl⟩
              rw [app.playerStep_native] at hnative
              rw [hmatch] at hnative
              simp only [PlayerCommand.toAction, step, FinDist.mem_support_pure] at hnative
              have hbridge : app.PendingOrResolved ready milestone who payload middle.native := by
                rw [hnative]
                exact Or.inr ⟨hready, execution.native.pool.nextSerial who, by
                  simp [MessagePool.submit]⟩
              obtain ⟨actions, _, hrun⟩ :=
                app.runPolicies_native_support players environment rest middle next hnext
              intro _
              exact run_pendingOrResolved app ready milestone who payload
                hprivateMilestone hprivateReady hhandlerMilestone hhandlerReady
                henvironmentMilestone henvironmentReady hresolve
                middle.native next.native actions hbridge hrun
            · apply ih middle hinvariantMiddle
              · rw [hhistory]
                intro hsubmitted
                obtain ⟨entry, hentry, hentryCommand⟩ := hsubmitted
                simp only [List.mem_append, List.mem_singleton] at hentry
                rcases hentry with hentry | rfl
                · exact hbefore ⟨entry, hentry, hentryCommand⟩
                · exact hmatch hentryCommand
              · exact hnext
          · have hhistory := app.playerStep_other_history actor who (Ne.symm hactor)
              execution command
              middle hstep
            apply ih middle hinvariantMiddle
            · simpa [hhistory] using hbefore
            · exact hnext
      | environment =>
          simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
          obtain ⟨command, _, hstep⟩ := hmiddle
          have hhistory := app.environmentStep_principalHistory execution command middle hstep
          apply ih middle hinvariantMiddle
          · simpa [hhistory] using hbefore
          · exact hnext

end Interaction.MessageApplication
