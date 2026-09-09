/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplication

/-! # Native message-application execution laws

These laws retain the distinction between published traffic and application
effects. The support characterization also accounts for stochastic application
steps; replaying a recorded command sequence need not determine a unique state.
-/

noncomputable section

namespace Interaction.MessageApplication

open GameTheory.Math.Probability

universe uPrincipal

variable {Principal : Type uPrincipal} [DecidableEq Principal]
variable (app : MessageApplication Principal)

@[simp] theorem includePending_pool (state : app.State) (id : MessageId Principal) :
    (app.includePending state id).pool = (state.pool.includePending id).state := by
  simp [includePending]

@[simp] theorem includePending_missing (state : app.State) (id : MessageId Principal)
    (hmissing : state.pool.lookup id = none) : app.includePending state id = state := by
  simp [includePending, MessagePool.includeApplication_missing, hmissing]

theorem includePending_accept (state : app.State) (id : MessageId Principal)
    (message : Message Principal app.Payload) (next : app.Application)
    (hlookup : state.pool.lookup id = some message)
    (hhandler : app.handle state.application message = some next) :
    app.includePending state id =
      ⟨next, (state.pool.includePending id).state, state.receipts ++ [(id, true)]⟩ := by
  simp [includePending, MessagePool.includeApplication_accept _ _ _ _ _ _ hlookup hhandler]

theorem includePending_reject (state : app.State) (id : MessageId Principal)
    (message : Message Principal app.Payload)
    (hlookup : state.pool.lookup id = some message)
    (hhandler : app.handle state.application message = none) :
    app.includePending state id =
      ⟨state.application, (state.pool.includePending id).state,
        state.receipts ++ [(id, false)]⟩ := by
  simp [includePending, MessagePool.includeApplication_reject _ _ _ _ _ hlookup hhandler]

/-- Rejection rolls back the application, not publication or earlier delivery. -/
theorem includePending_reject_observations (state : app.State) (id : MessageId Principal)
    (message : Message Principal app.Payload)
    (hlookup : state.pool.lookup id = some message)
    (hhandler : app.handle state.application message = none) :
    (app.includePending state id).application = state.application ∧
      (app.includePending state id).pool.ledger = state.pool.ledger ++ [message] ∧
      (∀ who, (app.includePending state id).pool.inbox who = state.pool.inbox who) ∧
      (app.includePending state id).receipts = state.receipts ++ [(id, false)] := by
  rw [app.includePending_reject state id message hlookup hhandler]
  exact ⟨rfl, MessagePool.include_ledger_of_lookup _ _ _ hlookup,
    MessagePool.include_preserves_inbox _ _, rfl⟩

/-- External application kernels cannot deliver messages or manufacture
inclusion receipts. Their own observable effects use application projections. -/
theorem step_environment_pool_receipts (state : app.State)
    (command : app.EnvironmentCommand) :
    (app.step state (.environment command)).map (fun next => (next.pool, next.receipts)) =
      FinDist.pure (state.pool, state.receipts) := by
  simp [step, FinDist.map_comp, Function.comp_def]

/-- A native supported path records every supplied command, including commands
whose application effect is a stutter. It does not assert any service bound. -/
inductive Executes : app.State → List app.Action → app.State → Prop where
  | nil (state : app.State) : Executes state [] state
  | cons {state next final : app.State} {action : app.Action} {rest : List app.Action}
      (hstep : next ∈ (app.step state action).support)
      (htail : Executes next rest final) : Executes state (action :: rest) final

theorem mem_run_support_iff (state final : app.State) (actions : List app.Action) :
    final ∈ (app.run actions state).support ↔ app.Executes state actions final := by
  induction actions generalizing state with
  | nil =>
      simp only [run_nil, FinDist.mem_support_pure]
      constructor
      · rintro rfl
        exact .nil _
      · intro h
        cases h
        rfl
  | cons action rest ih =>
      simp only [run_cons, FinDist.support_bind, Set.mem_iUnion, ih]
      constructor
      · rintro ⟨next, hstep, htail⟩
        exact .cons hstep htail
      · intro h
        cases h with
        | cons hstep htail => exact ⟨_, hstep, htail⟩

/-- Application invariants need preservation by every accepted handler and
every supported fixed-kernel result, not just by honest messages. -/
theorem step_application_invariant (invariant : app.Application → Prop)
    (hprivate : ∀ application who command, invariant application →
      invariant (app.privateStep application who command))
    (hhandler : ∀ application message next, invariant application →
      app.handle application message = some next → invariant next)
    (henvironment : ∀ application command next, invariant application →
      next ∈ (app.environmentStep application command).support → invariant next)
    (state next : app.State) (action : app.Action) (hstate : invariant state.application)
    (hnext : next ∈ (app.step state action).support) : invariant next.application := by
  cases action with
  | privateCommand who command =>
      simp only [step, FinDist.mem_support_pure] at hnext
      subst next
      exact hprivate _ _ _ hstate
  | submit who payload | replay who id | deliver who id =>
      simp only [step, FinDist.mem_support_pure] at hnext
      subst next
      exact hstate
  | «include» id =>
      simp only [step, FinDist.mem_support_pure] at hnext
      subst next
      cases hlookup : state.pool.lookup id with
      | none =>
          rw [app.includePending_missing state id hlookup]
          exact hstate
      | some message =>
          cases hresult : app.handle state.application message with
          | none =>
              rw [app.includePending_reject state id message hlookup hresult]
              exact hstate
          | some result =>
              rw [app.includePending_accept state id message result hlookup hresult]
              exact hhandler _ _ _ hstate hresult
  | environment command =>
      simp only [step, FinDist.support_map, Set.mem_image] at hnext
      obtain ⟨application, hsupported, rfl⟩ := hnext
      exact henvironment _ _ _ hstate hsupported

theorem run_application_invariant (invariant : app.Application → Prop)
    (hprivate : ∀ application who command, invariant application →
      invariant (app.privateStep application who command))
    (hhandler : ∀ application message next, invariant application →
      app.handle application message = some next → invariant next)
    (henvironment : ∀ application command next, invariant application →
      next ∈ (app.environmentStep application command).support → invariant next)
    (state final : app.State) (actions : List app.Action)
    (hstate : invariant state.application) (hfinal : final ∈ (app.run actions state).support) :
    invariant final.application := by
  have hexec := (app.mem_run_support_iff state final actions).mp hfinal
  clear hfinal
  induction hexec with
  | nil => exact hstate
  | cons hstep _ ih =>
      exact ih (app.step_application_invariant invariant hprivate hhandler henvironment
        _ _ _ hstate hstep)

end Interaction.MessageApplication
