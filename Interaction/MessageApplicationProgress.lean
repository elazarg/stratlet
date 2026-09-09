/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationService

/-! # Stable resolvers under inclusion service

Capacity and application progress are separate obligations. A resolver
envelope can force a milestone during an inclusion phase when interfering
includes preserve either its readiness or the milestone, and including that
envelope while ready establishes the milestone. Failed transactions and
replayed copies are still included by the native application semantics.
-/

noncomputable section

namespace Interaction.MessageApplication

open GameTheory.Math.Probability

universe uPrincipal

variable {Principal : Type uPrincipal} [DecidableEq Principal]
variable (app : MessageApplication Principal)

private theorem inclusion_step_invariant (invariant : app.State → Prop)
    (hincludes : ∀ state id, invariant state → invariant (app.includePending state id))
    (players : Principal → app.PlayerPolicy) (during : Nat → Prop)
    (environment : app.EnvironmentPolicy) (hservice : app.InclusionService during environment)
    (execution next : app.PolicyExecution) (hslot : during execution.environmentHistory.length)
    (hinvariant : invariant execution.native)
    (hnext : next ∈ (app.invoke players environment execution .environment).support) :
    invariant next.native := by
  simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at hnext
  obtain ⟨command, hcommand, hnext⟩ := hnext
  have hallowed := hservice execution.environmentHistory execution.native.environmentView
    command hslot hcommand
  cases hpending : execution.native.pool.pending with
  | nil =>
      simp only [State.environmentView, hpending] at hallowed
      subst command
      rw [environmentStep_wait] at hnext
      simp only [FinDist.mem_support_pure] at hnext
      subst next
      exact hinvariant
  | cons first rest =>
      simp only [State.environmentView, hpending] at hallowed
      obtain ⟨id, message, hlookup, rfl⟩ := hallowed
      simp only [environmentPolicyStep, advance, EnvironmentPolicyCommand.toAction,
        step, FinDist.pure_bind, FinDist.mem_support_pure] at hnext
      subst next
      exact hincludes _ id hinvariant

/-- Local native inclusion invariants lift to a reserved inclusion phase,
including randomized, payload-inspecting inclusion selectors. -/
theorem inclusion_phase_invariant (invariant : app.State → Prop)
    (hincludes : ∀ state id, invariant state → invariant (app.includePending state id))
    (players : Principal → app.PlayerPolicy) (during : Nat → Prop)
    (environment : app.EnvironmentPolicy) (hservice : app.InclusionService during environment)
    (count : Nat) (execution next : app.PolicyExecution)
    (hslots : ∀ offset < count, during (execution.environmentHistory.length + offset))
    (hinvariant : invariant execution.native)
    (hnext : next ∈ (app.runPolicies players environment
      (List.replicate count .environment) execution).support) : invariant next.native := by
  induction count generalizing execution with
  | zero =>
      simp only [List.replicate_zero, runPolicies, FinDist.mem_support_pure] at hnext
      subst next
      exact hinvariant
  | succ count ih =>
      simp only [List.replicate_succ, runPolicies, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨middle, hmiddle, hnext⟩ := hnext
      have hslot : during execution.environmentHistory.length := by
        simpa using hslots 0 (by omega)
      have hmid := inclusion_step_invariant app invariant hincludes players during environment
        hservice execution middle hslot hinvariant hmiddle
      have hstep := app.inclusion_step_length players during environment hservice
        execution middle hslot hmiddle
      apply ih middle ?_ hmid hnext
      intro offset hoffset
      rw [hstep.2]
      convert hslots (offset + 1) (by omega) using 1
      omega

/-- A ready resolver remains pending until it establishes the milestone,
unless an earlier competing inclusion establishes that milestone first.
The three premises concern individual native inclusions, not settlement. -/
theorem include_pending_or_resolved (ready milestone : app.State → Prop)
    (target : Message Principal app.Payload)
    (hpersistent : ∀ state id, milestone state → milestone (app.includePending state id))
    (hstable : ∀ state id, ready state →
      ready (app.includePending state id) ∨ milestone (app.includePending state id))
    (hresolve : ∀ state id, ready state → state.pool.lookup id = some target →
      milestone (app.includePending state id))
    (state : app.State) (id : MessageId Principal)
    (hstate : milestone state ∨ (ready state ∧ target ∈ state.pool.pending)) :
    milestone (app.includePending state id) ∨
      (ready (app.includePending state id) ∧
        target ∈ (app.includePending state id).pool.pending) := by
  rcases hstate with hdone | ⟨hready, hpending⟩
  · exact Or.inl (hpersistent state id hdone)
  rcases hstable state id hready with hready' | hdone
  · rcases MessagePool.pending_retained_or_selected state.pool id target hpending with
      hmem | hlookup
    · exact Or.inr ⟨hready', by simpa only [includePending_pool] using hmem⟩
    · exact Or.inl (hresolve state id hready hlookup)
  · exact Or.inl hdone

/-- Sufficient reserved capacity turns a stable pending resolver into actual
application progress. Queue clearance alone cannot supply the local readiness,
acceptance, or milestone-persistence premises. -/
theorem inclusion_phase_resolves (ready milestone : app.State → Prop)
    (target : Message Principal app.Payload)
    (hpersistent : ∀ state id, milestone state → milestone (app.includePending state id))
    (hstable : ∀ state id, ready state →
      ready (app.includePending state id) ∨ milestone (app.includePending state id))
    (hresolve : ∀ state id, ready state → state.pool.lookup id = some target →
      milestone (app.includePending state id))
    (players : Principal → app.PlayerPolicy) (during : Nat → Prop)
    (environment : app.EnvironmentPolicy) (hservice : app.InclusionService during environment)
    (count : Nat) (execution next : app.PolicyExecution)
    (hslots : ∀ offset < count, during (execution.environmentHistory.length + offset))
    (hcapacity : execution.native.pool.pending.length ≤ count)
    (hready : ready execution.native) (hpending : target ∈ execution.native.pool.pending)
    (hnext : next ∈ (app.runPolicies players environment
      (List.replicate count .environment) execution).support) : milestone next.native := by
  have hinvariant := app.inclusion_phase_invariant
    (fun state => milestone state ∨ (ready state ∧ target ∈ state.pool.pending))
    (fun state id => app.include_pending_or_resolved ready milestone target
      hpersistent hstable hresolve state id)
    players during environment hservice count execution next hslots
    (Or.inr ⟨hready, hpending⟩) hnext
  have hempty := app.inclusion_phase_empty players during environment hservice
    count execution next hslots hcapacity hnext
  simpa [hempty] using hinvariant

end Interaction.MessageApplication
