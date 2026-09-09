/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationAcceptedPrefix
import Vegas.Compile.ApplicationContinuationReadout
import Vegas.Compile.ApplicationPolicyFreshness
import Vegas.Compile.ApplicationService
import Vegas.Compile.ApplicationSourceOutcome
import Interaction.MessageApplicationCounters

/-! # Checkpoints for source-ordered application realization

A checkpoint relates a source suffix to an actual execution of the original
generated application, retaining the original lifted profile and service.
Its source environment and compiler cursor are proof data. The runtime gets
only the emitted image, local histories, and native observations.

The reached-execution premise retains an actual initialized policy-run witness.
Cache freshness and service-index alignment are additional invariants, not
properties asserted for arbitrary prefixes of that run.
-/

noncomputable section

namespace Vegas.ApplicationPlan

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Canonical initialization of the shared policy runner for a generated
image. It provisions public initial fields and empty message and local caches. -/
def initialExecution
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} (plan : ApplicationPlan accounted fresh state)
    (deadlineOf : Nat → Nat) : (plan.image deadlineOf).application.PolicyExecution :=
  PolicyExecution.initial (plan.image deadlineOf).application
    (MessageApplication.State.initial (plan.image deadlineOf).application
      (ApplicationImage.State.initial
        (ApplicationImage.Memory.initial (compileCore prog fresh state).graph)))

/-- A source-prefix invariant over the existing policy runner. In particular,
the suffix profile must be a continuation of the original profile, and the
native execution must be genuinely reachable under that original lift. -/
structure ForwardCheckpoint
    {rootContext Γ : VCtx P L} {rootPending pending : Finset VarId}
    {rootProg : VegasCore P L rootContext} {prog : VegasCore P L Γ}
    {rootAccounted : CommitmentAccounting rootPending rootProg}
    {accounted : CommitmentAccounting pending prog}
    {rootFresh : FreshBindings rootProg} {fresh : FreshBindings prog}
    {rootState : BuildState P L rootContext} {state : BuildState P L Γ}
    (root : ApplicationPlan rootAccounted rootFresh rootState)
    (rootProfile : SourceBehavioralProfile rootProg) (deadlineOf : Nat → Nat)
    (plan : ApplicationPlan accounted fresh state) (profile : SourceBehavioralProfile prog)
    (current : CoupledAt (compileCore prog fresh state).graph state)
    (execution : (root.image deadlineOf).application.PolicyExecution) : Prop where
  continuation : ProfileContinuation root rootProfile plan profile
  refines : execution.native.application.Refines current.current.graph.1
  reached : ∃ previous, execution ∈ ((root.image deadlineOf).application.runPolicies
    (root.liftProfile deadlineOf rootProfile) (root.image deadlineOf).serialService
    previous (root.initialExecution deadlineOf)).support
  aligned : (root.instructions deadlineOf).drop execution.environmentHistory.length =
    plan.instructions deadlineOf
  caches : plan.RemainingCachesEmpty (root.image deadlineOf) deadlineOf execution
  accepted : (root.image deadlineOf).AcceptedBindingPrefix state.nodes.length
    execution.native.application

namespace ForwardCheckpoint

variable {rootContext Γ : VCtx P L} {rootPending pending : Finset VarId}
variable {rootProg : VegasCore P L rootContext} {prog : VegasCore P L Γ}
variable {rootAccounted : CommitmentAccounting rootPending rootProg}
variable {accounted : CommitmentAccounting pending prog}
variable {rootFresh : FreshBindings rootProg} {fresh : FreshBindings prog}
variable {rootState : BuildState P L rootContext} {state : BuildState P L Γ}
variable {root : ApplicationPlan rootAccounted rootFresh rootState}
variable {rootProfile : SourceBehavioralProfile rootProg} {deadlineOf : Nat → Nat}
variable {plan : ApplicationPlan accounted fresh state} {profile : SourceBehavioralProfile prog}
variable {current : CoupledAt (compileCore prog fresh state).graph state}
variable {execution : (root.image deadlineOf).application.PolicyExecution}

/-- Any supported continuation of this native run remains a genuine run of
the same original profile. No source-dependent policy is spliced into it. -/
theorem reached_after
    (checkpoint : ForwardCheckpoint root rootProfile deadlineOf plan profile current execution)
    (schedule : List (@Invocation P))
    (next : (root.image deadlineOf).application.PolicyExecution)
    (hnext : next ∈ ((root.image deadlineOf).application.runPolicies
      (root.liftProfile deadlineOf rootProfile) (root.image deadlineOf).serialService
      schedule execution).support) :
    ∃ previous, next ∈ ((root.image deadlineOf).application.runPolicies
      (root.liftProfile deadlineOf rootProfile) (root.image deadlineOf).serialService
      previous (root.initialExecution deadlineOf)).support := by
  obtain ⟨previous, hprevious⟩ := checkpoint.reached
  refine ⟨previous ++ schedule, ?_⟩
  rw [MessageApplication.runPolicies_append, FinDist.support_bind]
  exact Set.mem_iUnion.mpr ⟨execution, Set.mem_iUnion.mpr ⟨hprevious, hnext⟩⟩

/-- The service's actual history selects the current suffix instruction. -/
theorem head_lookup
    (checkpoint : ForwardCheckpoint root rootProfile deadlineOf plan profile current execution)
    (code : ApplicationInstruction P L) (rest : List (ApplicationInstruction P L))
    (hhead : plan.instructions deadlineOf = code :: rest) :
    (root.image deadlineOf).instructions[execution.environmentHistory.length]? = some code := by
  have hfirst := congrArg (fun entries => entries[0]?) (checkpoint.aligned.trans hhead)
  simpa only [image, List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero] using hfirst

/-- Every instruction in the remaining plan is a member of the original
emitted image, independent of the dynamic service index. -/
theorem instruction_mem
    (checkpoint : ForwardCheckpoint root rootProfile deadlineOf plan profile current execution)
    (code : ApplicationInstruction P L) (hcode : code ∈ plan.instructions deadlineOf) :
    code ∈ root.instructions deadlineOf := by
  obtain ⟨before, hbefore⟩ := checkpoint.continuation.instructions_suffix deadlineOf
  rw [hbefore]
  exact List.mem_append_right before hcode

/-- One complete instruction phase advances the actual service index by one.
This counts invocations; acceptance and source progress are proved separately. -/
theorem aligned_after_phase
    (checkpoint : ForwardCheckpoint root rootProfile deadlineOf plan profile current execution)
    (code : ApplicationInstruction P L) (rest : List (ApplicationInstruction P L))
    (hhead : plan.instructions deadlineOf = code :: rest)
    (next : (root.image deadlineOf).application.PolicyExecution)
    (hnext : next ∈ ((root.image deadlineOf).application.runPolicies
      (root.liftProfile deadlineOf rootProfile) (root.image deadlineOf).serialService
      code.serviceInvocations execution).support) :
    (root.instructions deadlineOf).drop next.environmentHistory.length = rest := by
  have hlength := (root.image deadlineOf).application.runPolicies_environmentHistory_length
    (root.liftProfile deadlineOf rootProfile) (root.image deadlineOf).serialService
    code.serviceInvocations execution next hnext
  have hdrop := congrArg (List.drop 1) (checkpoint.aligned.trans hhead)
  rw [ApplicationInstruction.serviceInvocations_environment_count] at hlength
  rw [hlength]
  simpa only [List.drop_drop, List.drop_succ_cons, List.drop_zero] using hdrop

/-- Fresh envelope identifiers are derived from actual initialized execution,
not from an assumption that the current pool happens to be empty. -/
theorem lookup_nextSerial_eq_none
    (checkpoint : ForwardCheckpoint root rootProfile deadlineOf plan profile current execution)
    (who : P) :
    execution.native.pool.lookup (who, execution.native.pool.nextSerial who) = none := by
  obtain ⟨previous, hprevious⟩ := checkpoint.reached
  exact (root.image deadlineOf).application.runPolicies_initial_lookup_nextSerial_eq_none
    (root.liftProfile deadlineOf rootProfile) (root.image deadlineOf).serialService previous
    (ApplicationImage.State.initial
      (ApplicationImage.Memory.initial (compileCore rootProg rootFresh rootState).graph))
    execution hprevious who

/-- Actual private preparation agrees with the player's retained registration
cache throughout initialized execution. -/
theorem registrationConsistent
    (checkpoint : ForwardCheckpoint root rootProfile deadlineOf plan profile current execution) :
    (root.image deadlineOf).RegistrationConsistent execution := by
  obtain ⟨previous, hprevious⟩ := checkpoint.reached
  exact (root.image deadlineOf).runPolicies_registrationCache
    (ApplicationImage.Memory.initial (compileCore rootProg rootFresh rootState).graph)
    (root.liftProfile deadlineOf rootProfile) (root.image deadlineOf).serialService
    previous execution hprevious

/-- The original lifted policy supplies typed registration provenance for
each owner, interpreted in the structurally identical suffix graph. -/
theorem registeredBindings
    (checkpoint : ForwardCheckpoint root rootProfile deadlineOf plan profile current execution)
    (who : P) :
    (root.image deadlineOf).RegisteredBindings who
      (fun slot typed => ∃ spec : FieldSpec P L,
        (compileCore prog fresh state).graph.field? slot = some spec ∧ typed.ty = spec.ty)
      (execution.principalHistory who) execution.native.application := by
  obtain ⟨previous, hprevious⟩ := checkpoint.reached
  rw [← checkpoint.continuation.compile_eq]
  exact root.runPolicies_lifted_registeredBindings deadlineOf rootProfile who
    (root.liftProfile deadlineOf rootProfile) rfl (root.image deadlineOf).serialService
    (ApplicationImage.Memory.initial (compileCore rootProg rootFresh rootState).graph)
    (by intro field; rfl) previous execution hprevious

/-- The canonical start is a real checkpoint for every checked program with
an application plan. Progress still requires its separate backend conditions. -/
theorem initial (source : WFProgram P L)
    (plan : ApplicationPlan source.accounted source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx)))
    (profile : SourceBehavioralProfile source.core.prog) (deadlineOf : Nat → Nat) :
    ForwardCheckpoint plan profile deadlineOf plan profile
      (compiledInitialCoupled source.core) (plan.initialExecution deadlineOf) := by
  refine ⟨.refl, ApplicationImage.State.initial_refines _, ?_, rfl, ?_, ?_⟩
  · exact ⟨[], FinDist.mem_support_pure.mpr rfl⟩
  · exact plan.remainingCachesEmpty_of_empty_histories (plan.image deadlineOf)
      deadlineOf (plan.initialExecution deadlineOf) (fun _ => rfl)
  · exact ApplicationImage.AcceptedBindingPrefix.zero _ _

end ForwardCheckpoint
end Vegas.ApplicationPlan

/-- info: 'Vegas.ApplicationPlan.ForwardCheckpoint.reached_after' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.ForwardCheckpoint.reached_after

/-- info: 'Vegas.ApplicationPlan.ForwardCheckpoint.aligned_after_phase' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.ForwardCheckpoint.aligned_after_phase

/-- info: 'Vegas.ApplicationPlan.ForwardCheckpoint.initial' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.ForwardCheckpoint.initial
