/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationProfileContinuation
import Vegas.Compile.SourceReadoutAvailability

/-! # Readout availability at structural plan continuations

An execution starts from the original generated image and retains the original
lifted owner policy.  At a structurally related suffix, graph readiness and
native refinement suffice to recover the actual owner-local readout and its
source-view equation.  The source environment remains proof-only and is never
an input to the runtime policy.
-/

noncomputable section

namespace Vegas.ApplicationPlan.ProfileContinuation

open EventGraph ToEventGraph Interaction Interaction.MessageApplication

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A ready source decision in a structural suffix has an executable readout
under the original whole-plan lifted owner policy. Other players, the
environment, and the preceding schedule are unrestricted. -/
theorem runPolicies_ownerReadout?_of_ready_source_view
    {rootContext Γ Δ : VCtx P L} {rootPending pending : Finset VarId}
    {rootProg : VegasCore P L rootContext} {prog : VegasCore P L Γ}
    {rootAccounted : CommitmentAccounting rootPending rootProg}
    {accounted : CommitmentAccounting pending prog}
    {rootFresh : FreshBindings rootProg} {fresh : FreshBindings prog}
    {rootState : BuildState P L rootContext} {state : BuildState P L Γ}
    {root : ApplicationPlan rootAccounted rootFresh rootState}
    {plan : ApplicationPlan accounted fresh state}
    {rootProfile : SourceBehavioralProfile rootProg}
    {profile : SourceBehavioralProfile prog}
    (continuation : ProfileContinuation root rootProfile plan profile)
    (deadlineOf : Nat → Nat) (who : P)
    (players : P → (root.image deadlineOf).application.PlayerPolicy)
    (hwho : players who = root.liftProfile deadlineOf rootProfile who)
    (environment : (root.image deadlineOf).application.EnvironmentPolicy)
    (schedule : List (@Invocation P))
    (next : (root.image deadlineOf).application.PolicyExecution)
    (hnext : next ∈ ((root.image deadlineOf).application.runPolicies
      players environment schedule
      (PolicyExecution.initial (root.image deadlineOf).application
        (MessageApplication.State.initial (root.image deadlineOf).application
          (ApplicationImage.State.initial
            (ApplicationImage.Memory.initial
              (compileCore rootProg rootFresh rootState).graph))))).support)
    {name : VarId} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    (site : SourceDecisionSite who prog Δ name ty guard)
    (cfg : Config (compileCore prog fresh state).graph)
    (hrefines : next.native.application.Refines cfg)
    (hready : Ready (compileCore prog fresh state).graph cfg
      (site.compiledNode fresh state))
    (hinitial : ∀ ref ∈
        (eventGuardOf (decisionSiteState site fresh state) who guard).choiceReads,
      ∀ spec, (compileCore prog fresh state).graph.field? ref.field = some spec →
        ∀ value, spec.source = .initial value → spec.owner = none)
    (env : VEnv L Δ)
    (hagrees : (decisionSiteState site fresh state).ViewAgrees who cfg.store env) :
    ∃ reads : ReadEnv L
        (eventGuardOf (decisionSiteState site fresh state) who guard).choiceReads,
      (root.image deadlineOf).ownerReadout? who
          (eventGuardOf (decisionSiteState site fresh state) who guard).choiceReads
          (next.principalHistory who)
          (MessageApplication.State.observe (root.image deadlineOf).application
            next.native who) = some reads ∧
        ReadEnv.ofStore? cfg.store
            (eventGuardOf (decisionSiteState site fresh state) who guard).choiceReads =
          some reads ∧
        viewEnvOfReadEnv (decisionSiteState site fresh state) who reads =
          (env.toView who).eraseEnv := by
  have hcoversRoot := root.runPolicies_memory_covers deadlineOf players environment
    schedule next hnext
  have hcoversCompiledRoot : next.native.application.memory.Covers
      (compileCore rootProg rootFresh rootState).graph.initialFields.length := by
    change next.native.application.memory.Covers
      (compileCore rootProg rootFresh rootState).initialFields.length
    simpa only [compileCore_initialFields] using hcoversRoot
  have hcovers : next.native.application.memory.Covers
      (compileCore prog fresh state).graph.initialFields.length := by
    rw [← continuation.compile_eq]
    exact hcoversCompiledRoot
  have hbindingsRoot := root.runPolicies_lifted_registeredBindings deadlineOf
    rootProfile who players hwho environment
    (ApplicationImage.Memory.initial (compileCore rootProg rootFresh rootState).graph)
    (by intro field; rfl) schedule next hnext
  have hbindings : (root.image deadlineOf).RegisteredBindings who
      (fun slot typed => ∃ spec : FieldSpec P L,
        (compileCore prog fresh state).graph.field? slot = some spec ∧
          typed.ty = spec.ty)
      (next.principalHistory who) next.native.application := by
    rw [← continuation.compile_eq]
    exact hbindingsRoot
  obtain ⟨reads, hreadout, hview⟩ :=
    site.ownerReadout?_of_ready_source_view fresh state (root.image deadlineOf)
    (next.principalHistory who)
    (MessageApplication.State.observe (root.image deadlineOf).application next.native who)
    next.native.application rfl cfg hrefines hcovers hbindings hready hinitial env hagrees
  refine ⟨reads, hreadout, ?_, hview⟩
  exact site.ownerReadout?_graph_reads fresh state (root.image deadlineOf)
    (next.principalHistory who)
    (MessageApplication.State.observe (root.image deadlineOf).application next.native who)
    next.native.application rfl cfg hrefines hbindings.registrationMatches reads hreadout

end Vegas.ApplicationPlan.ProfileContinuation

/-- info:
'Vegas.ApplicationPlan.ProfileContinuation.runPolicies_ownerReadout?_of_ready_source_view'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.ApplicationPlan.ProfileContinuation.runPolicies_ownerReadout?_of_ready_source_view
