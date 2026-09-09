/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationSampleForward
import Vegas.Compile.ApplicationBindingForward
import Vegas.Compile.ApplicationPublicChoiceForward
import Vegas.Compile.ApplicationConditionalForward

/-! # The source law of the generated reference execution

The original source behavioral profile is lifted once into the public-message
application. Running its generated invocation list under the generated serial
service finishes with exactly the independent written-order source law on
public terminal bindings. The result includes completion, so an empty public
readout cannot conceal unfinished work.

The source and graph checkpoints in the proof are absent from runtime inputs.
The theorem concerns this reference service and compiled profiles, not progress
or deviation simulation for arbitrary runtime policies. Initial controller
readability and actual binding origins are separate backend conditions.
-/

noncomputable section

namespace Vegas.ApplicationPlan

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A genuine prefix of the fixed original execution extends to the source
law of its remaining plan. The completion flag and executable public decoder
are observed jointly. -/
theorem ForwardCheckpoint.service_public_law
    {rootContext Γ : VCtx P L} {rootPending pending : Finset VarId}
    {rootProg : VegasCore P L rootContext} {prog : VegasCore P L Γ}
    {rootAccounted : CommitmentAccounting rootPending rootProg}
    {accounted : CommitmentAccounting pending prog}
    {rootFresh : FreshBindings rootProg} {fresh : FreshBindings prog}
    {rootState : BuildState P L rootContext} {state : BuildState P L Γ}
    {root : ApplicationPlan rootAccounted rootFresh rootState}
    {rootProfile : SourceBehavioralProfile rootProg} {deadlineOf : Nat → Nat}
    (plan : ApplicationPlan accounted fresh state)
    (profile : SourceBehavioralProfile prog)
    (current : CoupledAt (compileCore prog fresh state).graph state)
    (execution : (root.image deadlineOf).application.PolicyExecution)
    (checkpoint : ForwardCheckpoint root rootProfile deadlineOf plan profile current execution)
    (hinitial : plan.InitialControllerReadsPublic)
    (horigins : (root.image deadlineOf).HasBindingOrigins) :
    let compiled := compileCore prog fresh state
    (((root.image deadlineOf).application.runPolicies
      (root.liftProfile deadlineOf rootProfile) (root.image deadlineOf).serialService
      (plan.image deadlineOf).serviceInvocations execution).map
        (fun out => (out.native.application.memory.finished compiled.graph.nodeCount,
          compiled.readPublicTerminal? out.native.application.memory))) =
      (denoteSource prog profile current.current.source).map fun terminal =>
        (true, some (cast (congrArg (VEnv L)
          (compileCore_terminalCtx_eq_sourceTerminalCtx prog fresh state).symm)
            terminal).erasePubEnv) := by
  revert profile current execution checkpoint hinitial
  induction plan with
  | ret empty fresh state =>
      intro profile current execution checkpoint _
      simp only [image, instructions, ApplicationImage.serviceInvocations,
        List.flatMap_nil, MessageApplication.runPolicies, FinDist.map_pure, denoteSource]
      apply congrArg FinDist.pure
      exact Prod.ext
        (current.finished_public_readout _ execution.native.application checkpoint.refines).1
        (current.finished_public_readout _ execution.native.application checkpoint.refines).2
  | sample nextPlan ih =>
      intro profile current execution checkpoint hinitial
      simp only [image, instructions, ApplicationImage.serviceInvocations,
        List.flatMap_cons, ApplicationInstruction.serviceInvocations,
        MessageApplication.runPolicies_append, FinDist.map_bind,
        denoteSource_sample]
      refine ForwardCheckpoint.sample_bind nextPlan profile current execution checkpoint _
        (fun env => (denoteSource _ profile.afterSample env).map _) ?_
      intro next native hnext
      exact ih profile.afterSample next native hnext hinitial
  | binding unrestricted nextPlan ih =>
      intro profile current execution checkpoint hinitial
      simp only [image, instructions, ApplicationImage.serviceInvocations,
        List.flatMap_cons, ApplicationInstruction.serviceInvocations,
        MessageApplication.runPolicies_append, FinDist.map_bind,
        denoteSource_commit]
      refine ForwardCheckpoint.binding_bind unrestricted nextPlan profile current execution
        checkpoint hinitial.1 _ (fun env => (denoteSource _ profile.afterCommit env).map _) ?_
      intro next native hnext
      exact ih profile.afterCommit next native hnext hinitial.2
  | publicChoice publicGuard nextPlan ih =>
      intro profile current execution checkpoint hinitial
      simp only [image, instructions, ApplicationImage.serviceInvocations,
        List.flatMap_cons, ApplicationInstruction.serviceInvocations,
        MessageApplication.runPolicies_append, FinDist.map_bind,
        denoteSource_commit, denoteSource_reveal, VEnv.cons_get_here]
      refine ForwardCheckpoint.publicChoice_bind publicGuard nextPlan profile current execution
        checkpoint hinitial.1 _
        (fun env => (denoteSource _ profile.afterCommit.afterReveal env).map _) ?_
      intro next native hnext
      exact ih profile.afterCommit.afterReveal next native hnext hinitial.2
  | conditional publicGuard nextPlan ih =>
      intro profile current execution checkpoint hinitial
      simp only [image, instructions, ApplicationImage.serviceInvocations,
        List.flatMap_cons, ApplicationInstruction.serviceInvocations,
        MessageApplication.runPolicies_append, FinDist.map_bind,
        denoteSource_commit, denoteSource_reveal, VEnv.cons_get_here]
      refine ForwardCheckpoint.conditional_bind publicGuard nextPlan profile current execution
        checkpoint hinitial.1 horigins _
        (fun env => (denoteSource _ profile.afterCommit.afterReveal env).map _) ?_
      intro next native hnext
      exact ih profile.afterCommit.afterReveal next native hnext hinitial.2
  | conditionalCopy specification publicGuard nextPlan ih =>
      intro profile current execution checkpoint hinitial
      simp only [image, instructions, ApplicationImage.serviceInvocations,
        List.flatMap_cons, ApplicationInstruction.serviceInvocations,
        MessageApplication.runPolicies_append, FinDist.map_bind,
        denoteSource_commit, denoteSource_reveal, VEnv.cons_get_here]
      refine ForwardCheckpoint.conditionalCopy_bind specification publicGuard nextPlan
        profile current execution checkpoint hinitial.1 horigins _
        (fun env => (denoteSource _ profile.afterCommit.afterReveal env).map _) ?_
      intro next native hnext
      exact ih profile.afterCommit.afterReveal next native hnext hinitial.2

/-- End-to-end forward law from an independently interpreted checked source
program to the generated public-message application. Players use the lift of
one source profile, and the environment uses the emitted image's serial service.
No per-phase readout, progress, or source-coupling premises remain. -/
theorem service_source_public_law (source : WFProgram P L)
    (plan : ApplicationPlan source.accounted source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx)))
    (deadlineOf : Nat → Nat)
    (profile : SourceBehavioralProfile source.core.prog)
    (hinitial : plan.InitialControllerReadsPublic)
    (horigins : (plan.image deadlineOf).HasBindingOrigins) :
    (((plan.image deadlineOf).application.runPolicies
      (plan.liftProfile deadlineOf profile) (plan.image deadlineOf).serialService
      (plan.image deadlineOf).serviceInvocations (plan.initialExecution deadlineOf)).map
        (fun out => (out.native.application.memory.finished (compile source.core).graph.nodeCount,
          (compile source.core).readPublicTerminal? out.native.application.memory))) =
      (denoteSource source.core.prog profile source.core.env).map fun terminal =>
        (true, some (cast (congrArg (VEnv L)
          (compileCore_terminalCtx_eq_sourceTerminalCtx source.core.prog source.core.fresh
            (BuildState.fromInitial
              (initialState source.core.Γ source.core.env source.core.wctx))).symm)
            terminal).erasePubEnv) := by
  exact ForwardCheckpoint.service_public_law plan profile (compiledInitialCoupled source.core)
    (plan.initialExecution deadlineOf) (ForwardCheckpoint.initial source plan profile deadlineOf)
    hinitial horigins

end Vegas.ApplicationPlan

/-- info: 'Vegas.ApplicationPlan.ForwardCheckpoint.service_public_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.ForwardCheckpoint.service_public_law

/-- info: 'Vegas.ApplicationPlan.service_source_public_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.service_source_public_law
