/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationMessageRequirement
import Vegas.Compile.ApplicationForwardCheckpoint
import Interaction.MessageApplicationMessageInvariant

/-! # Withholding at authenticated generated entry points

A principal can refuse to author any message. Starting without its messages,
replay and local delivery cannot supply one. If a generated node requires that
principal's submission, every finite supported execution leaves it unfinished,
regardless of the other policies, inclusion order, or clock advances.

This identifies a missing resolution mechanism, not an assumption that a
scheduler behaves unfairly. It rules out an exact completion-sensitive source
law for this deviation. It does not rule out implementations with additional
source-certified fallback entry points or weaker observations of outcomes.
-/

noncomputable section

namespace Vegas.ApplicationImage

open Interaction Interaction.MessageApplication GameTheory GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- No authored submission by the required principal means no completion of
this node. Private preparation, replay, waiting, all other principals, and the
environment remain unrestricted. -/
theorem RequiresSubmission.runPolicies_not_done
    {image : ApplicationImage P L} {node : Nat} {who : P}
    (required : image.RequiresSubmission node who)
    (players : P → image.application.PlayerPolicy)
    (environment : image.application.EnvironmentPolicy)
    (hsilent : ∀ history view payload,
      .submit payload ∉ (players who history view).support)
    (schedule : List (@Invocation P)) (execution next : image.application.PolicyExecution)
    (hpool : execution.native.pool.Satisfies (fun message => message.sender ≠ who))
    (hnotDone : execution.native.application.memory.done node = false)
    (hnext : next ∈
      (image.application.runPolicies players environment schedule execution).support) :
    next.native.application.memory.done node = false := by
  apply (image.application.runPolicies_message_application_invariant
    (fun message => message.sender ≠ who) (fun state => state.memory.done node = false)
    (fun state actor command hstate => RequiresSubmission.privateStep state actor command hstate)
    (fun state message next hstate hmessage hnext => required.handle state message next
      hstate hmessage hnext)
    (fun state command next hstate hnext =>
      required.environmentStep state command next hstate hnext)
    players environment ?_ schedule execution next hpool hnotDone hnext).2
  intro current actor payload hsubmit serial
  change actor ≠ who
  intro heq
  subst actor
  exact hsilent (current.principalHistory who)
    (State.observe image.application current.native who) payload hsubmit

end Vegas.ApplicationImage

namespace Vegas.ApplicationPlan

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- From canonical initialization, replacing a single principal by permanent
waiting prevents any node requiring its submission from completing. This
quantifies over every environment policy and finite invocation schedule. -/
theorem withholding_not_done (source : WFProgram P L)
    (plan : ApplicationPlan source.accounted source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx)))
    (deadlineOf : Nat → Nat) (node : Nat) (who : P)
    (required : (plan.image deadlineOf).RequiresSubmission node who)
    (players : Profile (policySignature P (plan.image deadlineOf).application))
    (environment : (plan.image deadlineOf).application.EnvironmentPolicy)
    (schedule : List (@Invocation P))
    (next : (plan.image deadlineOf).application.PolicyExecution)
    (hnext : next ∈ ((plan.image deadlineOf).application.runPolicies
      (Profile.update players who (fun _ _ => FinDist.pure .wait)) environment
      schedule (plan.initialExecution deadlineOf)).support) :
    next.native.application.memory.done node = false := by
  apply required.runPolicies_not_done
    (Profile.update players who (fun _ _ => FinDist.pure .wait)) environment ?_
    schedule (plan.initialExecution deadlineOf) next ?_ rfl hnext
  · intro history view payload
    simp only [Profile.update_same, FinDist.mem_support_pure, reduceCtorEq, not_false_eq_true]
  · exact MessagePool.Satisfies.empty

/-- The completion marginal is certainly false under the waiting deviation,
even if every actual submitted packet is included and the clock advances.
Such service assumptions cannot provide a missing owner-authored message. -/
theorem withholding_finished_law (source : WFProgram P L)
    (plan : ApplicationPlan source.accounted source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx)))
    (deadlineOf : Nat → Nat) (node : Nat) (who : P)
    (required : (plan.image deadlineOf).RequiresSubmission node who)
    (hnode : node < (compile source.core).graph.nodeCount)
    (players : Profile (policySignature P (plan.image deadlineOf).application))
    (environment : (plan.image deadlineOf).application.EnvironmentPolicy)
    (schedule : List (@Invocation P)) :
    (((plan.image deadlineOf).application.runPolicies
      (Profile.update players who (fun _ _ => FinDist.pure .wait)) environment
      schedule (plan.initialExecution deadlineOf)).map
        (fun out => out.native.application.memory.finished (compile source.core).graph.nodeCount)) =
      FinDist.pure false := by
  calc
    _ = ((plan.image deadlineOf).application.runPolicies
        (Profile.update players who (fun _ _ => FinDist.pure .wait)) environment
        schedule (plan.initialExecution deadlineOf)).map (fun _ => false) := by
      apply FinDist.map_congr_of_eq_on_support
      intro next hnext
      have hnotDone := plan.withholding_not_done source deadlineOf node who required players
        environment schedule next hnext
      apply Bool.eq_false_iff.mpr
      intro hfinished
      have hdone := List.all_eq_true.mp hfinished node (List.mem_range.mpr hnode)
      simp only [hnotDone, Bool.false_eq_true] at hdone
    _ = FinDist.pure false := FinDist.map_const _ false

/-- No source profile matches the completion-sensitive public-outcome law
of this runtime deviation. The decoder retains incompletion; it does not
silently reinterpret unfinished execution as a chosen source quit. -/
theorem withholding_no_source_public_law (source : WFProgram P L)
    (plan : ApplicationPlan source.accounted source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx)))
    (deadlineOf : Nat → Nat) (node : Nat) (who : P)
    (required : (plan.image deadlineOf).RequiresSubmission node who)
    (hnode : node < (compile source.core).graph.nodeCount)
    (players : Profile (policySignature P (plan.image deadlineOf).application))
    (environment : (plan.image deadlineOf).application.EnvironmentPolicy)
    (schedule : List (@Invocation P))
    (replacement : SourceBehavioralProfile source.core.prog) :
    (((plan.image deadlineOf).application.runPolicies
      (Profile.update players who (fun _ _ => FinDist.pure .wait)) environment
      schedule (plan.initialExecution deadlineOf)).map
        (fun out => (out.native.application.memory.finished (compile source.core).graph.nodeCount,
          (compile source.core).readPublicTerminal? out.native.application.memory))) ≠
      (denoteSource source.core.prog replacement source.core.env).map fun terminal =>
        (true, some (cast (congrArg (VEnv L)
          (compileCore_terminalCtx_eq_sourceTerminalCtx source.core.prog source.core.fresh
            (BuildState.fromInitial
              (initialState source.core.Γ source.core.env source.core.wctx))).symm)
            terminal).erasePubEnv) := by
  intro hlaw
  have hcompletion := congrArg (fun law => law.map Prod.fst) hlaw
  simp only [FinDist.map_comp, Function.comp_def, FinDist.map_const] at hcompletion
  rw [plan.withholding_finished_law source deadlineOf node who required hnode players
    environment schedule] at hcompletion
  have hfalse : false ∈ (FinDist.pure true).support := by
    rw [← hcompletion]
    exact FinDist.mem_support_pure.mpr rfl
  simp only [FinDist.mem_support_pure, Bool.false_eq_true] at hfalse

end Vegas.ApplicationPlan

/-- info: 'Vegas.ApplicationPlan.withholding_no_source_public_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.withholding_no_source_public_law
