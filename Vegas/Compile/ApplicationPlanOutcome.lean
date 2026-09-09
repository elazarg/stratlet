/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationPlanRefinement
import Vegas.Compile.ApplicationSourceOutcome

/-! # Written-order source outcomes of public-message executions

These theorems start from a checked source, a structural backend derivation,
and the actual empty-pool public runtime initialization. They quantify over
arbitrary supported native and policy runs, including malformed messages and
unopenable bindings. Runtime completion supplies a written-order source run
with the same public terminal outcome.

This initialization provisions no sealed initial commitments. The statements
give safety on completed executions, not progress, honest outcome-law equality,
or deviation adequacy. Those require initialization, service, controller, and
information conditions beyond this support-level result.
-/

noncomputable section

namespace Vegas.ApplicationPlan

open EventGraph ToEventGraph Interaction

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Every completed native run of a generated checked program has the public
outcome of an actual written-order source execution. The refinement relation
is established by the compiler proof, not supplied as a runtime premise. -/
theorem run_source_public_outcome (source : WFProgram P L)
    (plan : ApplicationPlan source.accounted source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx)))
    (deadlineOf : Nat → Nat)
    (actions : List (plan.image deadlineOf).application.Action)
    (next : (plan.image deadlineOf).application.State)
    (hnext : next ∈ ((plan.image deadlineOf).application.run actions
      (MessageApplication.State.initial (plan.image deadlineOf).application
        (ApplicationImage.State.initial
          (ApplicationImage.Memory.initial (compile source.core).graph)))).support)
    (hfinished : next.application.memory.finished (compile source.core).graph.nodeCount = true) :
    ∃ terminalEnv : VEnv L (compile source.core).terminalCtx,
      SmallStep.Star
        { ctx := source.core.Γ, env := source.core.env, cont := source.core.prog }
        { ctx := (compile source.core).terminalCtx, env := terminalEnv,
          cont := .ret (compile source.core).sourcePayoffs } ∧
      (compile source.core).readPublicTerminal? next.application.memory =
        some terminalEnv.erasePubEnv := by
  obtain ⟨cfg, hrefines⟩ := plan.run_refines deadlineOf source.core.env source.legal
    _ next actions ⟨_, ApplicationImage.State.initial_refines (compile source.core).graph⟩ hnext
  exact source_public_outcome_of_refines source.core next.application cfg hrefines hfinished

/-- Arbitrary randomized runtime players and environments cannot produce a
completed public outcome without a source execution witness. This does not
identify the players' source strategies or equate their outcome distributions. -/
theorem runPolicies_source_public_outcome (source : WFProgram P L)
    (plan : ApplicationPlan source.accounted source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx)))
    (deadlineOf : Nat → Nat)
    (players : P → (plan.image deadlineOf).application.PlayerPolicy)
    (environment : (plan.image deadlineOf).application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation P))
    (next : (plan.image deadlineOf).application.PolicyExecution)
    (hnext : next ∈ ((plan.image deadlineOf).application.runPolicies
      players environment schedule
      (MessageApplication.PolicyExecution.initial (plan.image deadlineOf).application
        (MessageApplication.State.initial (plan.image deadlineOf).application
          (ApplicationImage.State.initial
            (ApplicationImage.Memory.initial (compile source.core).graph))))).support)
    (hfinished : next.native.application.memory.finished
      (compile source.core).graph.nodeCount = true) :
    ∃ terminalEnv : VEnv L (compile source.core).terminalCtx,
      SmallStep.Star
        { ctx := source.core.Γ, env := source.core.env, cont := source.core.prog }
        { ctx := (compile source.core).terminalCtx, env := terminalEnv,
          cont := .ret (compile source.core).sourcePayoffs } ∧
      (compile source.core).readPublicTerminal? next.native.application.memory =
        some terminalEnv.erasePubEnv := by
  obtain ⟨cfg, hrefines⟩ := plan.runPolicies_refines deadlineOf source.core.env source.legal
    players environment schedule _ next
    ⟨_, ApplicationImage.State.initial_refines (compile source.core).graph⟩ hnext
  exact source_public_outcome_of_refines source.core next.native.application cfg hrefines hfinished

end Vegas.ApplicationPlan

/-- info: 'Vegas.ApplicationPlan.run_source_public_outcome' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.run_source_public_outcome

/-- info: 'Vegas.ApplicationPlan.runPolicies_source_public_outcome' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.runPolicies_source_public_outcome
