/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedPolicyLaws
import Vegas.Compile.SealedSource

/-! # Native public-message policy executions and the checked source

The bounded policy game runs the compiled application through its native
transition function. Every outcome in its support has an actual native action
trace, so the operational source theorem applies to adversarial policies too.
The conclusion remains support-level and conditional on graph termination;
it supplies neither a source policy nor a settlement guarantee.
-/

namespace Vegas.WFProgram

open EventGraph Interaction Interaction.SealedProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- Every supported policy-game execution is a graph prefix of the actual
checked compilation; terminal prefixes reconstruct the written source with
all terminal bindings and its payout evaluation. -/
theorem sealed_policy_source (source : WFProgram Player L) (ty : L.Ty)
    [DecidableEq (L.Val ty)]
    (supported : SealedFragment (ToEventGraph.compile source.core).graph ty)
    (rebroadcast : Bool)
    (players : Player → PlayerPolicy Player (L.Val ty) rebroadcast)
    (environment : EnvironmentPolicy Player (L.Val ty))
    (schedule : List (Invocation Player))
    (execution : PolicyExecution Player (L.Val ty))
    (hmem : execution ∈
      ((policyGame rebroadcast supported.compile environment schedule
        (SealedProgram.State.empty Player (L.Val ty))).play players).support) :
    ∃ cfg : Config (ToEventGraph.compile source.core).graph,
      (ToEventGraph.compile source.core).graph.decodeSealed ty execution.native = some cfg ∧
      Reachable (ToEventGraph.compile source.core).graph cfg ∧
      (Terminal (ToEventGraph.compile source.core).graph cfg →
        ∃ terminalEnv : VEnv L (ToEventGraph.compile source.core).terminalCtx,
          SmallStep.Star
            { ctx := source.core.Γ, env := source.core.env, cont := source.core.prog }
            { ctx := (ToEventGraph.compile source.core).terminalCtx,
              env := terminalEnv, cont := .ret (ToEventGraph.compile source.core).sourcePayoffs } ∧
          evalPayoffs? (ToEventGraph.compile source.core).payoffs cfg.store =
            some (evalPayoffs (ToEventGraph.compile source.core).sourcePayoffs terminalEnv) ∧
          ∀ {name bindTy}
            (h : VHasVar (ToEventGraph.compile source.core).terminalCtx name bindTy),
            Store.getAs cfg.store
              ((ToEventGraph.compile source.core).terminalState.fieldOf h) bindTy.base =
                some (terminalEnv.get h)) := by
  have htrace := runPolicies_native_eq_run_trace rebroadcast supported.compile
    players environment schedule (SealedProgram.State.empty Player (L.Val ty)) execution hmem
  rw [htrace]
  exact source.sealed_run_source ty supported execution.nativeTrace

end Vegas.WFProgram
