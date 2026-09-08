/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedTimeoutPolicyLaws
import Vegas.Compile.SealedTimeoutRefinement

/-! # Timed public-message policy executions and the checked source

The game evaluates the actual timed application. Every supported policy outcome
decodes to a reachable graph prefix, and every terminal decoded prefix has a
written-order source execution with the same bindings and payout evaluation.
Expiration can leave that prefix incomplete: runtime resolution is not source
termination. The theorem is a support correspondence, not a law comparison,
strategy backtranslation, or settlement guarantee.
-/

namespace Vegas.WFProgram

open EventGraph Interaction Interaction.SealedTimeout

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- Arbitrary timed player and environment policies retain the operational
source-prefix guarantee of the supported compiler fragment. -/
theorem sealed_timeout_policy_source (source : WFProgram Player L) (ty : L.Ty)
    [DecidableEq (L.Val ty)]
    (supported : SealedFragment (ToEventGraph.compile source.core).graph ty)
    (openingNode deadline : Nat)
    (players : Player → PlayerPolicy Player (L.Val ty))
    (environment : EnvironmentPolicy Player (L.Val ty))
    (schedule : List (Invocation Player))
    (execution : PolicyExecution Player (L.Val ty))
    (hmem : execution ∈
      ((policyGame ⟨supported.compile, openingNode, deadline⟩ environment schedule
        (State.empty Player (L.Val ty))).play players).support) :
    ∃ cfg : Config (ToEventGraph.compile source.core).graph,
      (ToEventGraph.compile source.core).graph.decodeSealedFrom ty
        execution.native.application.service
        (Config.initial (ToEventGraph.compile source.core).graph)
        execution.native.application.events = some cfg ∧
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
  have htrace := runPolicies_native_eq_run_trace
    ⟨supported.compile, openingNode, deadline⟩ players environment schedule
    (State.empty Player (L.Val ty)) execution hmem
  rw [htrace]
  exact source.sealed_timeout_run_source ty supported openingNode deadline execution.nativeTrace

end Vegas.WFProgram
