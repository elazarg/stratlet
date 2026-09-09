/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPolicyLaws
import Interaction.SealedTimeoutApplication
import Vegas.Compile.SealedTimeoutRefinement

/-! # Checked source support in the shared message-application game

The timed sealed compiler instance uses the shared observation-local policy
runner. Every supported execution still has the existing written-source
support guarantee. This is not a policy backtranslation, equality of outcome
laws, or proof of settlement. Final expiration may leave the source incomplete.
-/

namespace Vegas.WFProgram

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- The receipt-bearing shared policy game retains source-prefix correctness
for arbitrary player and environment policies of the timed sealed instance. -/
theorem sealed_timeout_message_policy_source (source : WFProgram Player L) (ty : L.Ty)
    [DecidableEq (L.Val ty)]
    (supported : SealedFragment (ToEventGraph.compile source.core).graph ty)
    (timed : SealedTimeout Player) (hprogram : timed.program = supported.compile)
    (players : Player → (timed.messageApplication (Value := L.Val ty)).PlayerPolicy)
    (environment : (timed.messageApplication (Value := L.Val ty)).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (execution : (timed.messageApplication (Value := L.Val ty)).PolicyExecution)
    (hmem : execution ∈
      (((timed.messageApplication (Value := L.Val ty)).policyGame environment schedule
        (timed.toSharedState (SealedTimeout.State.empty Player (L.Val ty)))).play
          players).support) :
    ∃ cfg : Config (ToEventGraph.compile source.core).graph,
      (ToEventGraph.compile source.core).graph.decodeSealedFrom ty
        execution.native.application.application.service
        (Config.initial (ToEventGraph.compile source.core).graph)
        execution.native.application.application.events = some cfg ∧
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
  have htrace := (timed.messageApplication (Value := L.Val ty)).runPolicies_initial_native_support
    players environment schedule
    (timed.toSharedState (SealedTimeout.State.empty Player (L.Val ty))) execution hmem
  rw [SealedTimeout.run_shared_actions] at htrace
  have hnative := FinDist.mem_support_pure.mp htrace
  rw [hnative]
  have htimed : timed = ⟨supported.compile, timed.openingNode, timed.deadline⟩ := by
    cases timed
    cases hprogram
    rfl
  have hsource := source.sealed_timeout_run_source ty supported timed.openingNode timed.deadline
    (execution.nativeTrace.map (SealedTimeout.fromSharedAction timed))
  simpa only [← htimed, SealedTimeout.toSharedState] using hsource

/--
info: 'Vegas.WFProgram.sealed_timeout_message_policy_source' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WFProgram.sealed_timeout_message_policy_source

end Vegas.WFProgram
