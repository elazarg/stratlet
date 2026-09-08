/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.KernelRound
import Vegas.EventGraph.ProtocolOrder

/-! # Native behavioral rounds and typed node execution -/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}

theorem behavioralJoint_internal_eq_policyNodeRound {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G) (policies : CommitPolicyProfile G)
    (state : ReachableConfig G) (trace : (toExecutionProtocol G hwf hguards).Trace state)
    (hterm : ¬ (toExecutionProtocol G hwf hguards).terminal state)
    (hinternal : (readyInternalNodes G state.1).Nonempty) :
    ((toInformationModel G hwf hguards).behavioralJoint
      (fun who => (policies who).behavioral hwf hguards) trace hterm).bind
      ((toExecutionProtocol G hwf hguards).step state) =
        runPolicyNodes hwf hguards policies state (protocolNodeRound G state.1.done) := by
  have hround : protocolNodeRound G state.1.done = [Classical.choose hinternal] := by
    have hnodes : readyInternalNodes G state.1 =
        readyInternalNodes G (skeletonConfig G state.1.done) :=
      readyInternalNodes_eq_of_done_eq rfl
    have hcanonical : (readyInternalNodes G (skeletonConfig G state.1.done)).Nonempty :=
      hnodes ▸ hinternal
    rw [protocolNodeRound, dif_pos hcanonical]
  simp only [hround, runPolicyNodes_cons, runPolicyNodes_nil, FinDist.bind_pure]
  calc
    _ = ((toInformationModel G hwf hguards).behavioralJoint
        (fun who => (policies who).behavioral hwf hguards) trace hterm).bind
        (fun _ => policyNodeStep hwf hguards policies state (Classical.choose hinternal)) := by
      apply FinDist.bind_congr
      intro command _
      exact canonical_internal_step_eq_policyNodeStep hwf hguards policies state command hinternal
    _ = _ := FinDist.bind_const _ _

end Vegas.EventGraph
