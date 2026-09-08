/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.KernelOrder
import Vegas.EventGraph.ProtocolOrder

/-! # Expanding policy-driven rounds into a complete node execution -/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}

/-- Execute canonical rounds as lists of actual typed node steps. -/
def runPolicyRounds {G : Graph Player L} (hwf : G.WF) (hguards : GuardLive G)
    (policies : CommitPolicyProfile G) : Nat → ReachableConfig G → FinDist (ReachableConfig G)
  | 0, state => FinDist.pure state
  | fuel + 1, state =>
      (runPolicyNodes hwf hguards policies state (protocolNodeRound G state.1.done)).bind
        (runPolicyRounds hwf hguards policies fuel)

theorem runPolicyRounds_of_terminal {G : Graph Player L} (hwf : G.WF)
    (hguards : GuardLive G) (policies : CommitPolicyProfile G)
    (fuel : Nat) (state : ReachableConfig G) (hterminal : Terminal G state.1) :
    runPolicyRounds hwf hguards policies fuel state = FinDist.pure state := by
  have hround : protocolNodeRound G state.1.done = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro node hmem
    exact (protocolNodeRound_readyOrder G state.1.done).not_mem_of_mem hmem (hterminal node)
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [runPolicyRounds, hround, runPolicyNodes_nil, FinDist.pure_bind, ih]

theorem runPolicyRounds_eq_plan {G : Graph Player L} (hwf : G.WF)
    (hguards : GuardLive G) (policies : CommitPolicyProfile G)
    (fuel : Nat) (state : ReachableConfig G) :
    runPolicyRounds hwf hguards policies fuel state =
      runPolicyNodes hwf hguards policies state (protocolNodePlan G fuel state.1.done) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      simp only [runPolicyRounds, protocolNodePlan, runPolicyNodes_append]
      apply FinDist.bind_congr
      intro next hnext
      rw [ih]
      have hdone := runPolicyNodes_support_done hwf hguards policies state _
        (protocolNodeRound_readyOrder G state.1.done) next hnext
      rw [protocolNodeRound_done] at hdone
      rw [hdone]

/-- Canonical batches and increasing node order induce exactly the same law
of terminal graph configurations. -/
theorem runPolicyRounds_eq_nodeOrder {G : Graph Player L} (hwf : G.WF)
    (hguards : GuardLive G) (policies : CommitPolicyProfile G) :
    runPolicyRounds hwf hguards policies G.nodeCount ⟨Config.initial G, .initial⟩ =
      runPolicyNodes hwf hguards policies ⟨Config.initial G, .initial⟩ G.nodeOrder := by
  rw [runPolicyRounds_eq_plan]
  exact runPolicyNodes_eq_nodeOrder hwf hguards policies _
    (protocolNodePlan_readyOrder G _ _) (protocolNodePlan_isFullOrder G)

theorem runPolicyRounds_terminal {G : Graph Player L} (hwf : G.WF)
    (hguards : GuardLive G) (policies : CommitPolicyProfile G)
    (fuel : Nat) (state : ReachableConfig G)
    (hbound : G.nodeCount ≤ state.1.done.card + fuel) (next : ReachableConfig G)
    (hnext : next ∈ (runPolicyRounds hwf hguards policies fuel state).support) :
    Terminal G next.1 := by
  rw [runPolicyRounds_eq_plan] at hnext
  exact runPolicyNodes_terminal hwf hguards policies state _
    (protocolNodePlan_readyOrder G _ _) (protocolNodePlan_complete G _ _ hbound) next hnext

end Vegas.EventGraph
