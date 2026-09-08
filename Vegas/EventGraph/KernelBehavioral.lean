/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.KernelPlan
import Vegas.EventGraph.KernelNativeFrontier

/-! # Complete native behavioral execution in written node order

The actual one-round correspondence is iterated and the resulting complete
legal order is exchanged with increasing node order. All probability and
read-dependency conditions are discharged for the declared-read kernels.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}

private theorem runBehavioralFrom_eq_policyRounds_of_step_eq {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G) (policies : CommitPolicyProfile G)
    (hstep : ∀ (state : ReachableConfig G)
      (trace : (toExecutionProtocol G hwf hguards).Trace state)
      (hterm : ¬ (toExecutionProtocol G hwf hguards).terminal state),
      ((toInformationModel G hwf hguards).behavioralJoint
        (fun who => (policies who).behavioral hwf hguards) trace hterm).bind
        ((toExecutionProtocol G hwf hguards).step state) =
          runPolicyNodes hwf hguards policies state (protocolNodeRound G state.1.done))
    (fuel : Nat) (history : (toExecutionProtocol G hwf hguards).History) :
    ((toInformationModel G hwf hguards).runBehavioralFrom
      (fun who => (policies who).behavioral hwf hguards) fuel history).map
      (fun later => later.state) = runPolicyRounds hwf hguards policies fuel history.state := by
  induction fuel generalizing history with
  | zero => simp [InformationModel.runBehavioralFrom, runPolicyRounds]
  | succ fuel ih =>
      by_cases hterm : (toExecutionProtocol G hwf hguards).terminal history.state
      · rw [InformationModel.runBehavioralFrom_of_terminal _ _ _ hterm,
          runPolicyRounds_of_terminal hwf hguards policies _ _ hterm, FinDist.map_pure]
      · rw [InformationModel.runBehavioralFrom_succ_of_not_terminal _ _ _ hterm,
          FinDist.map_bind]
        calc
          _ = (((toInformationModel G hwf hguards).behavioralJoint
              (fun who => (policies who).behavioral hwf hguards) history.trace hterm).bind
              ((toExecutionProtocol G hwf hguards).step history.state)).bind
                (runPolicyRounds hwf hguards policies fuel) := by
            rw [FinDist.bind_bind]
            apply FinDist.bind_congr
            intro draw _
            rw [FinDist.map_bindOnSupport]
            simp only [ih]
            exact FinDist.bindOnSupport_eq_bind _ _
          _ = _ := by rw [hstep]; rfl

/-- Every bounded native behavioral execution has exactly the configuration
law of its canonical typed node rounds. -/
theorem runBehavioralFrom_eq_policyRounds {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G) (policies : CommitPolicyProfile G)
    (hsingle : ∀ cfg who first second,
      ReadyCommitNode G cfg who first → ReadyCommitNode G cfg who second → first = second)
    (fuel : Nat) (history : (toExecutionProtocol G hwf hguards).History) :
    ((toInformationModel G hwf hguards).runBehavioralFrom
      (fun who => (policies who).behavioral hwf hguards) fuel history).map
      (fun later => later.state) = runPolicyRounds hwf hguards policies fuel history.state :=
  runBehavioralFrom_eq_policyRounds_of_step_eq hwf hguards policies
    (fun state trace hterm => behavioralJoint_eq_policyNodeRound hwf hguards policies
      state trace hterm (hsingle state.1)) fuel history

/-- The complete native graph game under declared-read policies has exactly
the terminal configuration law of increasing node-order execution. -/
theorem runBehavioral_eq_nodeOrder {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G) (policies : CommitPolicyProfile G)
    (hsingle : ∀ cfg who first second,
      ReadyCommitNode G cfg who first → ReadyCommitNode G cfg who second → first = second) :
    ((toInformationModel G hwf hguards).runBehavioral
      (fun who => (policies who).behavioral hwf hguards) G.nodeCount).map
      (fun history => history.state) =
        runPolicyNodes hwf hguards policies ⟨Config.initial G, .initial⟩ G.nodeOrder := by
  rw [InformationModel.runBehavioral,
    runBehavioralFrom_eq_policyRounds hwf hguards policies hsingle]
  exact runPolicyRounds_eq_nodeOrder hwf hguards policies

end Vegas.EventGraph
