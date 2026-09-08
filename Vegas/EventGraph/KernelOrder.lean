/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.KernelCommutation
import Vegas.EventGraph.KernelSchedule
import Vegas.EventGraph.Linearization

/-! # Probability-law invariance of legal graph execution orders

These theorems concern actual guarded policy, sample, and reveal laws. The
order-independence condition is the graph's declared-read discipline; no
separate probabilistic independence premise is supplied by callers.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}

/-- Every structural independent-swap chain preserves the complete law of the
actual policy-driven executor. -/
theorem Graph.ReadyOrder.Equivalent.runPolicyNodes_eq {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G) (policies : CommitPolicyProfile G)
    {done : Finset (Fin G.nodeCount)} {first second : List (Fin G.nodeCount)}
    (hequiv : Graph.ReadyOrder.Equivalent G done first second) :
    ∀ (state : ReachableConfig G), state.1.done = done →
      runPolicyNodes hwf hguards policies state first =
        runPolicyNodes hwf hguards policies state second := by
  induction hequiv with
  | refl => intro state _; rfl
  | @cons done first second node hnot hdeps _ ih =>
      intro state hdone
      simp only [runPolicyNodes_cons]
      apply FinDist.bind_congr
      intro next hnext
      have hready : Ready G state.1 node := by
        change node ∉ state.1.done ∧ G.prereqs node ⊆ state.1.done
        rw [hdone]
        exact ⟨hnot, hdeps⟩
      have hnextDone := policyNodeStep_support_done hwf hguards policies state node next hnext
      rw [if_pos hready, hdone] at hnextDone
      exact ih next hnextDone
  | swap first second rest hne hf hfd hs hsd =>
      intro state hdone
      have hfirst : Ready G state.1 first := by
        change first ∉ state.1.done ∧ G.prereqs first ⊆ state.1.done
        rw [hdone]
        exact ⟨hf, hfd⟩
      have hsecond : Ready G state.1 second := by
        change second ∉ state.1.done ∧ G.prereqs second ⊆ state.1.done
        rw [hdone]
        exact ⟨hs, hsd⟩
      simp only [runPolicyNodes_cons]
      have hpair := congrArg
        (fun law => law.bind (fun after => runPolicyNodes hwf hguards policies after rest))
        (policyNodeStep_comm hwf hguards policies state first second hfirst hsecond hne)
      simpa only [FinDist.bind_bind] using hpair
  | trans _ _ ih₁ ih₂ =>
      intro state hdone
      exact (ih₁ state hdone).trans (ih₂ state hdone)

/-- Any two legal orders of the same requested nodes have the same final
configuration law under arbitrary declared-read commitment policies. -/
theorem runPolicyNodes_eq_of_readyOrder_perm {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G) (policies : CommitPolicyProfile G)
    (state : ReachableConfig G) (first second : List (Fin G.nodeCount))
    (hfirst : G.ReadyOrder state.1.done first) (hsecond : G.ReadyOrder state.1.done second)
    (hperm : first.Perm second) :
    runPolicyNodes hwf hguards policies state first =
      runPolicyNodes hwf hguards policies state second :=
  (Graph.ReadyOrder.equivalent_of_perm hfirst hsecond hperm).runPolicyNodes_eq
    hwf hguards policies state rfl

/-- A legal full execution order has exactly the same law as increasing node
order, including every guarded decision and probabilistic sample. -/
theorem runPolicyNodes_eq_nodeOrder {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G) (policies : CommitPolicyProfile G)
    (order : List (Fin G.nodeCount))
    (horder : G.ReadyOrder ∅ order) (hfull : G.IsFullOrder order) :
    runPolicyNodes hwf hguards policies ⟨Config.initial G, .initial⟩ order =
      runPolicyNodes hwf hguards policies ⟨Config.initial G, .initial⟩ G.nodeOrder := by
  apply runPolicyNodes_eq_of_readyOrder_perm hwf hguards policies _ _ _ horder
    G.nodeOrder_readyOrder
  exact (List.perm_ext_iff_of_nodup hfull.1 (List.nodup_finRange _)).mpr
    (fun node => ⟨fun _ => G.mem_nodeOrder node, fun _ => hfull.2 node⟩)

end Vegas.EventGraph
