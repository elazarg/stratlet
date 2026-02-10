import Vegas.LetProtocol.ParentView
import Vegas.GameTheory.EFG
import Vegas.GameTheory.MAID
import Vegas.LetCore.Concrete

/-!
# Denotation Bridges: ParentProtoProg to MAID and EFG

Two bridge layers:
1. **Structural**: `ParentProtoProg.toMAIDNodes` / `ParentProtoProg.toMAID`
   extracts the DAG structure (nodes + parent sets) as a MAID diagram.
2. **Semantic**: `ParentProtoProg.toEFG` unfolds a `ParentProtoProg` (scoped to
   the bool-only fragment via `BasicLang`) into an `EFG.GameTree`.

This file lives in `LetProtocol` (not `GameTheory`) because it bridges FROM
protocol programs TO game-theoretic structures. `GameTheory` is self-contained.
-/

namespace Proto

open Defs Prog Env

variable {L : Language}

-- ============================================================
-- Layer 1: Structural — ParentProtoProg → MAID
-- ============================================================

/-- Extract MAID nodes from a `ParentProtoProg`.
    Each `sample` becomes a chance node, each `choose` becomes a decision node.
    Pure control flow (`ret`, `letDet`, `observe`) produces no MAID nodes. -/
def ParentProtoProg.toMAIDNodes : ParentProtoProg (L := L) Γ τ → List MAID.Node
  | .ret _ => []
  | .letDet _ k => toMAIDNodes k
  | .observe _ k => toMAIDNodes k
  | .sample id ps _ k =>
      { id := id, kind := .chance, parents := ps.parents } :: toMAIDNodes k
  | .choose id who ps _ k =>
      { id := id, kind := .decision who, parents := ps.parents } :: toMAIDNodes k

/-- The ids extracted by `toMAIDNodes` are exactly `yieldIds`. -/
theorem ParentProtoProg.toMAIDNodes_ids_eq_yieldIds
    (p : ParentProtoProg (L := L) Γ τ) :
    (p.toMAIDNodes.map MAID.Node.id) = p.yieldIds := by
  induction p with
  | ret _ => rfl
  | letDet _ _ ih => exact ih
  | observe _ _ ih => exact ih
  | sample id ps K _ ih =>
      simp only [toMAIDNodes, yieldIds, List.map_cons]
      exact congr_arg _ ih
  | choose id who ps A _ ih =>
      simp only [toMAIDNodes, yieldIds, List.map_cons]
      exact congr_arg _ ih

/-- Convert a `ParentProtoProg` to a MAID Diagram.
    Requires `NoDupYieldIds` on the embedded program for the `nodup_ids` proof. -/
def ParentProtoProg.toMAID (p : ParentProtoProg (L := L) Γ τ)
    (hnd : NoDupYieldIds (embed p)) : MAID.Diagram where
  nodes := p.toMAIDNodes
  nodup_ids := by
    rw [toMAIDNodes_ids_eq_yieldIds]
    rwa [NoDupYieldIds, yieldIds_embed] at hnd
  parents_exist := sorry  -- follows from sequential structure; deferred
  acyclic := True  -- placeholder

-- ============================================================
-- Layer 2: Semantic — ParentProtoProg → EFG.GameTree (bool-only)
-- ============================================================

/-- For all `choose` sites, the action list has no duplicates
    for all reachable observations. -/
def NodupActions : ParentProtoProg (L := L) Γ τ → Prop
  | .ret _ => True
  | .letDet _ k => NodupActions k
  | .observe _ k => NodupActions k
  | .sample _ _ _ k => NodupActions k
  | .choose _ _ ps A k =>
      (∀ obs : L.Env (viewOfVarSpec ps.vars).Δ, (A obs).Nodup) ∧ NodupActions k

/-- Convert a `ParentProtoProg` to an `EFG.GameTree`.
    Scoped to the bool-only fragment with `BasicLang`.
    The utility function maps terminal values to player payoffs. -/
def ParentProtoProg.toEFG
    (u : Proto.Utility (L := BasicLang) τ) :
    ParentProtoProg (L := BasicLang) Γ τ → BasicLang.Env Γ → EFG.GameTree Nat
  | .ret e, env =>
      .terminal (u (BasicLang.eval e env))
  | .letDet e k, env =>
      toEFG u k (BasicLang.eval e env, env)
  | .observe _c k, env =>
      -- Treat observe as transparent (skip the guard).
      -- A more careful version would prune unreachable branches.
      toEFG u k env
  | .sample _id ps K k, env =>
      let obs := (viewOfVarSpec ps.vars).proj env
      let dist := K obs
      -- Create EFG chance branches from the WDist weights
      let branches := dist.weights.map fun (v, w) =>
        (toEFG u k (v, env), w)
      .chance branches
  | .choose _id who ps A k, env =>
      let obs := (viewOfVarSpec ps.vars).proj env
      let actions := A obs
      let subtrees := actions.map fun v =>
        toEFG u k (v, env)
      .decision _id who subtrees

-- ============================================================
-- Correctness lemmas (sorry for now, proved in later milestones)
-- ============================================================

/-- The yield IDs of the EFG tree's decision nodes match the Proto's yield IDs.
    (Statement is informal; a precise version requires collecting pids from the EFG tree.) -/
theorem toEFG_yieldIds_match
    (p : ParentProtoProg (L := BasicLang) Γ τ)
    (u : Proto.Utility (L := BasicLang) τ) (env : BasicLang.Env Γ) :
    True := trivial  -- placeholder: precise statement deferred

/-- The resulting EFG tree is well-formed under appropriate conditions. -/
theorem toEFG_wfTree
    (p : ParentProtoProg (L := BasicLang) Γ τ)
    (u : Proto.Utility (L := BasicLang) τ) (env : BasicLang.Env Γ)
    (hnd : NodupActions p)
    (hwf : WFChanceOnProg ReachAll (ParentProtoProg.embed p)) :
    EFG.WFTree (p.toEFG u env) := sorry

end Proto
