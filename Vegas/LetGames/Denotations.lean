import Vegas.LetGames.ProtoGame
import Vegas.LetProtocol.ParentView
import GameTheory.EFG
import GameTheory.MAID
import Vegas.LetCore.Concrete

/-!
# Denotation Bridges: ParentProtoProg to MAID and EFG

Two bridge layers:
1. **Structural**: `ParentProtoProg.toMAIDNodes` / `ParentProtoProg.toMAID`
   extracts the DAG structure (nodes + parent sets) as a MAID diagram.
2. **Semantic**: `ParentProtoProg.toEFG` unfolds a `ParentProtoProg`
   (specialized to `BasicLang` and `NNReal`) into an `EFG.GameTree`.

This file bridges FROM protocol programs TO game-theoretic structures.
-/

namespace Proto

open Defs Prog Env

variable {L : Language}
variable {W : Type} [WeightModel W]

-- ============================================================
-- Layer 1: Structural — ParentProtoProg → MAID
-- ============================================================

/-- Extract MAID nodes from a `ParentProtoProg`.
    Each `sample` becomes a chance node, each `choose` becomes a decision node.
    Pure control flow (`ret`, `letDet`, `observe`) produces no MAID nodes. -/
def ParentProtoProg.toMAIDNodes : ParentProtoProg W Γ τ → List MAID.Node
  | .ret _ => []
  | .letDet _ k => toMAIDNodes k
  | .observe _ k => toMAIDNodes k
  | .sample id ps _ k =>
      { id := id, kind := .chance, parents := ps.parents,
        domainSize := 0 } :: toMAIDNodes k
  | .choose id who ps _ k =>
      { id := id, kind := .decision who, parents := ps.parents,
        domainSize := 0 } :: toMAIDNodes k

/-- The ids extracted by `toMAIDNodes` are exactly `yieldIds`. -/
theorem ParentProtoProg.toMAIDNodes_ids_eq_yieldIds
    (p : ParentProtoProg W Γ τ) :
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

/-- All parent references in yield sites point to yield IDs of the program.
    This is the structural precondition for `parents_exist` in the MAID diagram. -/
def AllParentsAreYieldIds (p : ParentProtoProg W Γ τ) : Prop :=
  ∀ n ∈ p.toMAIDNodes, ∀ pid ∈ n.parents, pid ∈ p.yieldIds

/-- Convert a `ParentProtoProg` to a MAID Diagram. -/
def ParentProtoProg.toMAID (p : ParentProtoProg W Γ τ)
    (hnd : NoDupYieldIds (embed p))
    (hallp : AllParentsAreYieldIds p)
    (htopo : MAID.TopologicalOrder p.toMAIDNodes) : MAID.Diagram where
  nodes := p.toMAIDNodes
  nodup_ids := by
    rw [toMAIDNodes_ids_eq_yieldIds]
    rwa [NoDupYieldIds, yieldIds_embed] at hnd
  parents_exist := by
    intro n hn pid hpid
    have h := hallp n hn pid hpid
    rw [← toMAIDNodes_ids_eq_yieldIds] at h
    exact List.mem_map.mp h
  acyclic := htopo

-- ============================================================
-- Layer 2: Semantic — ParentProtoProg → EFG.GameTree (BasicLang)
-- ============================================================

/-- For all `choose` sites, the action list has no duplicates
    for all observations. -/
def NodupActions : ParentProtoProg (L := L) W Γ τ → Prop
  | .ret _ => True
  | .letDet _ k => NodupActions k
  | .observe _ k => NodupActions k
  | .sample _ _ _ k => NodupActions k
  | .choose _ _ ps A k =>
      (∀ obs : L.Env (viewOfVarSpec ps.vars).Δ, (A obs).Nodup) ∧ NodupActions k

/-- For all `choose` sites, the action list is non-empty
    for all observations. -/
def NonEmptyActions : ParentProtoProg (L := L) W Γ τ → Prop
  | .ret _ => True
  | .letDet _ k => NonEmptyActions k
  | .observe _ k => NonEmptyActions k
  | .sample _ _ _ k => NonEmptyActions k
  | .choose _ _ ps A k =>
      (∀ obs : L.Env (viewOfVarSpec ps.vars).Δ, (A obs) ≠ []) ∧ NonEmptyActions k

/-- For all `choose` sites, the action list length is constant
    across all observations. -/
def ConstantArityAtSite : ParentProtoProg (L := L) W Γ τ → Prop
  | .ret _ => True
  | .letDet _ k => ConstantArityAtSite k
  | .observe _ k => ConstantArityAtSite k
  | .sample _ _ _ k => ConstantArityAtSite k
  | .choose _ _ ps A k =>
      (∀ obs₁ obs₂ : L.Env (viewOfVarSpec ps.vars).Δ,
        (A obs₁).length = (A obs₂).length) ∧ ConstantArityAtSite k

/-- Convert a `ParentProtoProg` to an `EFG.GameTree`.
    Specialized to `W = NNReal` because `EFG.GameTree` uses `NNReal` for chance weights,
    and to `BasicLang` because `toEFG` evaluates expressions concretely.
    The utility function maps terminal values to player payoffs. -/
def ParentProtoProg.toEFG
    (u : Proto.Utility (L := BasicLang) τ) :
    ParentProtoProg (W := NNReal) (L := BasicLang) Γ τ → BasicLang.Env Γ → EFG.GameTree Nat
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
-- Correctness lemmas
-- ============================================================

/-- The resulting EFG tree is well-formed under appropriate conditions. -/
theorem toEFG_wfTree
    (p : ParentProtoProg (W := NNReal) (L := BasicLang) Γ τ)
    (u : Proto.Utility (L := BasicLang) τ) (env : BasicLang.Env Γ)
    (hnd : NodupActions (L := BasicLang) p)
    (hne : NonEmptyActions (L := BasicLang) p)
    (hwf : WFChanceOnProg ReachAll (ParentProtoProg.embed p)) :
    EFG.WFTree (p.toEFG u env) := by
  induction p with
  | ret e => exact .terminal _
  | letDet e k ih => exact ih u (BasicLang.eval e env, env) hnd hne hwf
  | observe c k ih => exact ih u env hnd hne hwf
  | sample id ps K k ih =>
      have hprob : IsProb (K ((viewOfVarSpec ps.vars).proj env)) := hwf.1 env trivial
      apply EFG.WFTree.chance
      · -- branches ≠ []
        simp only [ne_eq, List.map_eq_nil_iff]
        intro h
        simp only [IsProb, WDist.mass, h, List.map_nil, List.sum_nil] at hprob
        exact absurd hprob (by norm_num)
      · -- (branches.map Prod.snd).sum = 1
        simp only [List.map_map]
        exact hprob
      · -- ∀ bt ∈ branches, WFTree bt.1
        intro bt hbt
        simp only [List.mem_map] at hbt
        obtain ⟨⟨v, w⟩, _, rfl⟩ := hbt
        exact ih u (v, env) hnd hne hwf.2
  | choose id who ps A k ih =>
      apply EFG.WFTree.decision
      · -- actions ≠ []
        simp only [ne_eq, List.map_eq_nil_iff]
        exact hne.1 _
      · -- ∀ t ∈ subtrees, WFTree t
        intro t ht
        simp only [List.mem_map] at ht
        obtain ⟨v, _, rfl⟩ := ht
        exact ih u (v, env) hnd.2 hne.2 hwf

end Proto
