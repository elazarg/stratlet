/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.Execution
import Mathlib.Data.List.Sort

/-! # Legal topological orders and adjacent independent swaps

The order relation is structural: it inspects completed nodes and prerequisites,
never stored values. Any two legal orders of the same nodes are connected by
swaps of nodes that are simultaneously ready.
-/

namespace Vegas.EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- Each listed node is unfinished and has all prerequisites completed when
its turn arrives. Lists may describe a proper prefix of graph execution. -/
def Graph.ReadyOrder (G : Graph Player L) :
    Finset (Fin G.nodeCount) → List (Fin G.nodeCount) → Prop
  | _, [] => True
  | done, node :: rest => node ∉ done ∧ G.prereqs node ⊆ done ∧
      G.ReadyOrder (insert node done) rest

namespace Graph.ReadyOrder

variable {G : Graph Player L}

/-- Completing an already-ready node early leaves a legal order after removing
that node's original occurrence, if any. -/
theorem insert_erase {done : Finset (Fin G.nodeCount)}
    {order : List (Fin G.nodeCount)} (horder : G.ReadyOrder done order)
    (node : Fin G.nodeCount) (hnot : node ∉ done) (hdeps : G.prereqs node ⊆ done) :
    G.ReadyOrder (insert node done) (order.erase node) := by
  induction order generalizing done with
  | nil => trivial
  | cons head tail ih =>
      rcases horder with ⟨hhead, hheadDeps, htail⟩
      by_cases heq : head = node
      · subst head
        simpa using htail
      · rw [List.erase_cons_tail (by simpa using heq)]
        refine ⟨by simp [heq, hhead],
          hheadDeps.trans (Finset.subset_insert node done), ?_⟩
        have hnodeAfter : node ∉ insert head done := by simp [Ne.symm heq, hnot]
        have htail' := ih htail hnodeAfter
          (hdeps.trans (Finset.subset_insert head done))
        simpa only [Finset.insert_comm] using htail'

/-- A finite chain of adjacent swaps of distinct simultaneously ready nodes.
Prefix closure records the exact completed-node set at each swap. -/
inductive Equivalent (G : Graph Player L) :
    Finset (Fin G.nodeCount) → List (Fin G.nodeCount) → List (Fin G.nodeCount) → Prop
  | refl (done order) : Equivalent G done order order
  | cons {done first second} (node : Fin G.nodeCount)
      (hnot : node ∉ done) (hdeps : G.prereqs node ⊆ done)
      (tail : Equivalent G (insert node done) first second) :
      Equivalent G done (node :: first) (node :: second)
  | swap {done} (first second : Fin G.nodeCount) (rest : List (Fin G.nodeCount))
      (hne : first ≠ second)
      (hfirst : first ∉ done) (hfirstDeps : G.prereqs first ⊆ done)
      (hsecond : second ∉ done) (hsecondDeps : G.prereqs second ⊆ done) :
      Equivalent G done (first :: second :: rest) (second :: first :: rest)
  | trans {done first middle last}
      (left : Equivalent G done first middle) (right : Equivalent G done middle last) :
      Equivalent G done first last

theorem Equivalent.symm {done : Finset (Fin G.nodeCount)}
    {first second : List (Fin G.nodeCount)} (h : Equivalent G done first second) :
    Equivalent G done second first := by
  induction h with
  | refl => exact .refl _ _
  | cons node hnot hdeps _ ih => exact .cons node hnot hdeps ih
  | swap first second rest hne hf hfd hs hsd =>
      exact .swap second first rest hne.symm hs hsd hf hfd
  | trans _ _ ih₁ ih₂ => exact .trans ih₂ ih₁

/-- A node ready at the initial checkpoint can be moved to the front of any
legal order containing it, through legal adjacent independent swaps. -/
theorem move_to_front {done : Finset (Fin G.nodeCount)}
    {order : List (Fin G.nodeCount)} (horder : G.ReadyOrder done order)
    (node : Fin G.nodeCount) (hnot : node ∉ done) (hdeps : G.prereqs node ⊆ done)
    (hmem : node ∈ order) : Equivalent G done order (node :: order.erase node) := by
  induction order generalizing done with
  | nil => cases hmem
  | cons head tail ih =>
      rcases horder with ⟨hhead, hheadDeps, htail⟩
      by_cases heq : head = node
      · subst head
        simpa using Equivalent.refl (G := G) done (node :: tail)
      · have hmemTail : node ∈ tail := (List.mem_cons.mp hmem).resolve_left (Ne.symm heq)
        have hnodeAfter : node ∉ insert head done := by simp [Ne.symm heq, hnot]
        have htailEq := ih htail hnodeAfter
          (hdeps.trans (Finset.subset_insert head done)) hmemTail
        rw [List.erase_cons_tail (by simpa using heq)]
        exact .trans (.cons head hhead hheadDeps htailEq)
          (.swap head node (tail.erase node) heq hhead hheadDeps hnot hdeps)

/-- All legal topological orders of the same nodes are connected by adjacent
swaps of simultaneously ready nodes. No probabilistic or policy hypothesis is
needed for this combinatorial fact. -/
theorem equivalent_of_perm {done : Finset (Fin G.nodeCount)}
    {first second : List (Fin G.nodeCount)}
    (hfirst : G.ReadyOrder done first) (hsecond : G.ReadyOrder done second)
    (hperm : first.Perm second) : Equivalent G done first second := by
  induction first generalizing done second with
  | nil =>
      have heq : second = [] := List.perm_nil.mp hperm.symm
      subst second
      exact .refl _ _
  | cons node tail ih =>
      rcases hfirst with ⟨hnot, hdeps, htail⟩
      have hmem : node ∈ second := hperm.mem_iff.mp List.mem_cons_self
      have hfront := move_to_front hsecond node hnot hdeps hmem
      have hrest := insert_erase hsecond node hnot hdeps
      have htailPerm : tail.Perm (second.erase node) :=
        List.Perm.cons_inv (hperm.trans (List.perm_cons_erase hmem))
      exact .trans (.cons node hnot hdeps (ih htail hrest htailPerm)) hfront.symm

/-- Increasing node ids form a legal order when the initial completed set is
exactly the omitted nodes: graph prerequisites always have smaller ids. -/
theorem of_sorted {done : Finset (Fin G.nodeCount)}
    {order : List (Fin G.nodeCount)} (hsorted : order.Pairwise (· < ·))
    (hcover : ∀ node, node ∈ done ↔ node ∉ order) : G.ReadyOrder done order := by
  induction order generalizing done with
  | nil => trivial
  | cons head tail ih =>
      obtain ⟨hheadLt, htailSorted⟩ := List.pairwise_cons.mp hsorted
      have hheadNot : head ∉ done := by
        intro hmem
        exact (hcover head).mp hmem List.mem_cons_self
      have hdeps : G.prereqs head ⊆ done := by
        intro prior hprior
        by_contra hnot
        have hmem : prior ∈ head :: tail := by
          by_contra hmissing
          exact hnot ((hcover prior).mpr hmissing)
        rcases List.mem_cons.mp hmem with heq | htail
        · exact (ne_of_lt (G.prereq_lt hprior)) (congrArg Fin.val heq)
        · exact (not_lt_of_ge (le_of_lt (G.prereq_lt hprior))) (hheadLt prior htail)
      refine ⟨hheadNot, hdeps, ih htailSorted ?_⟩
      intro node
      by_cases heq : node = head
      · subst node
        have hnotTail : head ∉ tail := fun hmem => lt_irrefl head (hheadLt head hmem)
        simp [hnotTail]
      · simp [heq, hcover node]

end Graph.ReadyOrder

/-- The compiler's increasing node enumeration is a legal topological order. -/
theorem Graph.nodeOrder_readyOrder (G : Graph Player L) :
    G.ReadyOrder ∅ G.nodeOrder := by
  apply Graph.ReadyOrder.of_sorted
  · simpa only [Graph.nodeOrder, List.sortedLT_iff_pairwise] using
      (List.sortedLT_finRange G.nodeCount)
  · intro node
    simp

end Vegas.EventGraph
