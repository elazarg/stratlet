/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.SealedMessages
import Vegas.Game.SourceCorrespondence

/-! # A compiled nullable two-player source

This four-event fixture has two independent source commitments followed by
their public reveals. `none` is an ordinary source choice denoting decline.
The graph used below is produced by the canonical core compiler.
-/

noncomputable section

namespace VegasTests.PendingSource

open Vegas EventGraph

abbrev Player := Fin 2

def core : VegasCore Player simpleExpr [] :=
  .commit 0 0 (b := .option .bool)
    (Expr.nullableCommitGuard (Expr.constBool true))
    (.commit 1 1 (b := .option .bool)
      (Expr.nullableCommitGuard (Expr.constBool true))
      (.reveal 2 0 0 (.there .here)
        (.reveal 3 1 1 (.there .here) (.ret []))))

def source : WFProgram Player simpleExpr where
  core := {
    Γ := []
    prog := core
    env := VEnv.empty simpleExpr
    wctx := by simp
    fresh := by simp [core, FreshBindings, Fresh] }
  accounted := CommitmentAccounting.ofRevealComplete core
    (by simp [core, FreshBindings, Fresh]) [] (by simp) (by decide)
  legal := by
    unfold core
    constructor
    · intro env
      exact ⟨declineValue .bool, evalExpr_nullableCommitGuard_declineValue _ _⟩
    · constructor
      · intro env
        exact ⟨declineValue .bool, evalExpr_nullableCommitGuard_declineValue _ _⟩
      · trivial

abbrev compiled := ToEventGraph.compile source.core
abbrev graph := compiled.graph
abbrev machine := Machine.compile source

instance finiteDomains : FiniteDomains source where
  context := inferInstanceAs (FiniteVCtx ([] : VCtx Player simpleExpr))
  program := {
    proof := .commit inferInstance (.commit inferInstance
      (.reveal inferInstance (.reveal inferInstance .ret))) }

def node (index : Fin 4) : Fin graph.nodeCount := index

theorem nodeCount : graph.nodeCount = 4 := rfl

theorem node0_prereqs : graph.prereqs (node 0) = ∅ := by decide
theorem node1_prereqs : graph.prereqs (node 1) = ∅ := by decide
theorem node2_prereqs : graph.prereqs (node 2) = {node 0, node 1} := by decide
theorem node3_prereqs : graph.prereqs (node 3) = {node 0, node 1} := by decide

theorem node2_messagePrerequisites : graph.messagePrerequisites (node 2) = [0, 1] := by
  decide

theorem node3_messagePrerequisites : graph.messagePrerequisites (node 3) = [0, 1] := by
  decide

theorem node_ty (index : Fin 4) : (graph.nodeRow (node index)).ty = .option .bool := by
  fin_cases index <;> rfl

theorem node0_commit : ∃ guard,
    (graph.nodeRow (node 0)).sem = .commit 0 guard ∧
      guard.ty = .option .bool ∧ guard.choiceReads = ∅ ∧
      ∀ (value : simpleExpr.Val guard.ty) reads, guard.eval value reads = true := by
  refine ⟨_, rfl, rfl, rfl, ?_⟩
  intro value reads
  cases value <;> rfl

theorem node1_commit : ∃ guard,
    (graph.nodeRow (node 1)).sem = .commit 1 guard ∧
      guard.ty = .option .bool ∧ guard.choiceReads = ∅ ∧
      ∀ (value : simpleExpr.Val guard.ty) reads, guard.eval value reads = true := by
  refine ⟨_, rfl, rfl, rfl, ?_⟩
  intro value reads
  cases value <;> rfl

theorem node2_reveal : (graph.nodeRow (node 2)).sem = .reveal 0 := rfl
theorem node3_reveal : (graph.nodeRow (node 3)).sem = .reveal 1 := rfl

theorem node2_target : graph.nodeTarget (node 2) = 2 := rfl
theorem node3_target : graph.nodeTarget (node 3) = 3 := rfl
theorem node0_target : graph.nodeTarget (node 0) = 0 := rfl
theorem node1_target : graph.nodeTarget (node 1) = 1 := rfl

def action0 (value : Option Bool) : CommitAction graph 0 :=
  ⟨node 0, ⟨.option .bool, value⟩⟩

def action1 (value : Option Bool) : CommitAction graph 1 :=
  ⟨node 1, ⟨.option .bool, value⟩⟩

theorem action0_available (value : Option Bool) :
    CommitAvailable graph (Config.initial graph) 0 (action0 value) := by
  refine ⟨⟨graph.nodeRow (node 0), _, graph.nodes_get?_nodeRow _, rfl, ?_, value,
    rfl, ⟨fun ref href => False.elim ?_⟩, ?_, ?_⟩⟩
  · change Ready graph (Config.initial graph) (node 0)
    exact ⟨by simp [Config.initial], by rw [node0_prereqs]; exact Finset.empty_subset _⟩
  · change ref ∈ (∅ : Finset (FieldRef simpleExpr)) at href
    exact Finset.notMem_empty ref href
  · change ReadEnv.ofStore? _ ∅ = some _
    simp only [ReadEnv.ofStore?, Finset.notMem_empty, false_implies, implies_true,
      dite_true]
    congr 1
    apply ReadEnv.ext
    intro ref href
    simp at href
  · cases value <;> rfl

theorem action1_available (value : Option Bool) :
    CommitAvailable graph (Config.initial graph) 1 (action1 value) := by
  refine ⟨⟨graph.nodeRow (node 1), _, graph.nodes_get?_nodeRow _, rfl, ?_, value,
    rfl, ⟨fun ref href => False.elim ?_⟩, ?_, ?_⟩⟩
  · change Ready graph (Config.initial graph) (node 1)
    exact ⟨by simp [Config.initial], by rw [node1_prereqs]; exact Finset.empty_subset _⟩
  · change ref ∈ (∅ : Finset (FieldRef simpleExpr)) at href
    exact Finset.notMem_empty ref href
  · change ReadEnv.ofStore? _ ∅ = some _
    simp only [ReadEnv.ofStore?, Finset.notMem_empty, false_implies, implies_true,
      dite_true]
    congr 1
    apply ReadEnv.ext
    intro ref href
    simp at href
  · cases value <;> rfl

def after0 (value : Option Bool) : Config graph :=
  (Config.initial graph).completeNode (node 0) ⟨.option .bool, value⟩

def afterBoth (left right : Option Bool) : Config graph :=
  (after0 left).completeNode (node 1) ⟨.option .bool, right⟩

theorem action1_available_after0 (left right : Option Bool) :
    CommitAvailable graph (after0 left) 1 (action1 right) := by
  rcases action0_available left with ⟨step⟩
  exact CommitAvailable.persist_after_other_ready_write compiled.graphWF
    (action1_available right) (graph.nodes_get?_nodeRow (node 0)) step.ready
      ⟨.option .bool, left⟩ (by
        apply Fin.ne_of_val_ne
        norm_num [action1, node]
        change ¬ graph.nodeCount = 1
        rw [nodeCount]
        decide)

theorem action0_available_after1 (left right : Option Bool) :
    CommitAvailable graph
      ((Config.initial graph).completeNode (node 1) ⟨.option .bool, right⟩)
      0 (action0 left) := by
  rcases action1_available right with ⟨step⟩
  exact CommitAvailable.persist_after_other_ready_write compiled.graphWF
    (action0_available left) (graph.nodes_get?_nodeRow (node 1)) step.ready
      ⟨.option .bool, right⟩ (by
        apply Fin.ne_of_val_ne
        norm_num [action0, node]
        change ¬ graph.nodeCount = 1
        rw [nodeCount]
        decide)

theorem sealedFragment : SealedFragment graph (.option .bool) where
  graphWF := compiled.graphWF
  rowType node := by fin_cases node <;> rfl
  noSamples node dist := by
    fin_cases node <;> intro h <;> cases h
  commitType node who guard hsem := by
    fin_cases node <;> cases hsem <;> rfl
  commitReads node who guard hsem := by
    fin_cases node <;> cases hsem <;> rfl
  commitGuard node who guard hsem value env := by
    fin_cases node <;> cases hsem <;> cases value <;> rfl
  revealSource node sourceField hsem := by
    fin_cases node
    · cases hsem
    · cases hsem
    · cases hsem; exact ⟨node 0, 0, _, rfl, rfl⟩
    · cases hsem; exact ⟨node 1, 1, _, rfl, rfl⟩

end VegasTests.PendingSource
