/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.OptionalDisclosure

/-!
# The concrete disclosure graph's execution spine

These configuration facts describe the optional-disclosure source's compiled
graph. Its accounting certificate is supplied in `DisclosureAccounting`.
The original binding remains sealed; the graph execution facts alone do not
establish a public-runtime strategy correspondence.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure

open Vegas EventGraph GameTheory GameTheory.Protocol GameTheory.Math.Probability

abbrev graph := program.graph

/-- Semantic values of a complete run, before erasing administrative nodes. -/
structure RunData where
  secret : Bool
  signal : Bool
  opening : Option Bool
  response : Bool

def RunData.Valid (data : RunData) : Prop :=
  data.opening = none ∨ data.opening = some data.secret

def RunData.value (data : RunData) : Fin 8 → TypedValue simpleExpr
  | 0 => ⟨.bool, data.secret⟩
  | 1 => ⟨.bool, false⟩
  | 2 => ⟨.bool, false⟩
  | 3 => ⟨.bool, data.signal⟩
  | 4 => ⟨.option .bool, data.opening⟩
  | 5 => ⟨.option .bool, data.opening⟩
  | 6 => ⟨.bool, data.response⟩
  | 7 => ⟨.bool, data.response⟩

def cfg (data : RunData) (phase : Fin 9) : Config graph :=
  (Config.initial graph).completeNodes
    (((List.finRange 8).take phase.val).map fun index => (node index, data.value index))

theorem cfg_initial (data : RunData) : cfg data 0 = Config.initial graph := rfl

theorem cfg_succ (data : RunData) (phase : Fin 8) :
    cfg data phase.succ =
      (cfg data phase.castSucc).completeNode (node phase) (data.value phase) := by
  fin_cases phase <;> rfl

theorem ready_iff (data : RunData) (phase : Fin 9) (index : Fin graph.nodeCount) :
    Ready graph (cfg data phase) index ↔ index.val = phase.val := by
  fin_cases phase <;> simp only [cfg, Config.completeNodes,
    show List.finRange 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl,
    List.take, List.map, List.foldl, Config.completeNode, Ready] <;>
    fin_cases index <;> decide

theorem terminal_iff (data : RunData) (phase : Fin 9) :
    Terminal graph (cfg data phase) ↔ phase = 8 := by
  fin_cases phase <;> simp only [cfg, Config.completeNodes,
    show List.finRange 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl,
    List.take, List.map, List.foldl, Config.completeNode, Terminal] <;> decide

theorem ready_commit_iff (data : RunData) (phase : Fin 9)
    (who : TestPlayer) (index : Fin graph.nodeCount) :
    ReadyCommitNode graph (cfg data phase) who index ↔
      index.val = phase.val ∧
        ((who = 0 ∧ (phase = 0 ∨ phase = 1 ∨ phase = 4)) ∨ (who = 1 ∧ phase = 6)) := by
  constructor
  · rintro ⟨row, guard, hrow, hsem, hready⟩
    have heq : row = graph.nodeRow index :=
      Option.some.inj (hrow.symm.trans (graph.nodes_get?_nodeRow index))
    subst row
    have hindex := (ready_iff data phase index).mp hready
    refine ⟨hindex, ?_⟩
    fin_cases phase <;> fin_cases index <;> norm_num at hindex
    all_goals cases hsem <;> simp
  · rintro ⟨hindex, hphase⟩
    rcases hphase with ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl⟩
    all_goals
      fin_cases index <;> norm_num at hindex
      exact ⟨_, _, rfl, rfl, (ready_iff _ _ _).mpr rfl⟩

theorem ready_internal_iff (data : RunData) (phase : Fin 9)
    (index : Fin graph.nodeCount) :
    ReadyInternalNode graph (cfg data phase) index ↔
      index.val = phase.val ∧ (phase = 2 ∨ phase = 3 ∨ phase = 5 ∨ phase = 7) := by
  constructor
  · rintro ⟨row, hrow, hsem, hready⟩
    have heq : row = graph.nodeRow index :=
      Option.some.inj (hrow.symm.trans (graph.nodes_get?_nodeRow index))
    subst row
    have hindex := (ready_iff data phase index).mp hready
    refine ⟨hindex, ?_⟩
    fin_cases phase <;> fin_cases index <;> norm_num at hindex
    all_goals first | contradiction | simp
  · rintro ⟨hindex, rfl | rfl | rfl | rfl⟩
    all_goals
      fin_cases index <;> norm_num at hindex
      exact ⟨_, rfl, trivial, (ready_iff _ _ _).mpr rfl⟩

theorem no_internal (data : RunData) (phase : Fin 9)
    (hphase : phase = 0 ∨ phase = 1 ∨ phase = 4 ∨ phase = 6) :
    readyInternalNodes graph (cfg data phase) = ∅ := by
  classical
  ext index
  simp only [readyInternalNodes, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.notMem_empty, iff_false, ready_internal_iff]
  rcases hphase with rfl | rfl | rfl | rfl <;> simp

theorem active_iff (data : RunData) (phase : Fin 9) (who : TestPlayer) :
    EventGraph.ActiveAt graph (cfg data phase) who ↔
      (who = 0 ∧ (phase = 0 ∨ phase = 1 ∨ phase = 4)) ∨ (who = 1 ∧ phase = 6) := by
  classical
  constructor
  · rintro ⟨_, _, hactive⟩
    obtain ⟨index, hindex⟩ := (Finset.mem_filter.mp hactive).2
    exact ((ready_commit_iff _ _ _ _).mp (Finset.mem_filter.mp hindex).2).2
  · intro hphase
    have hsmall : phase.val < 8 := by
      rcases hphase with ⟨_, rfl | rfl | rfl⟩ | ⟨_, rfl⟩ <;> decide
    have hstrategic : phase = 0 ∨ phase = 1 ∨ phase = 4 ∨ phase = 6 := by
      tauto
    refine ⟨?_, no_internal data phase hstrategic, Finset.mem_filter.mpr ?_⟩
    · rw [terminal_iff]
      intro heq
      subst phase
      contradiction
    · refine ⟨Finset.mem_univ _, ⟨phase.val, hsmall⟩, Finset.mem_filter.mpr ?_⟩
      exact ⟨Finset.mem_univ _, (ready_commit_iff _ _ _ _).mpr ⟨rfl, hphase⟩⟩

/-- info: 'VegasTests.OptionalDisclosure.ready_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.ready_iff

/-- info: 'VegasTests.OptionalDisclosure.terminal_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.terminal_iff

/-- info: 'VegasTests.OptionalDisclosure.active_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.active_iff

end VegasTests.OptionalDisclosure
