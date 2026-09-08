/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.PersistentDisclosure

/-! # The forced second disclosure choice

This file proves that the existing graph information model gives owner zero a
singleton administrative menu at the second checkpoint after a public refusal.
It does not identify that administrative move with runtime polling or repair
the source program's failure of `RevealComplete`.
-/

noncomputable section

namespace VegasTests.PersistentDisclosure

open Vegas EventGraph GameTheory GameTheory.Protocol GameTheory.Math.Probability

def program : Machine.Program Player simpleExpr :=
  Machine.ofCompiled compiled (ToEventGraph.compile_guardLive source legal)

structure RefusalData where
  secret : Bool
  signal : Bool
  response : Bool

def RefusalData.value (data : RefusalData) : Fin 8 → TypedValue simpleExpr
  | 0 => ⟨.bool, data.secret⟩
  | 1 => ⟨.bool, false⟩
  | 2 => ⟨.bool, false⟩
  | 3 => ⟨.bool, data.signal⟩
  | 4 => ⟨.option .bool, none⟩
  | 5 => ⟨.option .bool, none⟩
  | 6 => ⟨.bool, data.response⟩
  | 7 => ⟨.bool, data.response⟩

def refusalConfig (data : RefusalData) : Config graph :=
  (Config.initial graph).completeNodes
    [(node 0, data.value 0), (node 1, data.value 1),
     (node 2, data.value 2), (node 3, data.value 3),
     (node 4, data.value 4), (node 5, data.value 5),
     (node 6, data.value 6), (node 7, data.value 7)]

@[simp] theorem node_target (index : Fin 10) : graph.nodeTarget (node index) = index := by
  fin_cases index <;> rfl

theorem refusal_ready_iff (data : RefusalData) (index : Fin graph.nodeCount) :
    Ready graph (refusalConfig data) index ↔ index = node 8 := by
  rcases data with ⟨secret, signal, response⟩
  cases secret <;> cases signal <;> cases response <;>
    fin_cases index <;> decide

theorem refusal_field_five (data : RefusalData) :
    (refusalConfig data).store.getAs 5 (.option .bool) = some none := by
  simp [refusalConfig, Config.completeNodes, Config.completeNode, RefusalData.value,
    Config.initial, Store.getAs, TypedValue.as?]

theorem refusal_ready_commit_iff (data : RefusalData)
    (who : Player) (index : Fin graph.nodeCount) :
    ReadyCommitNode graph (refusalConfig data) who index ↔
      who = 0 ∧ index = node 8 := by
  constructor
  · rintro ⟨row, guard, hrow, hsem, hready⟩
    have heq : row = graph.nodeRow index :=
      Option.some.inj (hrow.symm.trans (graph.nodes_get?_nodeRow index))
    subst row
    have hindex := (refusal_ready_iff data index).mp hready
    subst index
    exact ⟨(NodeSem.commit.inj hsem).1.symm, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨_, _, rfl, rfl, (refusal_ready_iff data _).mpr rfl⟩

def refusalAction : FrontierAction graph (0 : Player) where
  value? index := if hindex : index = node 8 then
    some (cast (congrArg (fun i => simpleExpr.Val (graph.nodeRow i).ty) hindex.symm)
      (none : Option Bool)) else none

private theorem refusal_value_forced (data : RefusalData)
    (value : simpleExpr.Val (graph.nodeRow (node 8)).ty)
    (h : CommitAvailable graph (refusalConfig data) 0
      ⟨node 8, graph.nodeTypedValue (node 8) value⟩) :
    value = none := by
  obtain ⟨row, guard, hrow, hsem, _, chosen, hchosen, env, henv, hguard⟩ := h
  have heq : row = graph.nodeRow (node 8) :=
    Option.some.inj (hrow.symm.trans (graph.nodes_get?_nodeRow (node 8)))
  subst row
  cases hsem
  have hc : value = chosen := Option.some.inj hchosen
  subst chosen
  have hread := ReadEnv.ofStore?_read henv
    (ref := { field := 5, ty := .option .bool }) (by decide)
  have hnone : env.read { field := 5, ty := .option .bool } (by decide) = none := by
    rw [refusal_field_five] at hread
    exact (Option.some.inj hread).symm
  change (if (env.read { field := 5, ty := .option .bool } (by decide)).isNone
    then value.isNone else _) = true at hguard
  rw [hnone] at hguard
  cases value with
  | none => rfl
  | some value => simp at hguard

theorem refusal_action_exhaustive (data : RefusalData)
    (packet : FrontierAction graph (0 : Player))
    (havailable : FrontierAction.Available graph (refusalConfig data) 0 packet) :
    packet = refusalAction := by
  have hready : ReadyCommitNode graph (refusalConfig data) 0 (node 8) :=
    (refusal_ready_commit_iff data 0 (node 8)).mpr ⟨rfl, rfl⟩
  have hslot := havailable (node 8)
  rw [dif_pos hready] at hslot
  obtain ⟨value, hvalue, hcommit⟩ := hslot
  have hforced := refusal_value_forced data value hcommit
  subst value
  have hvalues : packet.value? = refusalAction.value? := by
    funext index
    by_cases heq : index = node 8
    · subst index
      simp only [refusalAction, dite_true]
      change packet.value? (node 8) = some (none : Option Bool)
      exact hvalue
    · have hnot : ¬ReadyCommitNode graph (refusalConfig data) 0 index := by
        intro h
        exact heq ((refusal_ready_commit_iff data 0 index).mp h).2
      have hnone := havailable index
      rw [dif_neg hnot] at hnone
      simpa [refusalAction, heq] using hnone
  cases packet
  exact congrArg FrontierAction.mk hvalues

theorem refusal_active (data : RefusalData) :
    EventGraph.ActiveAt graph (refusalConfig data) 0 := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro hterminal
    have hready := (refusal_ready_iff data (node 8)).mpr rfl
    exact hready.1 (hterminal (node 8))
  · apply Finset.eq_empty_iff_forall_notMem.mpr
    intro index hindex
    have hinternal : ReadyInternalNode graph (refusalConfig data) index :=
      (Finset.mem_filter.mp hindex).2
    obtain ⟨row, hrow, hkind, hready⟩ := hinternal
    have heq := (refusal_ready_iff data index).mp hready
    subst index
    have hroweq : row = graph.nodeRow (node 8) :=
      Option.some.inj (hrow.symm.trans (graph.nodes_get?_nodeRow (node 8)))
    subst row
    exact hkind
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ⟨node 8, Finset.mem_filter.mpr ?_⟩⟩
    exact ⟨Finset.mem_univ _, (refusal_ready_commit_iff data 0 _).mpr ⟨rfl, rfl⟩⟩

theorem second_choice_subsingleton (history : program.execution.History)
    (data : RefusalData) (hstate : history.state.1 = refusalConfig data) :
    Subsingleton (program.information.Choice 0
      (program.information.infoOf 0 history.trace)) := by
  apply program.information.subsingleton_choice_of_menu_subsingleton
  intro first hfirst second hsecond
  have hfirst' := (program.information.menu_adequate 0 history.trace first).mp hfirst
  have hsecond' := (program.information.menu_adequate 0 history.trace second).mp hsecond
  have hactive : program.execution.active history.state 0 := by
    change EventGraph.ActiveAt graph history.state.1 0
    rw [hstate]
    exact refusal_active data
  obtain ⟨firstAction, hfirstAction⟩ :=
    LegalOption.exists_eq_some_of_active first hfirst' hactive
  obtain ⟨secondAction, hsecondAction⟩ :=
    LegalOption.exists_eq_some_of_active second hsecond' hactive
  rw [hfirstAction] at hfirst'
  rw [hsecondAction] at hsecond'
  have hf := refusal_action_exhaustive data firstAction (hstate ▸ hfirst'.2)
  have hs := refusal_action_exhaustive data secondAction (hstate ▸ hsecond'.2)
  simp [hfirstAction, hsecondAction, hf, hs]

theorem policy_second_law (history : program.execution.History) (data : RefusalData)
    (hstate : history.state.1 = refusalConfig data)
    (policy : program.information.BehavioralPolicy 0) :
    policy (program.information.infoOf 0 history.trace) =
      FinDist.pure (Classical.choice (choice_nonempty graph program.graphWF program.guardLive 0
        (program.information.infoOf 0 history.trace))) := by
  let _ : Subsingleton (program.information.Choice 0
      (program.information.infoOf 0 history.trace)) :=
    second_choice_subsingleton history data hstate
  exact FinDist.eq_pure_of_subsingleton _ _

/-- info: 'VegasTests.PersistentDisclosure.second_choice_subsingleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms second_choice_subsingleton

/-- info: 'VegasTests.PersistentDisclosure.policy_second_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms policy_second_law

end VegasTests.PersistentDisclosure
