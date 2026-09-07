/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.QuittingSource
import VegasTests.ObservedAbort
import Vegas.Runtime.Harmonic

/-! # Completion laws of the compiled staged source -/

noncomputable section

namespace VegasTests.QuittingSource

open Vegas EventGraph GameTheory GameTheory.Protocol GameTheory.Math.Probability

abbrev graph := program.graph

def readBit (cfg : Config graph) (field : Nat) : Bool :=
  (Store.getAs cfg.store field .bool).getD false

def decode (cfg : Config graph) : ObservedAbort.Outcome :=
  ((readBit cfg 0, readBit cfg 1), readBit cfg 4, readBit cfg 7)

def coinLaw (cfg : Config graph) (index : Fin 10) : FinDist Bool :=
  if node index ∈ cfg.done then FinDist.pure (readBit cfg index)
  else ObservedAbort.fair

/-- Conditional completion law: retain sampled coins and draw only those
whose graph events have not executed. It ignores administrative markers. -/
def completionLaw (cfg : Config graph) : FinDist ObservedAbort.Outcome :=
  (coinLaw cfg 4).bind fun signal =>
    (coinLaw cfg 7).map fun future =>
      ((readBit cfg 0, readBit cfg 1), signal, future)

theorem nodeTarget (index : Nat) : graph.nodeTarget index = index := by
  change 0 + index = index
  omega

@[simp] theorem readBit_write_other (cfg : Config graph) (index : Fin 10)
    (value : TypedValue simpleExpr) (field : Nat) (hne : field ≠ index.val) :
    readBit (cfg.completeNode (node index) value) field = readBit cfg field := by
  simp [readBit, Config.completeNode, Store.getAs, Store.set, nodeTarget, node, hne]

@[simp] theorem readBit_write (cfg : Config graph) (index : Fin 10) (bit : Bool) :
    readBit (cfg.completeNode (node index) ⟨.bool, bit⟩) index = bit := by
  simp [readBit, Config.completeNode, Store.getAs, Store.set, nodeTarget, node, TypedValue.as?]

theorem coinLaw_write_other (cfg : Config graph) (index query : Fin 10)
    (value : TypedValue simpleExpr) (hne : query ≠ index) :
    coinLaw (cfg.completeNode (node index) value) query = coinLaw cfg query := by
  have hv : (query : Nat) ≠ index.val := fun heq => hne (Fin.ext heq)
  simp [coinLaw, Config.completeNode, node, hne, readBit, Store.getAs, Store.set,
    nodeTarget, hv]

theorem completionLaw_write_other (cfg : Config graph) (index : Fin 10)
    (value : TypedValue simpleExpr)
    (h0 : index ≠ 0) (h1 : index ≠ 1) (h4 : index ≠ 4) (h7 : index ≠ 7) :
    completionLaw (cfg.completeNode (node index) value) = completionLaw cfg := by
  unfold completionLaw
  rw [coinLaw_write_other _ _ _ _ (Ne.symm h4),
    coinLaw_write_other _ _ _ _ (Ne.symm h7)]
  have hv0 : 0 ≠ index.val := fun heq => h0 (Fin.ext heq.symm)
  have hv1 : 1 ≠ index.val := fun heq => h1 (Fin.ext heq.symm)
  simp [hv0, hv1]

theorem completionLaw_sample_signal (cfg : Config graph) (hnot : node 4 ∉ cfg.done) :
    (ObservedAbort.fair.map fun bit => cfg.completeNode (node 4) ⟨.bool, bit⟩).bind
      completionLaw = completionLaw cfg := by
  rw [FinDist.bind_map]
  simp only [completionLaw, coinLaw_write_other _ 4 7 _ (by decide),
    readBit_write_other _ 4 _ 0 (by decide), readBit_write_other _ 4 _ 1 (by decide)]
  have hcoin : ∀ bit, coinLaw (cfg.completeNode (node 4) ⟨.bool, bit⟩) 4 =
      FinDist.pure bit := by
    intro bit
    simp [coinLaw, Config.completeNode, readBit, node, Store.getAs, Store.set,
      nodeTarget, nodeCount, TypedValue.as?]
  simp only [hcoin, FinDist.pure_bind]
  simp only [coinLaw, if_neg hnot]

theorem completionLaw_sample_future (cfg : Config graph) (hnot : node 7 ∉ cfg.done) :
    (ObservedAbort.fair.map fun bit => cfg.completeNode (node 7) ⟨.bool, bit⟩).bind
      completionLaw = completionLaw cfg := by
  rw [FinDist.bind_map]
  simp only [completionLaw, coinLaw_write_other _ 7 4 _ (by decide),
    readBit_write_other _ 7 _ 0 (by decide), readBit_write_other _ 7 _ 1 (by decide)]
  have hcoin : ∀ bit, coinLaw (cfg.completeNode (node 7) ⟨.bool, bit⟩) 7 =
      FinDist.pure bit := by
    intro bit
    simp [coinLaw, Config.completeNode, readBit, node, Store.getAs, Store.set,
      nodeTarget, nodeCount, TypedValue.as?]
  simp only [hcoin, FinDist.map_pure]
  rw [FinDist.bind_comm]
  simp only [coinLaw, if_neg hnot, FinDist.map_eq_bind]

theorem completionLaw_terminal (cfg : Config graph) (hterminal : Terminal graph cfg) :
    completionLaw cfg = FinDist.pure (decode cfg) := by
  simp [completionLaw, coinLaw, hterminal (node 4), hterminal (node 7), decode]

theorem fairCoin_denote : fairCoin.denote = ObservedAbort.fair := by
  apply FinDist.ext_of_prob
  intro bit
  cases bit <;>
    simp [fairCoin, RationalLaw.prob_denote, Fin.sum_univ_two,
      FinDist.prob_uniformOfFintype]

theorem completionLaw_internal (cfg : Config graph) (event : InternalEvent graph)
    (step : InternalStep graph cfg event) :
    (stepInternal graph cfg step).bind completionLaw = completionLaw cfg := by
  cases step with
  | sample row dist hrow hsem ready env henv =>
      have heq : row = graph.nodeRow event.node :=
        Option.some.inj (hrow.symm.trans (graph.nodes_get?_nodeRow event.node))
      subst row
      rcases event with ⟨index⟩
      fin_cases index <;> cases hsem
      all_goals
        simp only [stepInternal, EventDist.eval, EventDist.evalLaw,
          ToEventGraph.eventDistOf, simpleExpr, evalLawDistExprDeps, ite_self,
          fairCoin_denote]
        first
        | exact completionLaw_sample_signal cfg ready.1
        | exact completionLaw_sample_future cfg ready.1
  | reveal row source hrow hsem ready value hvalue =>
      have heq : row = graph.nodeRow event.node :=
        Option.some.inj (hrow.symm.trans (graph.nodes_get?_nodeRow event.node))
      subst row
      rcases event with ⟨index⟩
      fin_cases index <;> cases hsem
      all_goals
        exact (FinDist.pure_bind _ _).trans
          (completionLaw_write_other cfg _ _ (by decide) (by decide) (by decide) (by decide))

def ChoicesFixed (cfg : Config graph) : Prop := node 0 ∈ cfg.done ∧ node 1 ∈ cfg.done

theorem commit_node (cfg : Config graph) (who : TestPlayer)
    (action : CommitAction graph who) (h : CommitAvailable graph cfg who action)
    (hfixed : ChoicesFixed cfg) : action.node = node 2 ∨ action.node = node 5 := by
  obtain ⟨step⟩ := h
  have heq : step.row = graph.nodeRow action.node :=
    Option.some.inj (step.row_get.symm.trans (graph.nodes_get?_nodeRow action.node))
  have hsem := heq ▸ step.sem_eq
  have hready := step.ready
  rcases action with ⟨index, value⟩
  fin_cases index
  · exact False.elim (hready.1 hfixed.1)
  · exact False.elim (hready.1 hfixed.2)
  · exact Or.inl rfl
  · cases hsem
  · cases hsem
  · exact Or.inr rfl
  · cases hsem
  · cases hsem
  · cases hsem
  · cases hsem

theorem completionLaw_frontier (state : program.State)
    (joint : ∀ who, Option (FrontierAction graph who))
    (hlegal : ∀ who action, joint who = some action →
      FrontierAction.Available graph state.1 who action)
    (hfixed : ChoicesFixed state.1) :
    completionLaw (applyFrontier graph program.graphWF state joint).1 =
      completionLaw state.1 := by
  rw [applyFrontier_val_of_available graph program.graphWF state joint hlegal]
  have hwrites : ∀ entry ∈ roundWrites joint (Finset.univ.toList : List TestPlayer),
      entry.1 = node 2 ∨ entry.1 = node 5 := by
    intro entry hentry
    obtain ⟨who, havailable⟩ := commitAvailable_of_mem_roundWrites hlegal hentry
    exact commit_node state.1 who _ havailable hfixed
  generalize roundWrites joint (Finset.univ.toList : List TestPlayer) = writes at *
  suffices ∀ cfg : Config graph, completionLaw (cfg.completeNodes writes) =
      completionLaw cfg from this state.1
  induction writes with
  | nil => intro cfg; rfl
  | cons entry rest ih =>
      intro cfg
      rw [Config.completeNodes_cons, ih (fun e he => hwrites e (List.mem_cons_of_mem _ he))]
      rcases hwrites entry (List.mem_cons_self) with h | h <;> rw [h] <;>
        exact completionLaw_write_other cfg _ _ (by decide) (by decide) (by decide) (by decide)

theorem completionLaw_step (state : program.State)
    (command : {joint // program.execution.Legal state joint})
    (hfixed : ChoicesFixed state.1) :
    (program.execution.step state command).bind (fun next => completionLaw next.1) =
      completionLaw state.1 := by
  classical
  change ((toExecutionProtocol graph program.graphWF program.guardLive).step state command).bind
    (fun next => completionLaw next.1) = _
  by_cases hinternal : (readyInternalNodes graph state.1).Nonempty
  · have hkernel (event : InternalEvent graph) (step : InternalStep graph state.1 event) :
        (stepAvailable graph state (.internal event step)).bind
          (fun next => completionLaw next.1) = completionLaw state.1 := by
      calc
        _ = ((stepAvailable graph state (.internal event step)).map Subtype.val).bind
            completionLaw := (FinDist.bind_map _ _ _).symm
        _ = (stepAvailableEvent graph state.1 (.internal event step)).bind completionLaw :=
          congrArg (fun law => law.bind completionLaw)
            (map_val_stepAvailable graph state (.internal event step))
        _ = completionLaw state.1 := completionLaw_internal state.1 event step
    rw [EventGraph.toExecutionProtocol_step_eq_stepReadyInternal graph program.graphWF
      program.guardLive state command hinternal]
    unfold EventGraph.stepReadyInternal
    exact hkernel _ _
  · rw [toExecutionProtocol_step_eq_pure_applyFrontier graph program.graphWF program.guardLive
      state command (Finset.not_nonempty_iff_eq_empty.mp hinternal), FinDist.pure_bind]
    apply completionLaw_frontier state command.1 _ hfixed
    intro who action haction
    have hlocal := command.2.2 who
    rw [haction] at hlocal
    exact hlocal.2

/-- From any reachable history after the two initial choices, arbitrary
behavioral continuation policies induce precisely the remaining-coin law. -/
theorem terminal_decode_law
    (profile : ∀ who, program.information.BehavioralPolicy who)
    (history : program.execution.History) (hfixed : ChoicesFixed history.state.1) :
    (program.terminalStateLaw profile history).map (fun state => decode state.1) =
      completionLaw history.state.1 := by
  have hrun := Runtime.runBehavioralFrom_harmonic program.information
    (fun state => ChoicesFixed state.1) (fun state => completionLaw state.1)
    (fun state command hfixed next hnext =>
      let hext := program.executionStep_extends state command hnext
      ⟨hext.done hfixed.1, hext.done hfixed.2⟩)
    completionLaw_step profile graph.nodeCount history hfixed
  rw [Machine.Program.terminalStateLaw, FinDist.map_comp, FinDist.map_eq_bind]
  calc
    _ = (program.information.runBehavioralFrom profile graph.nodeCount history).bind
        (fun next => completionLaw next.state.1) := by
      apply FinDist.bind_congr
      intro next hnext
      exact (completionLaw_terminal next.state.1
        (Scheduled.runBehavioralFrom_terminal_of_bound program.information profile
          program.boundedHorizon history next hnext)).symm
    _ = completionLaw history.state.1 := hrun

end VegasTests.QuittingSource
