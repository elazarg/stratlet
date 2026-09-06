/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosureInformation

/-! # Execution of every legal responder choice -/

noncomputable section

namespace VegasTests.OptionalDisclosure

open Vegas EventGraph GameTheory GameTheory.Protocol GameTheory.Math.Probability

def responseJoint (bit : Bool) := program.execution.singletonJoint 1 (some (responseAction bit))

theorem response_command (data : RunData) (state : program.State)
    (hstate : state.1 = cfg data 6)
    (command : {joint // program.execution.Legal state joint}) :
    command.1 = responseJoint (responseBit (command.1 1)) := by
  have hactive (who : TestPlayer) : program.execution.active state who ↔ who = 1 := by
    change Compiled.ActiveAt graph state.1 who ↔ _
    rw [hstate, active_iff]
    simp
  have hlocal := program.execution.legalOption_of_legal command.2 1
  obtain ⟨packet, hpacket⟩ := LegalOption.exists_eq_some_of_active (command.1 1) hlocal
    ((hactive 1).mpr rfl)
  rw [hpacket] at hlocal
  obtain ⟨bit, rfl⟩ := response_action_exhaustive data packet (hstate ▸ hlocal.2)
  rw [hpacket, responseBit_action]
  funext who
  by_cases heq : who = 1
  · subst who
    simpa [responseJoint] using hpacket
  · have hi := command.2.2 who
    cases hc : command.1 who with
    | none => simp [responseJoint, ExecutionProtocol.singletonJoint, heq]
    | some action =>
      rw [hc] at hi
      exact False.elim (heq ((hactive who).mp hi.1))

theorem response_step (data : RunData) (state : program.State)
    (hstate : state.1 = cfg data 6)
    (command : {joint // program.execution.Legal state joint}) :
    (program.execution.step state command).map Subtype.val =
      FinDist.pure (cfg { data with response := responseBit (command.1 1) } 7) := by
  classical
  change ((toExecutionProtocol graph program.graphWF program.guardLive).step state command).map
    Subtype.val = _
  rw [toExecutionProtocol_step_eq_pure_applyFrontier _ _ _ _ _
    (hstate ▸ no_internal data 6 (by simp)), FinDist.map_pure]
  have horder : [1] ∈ program.serializedSystem.schedules (publicObserve graph state.1) := by
    change [1].Nodup ∧ ∀ who : TestPlayer, who ∈ [1] ↔
      Compiled.ActiveAtView graph (publicObserve graph state.1) who
    refine ⟨by simp, ?_⟩
    intro who
    rw [Compiled.activeAtView_iff, hstate, active_iff]
    simp
  rw [← Compiled.applySerializedOrder_eq_applyFrontier graph program.graphWF program.guardLive
    state command.1 command.2 horder]
  rw [Compiled.applySerializedOrder_val program.graphWF command.1 state
    (fun who packet heq => by
      have hlocal := command.2.2 who
      rw [heq] at hlocal
      exact hlocal.2) (by simp : ([1] : List TestPlayer).Nodup)]
  rw [response_command data state hstate command, hstate]
  rfl

theorem final_reveal_step (data : RunData) (state : Config graph)
    (hstate : state = cfg data 7)
    (event : InternalEvent graph) (step : InternalStep graph state event) :
    stepInternal graph state step = FinDist.pure (cfg data 8) := by
  subst state
  cases step with
  | sample row dist hrow hsem ready env henv =>
    have heq : row = graph.nodeRow event.node :=
      Option.some.inj (hrow.symm.trans (graph.nodes_get?_nodeRow event.node))
    subst row
    rcases event with ⟨index⟩
    have hindex : index = node 7 := Fin.ext ((ready_iff _ _ _).mp ready)
    subst index
    cases hsem
  | reveal row source hrow hsem ready value hvalue =>
    have heq : row = graph.nodeRow event.node :=
      Option.some.inj (hrow.symm.trans (graph.nodes_get?_nodeRow event.node))
    subst row
    rcases event with ⟨index⟩
    have hindex : index = node 7 := Fin.ext ((ready_iff _ _ _).mp ready)
    subst index
    cases hsem
    have hv : data.response = value := by
      change some data.response = some value at hvalue
      exact Option.some.inj hvalue
    subst value
    rfl

theorem final_protocol_step (data : RunData) (state : program.State)
    (hstate : state.1 = cfg data 7)
    (command : {joint // program.execution.Legal state joint}) :
    (program.execution.step state command).map Subtype.val = FinDist.pure (cfg data 8) := by
  classical
  have hinternal : (readyInternalNodes graph state.1).Nonempty := by
    rw [hstate]
    refine ⟨node 7, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact (ready_internal_iff _ _ _).mpr ⟨rfl, by simp⟩
  have hkernel (event : InternalEvent graph) (step : InternalStep graph state.1 event) :
      (stepAvailable graph state (.internal event step)).map Subtype.val =
        FinDist.pure (cfg data 8) :=
    (map_val_stepAvailable graph state (.internal event step)).trans
      (final_reveal_step data state.1 hstate event step)
  change ((toExecutionProtocol graph program.graphWF program.guardLive).step state command).map
    Subtype.val = _
  rw [Compiled.toExecutionProtocol_step_eq_stepReadyInternal graph program.graphWF
    program.guardLive state command hinternal]
  unfold Compiled.stepReadyInternal
  exact hkernel _ _

theorem final_terminal_law
    (profile : ∀ who, program.information.BehavioralPolicy who)
    (history : program.execution.History) (data : RunData)
    (hstate : history.state.1 = cfg data 7) :
    (program.terminalStateLaw profile history).map Subtype.val = FinDist.pure (cfg data 8) := by
  have hterm : ¬ program.execution.terminal history.state := by
    change ¬ Terminal graph history.state.1
    rw [hstate, terminal_iff]
    decide
  rw [program.terminalStateLaw_step profile history hterm, FinDist.map_bind]
  calc
    _ = (program.information.behavioralJoint profile history.trace hterm).bind
        (fun _ => FinDist.pure (cfg data 8)) := by
      apply FinDist.bind_congr
      intro command _
      rw [FinDist.map_bindOnSupport]
      calc
        _ = (program.execution.step history.state command).bind
            (fun _ => FinDist.pure (cfg data 8)) := by
          apply FinDist.bindOnSupport_eq_bind_of_eq_on_support
          intro next hnext
          have hmem : next.1 ∈
              ((program.execution.step history.state command).map Subtype.val).support := by
            rw [FinDist.support_map]
            exact ⟨next, hnext, rfl⟩
          have hn : next.1 = cfg data 8 := by
            simpa only [final_protocol_step data history.state hstate command,
              FinDist.mem_support_pure] using hmem
          have ht : program.execution.terminal next := by
            change Terminal graph next.1
            rw [hn, terminal_iff]
          rw [program.terminalStateLaw_of_terminal profile _ ht, FinDist.map_pure]
          exact congrArg FinDist.pure hn
        _ = _ := FinDist.bind_const _ _
    _ = _ := FinDist.bind_const _ _

/-- Exact continuation law from every actual reply checkpoint, for all
behavioral profiles. The responder may use all of its legal runtime information. -/
theorem response_terminal_law
    (profile : ∀ who, program.information.BehavioralPolicy who)
    (history : program.execution.History) (data : RunData)
    (hstate : history.state.1 = cfg data 6) :
    (program.terminalStateLaw profile history).map Subtype.val =
      (responseLaw (profile 1) data.signal data.opening).map
        (fun bit => cfg { data with response := bit } 8) := by
  have hterm : ¬ program.execution.terminal history.state := by
    change ¬ Terminal graph history.state.1
    rw [hstate, terminal_iff]
    decide
  rw [program.terminalStateLaw_step profile history hterm, FinDist.map_bind]
  have hstep : ∀ command : {joint // program.execution.Legal history.state joint},
      ((program.execution.step history.state command).bindOnSupport fun _ realized =>
        program.terminalStateLaw profile (history.extend command.2 realized)).map Subtype.val =
      FinDist.pure (cfg { data with response := responseBit (command.1 1) } 8) := by
    intro command
    rw [FinDist.map_bindOnSupport]
    calc
      _ = (program.execution.step history.state command).bind
          (fun _ => FinDist.pure (cfg { data with response := responseBit (command.1 1) } 8)) := by
        apply FinDist.bindOnSupport_eq_bind_of_eq_on_support
        intro next hnext
        have hmem : next.1 ∈
            ((program.execution.step history.state command).map Subtype.val).support := by
          rw [FinDist.support_map]
          exact ⟨next, hnext, rfl⟩
        have hn : next.1 = cfg { data with response := responseBit (command.1 1) } 7 := by
          simpa only [response_step data history.state hstate command,
            FinDist.mem_support_pure] using hmem
        exact final_terminal_law profile (history.extend command.2 hnext) _ hn
      _ = _ := FinDist.bind_const _ _
  simp only [hstep]
  rw [← FinDist.map_eq_bind, InformationModel.behavioralJoint, FinDist.map_comp]
  calc
    _ = ((FinDist.pi fun who => profile who (program.information.infoOf who history.trace)).map
        (fun draws => draws 1)).map
          (fun choice => cfg { data with response := responseBit choice.1 } 8) := by
      rw [FinDist.map_comp]
      rfl
    _ = ((profile 1 (program.information.infoOf 1 history.trace)).map
        fun choice => responseBit choice.1).map
          (fun bit => cfg { data with response := bit } 8) := by
      rw [FinDist.map_apply_pi, FinDist.map_comp]
      rfl
    _ = _ := congrArg (fun law : FinDist Bool =>
      law.map (fun bit => cfg { data with response := bit } 8))
        (response_policy_factors (profile 1) history data hstate)

/-- info: 'VegasTests.OptionalDisclosure.response_terminal_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.response_terminal_law

end VegasTests.OptionalDisclosure
