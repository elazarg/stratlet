/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosureSites

/-! # Reachability of canonical disclosure prefixes

Every valid binding, signal, optional opening, and response determines reachable
graph configurations at all nine phases. The witnesses use the actual graph
protocol, including its guarded menus and supported public chance outcomes.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure

open Vegas EventGraph GameTheory.Protocol GameTheory.Math.Probability

private theorem reachable_of_map_pure (state : program.State)
    (command : {joint // program.execution.Legal state joint}) (target : Config graph)
    (hlaw : (program.execution.step state command).map Subtype.val = FinDist.pure target) :
    Reachable graph target := by
  obtain ⟨next, hnext⟩ := (program.execution.step state command).support_nonempty
  have hmapped : next.1 ∈
      ((program.execution.step state command).map Subtype.val).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  rw [hlaw, FinDist.mem_support_pure] at hmapped
  rw [← hmapped]
  exact next.2

private theorem phaseTwo_reachable (data : RunData) : Reachable graph (cfg data 2) := by
  let state : program.State := afterBinding data.secret
  have hstate : state.1 = cfg data 1 := by
    rw [afterBinding_val]
    rfl
  have hterm : ¬ program.execution.terminal state := by
    change ¬ Terminal graph state.1
    rw [hstate, terminal_iff]
    decide
  obtain ⟨joint, hlegal⟩ := program.execution.exists_legal hterm
  exact reachable_of_map_pure state ⟨joint, hlegal⟩ _
    (marker_step data state hstate ⟨joint, hlegal⟩)

private theorem phaseThree_reachable (data : RunData) : Reachable graph (cfg data 3) := by
  let state : program.State := ⟨cfg data 2, phaseTwo_reachable data⟩
  have hterm : ¬ program.execution.terminal state := by
    change ¬ Terminal graph (cfg data 2)
    rw [terminal_iff]
    decide
  obtain ⟨joint, hlegal⟩ := program.execution.exists_legal hterm
  let command := (⟨joint, hlegal⟩ : {joint // program.execution.Legal state joint})
  apply reachable_of_map_pure state command
  apply internal_step_law state command
  · change (readyInternalNodes graph (cfg data 2)).Nonempty
    refine ⟨node 2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact (ready_internal_iff _ _ _).mpr ⟨rfl, by simp⟩
  · intro event step
    exact marker_reveal_step data state.1 rfl event step

private theorem responseHistories (data : RunData) (hvalid : data.Valid) :
    ∃ middle final : program.execution.History,
      middle.state.1 = cfg data 5 ∧ final.state.1 = cfg data 6 := by
  obtain ⟨middle, final, hmiddle, hfinal⟩ :=
    response_site_realizable data.secret data.signal data.opening hvalid
  exact ⟨middle, final, hmiddle.trans (by rfl), hfinal.trans (by rfl)⟩

private theorem phaseSeven_reachable (data : RunData) (hvalid : data.Valid) :
    Reachable graph (cfg data 7) := by
  obtain ⟨_, history, _, hstate⟩ := responseHistories data hvalid
  let choice := responseChoice history data hstate data.response
  have hlocal := (program.information.menu_adequate 1 history.trace choice.1).mp choice.2
  let joint := program.execution.singletonJoint 1 choice.1
  have hlegal : program.execution.Legal history.state joint := by
    refine ⟨hlocal.1.1, ?_⟩
    intro who
    by_cases heq : who = 1
    · subst who
      simp only [joint, ExecutionProtocol.singletonJoint_self]
      exact hlocal
    · simp only [joint, ExecutionProtocol.singletonJoint_of_ne _ _ _ heq]
      intro hactive
      have hactive' : EventGraph.ActiveAt graph (cfg data 6) who := hstate ▸ hactive
      exact heq (by simpa [active_iff] using hactive')
  let command := (⟨joint, hlegal⟩ : {joint // program.execution.Legal history.state joint})
  apply reachable_of_map_pure history.state command
  have hbit : responseBit (command.1 1) = data.response := by
    change responseBit (some (responseAction data.response)) = data.response
    exact responseBit_action data.response
  simpa [hbit] using response_step data history.state hstate command

theorem cfg_reachable (data : RunData) (hvalid : data.Valid) (phase : Fin 9) :
    Reachable graph (cfg data phase) := by
  fin_cases phase
  · exact Reachable.initial
  · have hcfg : (afterBinding data.secret).1 = cfg data 1 := by
      rw [afterBinding_val]
      rfl
    exact hcfg ▸ (afterBinding data.secret).2
  · exact phaseTwo_reachable data
  · exact phaseThree_reachable data
  · obtain ⟨history, hsummary⟩ := opening_site_realizable data.secret data.signal
    have hstate : history.state.1 = cfg data 4 := by
      have := congrArg Prod.fst hsummary
      exact this.trans (by rfl)
    exact hstate ▸ history.state.2
  · obtain ⟨middle, _, hmiddle, _⟩ := responseHistories data hvalid
    exact hmiddle ▸ middle.state.2
  · obtain ⟨_, final, _, hfinal⟩ := responseHistories data hvalid
    exact hfinal ▸ final.state.2
  · exact phaseSeven_reachable data hvalid
  · let state : program.State := ⟨cfg data 7, phaseSeven_reachable data hvalid⟩
    have hterm : ¬ program.execution.terminal state := by
      change ¬ Terminal graph (cfg data 7)
      rw [terminal_iff]
      decide
    obtain ⟨joint, hlegal⟩ := program.execution.exists_legal hterm
    exact reachable_of_map_pure state ⟨joint, hlegal⟩ _
      (final_protocol_step data state rfl ⟨joint, hlegal⟩)

end VegasTests.OptionalDisclosure
