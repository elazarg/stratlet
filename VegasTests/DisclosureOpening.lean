/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosureCheckpoint
import VegasTests.DisclosureResponse

/-! # The guarded opening and its continuation -/

noncomputable section

namespace VegasTests.OptionalDisclosure

open Vegas EventGraph GameTheory GameTheory.Protocol GameTheory.Math.Probability

def openingAction (opening : Option Bool) : FrontierAction graph (0 : TestPlayer) where
  value? index := if hindex : index = node 4 then
    some (cast (congrArg (fun index => simpleExpr.Val (graph.nodeRow index).ty) hindex.symm)
      opening) else none

def openingValue (choice : Option (FrontierAction graph (0 : TestPlayer))) : Option Bool :=
  (choice.bind fun action => action.value? (node 4)).getD none

@[simp] theorem openingValue_action (opening : Option Bool) :
    openingValue (some (openingAction opening)) = opening := by
  simp [openingValue, openingAction]

/-- The graph's ideal guard permits exactly the source-defined alternatives.
This is not a theorem about validating cryptographic openings. -/
theorem opening_value_valid (data : RunData)
    (value : simpleExpr.Val (graph.nodeRow (node 4)).ty)
    (h : CommitAvailable graph (cfg data 4) 0
      ⟨node 4, graph.nodeTypedValue (node 4) value⟩) :
    value = none ∨ value = some data.secret := by
  obtain ⟨row, guard, hrow, hsem, _, chosen, hchosen, env, henv, hguard⟩ := h
  have heq : row = graph.nodeRow (node 4) :=
    Option.some.inj (hrow.symm.trans (graph.nodes_get?_nodeRow (node 4)))
  subst row
  cases hsem
  have hc : value = chosen := by
    change some value = some chosen at hchosen
    exact Option.some.inj hchosen
  subst chosen
  have hread := ReadEnv.ofStore?_read henv (ref := { field := 0, ty := .bool }) (by decide)
  have hsecret : env.read { field := 0, ty := .bool } (by decide) = data.secret := by
    change some data.secret = some (env.read { field := 0, ty := .bool } (by decide)) at hread
    exact (Option.some.inj hread).symm
  change (if value.isNone then true else decide
    (value = some (env.read { field := 0, ty := .bool } (by decide)))) = true at hguard
  rw [hsecret] at hguard
  cases value <;> simp_all

theorem opening_action_exhaustive (data : RunData)
    (packet : FrontierAction graph (0 : TestPlayer))
    (havailable : FrontierAction.Available graph (cfg data 4) 0 packet) :
    ∃ opening, (opening = none ∨ opening = some data.secret) ∧ packet = openingAction opening := by
  have hready : ReadyCommitNode graph (cfg data 4) 0 (node 4) :=
    (ready_commit_iff _ _ _ _).mpr ⟨rfl, by simp⟩
  have hslot := havailable (node 4)
  rw [dif_pos hready] at hslot
  obtain ⟨value, hvalue, hcommit⟩ := hslot
  refine ⟨value, opening_value_valid data value hcommit, ?_⟩
  have hvalues : packet.value? = (openingAction value).value? := by
    funext index
    by_cases heq : index = node 4
    · subst index
      simpa [openingAction] using hvalue
    · have hnot : ¬ ReadyCommitNode graph (cfg data 4) 0 index := by
        intro h
        exact heq (Fin.ext ((ready_commit_iff _ _ _ _).mp h).1)
      have hnone := havailable index
      rw [dif_neg hnot] at hnone
      simpa [openingAction, heq] using hnone
  cases packet
  exact congrArg FrontierAction.mk hvalues

theorem opening_action_available_of_available (data : RunData)
    (packet : FrontierAction graph (0 : TestPlayer))
    (havailable : FrontierAction.Available graph (cfg data 4) 0 packet)
    (opening : Option Bool) (hopening : opening = none ∨ opening = some data.secret) :
    FrontierAction.Available graph (cfg data 4) 0 (openingAction opening) := by
  intro index
  split
  next hready =>
    have hindex : index = node 4 := Fin.ext ((ready_commit_iff _ _ _ _).mp hready).1
    subst index
    refine ⟨opening, by simp [openingAction], ?_⟩
    have hslot := havailable (node 4)
    rw [dif_pos hready] at hslot
    obtain ⟨_, _, ⟨row, guard, hrow, hsem, _, _, _, env, henv, _⟩⟩ := hslot
    have heq : row = graph.nodeRow (node 4) :=
      Option.some.inj (hrow.symm.trans (graph.nodes_get?_nodeRow (node 4)))
    subst row
    cases hsem
    refine ⟨⟨_, _, rfl, rfl, hready.ready, opening, rfl, env, henv, ?_⟩⟩
    have hread := ReadEnv.ofStore?_read henv (ref := { field := 0, ty := .bool }) (by decide)
    have hsecret : env.read { field := 0, ty := .bool } (by decide) = data.secret := by
      change some data.secret = some (env.read { field := 0, ty := .bool } (by decide)) at hread
      exact (Option.some.inj hread).symm
    change (if opening.isNone then true else decide
      (opening = some (env.read { field := 0, ty := .bool } (by decide)))) = true
    rw [hsecret]
    rcases hopening with rfl | rfl <;> simp
  next hnot =>
    have hne : index ≠ node 4 := by
      rintro rfl
      exact hnot ((ready_commit_iff _ _ _ _).mpr ⟨rfl, by simp⟩)
    simp [openingAction, hne]

def openingJoint (opening : Option Bool) :=
  program.execution.singletonJoint 0 (some (openingAction opening))

theorem opening_command (data : RunData) (state : program.State)
    (hstate : state.1 = cfg data 4)
    (command : {joint // program.execution.Legal state joint}) :
    command.1 = openingJoint (openingValue (command.1 0)) := by
  have hactive (who : TestPlayer) : program.execution.active state who ↔ who = 0 := by
    change EventGraph.ActiveAt graph state.1 who ↔ _
    rw [hstate, active_iff]
    simp
  have hlocal := program.execution.legalOption_of_legal command.2 0
  obtain ⟨packet, hpacket⟩ := LegalOption.exists_eq_some_of_active (command.1 0) hlocal
    ((hactive 0).mpr rfl)
  rw [hpacket] at hlocal
  obtain ⟨opening, _, rfl⟩ := opening_action_exhaustive data packet (hstate ▸ hlocal.2)
  rw [hpacket, openingValue_action]
  funext who
  by_cases heq : who = 0
  · subst who
    simpa [openingJoint] using hpacket
  · have hi := command.2.2 who
    cases hc : command.1 who with
    | none => simp [openingJoint, ExecutionProtocol.singletonJoint, heq]
    | some action =>
      rw [hc] at hi
      exact False.elim (heq ((hactive who).mp hi.1))

theorem opening_step (data : RunData) (state : program.State)
    (hstate : state.1 = cfg data 4)
    (command : {joint // program.execution.Legal state joint}) :
    (program.execution.step state command).map Subtype.val =
      FinDist.pure (cfg { data with opening := openingValue (command.1 0) } 5) := by
  classical
  change ((toExecutionProtocol graph program.graphWF program.guardLive).step state command).map
    Subtype.val = _
  rw [toExecutionProtocol_step_eq_pure_applyFrontier _ _ _ _ _
    (hstate ▸ no_internal data 4 (by simp)), FinDist.map_pure]
  have horder : [0] ∈ program.serializedSystem.schedules (publicObserve graph state.1) := by
    change [0].Nodup ∧ ∀ who : TestPlayer, who ∈ [0] ↔
      EventGraph.ActiveAtView graph (publicObserve graph state.1) who
    refine ⟨by simp, ?_⟩
    intro who
    rw [EventGraph.activeAtView_iff, hstate, active_iff]
    simp
  rw [← EventGraph.applySerializedOrder_eq_applyFrontier graph program.graphWF program.guardLive
    state command.1 command.2 horder]
  rw [EventGraph.applySerializedOrder_val program.graphWF command.1 state
    (fun who packet heq => by
      have hlocal := command.2.2 who
      rw [heq] at hlocal
      exact hlocal.2) (by simp : ([0] : List TestPlayer).Nodup)]
  rw [opening_command data state hstate command, hstate]
  rfl

theorem opening_reveal_step (data : RunData) (state : Config graph)
    (hstate : state = cfg data 5)
    (event : InternalEvent graph) (step : InternalStep graph state event) :
    stepInternal graph state step = FinDist.pure (cfg data 6) := by
  subst state
  cases step with
  | sample row dist hrow hsem ready env henv =>
    have heq : row = graph.nodeRow event.node :=
      Option.some.inj (hrow.symm.trans (graph.nodes_get?_nodeRow event.node))
    subst row
    rcases event with ⟨index⟩
    have hindex : index = node 5 := Fin.ext ((ready_iff _ _ _).mp ready)
    subst index
    cases hsem
  | reveal row source hrow hsem ready value hvalue =>
    have heq : row = graph.nodeRow event.node :=
      Option.some.inj (hrow.symm.trans (graph.nodes_get?_nodeRow event.node))
    subst row
    rcases event with ⟨index⟩
    have hindex : index = node 5 := Fin.ext ((ready_iff _ _ _).mp ready)
    subst index
    cases hsem
    have hv : data.opening = value := by
      change some data.opening = some value at hvalue
      exact Option.some.inj hvalue
    subst value
    rfl

theorem opening_reveal_protocol_step (data : RunData) (state : program.State)
    (hstate : state.1 = cfg data 5)
    (command : {joint // program.execution.Legal state joint}) :
    (program.execution.step state command).map Subtype.val = FinDist.pure (cfg data 6) := by
  classical
  have hi : (readyInternalNodes graph state.1).Nonempty := by
    rw [hstate]
    refine ⟨node 5, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact (ready_internal_iff _ _ _).mpr ⟨rfl, by simp⟩
  exact internal_step_law state command hi _ (opening_reveal_step data state.1 hstate)

theorem opening_reveal_terminal_law
    (profile : ∀ who, program.information.BehavioralPolicy who)
    (history : program.execution.History) (data : RunData)
    (hstate : history.state.1 = cfg data 5) :
    (program.terminalStateLaw profile history).map Subtype.val =
      (responseLaw (profile 1) data.signal data.opening).map
        (fun bit => cfg { data with response := bit } 8) := by
  have hterm : ¬ program.execution.terminal history.state := by
    change ¬ Terminal graph history.state.1
    rw [hstate, terminal_iff]
    decide
  rw [program.terminalStateLaw_step profile history hterm, FinDist.map_bind]
  calc
    _ = (program.information.behavioralJoint profile history.trace hterm).bind
        (fun _ => (responseLaw (profile 1) data.signal data.opening).map
          (fun bit => cfg { data with response := bit } 8)) := by
      apply FinDist.bind_congr
      intro command _
      rw [FinDist.map_bindOnSupport]
      calc
        _ = (program.execution.step history.state command).bind
            (fun _ => (responseLaw (profile 1) data.signal data.opening).map
              (fun bit => cfg { data with response := bit } 8)) := by
          apply FinDist.bindOnSupport_eq_bind_of_eq_on_support
          intro next hnext
          have hmem : next.1 ∈
              ((program.execution.step history.state command).map Subtype.val).support := by
            rw [FinDist.support_map]
            exact ⟨next, hnext, rfl⟩
          have hn : next.1 = cfg data 6 := by
            simpa only [opening_reveal_protocol_step data history.state hstate command,
              FinDist.mem_support_pure] using hmem
          exact response_terminal_law profile (history.extend command.2 hnext) data hn
        _ = _ := FinDist.bind_const _ _
    _ = _ := FinDist.bind_const _ _

def openingLaw (policy : program.information.BehavioralPolicy 0)
    (secret signal : Bool) : FinDist (Option Bool) :=
  (policy (openingInfo secret signal)).map fun choice => openingValue choice.1

theorem opening_command_terminal_law
    (profile : ∀ who, program.information.BehavioralPolicy who)
    (history : program.execution.History) (secret signal : Bool)
    (hstate : history.state.1 = cfg ⟨secret, signal, none, false⟩ 4)
    (command : {joint // program.execution.Legal history.state joint}) :
    ((program.execution.step history.state command).bindOnSupport fun _ realized =>
      program.terminalStateLaw profile (history.extend command.2 realized)).map Subtype.val =
      (responseLaw (profile 1) signal (openingValue (command.1 0))).map
        (fun bit => cfg ⟨secret, signal, openingValue (command.1 0), bit⟩ 8) := by
  rw [FinDist.map_bindOnSupport]
  calc
    _ = (program.execution.step history.state command).bind
        (fun _ => (responseLaw (profile 1) signal (openingValue (command.1 0))).map
          (fun bit => cfg ⟨secret, signal, openingValue (command.1 0), bit⟩ 8)) := by
      apply FinDist.bindOnSupport_eq_bind_of_eq_on_support
      intro next hnext
      have hmem : next.1 ∈
          ((program.execution.step history.state command).map Subtype.val).support := by
        rw [FinDist.support_map]
        exact ⟨next, hnext, rfl⟩
      have hn : next.1 = cfg ⟨secret, signal, openingValue (command.1 0), false⟩ 5 := by
        simpa only [opening_step ⟨secret, signal, none, false⟩ history.state hstate command,
          FinDist.mem_support_pure] using hmem
      exact opening_reveal_terminal_law profile (history.extend command.2 hnext)
        ⟨secret, signal, openingValue (command.1 0), false⟩ hn
    _ = _ := FinDist.bind_const _ _

theorem opening_terminal_law
    (profile : ∀ who, program.information.BehavioralPolicy who)
    (history : program.execution.History) (secret signal : Bool)
    (hsummary : ownerSummary history = checkpointSummary secret signal 3) :
    (program.terminalStateLaw profile history).map Subtype.val =
      (openingLaw (profile 0) secret signal).bind fun opening =>
        (responseLaw (profile 1) signal opening).map
          (fun bit => cfg ⟨secret, signal, opening, bit⟩ 8) := by
  have hstate : history.state.1 = cfg ⟨secret, signal, none, false⟩ 4 :=
    congrArg Prod.fst hsummary
  have hinfo : program.information.infoOf 0 history.trace = openingInfo secret signal :=
    congrArg Prod.snd hsummary
  have hterm : ¬ program.execution.terminal history.state := by
    change ¬ Terminal graph history.state.1
    rw [hstate, terminal_iff]
    decide
  rw [program.terminalStateLaw_step profile history hterm, FinDist.map_bind]
  calc
    _ = (program.information.behavioralJoint profile history.trace hterm).bind
        (fun command => (responseLaw (profile 1) signal (openingValue (command.1 0))).map
          (fun bit => cfg ⟨secret, signal, openingValue (command.1 0), bit⟩ 8)) := by
      apply FinDist.bind_congr
      intro command _
      exact opening_command_terminal_law profile history secret signal hstate command
    _ = _ := by
      rw [InformationModel.behavioralJoint, FinDist.bind_map]
      calc
        _ = ((FinDist.pi fun who => profile who (program.information.infoOf who history.trace)).map
            (fun draws => draws 0)).bind (fun choice =>
              (responseLaw (profile 1) signal (openingValue choice.1)).map
                (fun bit => cfg ⟨secret, signal, openingValue choice.1, bit⟩ 8)) := by
          rw [FinDist.bind_map]
        _ = _ := by
          rw [FinDist.map_apply_pi]
          have hlaw : ((profile 0 (program.information.infoOf 0 history.trace)).map
              fun choice => openingValue choice.1) = openingLaw (profile 0) secret signal :=
            congrArg (fun info => (profile 0 info).map fun choice => openingValue choice.1) hinfo
          rw [← hlaw, FinDist.bind_map]

/-- info: 'VegasTests.OptionalDisclosure.opening_value_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.opening_value_valid

/-- info: 'VegasTests.OptionalDisclosure.opening_action_available_of_available' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.opening_action_available_of_available

end VegasTests.OptionalDisclosure
