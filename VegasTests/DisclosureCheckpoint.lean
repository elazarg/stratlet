/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosureBinding

/-! # Public chance after the hidden binding -/

noncomputable section

namespace VegasTests.OptionalDisclosure

open Vegas EventGraph GameTheory GameTheory.Protocol GameTheory.Math.Probability

def markerAction : FrontierAction graph (0 : TestPlayer) where
  value? index := if hindex : index = node 1 then
    some (cast (congrArg (fun index => simpleExpr.Val (graph.nodeRow index).ty) hindex.symm)
      false) else none

theorem marker_value (state : Config graph)
    (value : simpleExpr.Val (graph.nodeRow (node 1)).ty)
    (h : CommitAvailable graph state 0 ⟨node 1, graph.nodeTypedValue (node 1) value⟩) :
    value = false := by
  obtain ⟨row, guard, hrow, hsem, _, chosen, hchosen, _, _, hguard⟩ := h
  have heq : row = graph.nodeRow (node 1) :=
    Option.some.inj (hrow.symm.trans (graph.nodes_get?_nodeRow (node 1)))
  subst row
  cases hsem
  change (!chosen) = true at hguard
  have hc : chosen = false := by cases chosen <;> simp_all
  subst chosen
  change some value = some false at hchosen
  exact Option.some.inj hchosen

theorem marker_action_unique (data : RunData) (packet : FrontierAction graph (0 : TestPlayer))
    (havailable : FrontierAction.Available graph (cfg data 1) 0 packet) :
    packet = markerAction := by
  have hvalues : packet.value? = markerAction.value? := by
    funext index
    by_cases heq : index = node 1
    · subst index
      have hready : ReadyCommitNode graph (cfg data 1) 0 (node 1) :=
        (ready_commit_iff _ _ _ _).mpr ⟨rfl, by simp⟩
      have hslot := havailable (node 1)
      rw [dif_pos hready] at hslot
      obtain ⟨value, hvalue, hcommit⟩ := hslot
      have hf := marker_value _ value hcommit
      subst value
      simpa [markerAction] using hvalue
    · have hnot : ¬ ReadyCommitNode graph (cfg data 1) 0 index := by
        intro hready
        exact heq (Fin.ext ((ready_commit_iff _ _ _ _).mp hready).1)
      have hn := havailable index
      rw [dif_neg hnot] at hn
      simpa [markerAction, heq] using hn
  cases packet
  exact congrArg FrontierAction.mk hvalues

def markerJoint := program.execution.singletonJoint 0 (some markerAction)

theorem marker_command (data : RunData) (state : program.State)
    (hstate : state.1 = cfg data 1)
    (command : {joint // program.execution.Legal state joint}) : command.1 = markerJoint := by
  funext who
  have hlocal := command.2.2 who
  have hactive : program.execution.active state who ↔ who = 0 := by
    change EventGraph.ActiveAt graph state.1 who ↔ _
    rw [hstate, active_iff]
    simp
  cases hchoice : command.1 who with
  | none =>
    rw [hchoice] at hlocal
    have hne : who ≠ 0 := fun heq => hlocal (hactive.mpr heq)
    simp [markerJoint, ExecutionProtocol.singletonJoint, hne]
  | some packet =>
    rw [hchoice] at hlocal
    have heq := hactive.mp hlocal.1
    subst who
    have havailable : FrontierAction.Available graph (cfg data 1) 0 packet := hstate ▸ hlocal.2
    rw [marker_action_unique data packet havailable]
    simp [markerJoint]

theorem marker_step (data : RunData) (state : program.State)
    (hstate : state.1 = cfg data 1)
    (command : {joint // program.execution.Legal state joint}) :
    (program.execution.step state command).map Subtype.val = FinDist.pure (cfg data 2) := by
  classical
  change ((toExecutionProtocol graph program.graphWF program.guardLive).step state command).map
    Subtype.val = _
  rw [toExecutionProtocol_step_eq_pure_applyFrontier _ _ _ _ _
    (hstate ▸ no_internal data 1 (by simp)), FinDist.map_pure]
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
  rw [marker_command data state hstate command, hstate]
  rfl

theorem marker_reveal_step (data : RunData) (state : Config graph)
    (hstate : state = cfg data 2)
    (event : InternalEvent graph) (step : InternalStep graph state event) :
    stepInternal graph state step = FinDist.pure (cfg data 3) := by
  subst state
  cases step with
  | sample row dist hrow hsem ready env henv =>
    have heq : row = graph.nodeRow event.node :=
      Option.some.inj (hrow.symm.trans (graph.nodes_get?_nodeRow event.node))
    subst row
    rcases event with ⟨index⟩
    have hindex : index = node 2 := Fin.ext ((ready_iff _ _ _).mp ready)
    subst index
    cases hsem
  | reveal row source hrow hsem ready value hvalue =>
    have heq : row = graph.nodeRow event.node :=
      Option.some.inj (hrow.symm.trans (graph.nodes_get?_nodeRow event.node))
    subst row
    rcases event with ⟨index⟩
    have hindex : index = node 2 := Fin.ext ((ready_iff _ _ _).mp ready)
    subst index
    cases hsem
    have hf : false = value := by
      change some false = some value at hvalue
      exact Option.some.inj hvalue
    subst value
    rfl

theorem public_coin_step (data : RunData) (state : Config graph)
    (hstate : state = cfg data 3)
    (event : InternalEvent graph) (step : InternalStep graph state event) :
    stepInternal graph state step = fairCoin.denote.map
      (fun signal => cfg { data with signal := signal } 4) := by
  subst state
  cases step with
  | sample row dist hrow hsem ready env henv =>
    have heq : row = graph.nodeRow event.node :=
      Option.some.inj (hrow.symm.trans (graph.nodes_get?_nodeRow event.node))
    subst row
    rcases event with ⟨index⟩
    have hindex : index = node 3 := Fin.ext ((ready_iff _ _ _).mp ready)
    subst index
    cases hsem
    simp only [stepInternal, EventDist.eval, EventDist.evalLaw,
      ToEventGraph.eventDistOf, simpleExpr, evalLawDistExprDeps, ite_self]
    rfl
  | reveal row source hrow hsem ready value hvalue =>
    have heq : row = graph.nodeRow event.node :=
      Option.some.inj (hrow.symm.trans (graph.nodes_get?_nodeRow event.node))
    subst row
    rcases event with ⟨index⟩
    have hindex : index = node 3 := Fin.ext ((ready_iff _ _ _).mp ready)
    subst index
    cases hsem

theorem internal_step_law (state : program.State)
    (command : {joint // program.execution.Legal state joint})
    (hinternal : (readyInternalNodes graph state.1).Nonempty)
    (law : FinDist (Config graph))
    (hlaw : ∀ event step, stepInternal graph state.1 (event := event) step = law) :
    (program.execution.step state command).map Subtype.val = law := by
  have hkernel (event : InternalEvent graph) (step : InternalStep graph state.1 event) :
      (stepAvailable graph state (.internal event step)).map Subtype.val = law :=
    (map_val_stepAvailable graph state (.internal event step)).trans (hlaw event step)
  change ((toExecutionProtocol graph program.graphWF program.guardLive).step state command).map
    Subtype.val = _
  rw [EventGraph.toExecutionProtocol_step_eq_stepReadyInternal graph program.graphWF
    program.guardLive state command hinternal]
  unfold EventGraph.stepReadyInternal
  exact hkernel _ _

theorem internal_command (state : program.State)
    (command : {joint // program.execution.Legal state joint})
    (hinternal : (readyInternalNodes graph state.1).Nonempty) :
    command.1 = program.execution.noop := by
  apply program.execution.eq_noop_of_legal_of_inactive command.2
  intro who hactive
  exact (Finset.nonempty_iff_ne_empty.mp hinternal) hactive.2.1

def checkpointPhase : Fin 4 → Fin 9
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 4

def checkpointSummary (secret signal : Bool) (phase : Fin 4) : OwnerSummary :=
  (cfg ⟨secret, signal, none, false⟩ (checkpointPhase phase),
    { current := ownerSnapshot (cfg ⟨secret, signal, none, false⟩ (checkpointPhase phase))
      own := if phase = 0 then [(ownerSnapshot (Config.initial graph), bindingAction secret)]
        else [(ownerSnapshot (cfg ⟨secret, false, none, false⟩ 1), markerAction),
          (ownerSnapshot (Config.initial graph), bindingAction secret)] })

theorem ownerSummary_extend (history : program.execution.History)
    (command : {joint // program.execution.Legal history.state joint}) (next : program.State)
    (hnext : next ∈ (program.execution.step history.state command).support) :
    ownerSummary (history.extend command.2 hnext) =
      (next.1, (ownerSummary history).2.push (command.1 0) (ownerSnapshot next.1)) := rfl

theorem owner_run_one_bind (profile : ∀ who, program.information.BehavioralPolicy who)
    (history : program.execution.History) (hterm : ¬ program.execution.terminal history.state)
    {Outcome : Type} (kernel : OwnerSummary → FinDist Outcome) :
    (program.information.runBehavioralFrom profile 1 history).bind
        (fun next => kernel (ownerSummary next)) =
      (program.information.behavioralJoint profile history.trace hterm).bind fun command =>
        ((program.execution.step history.state command).map Subtype.val).bind fun state =>
          kernel (state, (ownerSummary history).2.push (command.1 0) (ownerSnapshot state)) := by
  rw [program.information.runBehavioralFrom_succ_of_not_terminal profile 0 hterm,
    FinDist.bind_bind]
  apply FinDist.bind_congr
  intro command _
  have hz (next : program.execution.History) :
      program.information.runBehavioralFrom profile 0 next = FinDist.pure next := rfl
  simp only [FinDist.bind_bindOnSupport, hz, FinDist.pure_bind, ownerSummary_extend,
    FinDist.bindOnSupport_eq_bind, FinDist.bind_map]
  rfl

def checkpointNext (secret signal : Bool) : Fin 3 → FinDist OwnerSummary
  | 0 => FinDist.pure (checkpointSummary secret signal 1)
  | 1 => FinDist.pure (checkpointSummary secret signal 2)
  | 2 => fairCoin.denote.map fun coin => checkpointSummary secret coin 3

theorem run_one_checkpoint (profile : ∀ who, program.information.BehavioralPolicy who)
    (history : program.execution.History) (secret signal : Bool) (phase : Fin 3)
    (hsummary : ownerSummary history = checkpointSummary secret signal phase.castSucc) :
    (program.information.runBehavioralFrom profile 1 history).map ownerSummary =
      checkpointNext secret signal phase := by
  have hstate : history.state.1 =
      cfg ⟨secret, signal, none, false⟩ (checkpointPhase phase.castSucc) :=
    congrArg Prod.fst hsummary
  have hinfo := congrArg Prod.snd hsummary
  have hterm : ¬ program.execution.terminal history.state := by
    change ¬ Terminal graph history.state.1
    rw [hstate]
    fin_cases phase <;> rw [terminal_iff] <;> decide
  rw [FinDist.map_eq_bind]
  apply (owner_run_one_bind profile history hterm FinDist.pure).trans
  calc
    _ = (program.information.behavioralJoint profile history.trace hterm).bind
        (fun _ => checkpointNext secret signal phase) := by
      apply FinDist.bind_congr
      intro command _
      fin_cases phase
      · rw [marker_step _ history.state hstate command, FinDist.pure_bind,
          marker_command _ history.state hstate command, hinfo]
        rfl
      · have hi : (readyInternalNodes graph history.state.1).Nonempty := by
          rw [hstate]
          refine ⟨node 2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
          exact (ready_internal_iff _ _ _).mpr ⟨rfl, by simp [checkpointPhase]⟩
        rw [internal_step_law history.state command hi _
          (marker_reveal_step _ history.state.1 hstate), FinDist.pure_bind,
          internal_command history.state command hi, hinfo]
        rfl
      · have hi : (readyInternalNodes graph history.state.1).Nonempty := by
          rw [hstate]
          refine ⟨node 3, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
          exact (ready_internal_iff _ _ _).mpr ⟨rfl, by simp [checkpointPhase]⟩
        rw [internal_step_law history.state command hi _
          (public_coin_step _ history.state.1 hstate), FinDist.bind_map,
          internal_command history.state command hi, hinfo]
        rfl
    _ = _ := FinDist.bind_const _ _

theorem run_add_owner_summary_pure (profile : ∀ who, program.information.BehavioralPolicy who)
    (history : program.execution.History) (first second : Nat) (middle : OwnerSummary)
    (law : FinDist OwnerSummary)
    (hfirst : (program.information.runBehavioralFrom profile first history).map ownerSummary =
      FinDist.pure middle)
    (hsecond : ∀ next, ownerSummary next = middle →
      (program.information.runBehavioralFrom profile second next).map ownerSummary = law) :
    (program.information.runBehavioralFrom profile (first + second) history).map
      ownerSummary = law := by
  rw [program.information.runBehavioralFrom_add, FinDist.map_bind]
  calc
    _ = (program.information.runBehavioralFrom profile first history).bind (fun _ => law) := by
      apply FinDist.bind_congr
      intro next hnext
      apply hsecond
      have hmem : ownerSummary next ∈
          ((program.information.runBehavioralFrom profile first history).map
            ownerSummary).support := by
        rw [FinDist.support_map]
        exact ⟨next, hnext, rfl⟩
      simpa only [hfirst, FinDist.mem_support_pure] using hmem
    _ = law := FinDist.bind_const _ _

theorem run_three_checkpoint (profile : ∀ who, program.information.BehavioralPolicy who)
    (history : program.execution.History) (secret : Bool)
    (hsummary : ownerSummary history = checkpointSummary secret false 0) :
    (program.information.runBehavioralFrom profile 3 history).map ownerSummary =
      fairCoin.denote.map (fun signal => checkpointSummary secret signal 3) := by
  apply run_add_owner_summary_pure profile history 1 2 (checkpointSummary secret false 1) _
    (run_one_checkpoint profile history secret false 0 hsummary)
  intro middle hmiddle
  apply run_add_owner_summary_pure profile middle 1 1 (checkpointSummary secret false 2) _
    (run_one_checkpoint profile middle secret false 1 hmiddle)
  intro next hnext
  exact run_one_checkpoint profile next secret false 2 hnext

/-- The exact law of the store and full owner information at the disclosure
decision, from initialization and for every behavioral profile. -/
theorem opening_checkpoint_law (profile : ∀ who, program.information.BehavioralPolicy who) :
    (program.information.runBehavioral profile 4).map ownerSummary =
      (bindingLaw (profile 0)).bind fun secret =>
        fairCoin.denote.map (fun signal => checkpointSummary secret signal 3) := by
  change (program.information.runBehavioralFrom profile (1 + 3)
    program.execution.initHistory).map ownerSummary = _
  rw [program.information.runBehavioralFrom_add, FinDist.map_bind]
  apply FinDist.bind_eq_of_map_eq _ _ ownerSummary bindingSummary (binding_summary_law profile)
  intro history _ secret _ hsummary
  exact run_three_checkpoint profile history secret hsummary

def openingInfo (secret signal : Bool) : PlayerInformation graph (0 : TestPlayer) :=
  (checkpointSummary secret signal 3).2

def decodeOpeningInfo (info : PlayerInformation graph (0 : TestPlayer)) : Bool × Bool :=
  (((info.own[1]?).map fun decision => bindingBit (some decision.2)).getD false,
    (info.current.1.fieldValue? 3).getD false)

theorem opening_signal_visible (secret signal : Bool) :
    (publicObserve graph (cfg ⟨secret, signal, none, false⟩ 4)).fieldValue? 3 = some signal := by
  have howner : (graph.fieldRow 3).owner = none := rfl
  have hsource : (graph.fieldRow 3).source = .event 3 := rfl
  simp only [publicObserve, howner, hsource]
  have hdone : (cfg ⟨secret, signal, none, false⟩ 4).nodeDone 3 := by
    change (cfg ⟨false, false, none, false⟩ 4).nodeDone 3
    unfold Config.nodeDone Config.doneIds
    decide
  rw [if_pos hdone]
  rfl

@[simp] theorem decode_openingInfo (secret signal : Bool) :
    decodeOpeningInfo (openingInfo secret signal) = (secret, signal) := by
  simp [decodeOpeningInfo, openingInfo, checkpointSummary, checkpointPhase,
    ownerSnapshot, opening_signal_visible]

theorem opening_information_iff (secret other signal coin : Bool) :
    openingInfo secret signal = openingInfo other coin ↔ (secret, signal) = (other, coin) := by
  constructor
  · intro heq
    simpa only [decode_openingInfo] using congrArg decodeOpeningInfo heq
  · intro heq
    cases Prod.mk.inj heq with
    | intro hsecret hsignal => rw [hsecret, hsignal]

/-- info: 'VegasTests.OptionalDisclosure.opening_checkpoint_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.opening_checkpoint_law

/-- info: 'VegasTests.OptionalDisclosure.opening_information_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.opening_information_iff

end VegasTests.OptionalDisclosure
