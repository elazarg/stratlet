/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.QuittingEquilibrium

/-! # Information at the compiled completion checkpoint -/

noncomputable section

namespace VegasTests.QuittingSource

open Vegas EventGraph GameTheory GameTheory.Protocol GameTheory.Math.Probability

instance fieldCountNeZero : NeZero graph.fieldCount := ⟨by decide⟩

theorem fieldCount : graph.fieldCount = 10 := rfl

/-- The four configurations between the simultaneous choices and completion.
The final parameter matters only after the public coin has been sampled. -/
def prefixCfg (bits : TestPlayer → Bool) (signal : Bool) : Fin 4 → Config graph
  | 0 => (after bits).1
  | 1 => ((after bits).1).completeNode (node 2) ⟨.bool, false⟩
  | 2 => (((after bits).1).completeNode (node 2) ⟨.bool, false⟩).completeNode
      (node 3) ⟨.bool, false⟩
  | 3 => ((((after bits).1).completeNode (node 2) ⟨.bool, false⟩).completeNode
      (node 3) ⟨.bool, false⟩).completeNode (node 4) ⟨.bool, signal⟩

theorem prefix_ready (bits : TestPlayer → Bool) (signal : Bool) (phase : Fin 4)
    (index : Fin graph.nodeCount) :
    Ready graph (prefixCfg bits signal phase) index ↔ index.val = phase.val + 2 := by
  fin_cases phase <;> simp only [prefixCfg, after_val, Ready, Config.completeNode] <;>
    fin_cases index <;> decide

theorem prefix_ready_commit (bits : TestPlayer → Bool) (signal : Bool) (phase : Fin 4)
    (who : TestPlayer) (index : Fin graph.nodeCount) :
    ReadyCommitNode graph (prefixCfg bits signal phase) who index ↔
      who = 0 ∧ (phase = 0 ∧ index = node 2 ∨ phase = 3 ∧ index = node 5) := by
  constructor
  · rintro ⟨row, guard, hrow, hsem, hready⟩
    have heq : row = graph.nodeRow index :=
      Option.some.inj (hrow.symm.trans (graph.nodes_get?_nodeRow index))
    subst row
    have hindex := (prefix_ready bits signal phase index).mp hready
    fin_cases phase <;> fin_cases index <;> norm_num at hindex
    all_goals cases hsem <;> simp [node, nodeCount]
  · rintro ⟨rfl, h | h⟩ <;> rcases h with ⟨rfl, rfl⟩ <;>
      exact ⟨_, _, rfl, rfl, (prefix_ready _ _ _ _).mpr rfl⟩

theorem prefix_ready_internal (bits : TestPlayer → Bool) (signal : Bool) (phase : Fin 4)
    (index : Fin graph.nodeCount) :
    ReadyInternalNode graph (prefixCfg bits signal phase) index ↔
      (phase = 1 ∧ index = node 3 ∨ phase = 2 ∧ index = node 4) := by
  constructor
  · rintro ⟨row, hrow, hsem, hready⟩
    have heq : row = graph.nodeRow index :=
      Option.some.inj (hrow.symm.trans (graph.nodes_get?_nodeRow index))
    subst row
    have hindex := (prefix_ready bits signal phase index).mp hready
    fin_cases phase <;> fin_cases index <;> norm_num at hindex
    all_goals cases hsem <;> simp [node, nodeCount]
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      exact ⟨_, rfl, trivial, (prefix_ready _ _ _ _).mpr rfl⟩

theorem prefix_noInternal (bits : TestPlayer → Bool) (signal : Bool) :
    readyInternalNodes graph (prefixCfg bits signal 0) = ∅ := by
  classical
  ext index
  simp [readyInternalNodes, prefix_ready_internal]

def markerAction : FrontierAction graph (0 : TestPlayer) where
  value? index := if index = node 2 then
    some (cast (congrArg simpleExpr.Val (node_ty index).symm) false) else none

theorem marker_value (cfg : Config graph) (value : simpleExpr.Val (graph.nodeRow (node 2)).ty)
    (h : CommitAvailable graph cfg (0 : TestPlayer)
      ⟨node 2, graph.nodeTypedValue (node 2) value⟩) : value = false := by
  obtain ⟨row, guard, hrow, hsem, hready, chosen, hchosen, env, henv, hguard⟩ := h
  have heq : row = graph.nodeRow (node 2) :=
    Option.some.inj (hrow.symm.trans (graph.nodes_get?_nodeRow (node 2)))
  subst row
  cases hsem
  change (!chosen) = true at hguard
  have hfalse : chosen = false := by cases chosen <;> simp_all
  subst chosen
  change some value = some false at hchosen
  exact Option.some.inj hchosen

theorem prefix_marker_action (bits : TestPlayer → Bool) (signal : Bool)
    (packet : FrontierAction graph (0 : TestPlayer))
    (h : FrontierAction.Available graph (prefixCfg bits signal 0) 0 packet) :
    packet = markerAction := by
  have hvalues : packet.value? = markerAction.value? := by
    funext index
    by_cases heq : index = node 2
    · subst index
      have hready := (prefix_ready_commit bits signal 0 0 (node 2)).mpr (by simp)
      have hv := h (node 2)
      rw [dif_pos hready] at hv
      obtain ⟨value, hvalue, havailable⟩ := hv
      have hfalse := marker_value _ value havailable
      subst value
      simpa [markerAction] using hvalue
    · have hnot : ¬ ReadyCommitNode graph (prefixCfg bits signal 0) 0 index := by
        simp [prefix_ready_commit, heq]
      have hv := h index
      rw [dif_neg hnot] at hv
      simpa [markerAction, heq] using hv
  cases packet
  exact congrArg FrontierAction.mk hvalues

theorem prefix_active (bits : TestPlayer → Bool) (signal : Bool) (who : TestPlayer) :
    EventGraph.ActiveAt graph (prefixCfg bits signal 0) who ↔ who = 0 := by
  classical
  constructor
  · rintro ⟨_, _, hactive⟩
    obtain ⟨index, hindex⟩ := (Finset.mem_filter.mp hactive).2
    exact ((prefix_ready_commit _ _ _ _ _).mp (Finset.mem_filter.mp hindex).2).1
  · rintro rfl
    refine ⟨?_, prefix_noInternal bits signal, Finset.mem_filter.mpr ?_⟩
    · intro hterm
      have hn := hterm (node 2)
      simp [prefixCfg, after_val, Config.completeNode, Config.initial, node] at hn
    · refine ⟨Finset.mem_univ _, node 2, Finset.mem_filter.mpr ?_⟩
      exact ⟨Finset.mem_univ _, (prefix_ready_commit _ _ _ _ _).mpr (by simp)⟩

def markerJoint := program.execution.singletonJoint 0 (some markerAction)

theorem marker_command (bits : TestPlayer → Bool) (signal : Bool) (state : program.State)
    (hstate : state.1 = prefixCfg bits signal 0)
    (command : {joint // program.execution.Legal state joint}) : command.1 = markerJoint := by
  funext who
  have hlocal := command.2.2 who
  have hactive : program.execution.active state who ↔ who = 0 := by
    change EventGraph.ActiveAt graph state.1 who ↔ _
    rw [hstate]
    exact prefix_active bits signal who
  cases hchoice : command.1 who with
  | none =>
      rw [hchoice] at hlocal
      have hne : who ≠ 0 := fun heq => hlocal (hactive.mpr heq)
      simp [markerJoint, ExecutionProtocol.singletonJoint, hne]
  | some packet =>
      rw [hchoice] at hlocal
      have heq := hactive.mp hlocal.1
      subst who
      have havailable : FrontierAction.Available graph (prefixCfg bits signal 0) 0 packet :=
        hstate ▸ hlocal.2
      rw [prefix_marker_action bits signal packet havailable]
      simp [markerJoint]

theorem marker_step (bits : TestPlayer → Bool) (signal : Bool) (state : program.State)
    (hstate : state.1 = prefixCfg bits signal 0)
    (command : {joint // program.execution.Legal state joint}) :
    (program.execution.step state command).map Subtype.val =
      FinDist.pure (prefixCfg bits signal 1) := by
  classical
  change ((toExecutionProtocol graph program.graphWF program.guardLive).step state command).map
    Subtype.val = _
  rw [toExecutionProtocol_step_eq_pure_applyFrontier _ _ _ _ _
    (hstate ▸ prefix_noInternal bits signal), FinDist.map_pure]
  have horder : [0] ∈ program.serializedSystem.schedules (publicObserve graph state.1) := by
    change [0].Nodup ∧ ∀ who : TestPlayer, who ∈ [0] ↔
      EventGraph.ActiveAtView graph (publicObserve graph state.1) who
    refine ⟨by simp, ?_⟩
    intro who
    rw [EventGraph.activeAtView_iff, hstate, prefix_active]
    simp
  rw [← EventGraph.applySerializedOrder_eq_applyFrontier graph program.graphWF program.guardLive
    state command.1 command.2 horder]
  rw [EventGraph.applySerializedOrder_val program.graphWF command.1 state
    (fun who packet heq => by
      have hlocal := command.2.2 who
      rw [heq] at hlocal
      exact hlocal.2) (by simp : ([0] : List TestPlayer).Nodup)]
  rw [marker_command bits signal state hstate command, hstate]
  rfl

theorem marker_reveal_step (bits : TestPlayer → Bool) (signal : Bool)
    (cfg : Config graph) (hcfg : cfg = prefixCfg bits signal 1)
    (event : InternalEvent graph) (step : InternalStep graph cfg event) :
    stepInternal graph cfg step = FinDist.pure (prefixCfg bits signal 2) := by
  subst cfg
  cases step with
  | sample row dist hrow hsem ready env henv =>
      have heq : row = graph.nodeRow event.node :=
        Option.some.inj (hrow.symm.trans (graph.nodes_get?_nodeRow event.node))
      subst row
      rcases event with ⟨index⟩
      have hindex : index = node 3 := Fin.ext ((prefix_ready _ _ _ _).mp ready)
      subst index
      cases hsem
  | reveal row source hrow hsem ready value hvalue =>
      have heq : row = graph.nodeRow event.node :=
        Option.some.inj (hrow.symm.trans (graph.nodes_get?_nodeRow event.node))
      subst row
      rcases event with ⟨index⟩
      have hindex : index = node 3 := Fin.ext ((prefix_ready _ _ _ _).mp ready)
      subst index
      cases hsem
      have hfalse : false = value := by
        change Store.getAs (prefixCfg bits signal 1).store 2 .bool = some value at hvalue
        simpa [prefixCfg, Config.completeNode, Store.getAs, Store.set, nodeTarget,
          TypedValue.as?, node, nodeCount] using hvalue
      subst value
      rfl

theorem public_coin_step (bits : TestPlayer → Bool) (signal : Bool)
    (cfg : Config graph) (hcfg : cfg = prefixCfg bits signal 2)
    (event : InternalEvent graph) (step : InternalStep graph cfg event) :
    stepInternal graph cfg step = ObservedAbort.fair.map (fun coin => prefixCfg bits coin 3) := by
  subst cfg
  cases step with
  | sample row dist hrow hsem ready env henv =>
      have heq : row = graph.nodeRow event.node :=
        Option.some.inj (hrow.symm.trans (graph.nodes_get?_nodeRow event.node))
      subst row
      rcases event with ⟨index⟩
      have hindex : index = node 4 := Fin.ext ((prefix_ready _ _ _ _).mp ready)
      subst index
      cases hsem
      simp only [stepInternal, EventDist.eval, EventDist.evalLaw,
        ToEventGraph.eventDistOf, simpleExpr, evalLawDistExprDeps, ite_self, fairCoin_denote]
      rfl
  | reveal row source hrow hsem ready value hvalue =>
      have heq : row = graph.nodeRow event.node :=
        Option.some.inj (hrow.symm.trans (graph.nodes_get?_nodeRow event.node))
      subst row
      rcases event with ⟨index⟩
      have hindex : index = node 4 := Fin.ext ((prefix_ready _ _ _ _).mp ready)
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

theorem prefix_internal_nonempty (bits : TestPlayer → Bool) (signal : Bool) (phase : Fin 4)
    (hphase : phase = 1 ∨ phase = 2) :
    (readyInternalNodes graph (prefixCfg bits signal phase)).Nonempty := by
  classical
  rcases hphase with rfl | rfl
  · exact ⟨node 3, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (prefix_ready_internal _ _ _ _).mpr (by simp)⟩⟩
  · exact ⟨node 4, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (prefix_ready_internal _ _ _ _).mpr (by simp)⟩⟩

theorem internal_command (state : program.State)
    (command : {joint // program.execution.Legal state joint})
    (hinternal : (readyInternalNodes graph state.1).Nonempty) :
    command.1 = program.execution.noop := by
  apply program.execution.eq_noop_of_legal_of_inactive command.2
  intro who hactive
  exact (Finset.nonempty_iff_ne_empty.mp hinternal) hactive.2.1

def snapshot (cfg : Config graph) : LocalSnapshot graph (0 : TestPlayer) :=
  (publicObserve graph cfg, observe graph cfg 0)

theorem secret_not_read (index : Fin graph.nodeCount) (guard : EventGuard simpleExpr)
    (hsem : graph.node? index = some (.commit 0 guard)) :
    ({ field := 1, ty := .bool } : FieldRef simpleExpr) ∉ guard.choiceReads := by
  fin_cases index <;> cases hsem <;> decide

theorem private_secret_absent (cfg : Config graph) (index : Fin graph.nodeCount) :
    (observe graph cfg 0).fieldValue? index 1 = none := by
  have hty : (graph.fieldRow 1).ty = .bool := rfl
  have hfield : (1 : Fin graph.fieldCount).val = 1 := rfl
  cases hnode : graph.node? index with
  | none => simp only [observe, hnode]
  | some sem =>
      cases sem with
      | sample dist => simp only [observe, hnode]
      | reveal source => simp only [observe, hnode]
      | commit actor guard =>
          by_cases hactor : actor = 0
          · subst actor
            simp only [observe, hnode, hty, hfield]
            simp [secret_not_read index guard hnode]
          · simp only [observe, hnode, dif_neg hactor]

theorem snapshot_eq_of_store (left right : Config graph)
    (hdone : left.done = right.done)
    (hstore : ∀ field, field ≠ 1 → left.store field = right.store field) :
    snapshot left = snapshot right := by
  unfold snapshot
  have hread (field : Nat) (ty : simpleExpr.Ty) (hne : field ≠ 1) :
      Store.getAs left.store field ty = Store.getAs right.store field ty := by
    simp only [Store.getAs, hstore field hne]
  apply Prod.ext
  · apply PublicObservation.ext hdone
    intro field
    by_cases heq : field = 1
    · subst field
      have howner : (graph.fieldRow 1).owner = some (1 : TestPlayer) := rfl
      simp [publicObserve, howner]
    · have hne : field.val ≠ 1 := fun h => heq (Fin.ext h)
      simp only [publicObserve, Config.nodeDone, Config.doneIds, hdone, hread _ _ hne]
  · apply Observation.ext
    · ext index
      simp only [observe, Finset.mem_filter, Finset.mem_univ, true_and]
      cases hnode : graph.node? index with
      | none => simp
      | some sem => cases sem <;> simp [Ready, hdone]
    · intro index field
      by_cases heq : field = 1
      · subst field
        rw [private_secret_absent, private_secret_absent]
      · have hne : field.val ≠ 1 := fun h => heq (Fin.ext h)
        simp only [observe, Ready, hdone, hread _ _ hne]

theorem prefix_snapshot_eq (bits other : TestPlayer → Bool) (signal : Bool)
    (phase : Fin 4) (hown : bits 0 = other 0) :
    snapshot (prefixCfg bits signal phase) = snapshot (prefixCfg other signal phase) := by
  apply snapshot_eq_of_store
  · fin_cases phase <;> simp [prefixCfg, after_val, Config.completeNode]
  · intro field hfield
    fin_cases phase <;>
      simp [prefixCfg, after_val, Config.completeNode, Store.set, nodeTarget, node, nodeCount,
        hfield, hown]

def prefixInfo (bits : TestPlayer → Bool) (signal : Bool) (phase : Fin 4) :
    PlayerInformation graph (0 : TestPlayer) where
  current := snapshot (prefixCfg bits signal phase)
  own := if phase = 0 then [(snapshot (Config.initial graph), action 0 (bits 0))]
    else [(snapshot (prefixCfg bits signal 0), markerAction),
      (snapshot (Config.initial graph), action 0 (bits 0))]

theorem prefixInfo_eq (bits other : TestPlayer → Bool) (signal : Bool)
    (phase : Fin 4) (hown : bits 0 = other 0) :
    prefixInfo bits signal phase = prefixInfo other signal phase := by
  apply PlayerInformation.ext
  · exact prefix_snapshot_eq bits other signal phase hown
  · simp only [prefixInfo, hown, prefix_snapshot_eq bits other signal 0 hown]

abbrev CheckpointSummary := Config graph × PlayerInformation graph (0 : TestPlayer)

def summarize (history : program.execution.History) : CheckpointSummary :=
  (history.state.1, program.information.infoOf 0 history.trace)

def prefixSummary (bits : TestPlayer → Bool) (signal : Bool) (phase : Fin 4) :
    CheckpointSummary := (prefixCfg bits signal phase, prefixInfo bits signal phase)

theorem run_zero (profile : ∀ who, program.information.BehavioralPolicy who)
    (history : program.execution.History) :
    program.information.runBehavioralFrom profile 0 history = FinDist.pure history := rfl

theorem summarize_extend (history : program.execution.History)
    (command : {joint // program.execution.Legal history.state joint}) (next : program.State)
    (hnext : next ∈ (program.execution.step history.state command).support) :
    summarize (history.extend command.2 hnext) =
      (next.1, (summarize history).2.push (command.1 0) (snapshot next.1)) := rfl

theorem run_one_bind (profile : ∀ who, program.information.BehavioralPolicy who)
    (history : program.execution.History) (hterm : ¬ program.execution.terminal history.state)
    {Outcome : Type} (kernel : CheckpointSummary → FinDist Outcome) :
    (program.information.runBehavioralFrom profile 1 history).bind
        (fun next => kernel (summarize next)) =
      (program.information.behavioralJoint profile history.trace hterm).bind fun command =>
        ((program.execution.step history.state command).map Subtype.val).bind fun cfg =>
          kernel (cfg, (summarize history).2.push (command.1 0) (snapshot cfg)) := by
  rw [program.information.runBehavioralFrom_succ_of_not_terminal profile 0 hterm,
    FinDist.bind_bind]
  apply FinDist.bind_congr
  intro command _
  simp only [FinDist.bind_bindOnSupport, run_zero, FinDist.pure_bind, summarize_extend,
    FinDist.bindOnSupport_eq_bind, FinDist.bind_map]
  rfl

theorem prefix_not_terminal (bits : TestPlayer → Bool) (signal : Bool) (phase : Fin 4) :
    ¬ Terminal graph (prefixCfg bits signal phase) := by
  let index : Fin graph.nodeCount := ⟨phase.val + 2, by change phase.val + 2 < 10; omega⟩
  have hready := (prefix_ready bits signal phase index).mpr rfl
  exact fun hterm => hready.1 (hterm index)

def prefixNext (bits : TestPlayer → Bool) (signal : Bool) : Fin 3 → FinDist CheckpointSummary
  | 0 => FinDist.pure (prefixSummary bits signal 1)
  | 1 => FinDist.pure (prefixSummary bits signal 2)
  | 2 => ObservedAbort.fair.map fun coin => prefixSummary bits coin 3

theorem run_one_prefix (profile : ∀ who, program.information.BehavioralPolicy who)
    (history : program.execution.History) (bits : TestPlayer → Bool) (signal : Bool)
    (phase : Fin 3) (hsummary : summarize history = prefixSummary bits signal phase.castSucc) :
    (program.information.runBehavioralFrom profile 1 history).map summarize =
      prefixNext bits signal phase := by
  have hstate : history.state.1 = prefixCfg bits signal phase.castSucc :=
    congrArg Prod.fst hsummary
  have hinfo : (summarize history).2 = prefixInfo bits signal phase.castSucc :=
    congrArg Prod.snd hsummary
  have hterm : ¬ program.execution.terminal history.state := by
    change ¬ Terminal graph history.state.1
    rw [hstate]
    exact prefix_not_terminal bits signal phase.castSucc
  rw [FinDist.map_eq_bind]
  apply (run_one_bind profile history hterm FinDist.pure).trans
  calc
    _ = (program.information.behavioralJoint profile history.trace hterm).bind
        (fun _ => prefixNext bits signal phase) := by
      apply FinDist.bind_congr
      intro command _
      fin_cases phase
      · rw [marker_step bits signal history.state hstate command, FinDist.pure_bind,
          marker_command bits signal history.state hstate command, hinfo]
        rfl
      · have hi : (readyInternalNodes graph history.state.1).Nonempty :=
          hstate ▸ prefix_internal_nonempty bits signal 1 (Or.inl rfl)
        rw [internal_step_law history.state command hi _
          (marker_reveal_step bits signal history.state.1 hstate), FinDist.pure_bind,
          internal_command history.state command hi, hinfo]
        rfl
      · have hi : (readyInternalNodes graph history.state.1).Nonempty :=
          hstate ▸ prefix_internal_nonempty bits signal 2 (Or.inr rfl)
        rw [internal_step_law history.state command hi _
          (public_coin_step bits signal history.state.1 hstate), FinDist.bind_map,
          internal_command history.state command hi, hinfo]
        rfl
    _ = _ := FinDist.bind_const _ _

theorem run_add_summary_pure (profile : ∀ who, program.information.BehavioralPolicy who)
    (history : program.execution.History) (first second : Nat) (middle : CheckpointSummary)
    (law : FinDist CheckpointSummary)
    (hfirst : (program.information.runBehavioralFrom profile first history).map summarize =
      FinDist.pure middle)
    (hsecond : ∀ next, summarize next = middle →
      (program.information.runBehavioralFrom profile second next).map summarize = law) :
    (program.information.runBehavioralFrom profile (first + second) history).map
      summarize = law := by
  rw [program.information.runBehavioralFrom_add, FinDist.map_bind]
  calc
    _ = (program.information.runBehavioralFrom profile first history).bind (fun _ => law) := by
      apply FinDist.bind_congr
      intro next hnext
      apply hsecond
      have hmem : summarize next ∈
          ((program.information.runBehavioralFrom profile first history).map
            summarize).support := by
        rw [FinDist.support_map]
        exact ⟨next, hnext, rfl⟩
      simpa only [hfirst, FinDist.mem_support_pure] using hmem
    _ = law := FinDist.bind_const _ _

theorem run_three_prefix (profile : ∀ who, program.information.BehavioralPolicy who)
    (history : program.execution.History) (bits : TestPlayer → Bool)
    (hsummary : summarize history = prefixSummary bits false 0) :
    (program.information.runBehavioralFrom profile 3 history).map summarize =
      ObservedAbort.fair.map (fun signal => prefixSummary bits signal 3) := by
  apply run_add_summary_pure profile history 1 2 (prefixSummary bits false 1) _
    (run_one_prefix profile history bits false 0 hsummary)
  intro middle hmiddle
  apply run_add_summary_pure profile middle 1 1 (prefixSummary bits false 2) _
    (run_one_prefix profile middle bits false 1 hmiddle)
  intro next hnext
  exact run_one_prefix profile next bits false 2 hnext

theorem run_initial_summary (profile : ∀ who, program.information.BehavioralPolicy who) :
    (program.information.runBehavioralFrom profile 1 program.execution.initHistory).map summarize =
      (FinDist.pi fun who => extractStrategy who (profile who)).map
        (fun bits => prefixSummary bits false 0) := by
  rw [FinDist.map_eq_bind]
  apply (run_one_bind profile program.execution.initHistory
    (initial_active 0).1 FinDist.pure).trans
  rw [InformationModel.behavioralJoint, FinDist.bind_map]
  unfold extractStrategy
  rw [FinDist.pi_map, FinDist.map_comp, FinDist.map_eq_bind]
  apply FinDist.bind_congr
  intro draws _
  let bits := fun who => (choiceEquiv who).symm (draws who)
  have hdraws : ∀ who, draws who = choice who (bits who) :=
    fun who => ((choiceEquiv who).apply_symm_apply (draws who)).symm
  have hcommand : (fun who => (draws who).1) = joint bits := by
    funext who
    rw [hdraws who]
    rfl
  have hlegal : program.execution.Legal program.execution.init
      (fun who => (draws who).1) := hcommand ▸ joint_legal bits
  have hstep : program.execution.step program.execution.init
      ⟨fun who => (draws who).1, hlegal⟩ = FinDist.pure (after bits) := by
    change (toExecutionProtocol graph program.graphWF program.guardLive).step _ _ = _
    rw [toExecutionProtocol_step_eq_pure_applyFrontier _ _ _ _ _ (initial_active 0).2.1]
    change FinDist.pure (applyFrontier graph program.graphWF program.execution.init
      (fun who => (draws who).1)) = _
    rw [hcommand]
    rfl
  change ((program.execution.step program.execution.init
    ⟨fun who => (draws who).1, hlegal⟩).map Subtype.val).bind _ = _
  rw [hstep, FinDist.map_pure, FinDist.pure_bind]
  simp only [hdraws 0]
  rfl

/-- Every behavioral profile reaches the actual completion checkpoint in
four rounds, with the exact joint law of its store and complete player-zero
information state. The opponent's hidden choice is absent from that information. -/
theorem checkpoint_summary_law (profile : ∀ who, program.information.BehavioralPolicy who) :
    (program.information.runBehavioral profile 4).map summarize =
      (FinDist.pi fun who => extractStrategy who (profile who)).bind fun bits =>
        ObservedAbort.fair.map (fun signal => prefixSummary bits signal 3) := by
  change (program.information.runBehavioralFrom profile (1 + 3)
    program.execution.initHistory).map summarize = _
  rw [program.information.runBehavioralFrom_add, FinDist.map_bind]
  apply FinDist.bind_eq_of_map_eq _ _ summarize (fun bits => prefixSummary bits false 0)
    (run_initial_summary profile)
  intro history _ bits _ hsummary
  exact run_three_prefix profile history bits hsummary

def decodeInfo (info : PlayerInformation graph (0 : TestPlayer)) : ObservedAbort.Info :=
  ((info.current.2.fieldValue? (node 5) 0).getD false,
    (info.current.1.fieldValue? 4).getD false)

theorem checkpoint_own_visible (bits : TestPlayer → Bool) (signal : Bool) :
    (observe graph (prefixCfg bits signal 3) 0).fieldValue? (node 5) 0 = some (bits 0) := by
  obtain ⟨guard, hguard⟩ : ∃ guard : EventGuard simpleExpr,
      (graph.nodeRow (node 5)).sem = .commit 0 guard := ⟨_, rfl⟩
  have hread : ({field := 0, ty := .bool} : FieldRef simpleExpr) ∈ guard.choiceReads := by
    cases hguard
    decide
  have hnode : graph.node? (node 5) = some (.commit 0 guard) :=
    (graph.node?_nodeRow (node 5)).trans (congrArg some hguard)
  have hty : (graph.fieldRow 0).ty = .bool := rfl
  simp only [observe, hnode, hty, Fin.val_zero,
    dif_pos ((prefix_ready bits signal 3 (node 5)).mpr rfl), dif_pos hread]
  simp [prefixCfg, after_val, hty,
    Config.completeNode, Store.getAs, Store.set, nodeTarget, node, nodeCount, TypedValue.as?]

theorem checkpoint_signal_visible (bits : TestPlayer → Bool) (signal : Bool) :
    (publicObserve graph (prefixCfg bits signal 3)).fieldValue? 4 = some signal := by
  have howner : (graph.fieldRow 4).owner = none := rfl
  have hsource : (graph.fieldRow 4).source = .event 4 := rfl
  have hty : (graph.fieldRow 4).ty = .bool := rfl
  simp only [publicObserve, howner, hsource]
  simp [prefixCfg, hty, Config.completeNode, Config.nodeDone, Config.doneIds,
    Store.getAs, Store.set, nodeTarget, node, nodeCount, fieldCount, TypedValue.as?]

@[simp] theorem decode_prefixInfo (bits : TestPlayer → Bool) (signal : Bool) :
    decodeInfo (prefixInfo bits signal 3) = (bits 0, signal) := by
  simp only [decodeInfo, prefixInfo, snapshot, checkpoint_own_visible,
    checkpoint_signal_visible, Option.getD_some]

def encodeInfo (info : ObservedAbort.Info) : PlayerInformation graph (0 : TestPlayer) :=
  prefixInfo (fun who => if who = 0 then info.1 else false) info.2 3

@[simp] theorem decode_encodeInfo (info : ObservedAbort.Info) :
    decodeInfo (encodeInfo info) = info := by
  simp [encodeInfo]

theorem prefixInfo_encode (bits : TestPlayer → Bool) (signal : Bool) :
    prefixInfo bits signal 3 = encodeInfo (bits 0, signal) :=
  prefixInfo_eq bits _ signal 3 (by simp)

/-- Equality of the complete checkpoint information state is exactly equality
of own bit and public signal, not merely equality of one projection. -/
theorem checkpoint_information_iff (bits other : TestPlayer → Bool) (signal coin : Bool) :
    prefixInfo bits signal 3 = prefixInfo other coin 3 ↔ (bits 0, signal) = (other 0, coin) := by
  constructor
  · intro heq
    simpa only [decode_prefixInfo] using congrArg decodeInfo heq
  · intro heq
    rw [prefixInfo_encode, prefixInfo_encode, heq]

/-- info: 'VegasTests.QuittingSource.checkpoint_summary_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.QuittingSource.checkpoint_summary_law

/-- info: 'VegasTests.QuittingSource.checkpoint_information_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.QuittingSource.checkpoint_information_iff

end VegasTests.QuittingSource
