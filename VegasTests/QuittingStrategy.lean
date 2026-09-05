/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.QuittingLaw

/-! # Initial strategies of the compiled staged source -/

noncomputable section

namespace VegasTests.QuittingSource

open Vegas EventGraph GameTheory GameTheory.Protocol GameTheory.Math.Probability

theorem node_ty (index : Fin graph.nodeCount) : (graph.nodeRow index).ty = .bool := by
  fin_cases index <;> rfl

theorem ready_initial (index : Fin graph.nodeCount) :
    Ready graph (Config.initial graph) index ↔ index = node 0 ∨ index = node 1 := by
  fin_cases index <;> decide

theorem ready_initial_iff (who : TestPlayer) (index : Fin graph.nodeCount) :
    ReadyCommitNode graph (Config.initial graph) who index ↔ index.val = who.val := by
  constructor
  · rintro ⟨row, guard, hrow, hsem, hready⟩
    have heq : row = graph.nodeRow index :=
      Option.some.inj (hrow.symm.trans (graph.nodes_get?_nodeRow index))
    subst row
    rcases (ready_initial index).mp hready with h | h <;> subst index
    all_goals exact congrArg Fin.val (NodeSem.commit.inj hsem).1
  · intro heq
    fin_cases who
    · have hindex : index = node 0 := Fin.ext heq
      subst index
      exact ⟨_, _, rfl, rfl, (ready_initial _).mpr (Or.inl rfl)⟩
    · have hindex : index = node 1 := Fin.ext heq
      subst index
      exact ⟨_, _, rfl, rfl, (ready_initial _).mpr (Or.inr rfl)⟩

theorem initial_active (who : TestPlayer) :
    Compiled.ActiveAt graph (Config.initial graph) who := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro hterminal
    simpa [Config.initial] using hterminal (node 0)
  · apply Finset.eq_empty_iff_forall_notMem.mpr
    intro index hindex
    obtain ⟨row, hrow, hsem, hready⟩ := (Finset.mem_filter.mp hindex).2
    have heq : row = graph.nodeRow index :=
      Option.some.inj (hrow.symm.trans (graph.nodes_get?_nodeRow index))
    subst row
    rcases (ready_initial index).mp hready with h | h <;> subst index <;> cases hsem
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ who, ?_⟩
    refine ⟨⟨who.val, Nat.lt_trans who.isLt (by decide)⟩, Finset.mem_filter.mpr ?_⟩
    exact ⟨Finset.mem_univ _, (ready_initial_iff who _).mpr rfl⟩

def action (who : TestPlayer) (bit : Bool) : FrontierAction graph who where
  value? index := if index.val = who.val then
    some (cast (congrArg simpleExpr.Val (node_ty index).symm) bit) else none

theorem action_available (who : TestPlayer) (bit : Bool) :
    FrontierAction.Available graph (Config.initial graph) who (action who bit) := by
  classical
  intro index
  split
  next hready =>
    have heq := (ready_initial_iff who index).mp hready
    refine ⟨cast (congrArg simpleExpr.Val (node_ty index).symm) bit,
      by simp [action, heq], ?_⟩
    fin_cases who <;> fin_cases index <;> norm_num at heq
    all_goals
      refine ⟨⟨_, _, rfl, rfl, hready.ready, bit, ?_,
        ⟨fun ref href => False.elim ?_⟩, ?_, ?_⟩⟩
      · rfl
      · change ref ∈ (∅ : Finset (FieldRef simpleExpr)) at href
        exact Finset.notMem_empty ref href
      · change ReadEnv.ofStore? _ ∅ = some _
        simp only [ReadEnv.ofStore?, Finset.notMem_empty, false_implies, implies_true,
          dite_true, Option.some.injEq]
        apply ReadEnv.ext
        intro ref href
        simp at href
      · rfl
  next hready =>
    simp [action, (ready_initial_iff who index).not.mp hready]

abbrev initialInfo (who : TestPlayer) :=
  program.information.infoOf who program.execution.initHistory.trace

def choice (who : TestPlayer) (bit : Bool) : program.information.Choice who (initialInfo who) :=
  ⟨some (action who bit), (program.information.menu_adequate who
    program.execution.initHistory.trace _).mpr
      ⟨initial_active who, action_available who bit⟩⟩

def ownNode (who : TestPlayer) : Fin graph.nodeCount :=
  ⟨who.val, Nat.lt_trans who.isLt (by decide)⟩

theorem choice_exhaustive (who : TestPlayer)
    (chosen : program.information.Choice who (initialInfo who)) :
    ∃ bit, chosen = choice who bit := by
  classical
  have hlocal := (program.information.menu_adequate who
    program.execution.initHistory.trace chosen.1).mp chosen.2
  obtain ⟨packet, hpacket⟩ := LegalOption.exists_eq_some_of_active chosen.1 hlocal
    (initial_active who)
  rw [hpacket] at hlocal
  have havailable : FrontierAction.Available graph (Config.initial graph) who packet := hlocal.2
  have hready : ReadyCommitNode graph (Config.initial graph) who (ownNode who) :=
    (ready_initial_iff who _).mpr rfl
  have hvalue := havailable (ownNode who)
  rw [dif_pos hready] at hvalue
  obtain ⟨value, hvalue, _⟩ := hvalue
  let bit : Bool := cast (congrArg simpleExpr.Val (node_ty (ownNode who))) value
  refine ⟨bit, Subtype.ext (hpacket.trans (congrArg some ?_))⟩
  have hvalues : packet.value? = (action who bit).value? := by
    funext index
    by_cases heq : index.val = who.val
    · have hindex : index = ownNode who := Fin.ext heq
      subst index
      rw [hvalue]
      simp [action, ownNode, bit]
    · have hnot := (ready_initial_iff who index).not.mpr heq
      have hnone := havailable index
      rw [dif_neg hnot] at hnone
      simpa [action, heq] using hnone
  cases packet
  exact congrArg FrontierAction.mk hvalues

theorem choice_injective (who : TestPlayer) : Function.Injective (choice who) := by
  intro left right heq
  have hvalues := congrArg
    (fun chosen => chosen.1.map (fun packet => packet.value? (ownNode who))) heq
  simp only [choice, Option.map_some, action, ownNode,
    ite_true, Option.some.injEq] at hvalues
  exact (Equiv.cast _).injective hvalues

def choiceEquiv (who : TestPlayer) : Bool ≃ program.information.Choice who (initialInfo who) :=
  Equiv.ofBijective (choice who) ⟨choice_injective who, fun chosen => by
    obtain ⟨bit, hbit⟩ := choice_exhaustive who chosen
    exact ⟨bit, hbit.symm⟩⟩

def joint (bits : TestPlayer → Bool) : ∀ who, Option (FrontierAction graph who) :=
  fun who => some (action who (bits who))

theorem joint_legal (bits : TestPlayer → Bool) :
    program.execution.Legal program.execution.init (joint bits) :=
  ⟨(initial_active 0).1, fun who => ⟨initial_active who, action_available who (bits who)⟩⟩

def after (bits : TestPlayer → Bool) : program.State :=
  applyFrontier graph program.graphWF program.execution.init (joint bits)

theorem after_val (bits : TestPlayer → Bool) :
    (after bits).1 = ((Config.initial graph).completeNode (node 0)
      ⟨.bool, bits 0⟩).completeNode (node 1) ⟨.bool, bits 1⟩ := by
  unfold after
  have horder : [0, 1] ∈ program.serializedSystem.schedules
      (publicObserve graph (Config.initial graph)) := by
    change [0, 1].Nodup ∧ ∀ who : TestPlayer, who ∈ [0, 1] ↔
      Compiled.ActiveAtView graph (publicObserve graph (Config.initial graph)) who
    refine ⟨by decide, ?_⟩
    intro who
    constructor
    · intro _
      exact (Compiled.activeAtView_iff _ _).mpr (initial_active who)
    · intro _
      fin_cases who <;> simp
  rw [← Compiled.applySerializedOrder_eq_applyFrontier graph program.graphWF program.guardLive
    program.execution.init (joint bits) (joint_legal bits) horder]
  rw [Compiled.applySerializedOrder_val program.graphWF (joint bits) program.execution.init
    (fun who packet heq => by
      have hp : packet = action who (bits who) := (Option.some.inj heq).symm
      subst packet
      exact action_available who (bits who)) (by decide : ([0, 1] : List TestPlayer).Nodup)]
  rfl

def bitCompletion (bits : TestPlayer → Bool) : FinDist ObservedAbort.Outcome :=
  ObservedAbort.fair.bind fun signal => ObservedAbort.fair.map fun future =>
    ((bits 0, bits 1), signal, future)

theorem completionLaw_after (bits : TestPlayer → Bool) :
    completionLaw (after bits).1 = bitCompletion bits := by
  rw [after_val]
  simp [completionLaw, coinLaw, Config.completeNode, Config.initial, node, nodeCount,
    readBit, Store.getAs, Store.set, nodeTarget, TypedValue.as?, bitCompletion]

def extractStrategy (who : TestPlayer) (policy : program.information.BehavioralPolicy who) :
    FinDist Bool := (policy (initialInfo who)).map (choiceEquiv who).symm

def liftStrategy (who : TestPlayer) (law : FinDist Bool) :
    program.information.BehavioralPolicy who := by
  classical
  exact Function.update ((program.defaultPureProfile who).toBehavioral)
    (initialInfo who) (law.map (choice who))

@[simp] theorem extract_lift (who : TestPlayer) (law : FinDist Bool) :
    extractStrategy who (liftStrategy who law) = law := by
  classical
  simp only [extractStrategy, liftStrategy, Function.update_self, FinDist.map_comp]
  have hinverse : (choiceEquiv who).symm ∘ choice who = id :=
    funext fun bit => (choiceEquiv who).symm_apply_apply bit
  rw [hinverse, FinDist.map_id]

/-- The compiled source's complete decoded law, for every behavioral profile.
Extraction consults only each player's initial information-local policy. -/
theorem decoded_law
    (profile : ∀ who, program.information.BehavioralPolicy who) :
    (program.terminalStateLaw profile program.execution.initHistory).map
      (fun state => decode state.1) =
    (FinDist.pi fun who => extractStrategy who (profile who)).bind bitCompletion := by
  have hterm : ¬ program.execution.terminal program.execution.init := (initial_active 0).1
  rw [program.terminalStateLaw_step profile _ hterm, FinDist.map_bind,
    InformationModel.behavioralJoint, FinDist.bind_map]
  unfold extractStrategy
  rw [FinDist.pi_map, FinDist.bind_map]
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
  have hstep : (program.execution.step program.execution.init
      ⟨fun who => (draws who).1, hlegal⟩) = FinDist.pure (after bits) := by
    change (toExecutionProtocol graph program.graphWF program.guardLive).step _ _ = _
    rw [toExecutionProtocol_step_eq_pure_applyFrontier _ _ _ _ _ (initial_active 0).2.1]
    change FinDist.pure (applyFrontier graph program.graphWF program.execution.init
      (fun who => (draws who).1)) = _
    rw [hcommand]
    rfl
  rw [FinDist.map_bindOnSupport]
  calc
    _ = (program.execution.step program.execution.init
        ⟨fun who => (draws who).1, hlegal⟩).bind (fun _ => bitCompletion bits) := by
      apply FinDist.bindOnSupport_eq_bind_of_eq_on_support
      intro next hnext
      have heq : next = after bits := by
        change next ∈ (program.execution.step program.execution.init
          ⟨fun who => (draws who).1, hlegal⟩).support at hnext
        simpa only [hstep, FinDist.mem_support_pure] using hnext
      rw [terminal_decode_law profile _ (by
        change ChoicesFixed next.1
        rw [heq, after_val]
        simp [ChoicesFixed, Config.completeNode])]
      change completionLaw next.1 = bitCompletion bits
      rw [heq, completionLaw_after]
    _ = bitCompletion bits := FinDist.bind_const _ _

theorem pi_two (laws : TestPlayer → FinDist Bool) :
    FinDist.pi laws = ((laws 0).product (laws 1)).map (finTwoArrowEquiv Bool).symm := by
  apply FinDist.ext_of_prob
  intro bits
  conv_rhs => rw [show bits = (finTwoArrowEquiv Bool).symm ((finTwoArrowEquiv Bool) bits)
    from ((finTwoArrowEquiv Bool).symm_apply_apply bits).symm]
  rw [FinDist.prob_map_of_injective _ (Equiv.injective _), FinDist.prob_product,
    FinDist.prob_pi]
  simp [Fin.prod_univ_two, finTwoArrowEquiv, piFinTwoEquiv]

theorem decoded_law_eq_kernel
    (profile : ∀ who, program.information.BehavioralPolicy who) :
    (program.game.behavioral.form.play profile).map (fun history => decode history.state.1) =
      ObservedAbort.sourcePlay (fun who => extractStrategy who (profile who)) := by
  change (program.information.runBehavioral profile graph.nodeCount).map _ = _
  calc
    _ =
      (program.terminalStateLaw profile program.execution.initHistory).map
        (fun state => decode state.1) := (FinDist.map_comp _ _ _).symm
    _ = (FinDist.pi fun who => extractStrategy who (profile who)).bind bitCompletion :=
      decoded_law profile
    _ = _ := by
      rw [pi_two, FinDist.bind_map]
      simp only [FinDist.product, FinDist.bind_bind, FinDist.bind_map, bitCompletion,
        ObservedAbort.sourcePlay, ObservedAbort.checkpoints, ObservedAbort.continuation]
      rfl

end VegasTests.QuittingSource
