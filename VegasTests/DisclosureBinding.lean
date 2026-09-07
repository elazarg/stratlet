/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosureTrace

/-! # The initial hidden binding of the disclosure encoding -/

noncomputable section

namespace VegasTests.OptionalDisclosure

open Vegas EventGraph GameTheory GameTheory.Protocol GameTheory.Math.Probability

def bindingAction (bit : Bool) : FrontierAction graph (0 : TestPlayer) where
  value? index := if hindex : index = node 0 then
    some (cast (congrArg (fun index => simpleExpr.Val (graph.nodeRow index).ty) hindex.symm)
      bit) else none

theorem binding_ready (who : TestPlayer) (index : Fin graph.nodeCount) :
    ReadyCommitNode graph (Config.initial graph) who index ↔ who = 0 ∧ index = node 0 := by
  change ReadyCommitNode graph (cfg ⟨false, false, none, false⟩ 0) who index ↔ _
  rw [ready_commit_iff]
  constructor
  · rintro ⟨hindex, hwho⟩
    exact ⟨by simpa using hwho, Fin.ext hindex⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, by simp⟩

theorem binding_active (who : TestPlayer) :
    EventGraph.ActiveAt graph (Config.initial graph) who ↔ who = 0 := by
  change EventGraph.ActiveAt graph (cfg ⟨false, false, none, false⟩ 0) who ↔ _
  rw [active_iff]
  simp

theorem binding_available (bit : Bool) :
    FrontierAction.Available graph (Config.initial graph) 0 (bindingAction bit) := by
  intro index
  split
  next hready =>
    have heq := ((binding_ready 0 index).mp hready).2
    subst index
    refine ⟨bit, by simp [bindingAction], ?_⟩
    refine ⟨⟨_, _, rfl, rfl, hready.ready, bit, rfl,
      ⟨fun ref href => False.elim ?_⟩, ?_, rfl⟩⟩
    · change ref ∈ (∅ : Finset (FieldRef simpleExpr)) at href
      exact Finset.notMem_empty ref href
    · change ReadEnv.ofStore? _ ∅ = some _
      simp only [ReadEnv.ofStore?, Finset.notMem_empty, false_implies, implies_true,
        dite_true, Option.some.injEq]
      apply ReadEnv.ext
      intro ref href
      simp at href
  next hnot =>
    have hne : index ≠ node 0 := fun heq => hnot ((binding_ready _ _).mpr ⟨rfl, heq⟩)
    simp [bindingAction, hne]

abbrev bindingInfo := program.information.infoOf 0 program.execution.initHistory.trace

def bindingChoice (bit : Bool) : program.information.Choice 0 bindingInfo :=
  ⟨some (bindingAction bit), (program.information.menu_adequate 0
    program.execution.initHistory.trace _).mpr
      ⟨(binding_active 0).mpr rfl, binding_available bit⟩⟩

def bindingBit (choice : Option (FrontierAction graph (0 : TestPlayer))) : Bool :=
  (choice.bind fun action => action.value? (node 0)).getD false

@[simp] theorem bindingBit_action (bit : Bool) :
    bindingBit (some (bindingAction bit)) = bit := by
  simp [bindingBit, bindingAction]

theorem binding_choice_exhaustive (choice : program.information.Choice 0 bindingInfo) :
    ∃ bit, choice = bindingChoice bit := by
  have hlocal := (program.information.menu_adequate 0
    program.execution.initHistory.trace choice.1).mp choice.2
  obtain ⟨packet, hpacket⟩ := LegalOption.exists_eq_some_of_active choice.1 hlocal
    ((binding_active 0).mpr rfl)
  rw [hpacket] at hlocal
  have havailable : FrontierAction.Available graph (Config.initial graph) 0 packet := hlocal.2
  have hready := (binding_ready 0 (node 0)).mpr ⟨rfl, rfl⟩
  obtain ⟨bit, hbit⟩ := havailable.value?_isSome_iff_readyCommitNode.mpr hready
  refine ⟨bit, Subtype.ext (hpacket.trans (congrArg some ?_))⟩
  have hvalues : packet.value? = (bindingAction bit).value? := by
    funext index
    by_cases heq : index = node 0
    · subst index
      simpa [bindingAction] using hbit
    · have hnot : ¬ ReadyCommitNode graph (Config.initial graph) 0 index := by
        simp [binding_ready, heq]
      have hnone := havailable index
      rw [dif_neg hnot] at hnone
      simpa [bindingAction, heq] using hnone
  cases packet
  exact congrArg FrontierAction.mk hvalues

def bindingChoiceEquiv : Bool ≃ program.information.Choice 0 bindingInfo where
  toFun := bindingChoice
  invFun := fun choice => bindingBit choice.1
  left_inv := bindingBit_action
  right_inv := by
    intro choice
    obtain ⟨bit, rfl⟩ := binding_choice_exhaustive choice
    change bindingChoice (bindingBit (some (bindingAction bit))) = _
    rw [bindingBit_action]

def bindingJoint (bit : Bool) := program.execution.singletonJoint 0 (some (bindingAction bit))

theorem bindingJoint_legal (bit : Bool) :
    program.execution.Legal program.execution.init (bindingJoint bit) := by
  refine ⟨((binding_active 0).mpr rfl).1, ?_⟩
  intro who
  by_cases heq : who = 0
  · subst who
    simp only [bindingJoint, ExecutionProtocol.singletonJoint_self]
    exact ⟨(binding_active 0).mpr rfl, binding_available bit⟩
  · simp only [bindingJoint, ExecutionProtocol.singletonJoint_of_ne _ _ _ heq]
    exact fun h => heq ((binding_active who).mp h)

def afterBinding (bit : Bool) : program.State :=
  applyFrontier graph program.graphWF program.execution.init (bindingJoint bit)

theorem afterBinding_val (bit : Bool) :
    (afterBinding bit).1 = cfg ⟨bit, false, none, false⟩ 1 := by
  classical
  unfold afterBinding
  have horder : [0] ∈ program.serializedSystem.schedules
      (publicObserve graph (Config.initial graph)) := by
    change [0].Nodup ∧ ∀ who : TestPlayer, who ∈ [0] ↔
      EventGraph.ActiveAtView graph (publicObserve graph (Config.initial graph)) who
    refine ⟨by simp, ?_⟩
    intro who
    rw [EventGraph.activeAtView_iff, binding_active]
    simp
  rw [← EventGraph.applySerializedOrder_eq_applyFrontier graph program.graphWF program.guardLive
    program.execution.init (bindingJoint bit) (bindingJoint_legal bit) horder]
  rw [EventGraph.applySerializedOrder_val program.graphWF (bindingJoint bit) program.execution.init
    (fun who packet heq => by
      have hlocal := (bindingJoint_legal bit).2 who
      rw [heq] at hlocal
      exact hlocal.2) (by simp : ([0] : List TestPlayer).Nodup)]
  rfl

def ownerSnapshot (state : Config graph) : LocalSnapshot graph (0 : TestPlayer) :=
  (publicObserve graph state, observe graph state 0)

abbrev OwnerSummary := Config graph × PlayerInformation graph (0 : TestPlayer)

def ownerSummary (history : program.execution.History) : OwnerSummary :=
  (history.state.1, program.information.infoOf 0 history.trace)

def bindingSummary (bit : Bool) : OwnerSummary :=
  (cfg ⟨bit, false, none, false⟩ 1,
    { current := ownerSnapshot (cfg ⟨bit, false, none, false⟩ 1)
      own := [(ownerSnapshot (Config.initial graph), bindingAction bit)] })

def bindingLaw (policy : program.information.BehavioralPolicy 0) : FinDist Bool :=
  (policy bindingInfo).map fun choice => bindingBit choice.1

/-- Every behavioral profile's initial binding law, retaining the owner's
complete information record for the informed disclosure decision. -/
theorem binding_summary_law (profile : ∀ who, program.information.BehavioralPolicy who) :
    (program.information.runBehavioral profile 1).map ownerSummary =
      (bindingLaw (profile 0)).map bindingSummary := by
  have hterm : ¬ program.execution.terminal program.execution.init :=
    ((binding_active 0).mpr rfl).1
  change (program.information.runBehavioralFrom profile 1 program.execution.initHistory).map
    ownerSummary = _
  rw [program.information.runBehavioralFrom_succ_of_not_terminal profile 0
    (h := program.execution.initHistory) hterm,
    FinDist.map_bind, InformationModel.behavioralJoint, FinDist.bind_map]
  have hdrawLaw : ∀ draws : ∀ who,
      program.information.Choice who
        (program.information.infoOf who program.execution.initHistory.trace),
      (program.execution.step program.execution.init
        ⟨fun who => (draws who).1, program.execution.legal_of_legalOption hterm
          (fun who => (program.information.menu_adequate who _ _).mp (draws who).2)⟩).bindOnSupport
          (fun _ realized =>
            (program.information.runBehavioralFrom profile 0
              (program.execution.initHistory.extend
                (program.execution.legal_of_legalOption hterm
                  (fun who => (program.information.menu_adequate who _ _).mp (draws who).2))
                realized)).map ownerSummary) =
      FinDist.pure (bindingSummary (bindingBit (draws 0).1)) := by
    intro draws
    obtain ⟨bit, hbit⟩ := binding_choice_exhaustive (draws 0)
    have hcommand : (fun who => (draws who).1) = bindingJoint bit := by
      funext who
      by_cases heq : who = 0
      · subst who
        rw [hbit]
        rfl
      · have hlocal := (program.information.menu_adequate who
          program.execution.initHistory.trace (draws who).1).mp (draws who).2
        have hn := LegalOption.eq_none_of_inactive (draws who).1 hlocal
          (fun h => heq ((binding_active who).mp h))
        simpa only [bindingJoint, ExecutionProtocol.singletonJoint_of_ne _ _ _ heq] using hn
    let command : {joint // program.execution.Legal program.execution.init joint} :=
      ⟨fun who => (draws who).1, hcommand ▸ bindingJoint_legal bit⟩
    have hstep : program.execution.step program.execution.init command =
        FinDist.pure (afterBinding bit) := by
      change (toExecutionProtocol graph program.graphWF program.guardLive).step _ _ = _
      rw [toExecutionProtocol_step_eq_pure_applyFrontier _ _ _ _ _
        ((binding_active 0).mpr rfl).2.1]
      change FinDist.pure (applyFrontier graph program.graphWF program.execution.init
        (fun who => (draws who).1)) = _
      rw [hcommand]
      rfl
    rw [hbit, show bindingBit (bindingChoice bit).1 = bit from bindingBit_action bit]
    calc
      _ = (program.execution.step program.execution.init command).bind
          (fun _ => FinDist.pure (bindingSummary bit)) := by
        apply FinDist.bindOnSupport_eq_bind_of_eq_on_support
        intro next hnext
        have hn : next = afterBinding bit := by
          change next ∈ (program.execution.step program.execution.init command).support at hnext
          simpa only [hstep, FinDist.mem_support_pure] using hnext
        subst next
        change (FinDist.pure _).map ownerSummary = _
        rw [FinDist.map_pure]
        apply congrArg FinDist.pure
        apply Prod.ext
        · exact afterBinding_val bit
        · change PlayerInformation.push _ (draws 0).1 (ownerSnapshot (afterBinding bit).1) = _
          rw [hbit, afterBinding_val]
          rfl
      _ = _ := FinDist.bind_const _ _
  calc
    _ = (FinDist.pi fun who => profile who
        (program.information.infoOf who program.execution.initHistory.trace)).bind
          (fun draws => FinDist.pure (bindingSummary (bindingBit (draws 0).1))) := by
      apply FinDist.bind_congr
      intro draws _
      rw [FinDist.map_bindOnSupport]
      exact hdrawLaw draws
    _ = _ := by
      rw [← FinDist.map_eq_bind]
      calc
        _ = ((FinDist.pi fun who => profile who
            (program.information.infoOf who program.execution.initHistory.trace)).map
              (fun draws => draws 0)).map
                (fun choice => bindingSummary (bindingBit choice.1)) := by
          rw [FinDist.map_comp]
          rfl
        _ = _ := by
          rw [FinDist.map_apply_pi]
          unfold bindingLaw
          rw [FinDist.map_comp]
          rfl

/-- info: 'VegasTests.OptionalDisclosure.binding_summary_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.binding_summary_law

end VegasTests.OptionalDisclosure
