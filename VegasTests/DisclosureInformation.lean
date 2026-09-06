/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.Recall
import VegasTests.DisclosureTrace

/-! # Full responder information at optional disclosure -/

noncomputable section

namespace VegasTests.OptionalDisclosure

open Vegas EventGraph GameTheory GameTheory.Protocol GameTheory.Math.Probability

def responseSnapshot (state : Config graph) : LocalSnapshot graph (1 : TestPlayer) :=
  (publicObserve graph state, observe graph state 1)

theorem response_snapshot_eq_of_store (left right : Config graph)
    (hdone : left.done = right.done)
    (hstore : ∀ field, field ≠ 0 → left.store field = right.store field) :
    responseSnapshot left = responseSnapshot right := by
  unfold responseSnapshot
  have hread (field : Nat) (ty : simpleExpr.Ty) (hne : field ≠ 0) :
      Store.getAs left.store field ty = Store.getAs right.store field ty := by
    simp only [Store.getAs, hstore field hne]
  apply Prod.ext
  · apply PublicObservation.ext hdone
    intro field
    by_cases heq : field = 0
    · subst field
      rw [original_absent_from_public, original_absent_from_public]
    · have hne : field.val ≠ 0 := fun h => heq (Fin.ext h)
      simp only [publicObserve, Config.nodeDone, Config.doneIds, hdone, hread _ _ hne]
  · apply Observation.ext
    · ext index
      simp only [observe, Finset.mem_filter, Finset.mem_univ, true_and]
      cases hnode : graph.node? index with
      | none => simp
      | some sem => cases sem <;> simp [Ready, hdone]
    · intro index field
      by_cases heq : field = 0
      · subst field
        rw [original_absent_from_response, original_absent_from_response]
      · have hne : field.val ≠ 0 := fun h => heq (Fin.ext h)
        simp only [observe, Ready, hdone, hread _ _ hne]

/-- The reply is the responder's first decision, for every actual history
ending at that checkpoint, independently of the players' policies. -/
theorem response_own_empty (history : program.execution.History) (data : RunData)
    (hstate : history.state.1 = cfg data 6) :
    (program.information.infoOf 1 history.trace).own = [] := by
  apply own_eq_nil_of_no_completed_choice graph program.graphWF program.guardLive 1 history.trace
  intro index row guard hrow hsem
  have heq : row = graph.nodeRow index :=
    Option.some.inj (hrow.symm.trans (graph.nodes_get?_nodeRow index))
  subst row
  fin_cases index <;> cases hsem
  rw [hstate]
  change node 6 ∉ (cfg ⟨false, false, none, false⟩ 6).done
  decide

theorem response_snapshot_eq (data other : RunData)
    (hsignal : data.signal = other.signal) (hopening : data.opening = other.opening) :
    responseSnapshot (cfg data 6) = responseSnapshot (cfg other 6) := by
  apply response_snapshot_eq_of_store
  · rfl
  · intro field hfield
    simp [cfg, show List.finRange 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl,
      Config.completeNodes, Config.completeNode, Store.set, Graph.nodeTarget, node,
      show graph.initialFields.length = 0 from rfl,
      RunData.value, hfield, hsignal, hopening]

theorem response_signal_visible (data : RunData) :
    (publicObserve graph (cfg data 6)).fieldValue? 3 = some data.signal := by
  have howner : (graph.fieldRow 3).owner = none := rfl
  have hsource : (graph.fieldRow 3).source = .event 3 := rfl
  simp only [publicObserve, howner, hsource]
  have hdone : (cfg data 6).nodeDone 3 := by
    change (cfg ⟨false, false, none, false⟩ 6).nodeDone 3
    unfold Config.nodeDone Config.doneIds
    decide
  rw [if_pos hdone]
  rfl

theorem response_opening_visible (data : RunData) :
    (publicObserve graph (cfg data 6)).fieldValue? 5 = some data.opening := by
  have howner : (graph.fieldRow 5).owner = none := rfl
  have hsource : (graph.fieldRow 5).source = .event 5 := rfl
  simp only [publicObserve, howner, hsource]
  have hdone : (cfg data 6).nodeDone 5 := by
    change (cfg ⟨false, false, none, false⟩ 6).nodeDone 5
    unfold Config.nodeDone Config.doneIds
    decide
  rw [if_pos hdone]
  rfl

/-- Canonical full information at the reply checkpoint; the original binding
is not a parameter. `none` remains publicly distinguishable from an opening. -/
def responseInfo (signal : Bool) (opening : Option Bool) :
    PlayerInformation graph (1 : TestPlayer) where
  current := responseSnapshot (cfg ⟨false, signal, opening, false⟩ 6)
  own := []

def decodeResponseInfo (info : PlayerInformation graph (1 : TestPlayer)) :
    Bool × Option Bool :=
  ((info.current.1.fieldValue? 3).getD false, (info.current.1.fieldValue? 5).getD none)

@[simp] theorem decode_responseInfo (signal : Bool) (opening : Option Bool) :
    decodeResponseInfo (responseInfo signal opening) = (signal, opening) := by
  simp only [decodeResponseInfo, responseInfo, responseSnapshot,
    response_signal_visible, response_opening_visible, Option.getD_some]

/-- Every actual history at the reply checkpoint has this complete information
state, not just this public projection. -/
theorem response_information (history : program.execution.History) (data : RunData)
    (hstate : history.state.1 = cfg data 6) :
    program.information.infoOf 1 history.trace = responseInfo data.signal data.opening := by
  apply PlayerInformation.ext
  · change ((toInfoSignals graph program.graphWF program.guardLive).infoOf 1
      history.trace).current = _
    rw [infoOf_toInfoSignals_current, hstate]
    exact response_snapshot_eq data ⟨false, data.signal, data.opening, false⟩ rfl rfl
  · exact response_own_empty history data hstate

theorem response_information_iff (left right : program.execution.History)
    (data other : RunData) (hleft : left.state.1 = cfg data 6)
    (hright : right.state.1 = cfg other 6) :
    program.information.infoOf 1 left.trace = program.information.infoOf 1 right.trace ↔
      (data.signal, data.opening) = (other.signal, other.opening) := by
  rw [response_information left data hleft, response_information right other hright]
  constructor
  · intro heq
    simpa only [decode_responseInfo] using congrArg decodeResponseInfo heq
  · intro heq
    cases Prod.mk.inj heq with
    | intro hsignal hopening => rw [hsignal, hopening]

def responseAction (bit : Bool) : FrontierAction graph (1 : TestPlayer) where
  value? index := if hindex : index = node 6 then
    some (cast (congrArg (fun index => simpleExpr.Val (graph.nodeRow index).ty) hindex.symm)
      bit) else none

def responseBit (choice : Option (FrontierAction graph (1 : TestPlayer))) : Bool :=
  (choice.bind fun action => action.value? (node 6)).getD false

theorem response_action_exhaustive (data : RunData)
    (packet : FrontierAction graph (1 : TestPlayer))
    (havailable : FrontierAction.Available graph (cfg data 6) 1 packet) :
    ∃ bit, packet = responseAction bit := by
  have hready : ReadyCommitNode graph (cfg data 6) 1 (node 6) :=
    (ready_commit_iff _ _ _ _).mpr ⟨rfl, by simp⟩
  obtain ⟨value, hvalue⟩ := havailable.value?_isSome_iff_readyCommitNode.mpr hready
  refine ⟨value, ?_⟩
  have hvalues : packet.value? = (responseAction value).value? := by
    funext index
    by_cases heq : index = node 6
    · subst index
      simpa [responseAction] using hvalue
    · have hnot : ¬ ReadyCommitNode graph (cfg data 6) 1 index := by
        intro h
        exact heq (Fin.ext ((ready_commit_iff _ _ _ _).mp h).1)
      have hnone := havailable index
      rw [dif_neg hnot] at hnone
      simpa [responseAction, heq] using hnone
  cases packet
  exact congrArg FrontierAction.mk hvalues

theorem response_choice_exhaustive (history : program.execution.History) (data : RunData)
    (hstate : history.state.1 = cfg data 6)
    (choice : program.information.Choice 1 (program.information.infoOf 1 history.trace)) :
    ∃ bit, choice.1 = some (responseAction bit) := by
  have hlocal := (program.information.menu_adequate 1 history.trace choice.1).mp choice.2
  have hactive : program.execution.active history.state 1 := by
    change Compiled.ActiveAt graph history.state.1 1
    rw [hstate, active_iff]
    simp
  obtain ⟨packet, hpacket⟩ := LegalOption.exists_eq_some_of_active choice.1 hlocal hactive
  rw [hpacket] at hlocal
  have havailable : FrontierAction.Available graph (cfg data 6) 1 packet := hstate ▸ hlocal.2
  obtain ⟨bit, rfl⟩ := response_action_exhaustive data packet havailable
  exact ⟨bit, hpacket⟩

def responseLaw (policy : program.information.BehavioralPolicy 1)
    (signal : Bool) (opening : Option Bool) : FinDist Bool :=
  (policy (responseInfo signal opening)).map fun choice => responseBit choice.1

theorem response_action_available_of_available (data : RunData)
    (packet : FrontierAction graph (1 : TestPlayer))
    (havailable : FrontierAction.Available graph (cfg data 6) 1 packet) (bit : Bool) :
    FrontierAction.Available graph (cfg data 6) 1 (responseAction bit) := by
  intro index
  split
  next hready =>
    have hindex : index = node 6 := Fin.ext ((ready_commit_iff _ _ _ _).mp hready).1
    subst index
    refine ⟨bit, by simp [responseAction], ?_⟩
    have hslot := havailable (node 6)
    rw [dif_pos hready] at hslot
    obtain ⟨_, _, ⟨row, guard, hrow, hsem, _, _, _, env, henv, _⟩⟩ := hslot
    have heq : row = graph.nodeRow (node 6) :=
      Option.some.inj (hrow.symm.trans (graph.nodes_get?_nodeRow (node 6)))
    subst row
    cases hsem
    exact ⟨⟨_, _, rfl, rfl, hready.ready, bit, rfl, env, henv, rfl⟩⟩
  next hnot =>
    have hne : index ≠ node 6 := by
      rintro rfl
      exact hnot ((ready_commit_iff _ _ _ _).mpr ⟨rfl, by simp⟩)
    simp [responseAction, hne]

/-- Both Boolean replies remain available at every actual reply checkpoint. -/
def responseChoice (history : program.execution.History) (data : RunData)
    (hstate : history.state.1 = cfg data 6) (bit : Bool) :
    program.information.Choice 1 (program.information.infoOf 1 history.trace) := by
  classical
  refine ⟨some (responseAction bit), ?_⟩
  obtain ⟨prior⟩ := choice_nonempty graph program.graphWF program.guardLive 1
    (program.information.infoOf 1 history.trace)
  have hlocal := (program.information.menu_adequate 1 history.trace prior.1).mp prior.2
  obtain ⟨old, hold⟩ := response_choice_exhaustive history data hstate prior
  rw [hold] at hlocal
  apply (program.information.menu_adequate 1 history.trace _).mpr
  refine ⟨hlocal.1, ?_⟩
  have havailable : FrontierAction.Available graph (cfg data 6) 1 (responseAction old) :=
    hstate ▸ hlocal.2
  change FrontierAction.Available graph history.state.1 1 (responseAction bit)
  rw [hstate]
  exact response_action_available_of_available data _ havailable bit

@[simp] theorem responseBit_action (bit : Bool) :
    responseBit (some (responseAction bit)) = bit := by
  simp [responseBit, responseAction]

theorem response_choice_roundtrip (history : program.execution.History) (data : RunData)
    (hstate : history.state.1 = cfg data 6)
    (choice : program.information.Choice 1 (program.information.infoOf 1 history.trace)) :
    responseChoice history data hstate (responseBit choice.1) = choice := by
  obtain ⟨bit, hbit⟩ := response_choice_exhaustive history data hstate choice
  apply Subtype.ext
  change some (responseAction (responseBit choice.1)) = choice.1
  rw [hbit, responseBit_action]

def responseChoiceEquiv (history : program.execution.History) (data : RunData)
    (hstate : history.state.1 = cfg data 6) :
    Bool ≃ program.information.Choice 1 (program.information.infoOf 1 history.trace) where
  toFun := responseChoice history data hstate
  invFun := fun choice => responseBit choice.1
  left_inv := fun bit => responseBit_action bit
  right_inv := response_choice_roundtrip history data hstate

/-- Every behavioral responder policy factors through the stated information
at every actual reply checkpoint, including off-equilibrium histories. -/
theorem response_policy_factors (policy : program.information.BehavioralPolicy 1)
    (history : program.execution.History) (data : RunData)
    (hstate : history.state.1 = cfg data 6) :
    ((policy (program.information.infoOf 1 history.trace)).map
      fun choice => responseBit choice.1) = responseLaw policy data.signal data.opening := by
  exact congrArg (fun info => (policy info).map fun choice => responseBit choice.1)
    (response_information history data hstate)

/-- info: 'VegasTests.OptionalDisclosure.response_information_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.response_information_iff

/-- info: 'VegasTests.OptionalDisclosure.response_choice_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.OptionalDisclosure.response_choice_roundtrip

end VegasTests.OptionalDisclosure
