/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosureLaw

/-! # Realizable disclosure information sites and their legal choices -/

noncomputable section

namespace VegasTests.OptionalDisclosure

open Vegas EventGraph GameTheory GameTheory.Protocol GameTheory.Math.Probability

def liftBinding (law : FinDist Bool) : program.information.BehavioralPolicy 0 := by
  classical
  exact Function.update ((program.defaultPureProfile 0).toBehavioral)
    bindingInfo (law.map bindingChoice)

@[simp] theorem bindingLaw_lift (law : FinDist Bool) : bindingLaw (liftBinding law) = law := by
  classical
  simp only [bindingLaw, liftBinding, Function.update_self, FinDist.map_comp]
  have hinverse : (fun choice => bindingBit choice.1) ∘ bindingChoice = id :=
    funext bindingBit_action
  rw [hinverse, FinDist.map_id]

def bindingProfile (secret : Bool) : ∀ who, program.information.BehavioralPolicy who := by
  classical
  exact Function.update (fun who => (program.defaultPureProfile who).toBehavioral)
    0 (liftBinding (FinDist.pure secret))

theorem coin_supported (signal : Bool) : signal ∈ fairCoin.denote.support := by
  rw [← FinDist.prob_pos_iff]
  unfold fairCoin
  rw [RationalLaw.prob_denote]
  dsimp
  rw [Fin.sum_univ_two]
  cases signal <;> norm_num

/-- Every proposed binding/signal information site has a real protocol history,
not just a syntactically constructible information value. -/
theorem opening_site_realizable (secret signal : Bool) :
    ∃ history : program.execution.History,
      ownerSummary history = checkpointSummary secret signal 3 := by
  classical
  have hlaw : (program.information.runBehavioral (bindingProfile secret) 4).map ownerSummary =
      fairCoin.denote.map (fun coin => checkpointSummary secret coin 3) := by
    rw [opening_checkpoint_law]
    simp only [bindingProfile, Function.update_self, bindingLaw_lift, FinDist.pure_bind]
  have hmem : checkpointSummary secret signal 3 ∈
      ((program.information.runBehavioral (bindingProfile secret) 4).map ownerSummary).support := by
    rw [hlaw, FinDist.support_map]
    exact ⟨signal, coin_supported signal, rfl⟩
  rw [FinDist.support_map] at hmem
  obtain ⟨history, _, hhistory⟩ := hmem
  exact ⟨history, hhistory⟩

theorem opening_choice_exhaustive (history : program.execution.History) (data : RunData)
    (hstate : history.state.1 = cfg data 4)
    (choice : program.information.Choice 0 (program.information.infoOf 0 history.trace)) :
    ∃ opening, (opening = none ∨ opening = some data.secret) ∧
      choice.1 = some (openingAction opening) := by
  have hlocal := (program.information.menu_adequate 0 history.trace choice.1).mp choice.2
  have hactive : program.execution.active history.state 0 := by
    change EventGraph.ActiveAt graph history.state.1 0
    rw [hstate, active_iff]
    simp
  obtain ⟨packet, hpacket⟩ := LegalOption.exists_eq_some_of_active choice.1 hlocal hactive
  rw [hpacket] at hlocal
  have havailable : FrontierAction.Available graph (cfg data 4) 0 packet := hstate ▸ hlocal.2
  obtain ⟨opening, hopening, rfl⟩ := opening_action_exhaustive data packet havailable
  exact ⟨opening, hopening, hpacket⟩

def openingChoice (history : program.execution.History) (data : RunData)
    (hstate : history.state.1 = cfg data 4) (opening : Option Bool)
    (hopening : opening = none ∨ opening = some data.secret) :
    program.information.Choice 0 (program.information.infoOf 0 history.trace) := by
  classical
  refine ⟨some (openingAction opening), ?_⟩
  obtain ⟨prior⟩ := choice_nonempty graph program.graphWF program.guardLive 0
    (program.information.infoOf 0 history.trace)
  have hlocal := (program.information.menu_adequate 0 history.trace prior.1).mp prior.2
  obtain ⟨old, _, hold⟩ := opening_choice_exhaustive history data hstate prior
  rw [hold] at hlocal
  apply (program.information.menu_adequate 0 history.trace _).mpr
  refine ⟨hlocal.1, ?_⟩
  have havailable : FrontierAction.Available graph (cfg data 4) 0 (openingAction old) :=
    hstate ▸ hlocal.2
  change FrontierAction.Available graph history.state.1 0 (openingAction opening)
  rw [hstate]
  exact opening_action_available_of_available data _ havailable opening hopening

def openingChoiceAt (secret signal : Bool) (complete : Bool) :
    program.information.Choice 0 (openingInfo secret signal) := by
  refine ⟨some (openingAction (if complete then some secret else none)), ?_⟩
  obtain ⟨history, hsummary⟩ := opening_site_realizable secret signal
  have hstate : history.state.1 = cfg ⟨secret, signal, none, false⟩ 4 :=
    congrArg Prod.fst hsummary
  have hinfo : program.information.infoOf 0 history.trace = openingInfo secret signal :=
    congrArg Prod.snd hsummary
  have hvalid : (if complete then some secret else none) = none ∨
      (if complete then some secret else none) = some secret := by
    cases complete <;> simp
  have hchoice := (openingChoice history ⟨secret, signal, none, false⟩ hstate _ hvalid).2
  change some (openingAction (if complete then some secret else none)) ∈
    program.information.menu 0 (program.information.infoOf 0 history.trace) at hchoice
  rw [hinfo] at hchoice
  exact hchoice

theorem response_site_realizable (secret signal : Bool) (opening : Option Bool)
    (hvalid : opening = none ∨ opening = some secret) :
    ∃ middle final : program.execution.History,
      middle.state.1 = cfg ⟨secret, signal, opening, false⟩ 5 ∧
      final.state.1 = cfg ⟨secret, signal, opening, false⟩ 6 := by
  classical
  let data : RunData := ⟨secret, signal, none, false⟩
  obtain ⟨history, hsummary⟩ := opening_site_realizable secret signal
  have hstate : history.state.1 = cfg data 4 := congrArg Prod.fst hsummary
  let choice := openingChoice history data hstate opening hvalid
  have hlocal := (program.information.menu_adequate 0 history.trace choice.1).mp choice.2
  let joint := program.execution.singletonJoint 0 choice.1
  have hlegal : program.execution.Legal history.state joint := by
    refine ⟨hlocal.1.1, ?_⟩
    intro who
    by_cases heq : who = 0
    · subst who
      simp only [joint, ExecutionProtocol.singletonJoint_self]
      exact hlocal
    · simp only [joint, ExecutionProtocol.singletonJoint_of_ne _ _ _ heq]
      intro hactive
      have hactive' : EventGraph.ActiveAt graph (cfg data 4) who := hstate ▸ hactive
      have heq' : who = 0 := by simpa [active_iff] using hactive'
      exact heq heq'
  let command := (⟨joint, hlegal⟩ : {joint // program.execution.Legal history.state joint})
  have hselected : openingValue (command.1 0) = opening := by
    simp only [command, joint, ExecutionProtocol.singletonJoint_self]
    exact openingValue_action opening
  obtain ⟨next, hnext⟩ := (program.execution.step history.state command).support_nonempty
  have hn : next.1 = cfg { data with opening := opening } 5 := by
    have hmem : next.1 ∈
        ((program.execution.step history.state command).map Subtype.val).support := by
      rw [FinDist.support_map]
      exact ⟨next, hnext, rfl⟩
    simpa only [opening_step data history.state hstate command, hselected,
      FinDist.mem_support_pure] using hmem
  let middle := history.extend command.2 hnext
  have hterm : ¬ program.execution.terminal middle.state := by
    change ¬ Terminal graph next.1
    rw [hn, terminal_iff]
    decide
  obtain ⟨joint', hlegal'⟩ := program.execution.exists_legal hterm
  let command' := (⟨joint', hlegal'⟩ :
    {joint // program.execution.Legal middle.state joint})
  obtain ⟨last, hlast⟩ := (program.execution.step middle.state command').support_nonempty
  refine ⟨middle, middle.extend command'.2 hlast, hn, ?_⟩
  have hmem : last.1 ∈
      ((program.execution.step middle.state command').map Subtype.val).support := by
    rw [FinDist.support_map]
    exact ⟨last, hlast, rfl⟩
  have hl : last.1 = cfg { data with opening := opening } 6 := by
    simpa only [opening_reveal_protocol_step { data with opening := opening }
      middle.state hn command', FinDist.mem_support_pure] using hmem
  exact hl

def responseChoiceAt (signal : Bool) (opening : Option Bool) (bit : Bool) :
    program.information.Choice 1 (responseInfo signal opening) := by
  refine ⟨some (responseAction bit), ?_⟩
  let data : RunData := ⟨opening.getD false, signal, opening, false⟩
  have hvalid : opening = none ∨ opening = some data.secret := by
    cases opening <;> simp [data]
  obtain ⟨_, history, _, hstate⟩ :=
    response_site_realizable data.secret signal opening hvalid
  have hinfo := response_information history data hstate
  have hchoice := (responseChoice history data hstate bit).2
  change some (responseAction bit) ∈
    program.information.menu 1 (program.information.infoOf 1 history.trace) at hchoice
  rw [hinfo] at hchoice
  exact hchoice

theorem openingChoiceAt_exhaustive (secret signal : Bool)
    (choice : program.information.Choice 0 (openingInfo secret signal)) :
    ∃ complete, choice = openingChoiceAt secret signal complete := by
  obtain ⟨history, hsummary⟩ := opening_site_realizable secret signal
  let data : RunData := ⟨secret, signal, none, false⟩
  have hstate : history.state.1 = cfg data 4 := congrArg Prod.fst hsummary
  have hinfo : program.information.infoOf 0 history.trace = openingInfo secret signal :=
    congrArg Prod.snd hsummary
  have hmember : choice.1 ∈ program.information.menu 0
      (program.information.infoOf 0 history.trace) := by
    rw [hinfo]
    exact choice.2
  obtain ⟨opening, hopening, hchoice⟩ :=
    opening_choice_exhaustive history data hstate ⟨choice.1, hmember⟩
  rcases hopening with rfl | rfl
  · exact ⟨false, Subtype.ext hchoice⟩
  · exact ⟨true, Subtype.ext hchoice⟩

theorem responseChoiceAt_exhaustive (signal : Bool) (opening : Option Bool)
    (choice : program.information.Choice 1 (responseInfo signal opening)) :
    ∃ bit, choice = responseChoiceAt signal opening bit := by
  let data : RunData := ⟨opening.getD false, signal, opening, false⟩
  have hvalid : opening = none ∨ opening = some data.secret := by
    cases opening <;> simp [data]
  obtain ⟨_, history, _, hstate⟩ :=
    response_site_realizable data.secret signal opening hvalid
  have hinfo := response_information history data hstate
  have hmember : choice.1 ∈ program.information.menu 1
      (program.information.infoOf 1 history.trace) := by
    rw [hinfo]
    exact choice.2
  obtain ⟨bit, hchoice⟩ := response_choice_exhaustive history data hstate ⟨choice.1, hmember⟩
  exact ⟨bit, Subtype.ext hchoice⟩

end VegasTests.OptionalDisclosure
