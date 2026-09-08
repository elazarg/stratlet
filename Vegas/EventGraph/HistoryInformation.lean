/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.Information
import Vegas.EventGraph.Confluence

/-! # Reconstruction of event-graph trace information -/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- An unfinished event's output field is absent in every reachable store. -/
theorem reachable_getAs_nodeTarget_eq_none {G : Graph Player L}
    {cfg : Config G} (hreach : Reachable G cfg) (node : Fin G.nodeCount)
    (hnot : node ∉ cfg.done) (ty : L.Ty) :
    Store.getAs cfg.store (G.nodeTarget node) ty = none := by
  induction hreach with
  | initial =>
      simp [Config.initial, Graph.initialStore, Store.getAs,
        G.field?_nodeTarget (G.nodes_get?_nodeRow node),
        FieldSpec.initialValue?]
  | @step prior next hprior event hnext ih =>
      obtain ⟨written, hnextEq⟩ :=
        stepAvailableEvent_support_completeNode event hnext
      subst next
      have hne : node ≠ event.node := by
        intro heq
        subst node
        exact hnot (Finset.mem_insert_self event.node prior.done)
      rw [Config.completeNode, Store.getAs_set_ne _
        (Config.nodeTarget_ne_of_ne (G := G) hne) written]
      exact ih (fun hdone => hnot (Finset.mem_insert_of_mem hdone))

/-- Visible-store equality at later reachable endpoints reconstructs visible
store equality at equal structural prefixes. -/
theorem VisibleStoreEq.of_extensions {G : Graph Player L} {who : Player}
    {left right laterLeft laterRight : ReachableConfig G}
    (hleft : left.1.Extends laterLeft.1)
    (hright : right.1.Extends laterRight.1)
    (hdone : left.1.done = right.1.done)
    (hlater : VisibleStoreEq who laterLeft.1 laterRight.1) :
    VisibleStoreEq who left.1 right.1 := by
  intro field hvisible
  by_cases hinitial : (field : Nat) < G.initialFields.length
  · rw [reachable_getAs_of_initial_field left.2 hinitial,
      reachable_getAs_of_initial_field right.2 hinitial]
  · have hnodeLt : (field : Nat) - G.initialFields.length < G.nodeCount := by
      have hfieldLt := field.isLt
      unfold Graph.fieldCount at hfieldLt
      omega
    let node : Fin G.nodeCount :=
      ⟨(field : Nat) - G.initialFields.length, hnodeLt⟩
    have htarget : G.nodeTarget node = (field : Nat) := by
      unfold Graph.nodeTarget
      dsimp [node]
      omega
    by_cases hdoneLeft : node ∈ left.1.done
    · have hdoneRight : node ∈ right.1.done := hdone ▸ hdoneLeft
      have hsettledLeft : left.1.FieldSettled field := by
        intro other hother heq
        have heqNode : other = node := by
          apply Fin.ext
          unfold Graph.nodeTarget at heq htarget
          omega
        exact hother (heqNode ▸ hdoneLeft)
      have hsettledRight : right.1.FieldSettled field := by
        intro other hother heq
        have heqNode : other = node := by
          apply Fin.ext
          unfold Graph.nodeTarget at heq htarget
          omega
        exact hother (heqNode ▸ hdoneRight)
      rw [← hleft.getAs field (G.fieldRow field).ty hsettledLeft,
        ← hright.getAs field (G.fieldRow field).ty hsettledRight]
      exact hlater field hvisible
    · have hdoneRight : node ∉ right.1.done := by
        simpa only [← hdone] using hdoneLeft
      rw [← htarget,
        reachable_getAs_nodeTarget_eq_none left.2 node hdoneLeft,
        reachable_getAs_nodeTarget_eq_none right.2 node hdoneRight]

variable [Fintype Player]

theorem applyFrontier_getAs_of_value {G : Graph Player L} (hwf : G.WF)
    (state : ReachableConfig G)
    (joint : ∀ who, Option (FrontierAction G who))
    (havailable : ∀ who action, joint who = some action →
      FrontierAction.Available G state.1 who action)
    {who : Player} {action : FrontierAction G who}
    (haction : joint who = some action) {node : Fin G.nodeCount}
    {value : L.Val (G.nodeRow node).ty}
    (hvalue : action.value? node = some value) :
    Store.getAs (applyFrontier G hwf state joint).1.store
      (G.nodeTarget node) (G.nodeRow node).ty = some value := by
  rw [applyFrontier_val_of_available G hwf state joint havailable]
  have hmem : (node, G.nodeTypedValue node value) ∈
      roundWrites joint (Finset.univ.toList : List Player) :=
    (mem_roundWrites_iff joint _ _).mpr ⟨who, by simp,
      (mem_playerWrites_iff joint who _).mpr ⟨action, haction,
        (mem_actionWrites_iff action _).mpr ⟨value, hvalue, rfl⟩⟩⟩
  rw [Config.completeNodes_getAs_of_mem state.1 _
    (roundWrites_nodes_nodup havailable Finset.univ.nodup_toList)
    hmem]
  simp [Graph.nodeTypedValue, TypedValue.as?]

/-- A raw transition's terminal visible store determines the acting player's
frontier packet and reconstructs the visible store at its predecessor. -/
theorem protocolStep_visible_injective {G : Graph Player L} (hwf : G.WF)
    (hguards : GuardLive G) (who : Player)
    {left right nextLeft nextRight : ReachableConfig G}
    (leftCommand : {joint // (toExecutionProtocol G hwf hguards).Legal left joint})
    (rightCommand : {joint // (toExecutionProtocol G hwf hguards).Legal right joint})
    (leftRealized : nextLeft ∈
      ((toExecutionProtocol G hwf hguards).step left leftCommand).support)
    (rightRealized : nextRight ∈
      ((toExecutionProtocol G hwf hguards).step right rightCommand).support)
    (hdone : left.1.done = right.1.done)
    (hvisible : VisibleStoreEq who nextLeft.1 nextRight.1) :
    VisibleStoreEq who left.1 right.1 ∧
      leftCommand.1 who = rightCommand.1 who := by
  have hpriorVisible := VisibleStoreEq.of_extensions
    (extends_of_toExecutionProtocol_step G hwf hguards left leftCommand leftRealized)
    (extends_of_toExecutionProtocol_step G hwf hguards right rightCommand rightRealized)
    hdone hvisible
  refine ⟨hpriorVisible, ?_⟩
  have hactive : (toExecutionProtocol G hwf hguards).active left who ↔
      (toExecutionProtocol G hwf hguards).active right who := by
    change (¬Terminal G left.1 ∧ readyInternalNodes G left.1 = ∅ ∧
      who ∈ activePlayers G left.1) ↔
      (¬Terminal G right.1 ∧ readyInternalNodes G right.1 = ∅ ∧
        who ∈ activePlayers G right.1)
    rw [readyInternalNodes_eq_of_done_eq hdone,
      show activePlayers G left.1 = activePlayers G right.1 by
        unfold activePlayers
        congr 1
        funext actor
        exact congrArg Finset.Nonempty
          (readyCommitNodes_eq_of_done_eq hdone actor)]
    simp only [Terminal, hdone]
  have hlocalLeft := leftCommand.2.2 who
  have hlocalRight := rightCommand.2.2 who
  cases hleft : leftCommand.1 who with
  | none =>
      cases hright : rightCommand.1 who with
      | none => rfl
      | some rightAction =>
          rw [hleft] at hlocalLeft
          rw [hright] at hlocalRight
          exact False.elim (hlocalLeft (hactive.mpr hlocalRight.1))
  | some leftAction =>
      cases hright : rightCommand.1 who with
      | none =>
          rw [hleft] at hlocalLeft
          rw [hright] at hlocalRight
          exact False.elim (hlocalRight (hactive.mp hlocalLeft.1))
      | some rightAction =>
          rw [hleft] at hlocalLeft
          rw [hright] at hlocalRight
          apply congrArg some
          apply congrArg FrontierAction.mk
          funext node
          have hleftAvailable := hlocalLeft.2
          have hrightAvailable := hlocalRight.2
          have hreadyEq : ReadyCommitNode G left.1 who node ↔
              ReadyCommitNode G right.1 who node := by
            simp only [ReadyCommitNode, Ready, hdone]
          cases hleftValue : leftAction.value? node with
          | none =>
              cases hrightValue : rightAction.value? node with
              | none => rfl
              | some value =>
                  have hreadyRight :=
                    hrightAvailable.readyCommitNode_of_value hrightValue
                  obtain ⟨leftValue, hsome⟩ :=
                    hleftAvailable.value?_isSome_iff_readyCommitNode.mpr
                      (hreadyEq.mpr hreadyRight)
                  rw [hleftValue] at hsome
                  cases hsome
          | some leftValue =>
              have hreadyLeft :=
                hleftAvailable.readyCommitNode_of_value hleftValue
              obtain ⟨rightValue, hrightValue⟩ :=
                hrightAvailable.value?_isSome_iff_readyCommitNode.mpr
                  (hreadyEq.mp hreadyLeft)
              rw [hrightValue]
              congr 1
              have hnoInternalLeft : readyInternalNodes G left.1 = ∅ :=
                hlocalLeft.1.2.1
              have hnoInternalRight : readyInternalNodes G right.1 = ∅ :=
                hlocalRight.1.2.1
              rw [toExecutionProtocol_step_eq_pure_applyFrontier
                G hwf hguards left leftCommand hnoInternalLeft,
                FinDist.mem_support_pure] at leftRealized
              rw [toExecutionProtocol_step_eq_pure_applyFrontier
                G hwf hguards right rightCommand hnoInternalRight,
                FinDist.mem_support_pure] at rightRealized
              subst nextLeft
              subst nextRight
              have havailableLeft : ∀ actor action,
                  leftCommand.1 actor = some action →
                    FrontierAction.Available G left.1 actor action := by
                intro actor action haction
                have hlocal := leftCommand.2.2 actor
                rw [haction] at hlocal
                exact hlocal.2
              have havailableRight : ∀ actor action,
                  rightCommand.1 actor = some action →
                    FrontierAction.Available G right.1 actor action := by
                intro actor action haction
                have hlocal := rightCommand.2.2 actor
                rw [haction] at hlocal
                exact hlocal.2
              have hrowOwner : (G.nodeRow node).owner = some who := by
                rcases hreadyLeft with ⟨row, guard, hrow, hsem, _⟩
                have hnodeWF := hwf (node : Nat) row hrow
                unfold Graph.nodeWFAt at hnodeWF
                rw [hsem] at hnodeWF
                have hrowEq : row = G.nodeRow node := by
                  have hrowGet : G.nodes[(node : Nat)]? = some row := hrow
                  rw [G.nodes_get?_nodeRow node] at hrowGet
                  exact (Option.some.inj hrowGet).symm
                simpa [hrowEq] using hnodeWF.2.2.1
              have hfieldOwner :
                  (G.fieldRow ⟨G.nodeTarget node,
                    StateSnapshot.nodeTarget_lt_fieldCount G node⟩).owner =
                    some who := by
                rw [StateSnapshot.fieldRow_nodeTarget G node]
                exact hrowOwner
              have hstoreEq := hvisible
                ⟨G.nodeTarget node,
                  StateSnapshot.nodeTarget_lt_fieldCount G node⟩
                (Or.inr hfieldOwner)
              rw [StateSnapshot.fieldRow_nodeTarget G node] at hstoreEq
              rw [applyFrontier_getAs_of_value hwf left leftCommand.1
                  havailableLeft hleft hleftValue,
                applyFrontier_getAs_of_value hwf right rightCommand.1
                  havailableRight hright hrightValue] at hstoreEq
              exact Option.some.inj hstoreEq

/-- For the canonical raw graph protocol, trace length and the terminal
complete visible store determine the player's entire perfect-recall
information, including every earlier own frontier packet. -/
theorem infoOf_eq_of_length_eq_of_visibleStoreEq
    {G : Graph Player L} (hwf : G.WF) (hguards : GuardLive G) (who : Player)
    {left right : ReachableConfig G}
    (first : (toExecutionProtocol G hwf hguards).Trace left)
    (second : (toExecutionProtocol G hwf hguards).Trace right)
    (hlength : first.length = second.length)
    (hvisible : VisibleStoreEq who left.1 right.1) :
    (toInfoSignals G hwf hguards).infoOf who first =
      (toInfoSignals G hwf hguards).infoOf who second := by
  let motive := fun (left : ReachableConfig G)
      (first : (toExecutionProtocol G hwf hguards).Trace left) =>
    ∀ {right : ReachableConfig G}
      (second : (toExecutionProtocol G hwf hguards).Trace right),
      first.length = second.length →
      VisibleStoreEq who left.1 right.1 →
      (toInfoSignals G hwf hguards).infoOf who first =
        (toInfoSignals G hwf hguards).infoOf who second
  apply (@GameTheory.Protocol.ExecutionProtocol.Trace.rec Player
    (toExecutionProtocol G hwf hguards) motive)
  · intro right second hlength hvisible
    exact @GameTheory.Protocol.ExecutionProtocol.Trace.rec Player
      (toExecutionProtocol G hwf hguards)
      (fun right second =>
        (ExecutionProtocol.Trace.start :
          (toExecutionProtocol G hwf hguards).Trace _).length = second.length →
        VisibleStoreEq who (Config.initial G) right.1 →
        (toInfoSignals G hwf hguards).infoOf who .start =
          (toInfoSignals G hwf hguards).infoOf who second)
      (by intro _ _; rfl)
      (by
        intro source target prior joint legal realized ih hlength _
        simp only [ExecutionProtocol.Trace.length] at hlength
        omega)
      right second hlength hvisible
  · intro source target prior joint legal realized ih right second hlength
      hvisible
    exact @GameTheory.Protocol.ExecutionProtocol.Trace.rec Player
      (toExecutionProtocol G hwf hguards)
      (fun right second =>
        (prior.extend joint legal realized).length = second.length →
        VisibleStoreEq who target.1 right.1 →
        (toInfoSignals G hwf hguards).infoOf who
            (prior.extend joint legal realized) =
          (toInfoSignals G hwf hguards).infoOf who second)
      (by
        intro hlength _
        simp only [ExecutionProtocol.Trace.length] at hlength
        omega)
      (by
        intro secondSource secondTarget secondPrior secondJoint secondLegal
          secondRealized _ih hlength hvisible
        have hpriorLength : prior.length = secondPrior.length := by
          simpa only [ExecutionProtocol.Trace.length, Nat.add_right_cancel_iff]
            using hlength
        have hpriorDone : source.1.done = secondSource.1.done := by
          rw [toExecutionProtocol_trace_done G hwf hguards prior,
            toExecutionProtocol_trace_done G hwf hguards secondPrior,
            hpriorLength]
        obtain ⟨hpriorVisible, hchoice⟩ :=
          protocolStep_visible_injective hwf hguards who
            ⟨joint, legal⟩ ⟨secondJoint, secondLegal⟩ realized secondRealized
            hpriorDone hvisible
        have hpriorInfo := ih secondPrior hpriorLength hpriorVisible
        have htargetDone : target.1.done = secondTarget.1.done := by
          rw [toExecutionProtocol_trace_done G hwf hguards
              (.extend prior joint legal realized),
            toExecutionProtocol_trace_done G hwf hguards
              (.extend secondPrior secondJoint secondLegal secondRealized),
            hlength]
        have hcurrent := localSnapshot_eq_of_visibleStoreEq hwf who
          htargetDone hvisible
        change joint who = secondJoint who at hchoice
        rw [InfoSignals.infoOf_extend, InfoSignals.infoOf_extend]
        change PlayerInformation.push _ (joint who)
            (publicObserve G target.1, observe G target.1 who) =
          PlayerInformation.push _ (secondJoint who)
            (publicObserve G secondTarget.1, observe G secondTarget.1 who)
        rw [hpriorInfo, hchoice, hcurrent])
      right second hlength hvisible
  · exact hlength
  · exact hvisible

/-- A fixed owned commit node can be ready at only one canonical raw-trace
depth. Thus source decision sites do not need an additional checkpoint-time
index when related to graph histories. -/
theorem trace_length_eq_of_readyCommitNode
    {G : Graph Player L} (hwf : G.WF) (hguards : GuardLive G)
    (who : Player) (node : Fin G.nodeCount)
    {left right : ReachableConfig G}
    (first : (toExecutionProtocol G hwf hguards).Trace left)
    (second : (toExecutionProtocol G hwf hguards).Trace right)
    (hreadyLeft : ReadyCommitNode G left.1 who node)
    (hreadyRight : ReadyCommitNode G right.1 who node)
    (hactiveLeft : (toExecutionProtocol G hwf hguards).active left who)
    (hactiveRight : (toExecutionProtocol G hwf hguards).active right who) :
    first.length = second.length := by
  apply Nat.le_antisymm
  · by_contra hnot
    have hlt : second.length < first.length := by omega
    have hnextLe : second.length + 1 ≤ first.length := by omega
    have hdoneSecond := toExecutionProtocol_trace_done G hwf hguards second
    have hdoneFirst := toExecutionProtocol_trace_done G hwf hguards first
    have hmemNext : node ∈ protocolDoneAt G (second.length + 1) := by
      change node ∈ protocolDoneStep G (protocolDoneAt G second.length)
      rw [← hdoneSecond]
      exact hreadyRight.mem_protocolDoneStep_of_no_internal hactiveRight.2.1
    have hmemFirst := protocolDoneAt_monotone G hnextLe hmemNext
    rw [← hdoneFirst] at hmemFirst
    exact hreadyLeft.ready.1 hmemFirst
  · by_contra hnot
    have hlt : first.length < second.length := by omega
    have hnextLe : first.length + 1 ≤ second.length := by omega
    have hdoneFirst := toExecutionProtocol_trace_done G hwf hguards first
    have hdoneSecond := toExecutionProtocol_trace_done G hwf hguards second
    have hmemNext : node ∈ protocolDoneAt G (first.length + 1) := by
      change node ∈ protocolDoneStep G (protocolDoneAt G first.length)
      rw [← hdoneFirst]
      exact hreadyLeft.mem_protocolDoneStep_of_no_internal hactiveLeft.2.1
    have hmemSecond := protocolDoneAt_monotone G hnextLe hmemNext
    rw [← hdoneSecond] at hmemSecond
    exact hreadyRight.ready.1 hmemSecond

end Vegas.EventGraph
