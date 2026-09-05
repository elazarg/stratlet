/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Scheduled.Skeleton
import Vegas.Scheduled.Replay

/-!
# Immutable observations and compact source information

Values already available in an immutable graph cannot be overwritten by a
later legal event. Together with the structural checkpoint timeline, this
allows earlier observations to be recovered from compact player information.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Vegas.EventGraph

open GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- No unfinished node can write this field. -/
def Config.FieldSettled {G : Graph Player L} (cfg : Config G) (field : Nat) : Prop :=
  ∀ node : Fin G.nodeCount, node ∉ cfg.done → field ≠ G.nodeTarget node

/-- A later configuration retains every field that was already settled. -/
structure Config.Extends {G : Graph Player L} (before after : Config G) : Prop where
  done : before.done ⊆ after.done
  store : ∀ field, before.FieldSettled field → after.store field = before.store field

theorem Config.Extends.refl {G : Graph Player L} (cfg : Config G) : cfg.Extends cfg :=
  ⟨Finset.Subset.refl _, fun _ _ => rfl⟩

theorem Config.FieldSettled.mono {G : Graph Player L} {before after : Config G}
    {field : Nat} (hfield : before.FieldSettled field) (hdone : before.done ⊆ after.done) :
    after.FieldSettled field := by
  intro node hnot
  exact hfield node (fun hmem => hnot (hdone hmem))

theorem Config.Extends.trans {G : Graph Player L} {before middle after : Config G}
    (hfirst : before.Extends middle) (hsecond : middle.Extends after) :
    before.Extends after := by
  refine ⟨hfirst.done.trans hsecond.done, ?_⟩
  intro field hfield
  exact (hsecond.store field (hfield.mono hfirst.done)).trans (hfirst.store field hfield)

theorem Config.Extends.completeNode {G : Graph Player L} {before after : Config G}
    (hextends : before.Extends after) (node : Fin G.nodeCount)
    (hnot : node ∉ before.done) (written : TypedValue L) :
    before.Extends (after.completeNode node written) := by
  refine ⟨hextends.done.trans (Finset.subset_insert _ _), ?_⟩
  intro field hfield
  change Store.set after.store (G.nodeTarget node) written field = before.store field
  rw [Store.set_ne _ (hfield node hnot), hextends.store field hfield]

theorem Config.extends_completeNodes {G : Graph Player L} (before : Config G)
    (steps : List (Fin G.nodeCount × TypedValue L))
    (hnot : ∀ step ∈ steps, step.1 ∉ before.done) :
    before.Extends (before.completeNodes steps) := by
  have helper : ∀ (after : Config G), before.Extends after →
      before.Extends (after.completeNodes steps) := by
    induction steps with
    | nil => intro after hextends; exact hextends
    | cons step rest ih =>
        intro after hextends
        rw [Config.completeNodes_cons]
        exact ih (fun tail htail => hnot tail (List.mem_cons_of_mem _ htail)) _
          (hextends.completeNode step.1 (hnot step (List.mem_cons_self)) step.2)
  exact helper before (Config.Extends.refl before)

theorem Config.Extends.getAs {G : Graph Player L} {before after : Config G}
    (hextends : before.Extends after) (field : Nat) (ty : L.Ty)
    (hfield : before.FieldSettled field) :
    Store.getAs after.store field ty = Store.getAs before.store field ty := by
  simp only [Store.getAs, hextends.store field hfield]

/-- Every read of a ready node is protected from all later writes. -/
theorem Ready.fieldSettled_of_read {G : Graph Player L} (hwf : G.WF)
    {cfg : Config G} {node : Fin G.nodeCount} {event : EventNode Player L}
    (hnode : G.nodes[node]? = some event) (hready : Ready G cfg node)
    {field : Nat} (hread : field ∈ event.sem.reads) : cfg.FieldSettled field := by
  intro other hnot heq
  rw [heq] at hread
  have hother := G.nodes_get?_nodeRow other
  have havailable := (hwf node event hnode).1 (G.nodeTarget other) hread
  unfold Graph.fieldAvailableBefore at havailable
  rw [G.field?_nodeTarget hother] at havailable
  simp only [decide_eq_true_eq] at havailable
  exact hnot (hready.2
    (G.nodeTarget_mem_prereqs_of_read hnode hother havailable hread))

theorem extends_of_stepReadyInternal {G : Graph Player L} (hwf : G.WF)
    (state : ReachableConfig G)
    (hinternal : (readyInternalNodes G state.1).Nonempty)
    {next : ReachableConfig G}
    (hnext : next ∈ (Compiled.stepReadyInternal hwf state hinternal).support) :
    state.1.Extends next.1 := by
  have hraw : next.1 ∈
      ((Compiled.stepReadyInternal hwf state hinternal).map Subtype.val).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  unfold Compiled.stepReadyInternal at hraw
  simp only [map_val_stepAvailable] at hraw
  obtain ⟨written, hwritten⟩ := stepAvailableEvent_support_completeNode _ hraw
  rw [hwritten]
  have hready := (Finset.mem_filter.mp (Classical.choose_spec hinternal)).2
  rcases hready with ⟨row, hrow, hkind, hready⟩
  exact (Config.Extends.refl state.1).completeNode _ hready.1 written

theorem extends_of_settleInternal {G : Graph Player L} (hwf : G.WF)
    (fuel : Nat) (state : ReachableConfig G) {next : ReachableConfig G}
    (hnext : next ∈ (Compiled.settleInternal hwf fuel state).support) :
    state.1.Extends next.1 := by
  induction fuel generalizing state with
  | zero =>
      rw [Compiled.settleInternal_zero, FinDist.mem_support_pure] at hnext
      subst next
      exact Config.Extends.refl _
  | succ fuel ih =>
      unfold Compiled.settleInternal at hnext
      split at hnext
      next hinternal =>
        rw [FinDist.support_bind] at hnext
        obtain ⟨middle, hmiddle, hnext⟩ := Set.mem_iUnion₂.mp hnext
        exact (extends_of_stepReadyInternal hwf state hinternal hmiddle).trans (ih _ hnext)
      next _ =>
        rw [FinDist.mem_support_pure] at hnext
        subst next
        exact Config.Extends.refl _

def Config.fieldAvailable {G : Graph Player L} (cfg : Config G)
    (spec : FieldSpec Player L) : Prop :=
  match spec.source with
  | .initial _ => True
  | .event node => cfg.nodeDone node

theorem Config.fieldSettled_of_available {G : Graph Player L} (cfg : Config G)
    (field : Fin G.fieldCount)
    (havailable : cfg.fieldAvailable (G.fieldRow field)) : cfg.FieldSettled field := by
  intro other hnot heq
  have hget := G.field?_fieldRow field
  rw [heq, G.field?_nodeTarget (G.nodes_get?_nodeRow other)] at hget
  have hspec := (Option.some.inj hget).symm
  rw [hspec] at havailable
  obtain ⟨prior, hprior, heq⟩ := Finset.mem_image.mp havailable
  exact hnot ((Fin.ext heq : prior = other) ▸ hprior)

theorem publicObserve_eq_of_extensions {G : Graph Player L}
    {left right laterLeft laterRight : Config G}
    (hleft : left.Extends laterLeft) (hright : right.Extends laterRight)
    (hdone : left.done = right.done)
    (hobs : publicObserve G laterLeft = publicObserve G laterRight) :
    publicObserve G left = publicObserve G right := by
  classical
  apply PublicObservation.ext hdone
  intro field
  have hfields := congrArg (fun seen : PublicObservation G => seen.fieldValue? field) hobs
  simp only [publicObserve] at hfields ⊢
  by_cases howner : (G.fieldRow field).owner = none
  · simp only [if_pos howner] at hfields ⊢
    cases hsource : (G.fieldRow field).source with
    | initial value =>
        simp only [hsource] at hfields ⊢
        rw [hleft.getAs _ _ (left.fieldSettled_of_available field
            (by simp [Config.fieldAvailable, hsource])),
          hright.getAs _ _ (right.fieldSettled_of_available field
            (by simp [Config.fieldAvailable, hsource]))] at hfields
        exact hfields
    | event node =>
        simp only [hsource] at hfields ⊢
        by_cases hnode : node < G.nodeCount
        · simp only [dif_pos hnode] at hfields ⊢
          have hdoneEq : left.nodeDone node ↔ right.nodeDone node := by
            simp only [Config.nodeDone, Config.doneIds, hdone]
          by_cases hdoneLeft : left.nodeDone node
          · have hdoneRight := hdoneEq.mp hdoneLeft
            have hafterLeft : laterLeft.nodeDone node := by
              rcases Finset.mem_image.mp hdoneLeft with ⟨prior, hprior, heq⟩
              exact Finset.mem_image.mpr ⟨prior, hleft.done hprior, heq⟩
            have hafterRight : laterRight.nodeDone node := by
              rcases Finset.mem_image.mp hdoneRight with ⟨prior, hprior, heq⟩
              exact Finset.mem_image.mpr ⟨prior, hright.done hprior, heq⟩
            simp only [if_pos hdoneLeft, if_pos hdoneRight] at ⊢
            simp only [if_pos hafterLeft, if_pos hafterRight] at hfields
            rw [hleft.getAs _ _ (left.fieldSettled_of_available field
                (by simpa [Config.fieldAvailable, hsource] using hdoneLeft)),
              hright.getAs _ _ (right.fieldSettled_of_available field
                (by simpa [Config.fieldAvailable, hsource] using hdoneRight))] at hfields
            exact hfields
          · simp [hdoneLeft, hdoneEq.not.mp hdoneLeft]
        · simp [hnode]
  · simp [howner]

/-- A private frontier observation can be recovered from a later observation
as long as its ready commitments have not yet been submitted. -/
theorem observe_eq_of_extensions {G : Graph Player L} (hwf : G.WF) (who : Player)
    {left right laterLeft laterRight : Config G}
    (hleft : left.Extends laterLeft) (hright : right.Extends laterRight)
    (hdone : left.done = right.done)
    (hremainLeft : ∀ node, ReadyCommitNode G left who node → node ∉ laterLeft.done)
    (hremainRight : ∀ node, ReadyCommitNode G right who node → node ∉ laterRight.done)
    (hobs : observe G laterLeft who = observe G laterRight who) :
    observe G left who = observe G right who := by
  classical
  apply Observation.ext
  · rw [observe_ready_eq_readyCommitNodes, observe_ready_eq_readyCommitNodes]
    exact readyCommitNodes_eq_of_done_eq hdone who
  intro node field
  have hfields := congrArg (fun seen : Observation G who => seen.fieldValue? node field) hobs
  simp only [observe, Graph.node?_nodeRow] at hfields ⊢
  cases hsem : (G.nodeRow node).sem with
  | sample dist => rfl
  | reveal source => rfl
  | commit actor guard =>
      simp only [hsem] at hfields ⊢
      by_cases hactor : actor = who
      · subst actor
        have hreadyEq : Ready G left node ↔ Ready G right node := by simp only [Ready, hdone]
        by_cases hready : Ready G left node
        · have hreadyRight := hreadyEq.mp hready
          have hcommitLeft : ReadyCommitNode G left who node :=
            ⟨G.nodeRow node, guard, G.nodes_get?_nodeRow node, hsem, hready⟩
          have hcommitRight : ReadyCommitNode G right who node :=
            ⟨G.nodeRow node, guard, G.nodes_get?_nodeRow node, hsem, hreadyRight⟩
          have hafterLeft : Ready G laterLeft node :=
            ⟨hremainLeft node hcommitLeft, fun prior hp => hleft.done (hready.2 hp)⟩
          have hafterRight : Ready G laterRight node :=
            ⟨hremainRight node hcommitRight, fun prior hp => hright.done (hreadyRight.2 hp)⟩
          simp only [dif_pos hready, dif_pos hreadyRight] at ⊢
          simp only [dif_pos hafterLeft, dif_pos hafterRight] at hfields
          by_cases hread :
              ({ field := field, ty := (G.fieldRow field).ty } : FieldRef L) ∈ guard.choiceReads
          · simp only [dif_pos hread] at hfields ⊢
            have hread' : (field : Nat) ∈ (G.nodeRow node).sem.reads := by
              rw [hsem]
              exact Finset.mem_image.mpr ⟨_, hread, rfl⟩
            rw [hleft.getAs _ _
                (hready.fieldSettled_of_read hwf (G.nodes_get?_nodeRow node) hread'),
              hright.getAs _ _
                (hreadyRight.fieldSettled_of_read hwf
                  (G.nodes_get?_nodeRow node) hread')] at hfields
            exact hfields
          · simp [hread]
        · simp [hready, hreadyEq.not.mp hready]
      · simp [hactor]

theorem ReadyCommitNode.ne_internal {G : Graph Player L} {cfg : Config G}
    {who : Player} {node other : Fin G.nodeCount}
    (hcommit : ReadyCommitNode G cfg who node)
    (hinternal : ReadyInternalNode G cfg other) : node ≠ other := by
  intro heq
  subst other
  rcases hcommit with ⟨row, guard, hrow, hsem, _⟩
  rcases hinternal with ⟨otherRow, hotherRow, hkind, _⟩
  have hrows := Option.some.inj (hrow.symm.trans hotherRow)
  subst otherRow
  rw [hsem] at hkind
  exact hkind

theorem ReadyCommitNode.after_stepReadyInternal {G : Graph Player L} (hwf : G.WF)
    {state : ReachableConfig G} {who : Player} {node : Fin G.nodeCount}
    (hcommit : ReadyCommitNode G state.1 who node)
    (hinternal : (readyInternalNodes G state.1).Nonempty)
    {next : ReachableConfig G}
    (hnext : next ∈ (Compiled.stepReadyInternal hwf state hinternal).support) :
    ReadyCommitNode G next.1 who node := by
  have hgrow := extends_of_stepReadyInternal hwf state hinternal hnext
  have hdone := stepReadyInternal_done hwf state hinternal hnext
  have hneq := hcommit.ne_internal
    (Finset.mem_filter.mp (Classical.choose_spec hinternal)).2
  rcases hcommit with ⟨row, guard, hrow, hsem, hready⟩
  refine ⟨row, guard, hrow, hsem, ?_, fun prior hp => hgrow.done (hready.2 hp)⟩
  rw [hdone]
  simpa only [Finset.mem_insert, not_or] using And.intro hneq hready.1

theorem ReadyCommitNode.after_settleInternal {G : Graph Player L} (hwf : G.WF)
    (fuel : Nat) {state : ReachableConfig G} {who : Player} {node : Fin G.nodeCount}
    (hcommit : ReadyCommitNode G state.1 who node)
    {next : ReachableConfig G}
    (hnext : next ∈ (Compiled.settleInternal hwf fuel state).support) :
    ReadyCommitNode G next.1 who node := by
  induction fuel generalizing state with
  | zero =>
      rw [Compiled.settleInternal_zero, FinDist.mem_support_pure] at hnext
      subst next
      exact hcommit
  | succ fuel ih =>
      unfold Compiled.settleInternal at hnext
      split at hnext
      next hinternal =>
        rw [FinDist.support_bind] at hnext
        obtain ⟨middle, hmiddle, hnext⟩ := Set.mem_iUnion₂.mp hnext
        exact ih (hcommit.after_stepReadyInternal hwf hinternal hmiddle) hnext
      next _ =>
        rw [FinDist.mem_support_pure] at hnext
        subst next
        exact hcommit

variable [Fintype Player]

theorem extends_applyFrontier_of_legal (G : Graph Player L) (hwf : G.WF)
    (hguards : GuardLive G) (state : ReachableConfig G)
    (joint : ∀ who, Option (FrontierAction G who))
    (hlegal : (toExecutionProtocol G hwf hguards).Legal state joint) :
    state.1.Extends (applyFrontier G hwf state joint).1 := by
  have havailable : ∀ who action, joint who = some action →
      FrontierAction.Available G state.1 who action := by
    intro who action haction
    have hlocal := hlegal.2 who
    rw [haction] at hlocal
    exact hlocal.2
  rw [applyFrontier_val_of_available G hwf state joint havailable]
  apply Config.extends_completeNodes
  intro written hwritten
  obtain ⟨who, hwho⟩ := commitAvailable_of_mem_roundWrites havailable hwritten
  exact (Classical.choice hwho).ready.1

theorem ReadyCommitNode.after_applyFrontier_of_none {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G) {state : ReachableConfig G}
    {who : Player} {node : Fin G.nodeCount}
    (hcommit : ReadyCommitNode G state.1 who node)
    (joint : ∀ actor, Option (FrontierAction G actor))
    (hlegal : (toExecutionProtocol G hwf hguards).Legal state joint)
    (hnone : joint who = none) :
    ReadyCommitNode G (applyFrontier G hwf state joint).1 who node := by
  classical
  have havailable : ∀ actor action, joint actor = some action →
      FrontierAction.Available G state.1 actor action := by
    intro actor action haction
    have hlocal := hlegal.2 actor
    rw [haction] at hlocal
    exact hlocal.2
  have hgrow := extends_applyFrontier_of_legal G hwf hguards state joint hlegal
  have hnotDone : node ∉ (applyFrontier G hwf state joint).1.done := by
    rw [applyFrontier_val_of_available G hwf state joint havailable,
      Config.completeNodes_done, Finset.mem_union]
    rintro (hdone | hwrite)
    · exact hcommit.ready.1 hdone
    · obtain ⟨written, hwritten, hnode⟩ := List.mem_map.mp (List.mem_toFinset.mp hwrite)
      obtain ⟨actor, _, hactor⟩ := (mem_roundWrites_iff joint _ written).mp hwritten
      obtain ⟨action, haction, hwrite⟩ := (mem_playerWrites_iff joint actor written).mp hactor
      have hready := readyCommitNode_of_mem_actionWrites (havailable actor action haction) hwrite
      rw [hnode] at hready
      have hactor := hready.owner_unique hcommit
      subst actor
      rw [hnone] at haction
      cases haction
  rcases hcommit with ⟨row, guard, hrow, hsem, hready⟩
  exact ⟨row, guard, hrow, hsem, hnotDone, fun prior hp => hgrow.done (hready.2 hp)⟩

end Vegas.EventGraph

namespace Vegas.Machine.Program

open GameTheory.Protocol GameTheory.Math.Probability EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}

theorem serializedStep_settle_support (program : Program Player L)
    (source : program.execution.History) (log : List (List Player))
    (command : {joint // program.serializedArena.execution.Legal ⟨source.state, log⟩ joint})
    {next : program.serializedArena.execution.State}
    (hnext : next ∈ (program.serializedArena.execution.step ⟨source.state, log⟩ command).support) :
    next.base ∈ (Compiled.settleInternal program.graphWF program.graph.nodeCount
      (applyFrontier program.graph program.graphWF source.state
        (fun who => command.1 (.player who)))).support := by
  have hbase : next.base ∈
      ((program.serializedArena.execution.step ⟨source.state, log⟩ command).map
        ScheduledSystem.State.base).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  rw [← program.expandRound_map_state_eq_serialized_step source log command,
    program.expandRound_map_state] at hbase
  exact hbase

theorem serializedStep_extends (program : Program Player L)
    {state : program.serializedArena.execution.State}
    (trace : program.serializedArena.execution.Trace state)
    (command : {joint // program.serializedArena.execution.Legal state joint})
    {next : program.serializedArena.execution.State}
    (hnext : next ∈ (program.serializedArena.execution.step state command).support) :
    state.base.1.Extends next.base.1 := by
  obtain ⟨source, hstate, _⟩ := program.serializedTrace_has_sourceHistory trace
  rcases state with ⟨base, log⟩
  dsimp only at hstate
  subst base
  exact (extends_applyFrontier_of_legal program.graph program.graphWF program.guardLive
    source.state _ (program.serializedPlayers_legal command)).trans
      (extends_of_settleInternal program.graphWF program.graph.nodeCount _
        (program.serializedStep_settle_support source log command hnext))

theorem serializedStep_readyCommit_of_none (program : Program Player L)
    {state : program.serializedArena.execution.State}
    (trace : program.serializedArena.execution.Trace state)
    (command : {joint // program.serializedArena.execution.Legal state joint})
    {next : program.serializedArena.execution.State}
    (hnext : next ∈ (program.serializedArena.execution.step state command).support)
    (who : Player) (hnone : command.1 (.player who) = none)
    {node : Fin program.graph.nodeCount}
    (hready : ReadyCommitNode program.graph state.base.1 who node) :
    ReadyCommitNode program.graph next.base.1 who node := by
  obtain ⟨source, hstate, _⟩ := program.serializedTrace_has_sourceHistory trace
  rcases state with ⟨base, log⟩
  dsimp only at hstate
  subst base
  exact (hready.after_applyFrontier_of_none program.graphWF program.guardLive _
    (program.serializedPlayers_legal command) hnone).after_settleInternal
      program.graphWF program.graph.nodeCount
      (program.serializedStep_settle_support source log command hnext)

/-- Matching compact information after a round determines both the preceding
compact information and the player's submission. No hidden state is inspected
by a reconstructed policy; this is a relation between legal histories. -/
theorem serializedStep_compact_injective (program : Program Player L) (who : Player)
    {left right nextLeft nextRight : program.serializedArena.execution.State}
    (first : program.serializedArena.execution.Trace left)
    (second : program.serializedArena.execution.Trace right)
    (leftCommand : {joint // program.serializedArena.execution.Legal left joint})
    (rightCommand : {joint // program.serializedArena.execution.Legal right joint})
    (leftRealized : nextLeft ∈
      (program.serializedArena.execution.step left leftCommand).support)
    (rightRealized : nextRight ∈
      (program.serializedArena.execution.step right rightCommand).support)
    (hdone : left.base.1.done = right.base.1.done)
    (hcompact : program.eraseSerializedPlayerInformation who
        (program.serializedArena.information.infoOf (.player who)
          (.extend first leftCommand.1 leftCommand.2 leftRealized)) =
      program.eraseSerializedPlayerInformation who
        (program.serializedArena.information.infoOf (.player who)
          (.extend second rightCommand.1 rightCommand.2 rightRealized))) :
    program.eraseSerializedPlayerInformation who
        (program.serializedArena.information.infoOf (.player who) first) =
      program.eraseSerializedPlayerInformation who
        (program.serializedArena.information.infoOf (.player who) second) ∧
      leftCommand.1 (.player who) = rightCommand.1 (.player who) := by
  change program.eraseSerializedPlayerInformation who
      (ScheduledSystem.RevealingInfo.push program.serializedSystem
        (program.serializedArena.information.infoOf (.player who) first)
        (leftCommand.1 (.player who)) _ _) =
    program.eraseSerializedPlayerInformation who
      (ScheduledSystem.RevealingInfo.push program.serializedSystem
        (program.serializedArena.information.infoOf (.player who) second)
        (rightCommand.1 (.player who)) _ _) at hcompact
  rw [program.eraseSerializedPlayerInformation_push,
    program.eraseSerializedPlayerInformation_push] at hcompact
  have hactive : program.serializedSystem.active left.base who ↔
      program.serializedSystem.active right.base who :=
    Compiled.activeAt_iff_of_done_eq hdone
  have hlocalLeft := leftCommand.2.2 (.player who)
  have hlocalRight := rightCommand.2.2 (.player who)
  have hown := congrArg PlayerInformation.own hcompact
  have hcurrent := congrArg PlayerInformation.current hcompact
  change (publicObserve program.graph nextLeft.base.1, observe program.graph nextLeft.base.1 who) =
    (publicObserve program.graph nextRight.base.1, observe program.graph nextRight.base.1 who)
      at hcurrent
  cases hleft : leftCommand.1 (.player who) <;>
    cases hright : rightCommand.1 (.player who)
  · simp only [PlayerInformation.push, hleft, hright] at hown
    refine ⟨PlayerInformation.ext ?_ hown, rfl⟩
    have hExtLeft := program.serializedStep_extends first leftCommand leftRealized
    have hExtRight := program.serializedStep_extends second rightCommand rightRealized
    have hpublic := publicObserve_eq_of_extensions hExtLeft hExtRight hdone
      (congrArg Prod.fst hcurrent)
    have hprivate := observe_eq_of_extensions program.graphWF who hExtLeft hExtRight hdone
      (fun node hready =>
        (program.serializedStep_readyCommit_of_none first leftCommand leftRealized who
          hleft hready).ready.1)
      (fun node hready =>
        (program.serializedStep_readyCommit_of_none second rightCommand rightRealized who
          hright hready).ready.1)
      (congrArg Prod.snd hcurrent)
    change (program.serializedSystem.revealingSignals.infoOf (.player who) first).current =
      (program.serializedSystem.revealingSignals.infoOf (.player who) second).current
    rw [program.serializedSystem.revealing_infoOf_current,
      program.serializedSystem.revealing_infoOf_current]
    exact Prod.ext hpublic hprivate
  · rw [hleft] at hlocalLeft
    rw [hright] at hlocalRight
    exact False.elim (hlocalLeft (hactive.mpr hlocalRight.1))
  · rw [hleft] at hlocalLeft
    rw [hright] at hlocalRight
    exact False.elim (hlocalRight (hactive.mp hlocalLeft.1))
  · simp only [PlayerInformation.push, hleft, hright] at hown
    have hpairs := List.cons.inj hown
    refine ⟨PlayerInformation.ext (congrArg Prod.fst hpairs.1) hpairs.2, ?_⟩
    exact congrArg some (congrArg Prod.snd hpairs.1)

/-- The canonical source's compact player information loses no order-free
runtime information. In particular, every passive observation is recoverable
from the current immutable snapshot and remembered own decisions. -/
theorem serializedBlindInfo_eq_of_compact_eq (program : Program Player L) (who : Player)
    {left right : program.serializedArena.execution.State}
    (first : program.serializedArena.execution.Trace left)
    (second : program.serializedArena.execution.Trace right)
    (hcompact : program.eraseSerializedPlayerInformation who
        (program.serializedArena.information.infoOf (.player who) first) =
      program.eraseSerializedPlayerInformation who
        (program.serializedArena.information.infoOf (.player who) second)) :
    program.serializedSystem.blindSignals.infoOf (.player who) first =
      program.serializedSystem.blindSignals.infoOf (.player who) second := by
  have hdone : left.base.1.done = right.base.1.done := by
    have hcurrent := congrArg (fun info : PlayerInformation program.graph who =>
      info.current.1.done) hcompact
    change (program.serializedSystem.revealingSignals.infoOf (.player who) first).current.1.done =
      (program.serializedSystem.revealingSignals.infoOf (.player who) second).current.1.done
        at hcurrent
    rw [program.serializedSystem.revealing_infoOf_current,
      program.serializedSystem.revealing_infoOf_current] at hcurrent
    exact hcurrent
  have hlength := program.serializedTrace_length_eq_of_done_eq first second hdone
  induction first generalizing right with
  | start =>
      cases second with
      | start => rfl
      | extend _ _ _ _ => simp only [ExecutionProtocol.Trace.length] at hlength; omega
  | @extend left nextLeft first leftJoint leftLegal leftRealized ih =>
      cases second with
      | start => simp only [ExecutionProtocol.Trace.length] at hlength; omega
      | @extend right nextRight second rightJoint rightLegal rightRealized =>
          have hpriorLength : first.length = second.length := by
            simpa only [ExecutionProtocol.Trace.length, Nat.add_right_cancel_iff] using hlength
          have hpriorDone : left.base.1.done = right.base.1.done := by
            rw [program.serializedTrace_done first,
              program.serializedTrace_done second, hpriorLength]
          obtain ⟨hpriorCompact, hchoice⟩ :=
            program.serializedStep_compact_injective who first second
              ⟨leftJoint, leftLegal⟩ ⟨rightJoint, rightLegal⟩
              leftRealized rightRealized hpriorDone hcompact
          have hprior := ih second hpriorCompact hpriorDone hpriorLength
          have hcurrent := congrArg PlayerInformation.current hcompact
          rw [InfoSignals.infoOf_extend, InfoSignals.infoOf_extend]
          change ScheduledSystem.BlindInfo.push program.serializedSystem
            (program.serializedSystem.blindSignals.infoOf (.player who) first)
            (leftJoint (.player who)) _ =
              ScheduledSystem.BlindInfo.push program.serializedSystem
                (program.serializedSystem.blindSignals.infoOf (.player who) second)
                (rightJoint (.player who)) _
          congr 1

end Vegas.Machine.Program
