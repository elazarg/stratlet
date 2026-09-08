/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.Skeleton
import Vegas.EventGraph.FiniteState

/-! # Immutable event-graph observations -/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- Two configurations agree on the complete store visible to one player:
all public fields and every field owned by that player, whether or not the
field occurs in the current decision footprint. -/
def VisibleStoreEq {G : Graph Player L} (who : Player)
    (left right : Config G) : Prop :=
  ∀ field : Fin G.fieldCount,
    (G.fieldRow field).owner = none ∨
      (G.fieldRow field).owner = some who →
    Store.getAs left.store field (G.fieldRow field).ty =
      Store.getAs right.store field (G.fieldRow field).ty

theorem VisibleStoreEq.refl {G : Graph Player L} (who : Player) (cfg : Config G) :
    VisibleStoreEq who cfg cfg := by
  intro field _
  rfl

theorem VisibleStoreEq.symm {G : Graph Player L} {who : Player}
    {left right : Config G} (h : VisibleStoreEq who left right) :
    VisibleStoreEq who right left := by
  intro field hvisible
  exact (h field hvisible).symm

/-- Complete visible-store agreement and the structural checkpoint determine
the graph-local snapshot used at a player decision. -/
theorem localSnapshot_eq_of_visibleStoreEq {G : Graph Player L} (hwf : G.WF)
    (who : Player) {left right : Config G}
    (hdone : left.done = right.done)
    (hstore : VisibleStoreEq who left right) :
    (publicObserve G left, observe G left who) =
      (publicObserve G right, observe G right who) := by
  classical
  apply Prod.ext
  · apply PublicObservation.ext hdone
    intro field
    simp only [publicObserve]
    by_cases howner : (G.fieldRow field).owner = none
    · simp only [if_pos howner]
      cases hsource : (G.fieldRow field).source with
      | initial value => exact hstore field (Or.inl howner)
      | event node =>
          by_cases hnode : node < G.nodeCount
          · simp only [dif_pos hnode]
            have hdoneNode : left.nodeDone node ↔ right.nodeDone node := by
              simp only [Config.nodeDone, Config.doneIds, hdone]
            by_cases hleft : left.nodeDone node
            · simp only [if_pos hleft, if_pos (hdoneNode.mp hleft)]
              exact hstore field (Or.inl howner)
            · simp only [if_neg hleft, if_neg (hdoneNode.not.mp hleft)]
          · simp [hnode]
    · simp [howner]
  · apply Observation.ext
    · rw [observe_ready_eq_readyCommitNodes, observe_ready_eq_readyCommitNodes]
      exact readyCommitNodes_eq_of_done_eq hdone who
    · intro node field
      simp only [observe, Graph.node?_nodeRow]
      cases hsem : (G.nodeRow node).sem with
      | sample dist => rfl
      | reveal source => rfl
      | commit actor guard =>
          simp only
          by_cases hactor : actor = who
          · subst actor
            rw [dif_pos rfl, dif_pos rfl]
            have hready : Ready G left node ↔ Ready G right node := by
              simp only [Ready, hdone]
            by_cases hleft : Ready G left node
            · simp only [dif_pos hleft, dif_pos (hready.mp hleft)]
              let ref : FieldRef L :=
                { field := field, ty := (G.fieldRow field).ty }
              by_cases hread : ref ∈ guard.choiceReads
              · change FieldRef.mk (field : Nat) (G.fieldRow field).ty ∈
                    guard.choiceReads at hread
                simp only [dif_pos hread]
                have hrowWF := hwf (node : Nat) (G.nodeRow node)
                  (G.nodes_get?_nodeRow node)
                unfold Graph.nodeWFAt at hrowWF
                rw [hsem] at hrowWF
                obtain ⟨spec, hfield, _hty, hvisible⟩ :=
                  hrowWF.2.2.2 ref hread
                have hrow : G.fieldRow field = spec :=
                  G.fieldRow_eq_of_field?_some hfield field.isLt
                exact hstore field (by simpa [hrow] using hvisible)
              · change FieldRef.mk (field : Nat) (G.fieldRow field).ty ∉
                    guard.choiceReads at hread
                simp only [dif_neg hread]
            · rw [dif_neg hleft, dif_neg (hready.not.mp hleft)]
          · rw [dif_neg hactor, dif_neg hactor]

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
    (hnext : next ∈ (EventGraph.stepReadyInternal hwf state hinternal).support) :
    state.1.Extends next.1 := by
  have hraw : next.1 ∈
      ((EventGraph.stepReadyInternal hwf state hinternal).map Subtype.val).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  unfold EventGraph.stepReadyInternal at hraw
  simp only [map_val_stepAvailable] at hraw
  obtain ⟨written, hwritten⟩ := stepAvailableEvent_support_completeNode _ hraw
  rw [hwritten]
  have hready := (Finset.mem_filter.mp (Classical.choose_spec hinternal)).2
  rcases hready with ⟨row, hrow, hkind, hready⟩
  exact (Config.Extends.refl state.1).completeNode _ hready.1 written

theorem extends_of_settleInternal {G : Graph Player L} (hwf : G.WF)
    (fuel : Nat) (state : ReachableConfig G) {next : ReachableConfig G}
    (hnext : next ∈ (EventGraph.settleInternal hwf fuel state).support) :
    state.1.Extends next.1 := by
  induction fuel generalizing state with
  | zero =>
      rw [EventGraph.settleInternal_zero, FinDist.mem_support_pure] at hnext
      subst next
      exact Config.Extends.refl _
  | succ fuel ih =>
      unfold EventGraph.settleInternal at hnext
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
    (hnext : next ∈ (EventGraph.stepReadyInternal hwf state hinternal).support) :
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
    (hnext : next ∈ (EventGraph.settleInternal hwf fuel state).support) :
    ReadyCommitNode G next.1 who node := by
  induction fuel generalizing state with
  | zero =>
      rw [EventGraph.settleInternal_zero, FinDist.mem_support_pure] at hnext
      subst next
      exact hcommit
  | succ fuel ih =>
      unfold EventGraph.settleInternal at hnext
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

theorem extends_of_toExecutionProtocol_step (G : Graph Player L) (hwf : G.WF)
    (hguards : GuardLive G) (state : ReachableConfig G)
    (legal : { joint // (toExecutionProtocol G hwf hguards).Legal state joint })
    {next : ReachableConfig G}
    (hnext : next ∈
      ((toExecutionProtocol G hwf hguards).step state legal).support) :
    state.1.Extends next.1 := by
  classical
  unfold toExecutionProtocol at hnext
  change next ∈ (if hinternal : (readyInternalNodes G state.1).Nonempty then
    stepReadyInternal hwf state hinternal
  else FinDist.pure (applyFrontier G hwf state legal.1)).support at hnext
  by_cases hinternal : (readyInternalNodes G state.1).Nonempty
  · rw [dif_pos hinternal] at hnext
    exact extends_of_stepReadyInternal hwf state hinternal hnext
  · rw [dif_neg hinternal, FinDist.mem_support_pure] at hnext
    subst next
    exact extends_applyFrontier_of_legal G hwf hguards state legal.1 legal.2

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
