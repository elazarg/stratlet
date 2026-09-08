/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.SourceOrder
import Vegas.EventGraph.HistoryInformation

/-! # Information structure of compiled source decisions -/

noncomputable section

namespace Vegas.ToEventGraph

open EventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A player has at most one ready source commitment in a compiled frontier. -/
theorem compiled_readyCommitNode_unique
    (program : GraphProgram P L)
    (cfg : Config (compile program).graph) (who : P)
    {left right : Fin (compile program).graph.nodeCount}
    (hleft : ReadyCommitNode (compile program).graph cfg who left)
    (hright : ReadyCommitNode (compile program).graph cfg who right) :
    left = right := by
  classical
  by_contra hne
  rcases hleft with ⟨leftRow, leftGuard, hleftRow, hleftSem, hleftReady⟩
  rcases hright with ⟨rightRow, rightGuard, hrightRow, hrightSem, hrightReady⟩
  let init := initialState program.Γ program.env program.wctx
  let state := BuildState.fromInitial init
  let result := compileCore program.prog program.fresh state
  have hcovered : FieldsCovered state := by
    apply BuildState.fromInitial_fieldsCovered
    exact initialState_fieldsCovered program.env program.wctx
  have excludeEarlier
      {earlier later : Fin result.graph.nodeCount}
      (hlt : (earlier : Nat) < (later : Nat))
      (earlierRow laterRow : EventNode P L)
      (hearlierRow : result.graph.nodes[earlier]? = some earlierRow)
      (hlaterRow : result.graph.nodes[later]? = some laterRow)
      (earlierGuard laterGuard : EventGuard L)
      (hearlierSem : earlierRow.sem = .commit who earlierGuard)
      (hlaterSem : laterRow.sem = .commit who laterGuard)
      (hearlierReady : Ready result.graph cfg earlier)
      (hlaterReady : Ready result.graph cfg later) : False := by
    rcases compileCore_sameOwner_dependency program.prog program.fresh state hcovered
      (by simp [state]) hlt earlierRow laterRow hearlierRow hlaterRow who
      hearlierSem hlaterSem with
      ⟨_, _, _, sourceGuard, site, _, hlaterSiteRow, hread⟩
    have hnot := Ready.nodeTarget_not_mem_reads_of_ready result.graphWF
      hlaterSiteRow hearlierRow hlaterReady hearlierReady
    apply hnot
    rw [show
      ((decisionSiteState site program.fresh state).commitEvent who sourceGuard).sem =
        .commit who (eventGuardOf (decisionSiteState site program.fresh state)
          who sourceGuard) by rfl]
    exact Finset.mem_image.mpr ⟨_, hread, rfl⟩
  change left ≠ right at hne
  have horder : (left : Nat) < (right : Nat) ∨ (right : Nat) < (left : Nat) :=
    Nat.lt_or_gt_of_ne (fun heq => hne (Fin.ext heq))
  change result.graph.nodes[left]? = some leftRow at hleftRow
  change result.graph.nodes[right]? = some rightRow at hrightRow
  change Ready result.graph cfg left at hleftReady
  change Ready result.graph cfg right at hrightReady
  rcases horder with hlr | hrl
  · exact excludeEarlier hlr leftRow rightRow hleftRow hrightRow leftGuard rightGuard
      hleftSem hrightSem hleftReady hrightReady
  · exact excludeEarlier hrl rightRow leftRow hrightRow hleftRow rightGuard leftGuard
      hrightSem hleftSem hrightReady hleftReady

/-- At a ready compiled source decision, every visible event field from that
decision onward is still absent.  Public sample and reveal events retain the
source-order publication barrier, while a later private commitment visible to
the same player depends on the earlier commitment. -/
theorem compiled_visible_future_not_done
    (program : GraphProgram P L) (who : P)
    {cfg : Config (compile program).graph}
    (hreach : Reachable (compile program).graph cfg)
    {current future : Fin (compile program).graph.nodeCount}
    (hcurrent : ReadyCommitNode (compile program).graph cfg who current)
    (hle : (current : Nat) ≤ (future : Nat))
    (hvisible : ((compile program).graph.nodeRow future).owner = none ∨
      ((compile program).graph.nodeRow future).owner = some who) :
    future ∉ cfg.done := by
  classical
  rcases hcurrent with ⟨currentRow, currentGuard, hcurrentRow,
    hcurrentSem, hready⟩
  by_cases heq : future = current
  · subst future
    exact hready.1
  have hlt : (current : Nat) < (future : Nat) := by
    omega
  intro hdone
  have hprior : current ∈ ((compile program).graph.prereqs future) := by
    let init := initialState program.Γ program.env program.wctx
    let state := BuildState.fromInitial init
    let result := compileCore program.prog program.fresh state
    change result.graph.nodes[current]? = some currentRow at hcurrentRow
    change Ready result.graph cfg current at hready
    change ((result.graph.nodeRow future).owner = none ∨
      (result.graph.nodeRow future).owner = some who) at hvisible
    change (current : Nat) < (future : Nat) at hlt
    have hfutureRow := result.graph.nodes_get?_nodeRow future
    cases hsem : (result.graph.nodeRow future).sem with
    | sample dist =>
        exact result.graph.prior_commit_mem_prereqs_of_sample hfutureRow
          hcurrentRow hlt hsem hcurrentSem
    | reveal source =>
        exact result.graph.prior_commit_mem_prereqs_of_reveal hfutureRow
          hcurrentRow hlt hsem hcurrentSem
    | commit actor guard =>
        have hfutureOwner : (result.graph.nodeRow future).owner = some actor := by
          have hwf := result.graphWF (future : Nat) (result.graph.nodeRow future)
            hfutureRow
          unfold Graph.nodeWFAt at hwf
          rw [hsem] at hwf
          exact hwf.2.2.1
        have hactor : actor = who := by
          rcases hvisible with hpublic | hprivate
          · rw [hfutureOwner] at hpublic
            contradiction
          · exact Option.some.inj (hfutureOwner.symm.trans hprivate)
        subst actor
        have hcovered : FieldsCovered state := by
          apply BuildState.fromInitial_fieldsCovered
          exact initialState_fieldsCovered program.env program.wctx
        rcases compileCore_sameOwner_dependency program.prog program.fresh state
          hcovered (by simp [state]) hlt currentRow (result.graph.nodeRow future)
          hcurrentRow hfutureRow who hcurrentSem hsem with
          ⟨_, _, _, sourceGuard, site, _, hsiteRow, hread⟩
        apply result.graph.nodeTarget_mem_prereqs_of_read hsiteRow hcurrentRow hlt
        change result.graph.nodeTarget current ∈
          (NodeSem.commit who (eventGuardOf
            (decisionSiteState site program.fresh state) who sourceGuard)).reads
        exact Finset.mem_image.mpr ⟨_, hread, rfl⟩
  exact hready.1 ((reachable_donePrereqs hreach hdone) hprior)

/-- Equality on the source-visible prefix at a common ready decision reconstructs
the complete event-graph visible store.  Later visible fields are absent on
both sides by the compiler's source-order dependencies. -/
theorem compiled_visibleStoreEq_of_prefix
    (program : GraphProgram P L) (who : P)
    {left right : Config (compile program).graph}
    (hleftReach : Reachable (compile program).graph left)
    (hrightReach : Reachable (compile program).graph right)
    {current : Fin (compile program).graph.nodeCount}
    (hleftReady : ReadyCommitNode (compile program).graph left who current)
    (hrightReady : ReadyCommitNode (compile program).graph right who current)
    (hprefix : ∀ field : Fin (compile program).graph.fieldCount,
      (field : Nat) < (compile program).graph.nodeTarget current →
      ((compile program).graph.fieldRow field).owner = none ∨
        ((compile program).graph.fieldRow field).owner = some who →
      Store.getAs left.store field
          ((compile program).graph.fieldRow field).ty =
        Store.getAs right.store field
          ((compile program).graph.fieldRow field).ty) :
    VisibleStoreEq who left right := by
  intro field hvisible
  by_cases hpast : (field : Nat) < (compile program).graph.nodeTarget current
  · exact hprefix field hpast hvisible
  have hfieldNode : (compile program).graph.initialFields.length ≤ (field : Nat) := by
    unfold Graph.nodeTarget at hpast
    omega
  have hfutureLt : (field : Nat) - (compile program).graph.initialFields.length <
      (compile program).graph.nodeCount := by
    have := field.isLt
    unfold Graph.fieldCount at this
    omega
  let future : Fin (compile program).graph.nodeCount :=
    ⟨(field : Nat) - (compile program).graph.initialFields.length, hfutureLt⟩
  have htarget : (compile program).graph.nodeTarget future = (field : Nat) := by
    unfold Graph.nodeTarget
    dsimp [future]
    omega
  have hfieldEq : field =
      ⟨(compile program).graph.nodeTarget future,
        StateSnapshot.nodeTarget_lt_fieldCount (compile program).graph future⟩ := by
    apply Fin.ext
    change (field : Nat) = (compile program).graph.nodeTarget future
    exact htarget.symm
  have hle : (current : Nat) ≤ (future : Nat) := by
    unfold Graph.nodeTarget at hpast htarget
    omega
  have hrow : (compile program).graph.fieldRow field =
      { ty := ((compile program).graph.nodeRow future).ty
        owner := ((compile program).graph.nodeRow future).owner
        source := .event (future : Nat) } := by
    rw [hfieldEq, StateSnapshot.fieldRow_nodeTarget]
  have hfutureVisible : ((compile program).graph.nodeRow future).owner = none ∨
      ((compile program).graph.nodeRow future).owner = some who := by
    simpa only [hrow] using hvisible
  have hleftNot := compiled_visible_future_not_done program who hleftReach
    hleftReady hle hfutureVisible
  have hrightNot := compiled_visible_future_not_done program who hrightReach
    hrightReady hle hfutureVisible
  rw [hfieldEq, StateSnapshot.fieldRow_nodeTarget,
    EventGraph.reachable_getAs_nodeTarget_eq_none hleftReach future hleftNot,
    EventGraph.reachable_getAs_nodeTarget_eq_none hrightReach future hrightNot]

/-- Equality on the declared reads of a structural source decision determines
the complete visible store at that decision in any two reachable executions. -/
theorem decisionSite_visibleStoreEq
    (program : GraphProgram P L) (who : P)
    {Δ : VCtx P L} {x : VarId} {b : L.Ty}
    {guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    (site : SourceDecisionSite who program.prog Δ x b guard)
    {left right : Config (compile program).graph}
    (hleftReach : Reachable (compile program).graph left)
    (hrightReach : Reachable (compile program).graph right)
    {current : Fin (compile program).graph.nodeCount}
    (hnode : (current : Nat) = (decisionSiteState site program.fresh
      (BuildState.fromInitial (initialState program.Γ program.env program.wctx))).nodes.length)
    (hleftReady : ReadyCommitNode (compile program).graph left who current)
    (hrightReady : ReadyCommitNode (compile program).graph right who current)
    (hreads : ∀ ref,
      ref ∈ (eventGuardOf (decisionSiteState site program.fresh
        (BuildState.fromInitial (initialState program.Γ program.env program.wctx)))
          who guard).choiceReads →
      Store.getAs left.store ref.field ref.ty =
        Store.getAs right.store ref.field ref.ty) :
    VisibleStoreEq who left right := by
  let state := BuildState.fromInitial (initialState program.Γ program.env program.wctx)
  let siteState := decisionSiteState site program.fresh state
  apply compiled_visibleStoreEq_of_prefix program who hleftReach hrightReach
    hleftReady hrightReady
  intro field hpast hvisible
  have hinitial : siteState.initialFields = (compile program).graph.initialFields := by
    rw [decisionSiteState_initialFields site program.fresh state]
    change state.initialFields = (compileCore program.prog program.fresh state).initialFields
    exact (compileCore_initialFields program.prog program.fresh state).symm
  have hfield : (field : Nat) < siteState.initialFields.length + siteState.nodes.length := by
    unfold Graph.nodeTarget at hpast
    rw [hnode, ← hinitial] at hpast
    exact hpast
  let siteGraph : Graph P L :=
    { initialFields := siteState.initialFields, nodes := siteState.nodes }
  have hlookup : siteGraph.field? field =
      some ((compile program).graph.fieldRow field) := by
    dsimp only [siteGraph]
    rw [decisionSiteState_field?_eq_compileCore site program.fresh state field hfield]
    exact (compile program).graph.field?_fieldRow field
  have hmem := visibleField_mem_visibleFieldRefs siteState
    (decisionSiteState_initial_fieldsCovered site program.fresh program.env program.wctx)
    who field hfield ((compile program).graph.fieldRow field) hlookup hvisible
  apply hreads { field := field, ty := ((compile program).graph.fieldRow field).ty }
  change _ ∈ (visibleFieldRefs siteState who)
  exact hmem

end Vegas.ToEventGraph
