/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.Confluence
import Vegas.EventGraph.KernelPolicy

/-!
# Law-level execution of graph-node kernels

This module isolates the probabilistic calculation used when independent graph
nodes are linearized.  A node kernel returns the typed value written by that
node.  Execution uses the real graph operation `Config.completeNode`; it does
not introduce a second store semantics.

The local swap theorem separates two obligations needed by compiler
instantiations: each node's declared-read law is unchanged by the other ready
node's write, and the nodes are distinct.  The former is discharged for graph
code by read-footprint locality; the latter invokes the existing configuration
diamond.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}

namespace AvailableEvent

variable {G : Graph Player L} {cfg : Config G}

private theorem internalStep_eq {event : InternalEvent G}
    (first second : InternalStep G cfg event) : first = second := by
  cases first with
  | sample firstRow firstDist firstRowGet firstSem firstReady firstEnv firstEnvOk =>
      cases second with
      | sample secondRow secondDist secondRowGet secondSem secondReady secondEnv secondEnvOk =>
          have hrow : firstRow = secondRow :=
            Option.some.inj (firstRowGet.symm.trans secondRowGet)
          subst secondRow
          have hdist : firstDist = secondDist :=
            NodeSem.sample.inj (firstSem.symm.trans secondSem)
          subst secondDist
          have henv : firstEnv = secondEnv :=
            Option.some.inj (firstEnvOk.symm.trans secondEnvOk)
          subst secondEnv
          rfl
      | reveal secondRow source secondRowGet secondSem _ value _ =>
          have hrow : firstRow = secondRow :=
            Option.some.inj (firstRowGet.symm.trans secondRowGet)
          subst secondRow
          simp [firstSem] at secondSem
  | reveal firstRow source firstRowGet firstSem firstReady firstValue firstValueOk =>
      cases second with
      | sample secondRow secondDist secondRowGet secondSem _ env _ =>
          have hrow : firstRow = secondRow :=
            Option.some.inj (firstRowGet.symm.trans secondRowGet)
          subst secondRow
          simp [firstSem] at secondSem
      | reveal secondRow secondSource secondRowGet secondSem secondReady
          secondValue secondValueOk =>
          have hrow : firstRow = secondRow :=
            Option.some.inj (firstRowGet.symm.trans secondRowGet)
          subst secondRow
          have hsource : source = secondSource :=
            NodeSem.reveal.inj (firstSem.symm.trans secondSem)
          subst secondSource
          have hvalue : firstValue = secondValue :=
            Option.some.inj (firstValueOk.symm.trans secondValueOk)
          subst secondValue
          rfl

/-- The law of the typed write performed by an actual available primitive
event.  Commitment events have already received their policy-selected value;
sample events retain their graph distribution, and reveals are point laws. -/
def writeLaw (event : AvailableEvent G cfg) : FinDist (TypedValue L) :=
  match event with
  | .commit _ _ step =>
      FinDist.pure { ty := step.guard.ty, value := step.value }
  | .internal _ step =>
      match step with
      | .sample _ dist _ _ _ env _ =>
          (dist.eval env).map fun value => { ty := dist.ty, value := value }
      | .reveal row _ _ _ _ value _ =>
          FinDist.pure { ty := row.ty, value := value }

theorem writeLaw_internal_eq_of_node_eq
    {firstEvent secondEvent : InternalEvent G}
    (first : InternalStep G cfg firstEvent)
    (second : InternalStep G cfg secondEvent)
    (hnode : firstEvent.node = secondEvent.node) :
    (AvailableEvent.internal firstEvent first).writeLaw =
      (AvailableEvent.internal secondEvent second).writeLaw := by
  cases firstEvent with
  | mk firstNode =>
      cases secondEvent with
      | mk secondNode =>
          simp only at hnode
          subst secondNode
          rw [internalStep_eq first second]

theorem writeLaw_eq_of_node_eq_of_internal
    (first second : AvailableEvent G cfg)
    (hnode : first.node = second.node)
    (hinternal : NodeSem.isInternal (G.nodeRow first.node).sem = true) :
    first.writeLaw = second.writeLaw := by
  cases first with
  | commit firstWho firstAction firstStep =>
      change NodeSem.isInternal (G.nodeRow firstAction.node).sem = true at hinternal
      have hrow : G.nodeRow firstAction.node = firstStep.row :=
        Option.some.inj
          ((G.nodes_get?_nodeRow firstAction.node).symm.trans firstStep.row_get)
      rw [hrow, firstStep.sem_eq] at hinternal
      simp [NodeSem.isInternal] at hinternal
  | internal firstEvent firstStep =>
      cases second with
      | commit secondWho secondAction secondStep =>
          change NodeSem.isInternal (G.nodeRow firstEvent.node).sem = true at hinternal
          have hrow : G.nodeRow secondAction.node = secondStep.row :=
            Option.some.inj
              ((G.nodes_get?_nodeRow secondAction.node).symm.trans
                secondStep.row_get)
          have hnodes : firstEvent.node = secondAction.node := by
            simpa using hnode
          rw [hnodes, hrow, secondStep.sem_eq] at hinternal
          simp [NodeSem.isInternal] at hinternal
      | internal secondEvent secondStep =>
          exact writeLaw_internal_eq_of_node_eq firstStep secondStep hnode

/-- `writeLaw` is exactly the probability layer of the canonical primitive
graph transition. -/
theorem stepAvailableEvent_eq_writeLaw_map
    (event : AvailableEvent G cfg) :
    stepAvailableEvent G cfg event =
      event.writeLaw.map fun written =>
        cfg.completeNode event.node written := by
  cases event with
  | commit who action step =>
      simp [stepAvailableEvent, stepCommit, writeLaw]
  | internal internal step =>
      cases step <;>
        simp [stepAvailableEvent, stepInternal, writeLaw,
          FinDist.map_comp, Function.comp_def]

/-- Transporting an actual event across a distinct ready write preserves its
entire typed write law, not only its support. -/
theorem exists_after_other_ready_write_writeLaw_eq
    (hwf : G.WF) (event : AvailableEvent G cfg)
    {other : Fin G.nodeCount} {otherRow : EventNode Player L}
    (hotherRow : G.nodes[other]? = some otherRow)
    (hotherReady : Ready G cfg other) (otherWritten : TypedValue L)
    (hne : event.node ≠ other) :
    ∃ event' : AvailableEvent G (cfg.completeNode other otherWritten),
      event'.node = event.node ∧ event'.writeLaw = event.writeLaw := by
  cases event with
  | commit who action step =>
      have htargetNot : G.nodeTarget other ∉ step.row.sem.reads :=
        Ready.nodeTarget_not_mem_reads_of_ready
          hwf step.row_get hotherRow step.ready hotherReady
      have hnotRead : ∀ ref, ref ∈ step.guard.choiceReads →
          ref.field ≠ G.nodeTarget other := by
        intro ref href heq
        apply htargetNot
        rw [step.sem_eq]
        exact Finset.mem_image.mpr ⟨ref, href, heq⟩
      let step' : CommitStep G
          (cfg.completeNode other otherWritten) who action :=
        { row := step.row, guard := step.guard, row_get := step.row_get,
          sem_eq := step.sem_eq, ready := step.ready.completeNode_of_ne hne,
          value := step.value, value_ok := step.value_ok, env := step.env,
          env_ok := ReadEnv.ofStore?_completeNode_of_not_read
            (value := otherWritten) step.env_ok hnotRead,
          guard_ok := step.guard_ok }
      exact ⟨.commit who action step', rfl, rfl⟩
  | internal internalEvent step =>
      cases step with
      | sample row dist row_get sem_eq ready env env_ok =>
          have htargetNot : G.nodeTarget other ∉ row.sem.reads :=
            Ready.nodeTarget_not_mem_reads_of_ready
              hwf row_get hotherRow ready hotherReady
          have hnotRead : ∀ ref, ref ∈ dist.reads →
              ref.field ≠ G.nodeTarget other := by
            intro ref href heq
            apply htargetNot
            rw [sem_eq]
            exact Finset.mem_image.mpr ⟨ref, href, heq⟩
          let step' : InternalStep G
              (cfg.completeNode other otherWritten) internalEvent :=
            .sample row dist row_get sem_eq (ready.completeNode_of_ne hne) env
              (ReadEnv.ofStore?_completeNode_of_not_read
                (value := otherWritten) env_ok hnotRead)
          exact ⟨.internal internalEvent step', rfl, rfl⟩
      | reveal row source row_get sem_eq ready value value_ok =>
          have htargetNot : G.nodeTarget other ∉ row.sem.reads :=
            Ready.nodeTarget_not_mem_reads_of_ready
              hwf row_get hotherRow ready hotherReady
          have hsourceNe : source ≠ G.nodeTarget other := by
            intro heq
            apply htargetNot
            rw [sem_eq]
            simp [NodeSem.reads, heq]
          have hvalue :
              Store.getAs (cfg.completeNode other otherWritten).store
                source row.ty = some value := by
            rw [Config.completeNode]
            exact (Store.getAs_set_ne cfg.store hsourceNe
              otherWritten row.ty).trans value_ok
          let step' : InternalStep G
              (cfg.completeNode other otherWritten) internalEvent :=
            .reveal row source row_get sem_eq
              (ready.completeNode_of_ne hne) value hvalue
          exact ⟨.internal internalEvent step', rfl, rfl⟩

/-- Canonically choose the persisted evidence for an event after its distinct
ready peer writes.  The following lemmas ensure the choice cannot affect its
node or probability law. -/
def afterWrite (hwf : G.WF) (event other : AvailableEvent G cfg)
    (written : TypedValue L) (hne : event.node ≠ other.node) :
    AvailableEvent G (cfg.completeNode other.node written) :=
  Classical.choose (event.exists_after_other_ready_write_writeLaw_eq hwf
    (G.nodes_get?_nodeRow other.node) other.ready written hne)

@[simp] theorem afterWrite_node (hwf : G.WF)
    (event other : AvailableEvent G cfg) (written : TypedValue L)
    (hne : event.node ≠ other.node) :
    (afterWrite hwf event other written hne).node = event.node :=
  (Classical.choose_spec
    (event.exists_after_other_ready_write_writeLaw_eq hwf
      (G.nodes_get?_nodeRow other.node) other.ready written hne)).1

@[simp] theorem afterWrite_writeLaw (hwf : G.WF)
    (event other : AvailableEvent G cfg) (written : TypedValue L)
    (hne : event.node ≠ other.node) :
    (afterWrite hwf event other written hne).writeLaw = event.writeLaw :=
  (Classical.choose_spec
    (event.exists_after_other_ready_write_writeLaw_eq hwf
      (G.nodes_get?_nodeRow other.node) other.ready written hne)).2
/-- The two-step law obtained by sampling the write laws of two simultaneously
available primitive events and applying their real graph updates. -/
def pairLaw (left right : AvailableEvent G cfg) : FinDist (Config G) :=
  left.writeLaw.bind fun leftWritten =>
    right.writeLaw.map fun rightWritten =>
      (cfg.completeNode left.node leftWritten).completeNode
        right.node rightWritten

/-- The genuinely sequential form of `pairLaw`: after the first actual write,
the second event uses availability evidence transported to the new graph
configuration. -/
def sequentialPairLaw (hwf : G.WF) (left right : AvailableEvent G cfg)
    (hne : right.node ≠ left.node) : FinDist (Config G) :=
  left.writeLaw.bind fun leftWritten =>
    let right' := afterWrite hwf right left leftWritten hne
    right'.writeLaw.map fun rightWritten =>
      (cfg.completeNode left.node leftWritten).completeNode
        right'.node rightWritten

theorem sequentialPairLaw_eq_pairLaw (hwf : G.WF)
    (left right : AvailableEvent G cfg) (hne : right.node ≠ left.node) :
    sequentialPairLaw hwf left right hne = pairLaw left right := by
  unfold sequentialPairLaw pairLaw
  apply FinDist.bind_congr
  intro leftWritten _
  simp

/-- Actual primitive-event write laws commute at a shared checkpoint.  Read
locality is not postulated here: `exists_after_other_ready_write_writeLaw_eq`
proves that each law is unchanged across the peer write from graph readiness
and declared footprints. -/
theorem pairLaw_comm (left right : AvailableEvent G cfg)
    (hne : left.node ≠ right.node) :
    pairLaw left right = pairLaw right left := by
  unfold pairLaw
  simp only [FinDist.map_eq_bind]
  rw [FinDist.bind_comm]
  apply FinDist.bind_congr
  intro rightWritten _
  apply FinDist.bind_congr
  intro leftWritten _
  rw [Config.completeNode_comm cfg leftWritten rightWritten hne]

/-- Two actual sequential primitive-event laws agree in either order, with
availability and read environments transported after the first realized
write. -/
theorem sequentialPairLaw_comm (hwf : G.WF)
    (left right : AvailableEvent G cfg) (hne : left.node ≠ right.node) :
    sequentialPairLaw hwf left right hne.symm =
      sequentialPairLaw hwf right left hne := by
  rw [sequentialPairLaw_eq_pairLaw, sequentialPairLaw_eq_pairLaw]
  exact pairLaw_comm left right hne

/-- Adjacent-swap law with an arbitrary continuation from the resulting graph
configuration.  This is the compositional form used inside a full lawful
schedule: the suffix may contain any number of later graph events. -/
theorem sequentialPair_bind_comm (hwf : G.WF)
    (left right : AvailableEvent G cfg) (hne : left.node ≠ right.node)
    {Outcome : Type} (continuation : Config G → FinDist Outcome) :
    (left.writeLaw.bind fun leftWritten =>
      let right' := afterWrite hwf right left leftWritten hne.symm
      right'.writeLaw.bind fun rightWritten =>
        continuation ((cfg.completeNode left.node leftWritten).completeNode
          right'.node rightWritten)) =
    (right.writeLaw.bind fun rightWritten =>
      let left' := afterWrite hwf left right rightWritten hne
      left'.writeLaw.bind fun leftWritten =>
        continuation ((cfg.completeNode right.node rightWritten).completeNode
          left'.node leftWritten)) := by
  simp only [afterWrite_writeLaw, afterWrite_node]
  rw [FinDist.bind_comm]
  apply FinDist.bind_congr
  intro rightWritten _
  apply FinDist.bind_congr
  intro leftWritten _
  rw [Config.completeNode_comm cfg leftWritten rightWritten hne]

end AvailableEvent

/-! ## Declared-read commitment kernels -/

/-- The typed law of a ready declared-read commitment kernel is unchanged by
a distinct simultaneously ready graph write.  Both sides reduce to the same
explicit policy/read law via `commitValueLaw_typed`; no store-level policy or
independence premise is assumed. -/
theorem commitValueLaw_typed_after_other_ready_write
    {G : Graph Player L} (hwf : G.WF)
    {cfg : Config G} (hcoherent : StoreCoherent G cfg)
    (who : Player) (policy : CommitPolicy G who)
    (node other : Fin G.nodeCount) (hready : ReadyCommitNode G cfg who node)
    {otherRow : EventNode Player L} (hotherRow : G.nodes[other]? = some otherRow)
    (hotherReady : Ready G cfg other) (written : TypedValue L)
    (hcoherentAfter : StoreCoherent G (cfg.completeNode other written))
    (hne : node ≠ other) (guard : EventGuard L)
    (hsem : (G.nodeRow node).sem = .commit who guard)
    (reads : ReadEnv L guard.choiceReads)
    (hreads : ReadEnv.ofStore? cfg.store guard.choiceReads = some reads) :
    (commitValueLaw hwf (cfg.completeNode other written) hcoherentAfter
        who policy node
        ⟨G.nodeRow node, guard, G.nodes_get?_nodeRow node, hsem,
          hready.ready.completeNode_of_ne hne⟩).map
          (fun value => G.nodeTypedValue node value.1) =
      (commitValueLaw hwf cfg hcoherent who policy node hready).map
        (fun value => G.nodeTypedValue node value.1) := by
  have htargetNot : G.nodeTarget other ∉ (G.nodeRow node).sem.reads :=
    Ready.nodeTarget_not_mem_reads_of_ready hwf
      (G.nodes_get?_nodeRow node) hotherRow hready.ready hotherReady
  have hnotRead : ∀ ref, ref ∈ guard.choiceReads →
      ref.field ≠ G.nodeTarget other := by
    intro ref href heq
    apply htargetNot
    rw [hsem]
    exact Finset.mem_image.mpr ⟨ref, href, heq⟩
  have hreadsAfter :
      ReadEnv.ofStore? (cfg.completeNode other written).store
        guard.choiceReads = some reads :=
    ReadEnv.ofStore?_completeNode_of_not_read
      (value := written) hreads hnotRead
  rw [commitValueLaw_typed hwf (cfg.completeNode other written)
      hcoherentAfter who policy node _ guard hsem reads hreadsAfter,
    commitValueLaw_typed hwf cfg hcoherent who policy node hready
      guard hsem reads hreads]

/-! ## Policy-driven node schedules -/

/-- One declared-read commitment kernel per player. -/
abbrev CommitPolicyProfile (G : Graph Player L) := ∀ who, CommitPolicy G who

/-- A policy-selected typed write together with the actual primitive graph
event and support evidence for that write. -/
structure PolicyWrite {G : Graph Player L} (state : ReachableConfig G)
    (node : Fin G.nodeCount) where
  written : TypedValue L
  event : AvailableEvent G state.1
  event_node : event.node = node
  supported : state.1.completeNode event.node written ∈
    (stepAvailableEvent G state.1 event).support

/-- The canonical actual event selected at a ready node. -/
def readyEvent [Fintype Player] {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G) (state : ReachableConfig G)
    (node : Fin G.nodeCount) (hready : Ready G state.1 node) :
    AvailableEvent G state.1 :=
  Classical.choose (exists_availableEvent_of_ready hwf hguards hready)

@[simp] theorem readyEvent_node [Fintype Player] {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G) (state : ReachableConfig G)
    (node : Fin G.nodeCount) (hready : Ready G state.1 node) :
    (readyEvent hwf hguards state node hready).node = node :=
  Classical.choose_spec (exists_availableEvent_of_ready hwf hguards hready)

/-- The actual typed-write law at a ready node. Commitments use the supplied
declared-read policy; samples and reveals use the canonical primitive event. -/
def policyValueLaw [Fintype Player] {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G)
    (policies : CommitPolicyProfile G)
    (state : ReachableConfig G) (node : Fin G.nodeCount)
    (hready : Ready G state.1 node) : FinDist (PolicyWrite state node) := by
  classical
  match hsem : (G.nodeRow node).sem with
  | .commit who guard =>
      let readyCommit : ReadyCommitNode G state.1 who node :=
        ⟨G.nodeRow node, guard, G.nodes_get?_nodeRow node, hsem, hready⟩
      exact
        (commitValueLaw hwf state.1 (reachable_storeCoherent hwf state.2)
          who (policies who) node readyCommit).map fun selected => by
            let action : CommitAction G who :=
              { node := node, value := G.nodeTypedValue node selected.1 }
            let step : CommitStep G state.1 who action :=
              Classical.choice selected.2
            let event : AvailableEvent G state.1 := .commit who action step
            refine ⟨action.value, event, rfl, ?_⟩
            change state.1.completeNode action.node action.value ∈
              (FinDist.pure
                (state.1.completeNode action.node
                  { ty := step.guard.ty, value := step.value })).support
            rw [step.written_eq_action]
            exact FinDist.mem_support_pure.mpr rfl
  | .sample _ =>
      let event := readyEvent hwf hguards state node hready
      have hnode := readyEvent_node hwf hguards state node hready
      exact event.writeLaw.bindOnSupport fun written hwritten =>
        FinDist.pure
          { written := written
            event := event
            event_node := hnode
            supported := by
              rw [AvailableEvent.stepAvailableEvent_eq_writeLaw_map,
                FinDist.support_map]
              exact ⟨written, hwritten, rfl⟩ }
  | .reveal _ =>
      let event := readyEvent hwf hguards state node hready
      have hnode := readyEvent_node hwf hguards state node hready
      exact event.writeLaw.bindOnSupport fun written hwritten =>
        FinDist.pure
          { written := written
            event := event
            event_node := hnode
            supported := by
              rw [AvailableEvent.stepAvailableEvent_eq_writeLaw_map,
                FinDist.support_map]
              exact ⟨written, hwritten, rfl⟩ }

theorem map_written_policyValueLaw_of_commit [Fintype Player]
    {G : Graph Player L} (hwf : G.WF) (hguards : GuardLive G)
    (policies : CommitPolicyProfile G) (state : ReachableConfig G)
    (node : Fin G.nodeCount) (hready : Ready G state.1 node)
    (who : Player) (guard : EventGuard L)
    (hsem : (G.nodeRow node).sem = .commit who guard) :
    (policyValueLaw hwf hguards policies state node hready).map
        PolicyWrite.written =
      (commitValueLaw hwf state.1 (reachable_storeCoherent hwf state.2)
        who (policies who) node
        ⟨G.nodeRow node, guard, G.nodes_get?_nodeRow node, hsem, hready⟩).map
          (fun value => G.nodeTypedValue node value.1) := by
  unfold policyValueLaw
  split
  next branchWho branchGuard branchSem =>
    have hparts := NodeSem.commit.inj (branchSem.symm.trans hsem)
    cases hparts.1
    cases hparts.2
    simp only [FinDist.map_comp]
    rfl
  next dist branchSem => simp [branchSem] at hsem
  next source branchSem => simp [branchSem] at hsem

theorem map_written_policyValueLaw_of_internal [Fintype Player]
    {G : Graph Player L} (hwf : G.WF) (hguards : GuardLive G)
    (policies : CommitPolicyProfile G) (state : ReachableConfig G)
    (node : Fin G.nodeCount) (hready : Ready G state.1 node)
    (hinternal : NodeSem.isInternal (G.nodeRow node).sem = true) :
    (policyValueLaw hwf hguards policies state node hready).map
        PolicyWrite.written =
      (readyEvent hwf hguards state node hready).writeLaw := by
  unfold policyValueLaw
  split
  next who guard hsem => simp [hsem, NodeSem.isInternal] at hinternal
  next dist hsem =>
      simp only [FinDist.map_bindOnSupport]
      rw [FinDist.bindOnSupport_eq_bind_of_eq_on_support
        (g := fun written => FinDist.pure written)]
      · exact FinDist.bind_pure _
      · intro written hwritten
        simp
  next source hsem =>
      simp only [FinDist.map_bindOnSupport]
      rw [FinDist.bindOnSupport_eq_bind_of_eq_on_support
        (g := fun written => FinDist.pure written)]
      · exact FinDist.bind_pure _
      · intro written hwritten
        simp

/-- The reachable successor carried by a supported policy write. -/
def PolicyWrite.next {G : Graph Player L} {state : ReachableConfig G}
    {node : Fin G.nodeCount} (write : PolicyWrite state node) :
    ReachableConfig G :=
  ⟨state.1.completeNode write.event.node write.written,
    Reachable.step state.2 write.event write.supported⟩

/-- A distinct ready node has exactly the same typed policy-write law after a
supported peer write. -/
theorem map_written_policyValueLaw_after_other [Fintype Player]
    {G : Graph Player L} (hwf : G.WF) (hguards : GuardLive G)
    (policies : CommitPolicyProfile G) (state : ReachableConfig G)
    (node other : Fin G.nodeCount)
    (hnodeReady : Ready G state.1 node) (hotherReady : Ready G state.1 other)
    (hne : node ≠ other) (otherWrite : PolicyWrite state other) :
    let after := otherWrite.next
    let hreadyAfter : Ready G after.1 node := by
      apply hnodeReady.completeNode_of_ne
      intro heq
      apply hne
      rw [← otherWrite.event_node]
      exact heq
    (policyValueLaw hwf hguards policies after node hreadyAfter).map
        PolicyWrite.written =
      (policyValueLaw hwf hguards policies state node hnodeReady).map
        PolicyWrite.written := by
  dsimp only
  let hreadyAfter : Ready G (otherWrite.next).1 node := by
    apply hnodeReady.completeNode_of_ne
    intro heq
    apply hne
    rw [← otherWrite.event_node]
    exact heq
  cases hsem : (G.nodeRow node).sem with
  | commit who guard =>
      let beforeCommit : ReadyCommitNode G state.1 who node :=
        ⟨G.nodeRow node, guard, G.nodes_get?_nodeRow node, hsem, hnodeReady⟩
      let afterCommit : ReadyCommitNode G (otherWrite.next).1 who node :=
        ⟨G.nodeRow node, guard, G.nodes_get?_nodeRow node, hsem, hreadyAfter⟩
      rw [map_written_policyValueLaw_of_commit hwf hguards policies
          otherWrite.next node hreadyAfter who guard hsem,
        map_written_policyValueLaw_of_commit hwf hguards policies
          state node hnodeReady who guard hsem]
      obtain ⟨selected, _hselected⟩ :=
        (commitValueLaw hwf state.1 (reachable_storeCoherent hwf state.2)
          who (policies who) node beforeCommit).support_nonempty
      obtain ⟨step⟩ := selected.2
      have hotherReadyEvent : Ready G state.1 otherWrite.event.node := by
        simpa [otherWrite.event_node] using hotherReady
      have hneEvent : node ≠ otherWrite.event.node := by
        simpa [otherWrite.event_node] using hne
      simpa [PolicyWrite.next] using
        commitValueLaw_typed_after_other_ready_write hwf
          (reachable_storeCoherent hwf state.2) who (policies who) node
          otherWrite.event.node beforeCommit
          (G.nodes_get?_nodeRow otherWrite.event.node) hotherReadyEvent
          otherWrite.written (reachable_storeCoherent hwf otherWrite.next.2)
          hneEvent step.guard
          ((congrArg EventNode.sem
            (Option.some.inj ((G.nodes_get?_nodeRow node).symm.trans
              step.row_get))).trans step.sem_eq)
          step.env step.env_ok
  | sample dist =>
      rw [map_written_policyValueLaw_of_internal hwf hguards policies
          otherWrite.next node hreadyAfter (by simp [hsem, NodeSem.isInternal]),
        map_written_policyValueLaw_of_internal hwf hguards policies
          state node hnodeReady (by simp [hsem, NodeSem.isInternal])]
      let beforeEvent := readyEvent hwf hguards state node hnodeReady
      have hbeforeOther : beforeEvent.node ≠ otherWrite.event.node := by
        rw [readyEvent_node, otherWrite.event_node]
        exact hne
      let transported := AvailableEvent.afterWrite hwf beforeEvent
        otherWrite.event otherWrite.written hbeforeOther
      calc
        (readyEvent hwf hguards otherWrite.next node hreadyAfter).writeLaw =
            transported.writeLaw := by
          symm
          apply AvailableEvent.writeLaw_eq_of_node_eq_of_internal
          · simp [transported, beforeEvent]
          · simp [hsem, NodeSem.isInternal, transported, beforeEvent]
        _ = beforeEvent.writeLaw := by simp [transported]
  | reveal source =>
      rw [map_written_policyValueLaw_of_internal hwf hguards policies
          otherWrite.next node hreadyAfter (by simp [hsem, NodeSem.isInternal]),
        map_written_policyValueLaw_of_internal hwf hguards policies
          state node hnodeReady (by simp [hsem, NodeSem.isInternal])]
      let beforeEvent := readyEvent hwf hguards state node hnodeReady
      have hbeforeOther : beforeEvent.node ≠ otherWrite.event.node := by
        rw [readyEvent_node, otherWrite.event_node]
        exact hne
      let transported := AvailableEvent.afterWrite hwf beforeEvent
        otherWrite.event otherWrite.written hbeforeOther
      calc
        (readyEvent hwf hguards otherWrite.next node hreadyAfter).writeLaw =
            transported.writeLaw := by
          symm
          apply AvailableEvent.writeLaw_eq_of_node_eq_of_internal
          · simp [transported, beforeEvent]
          · simp [hsem, NodeSem.isInternal, transported, beforeEvent]
        _ = beforeEvent.writeLaw := by simp [transported]
/-- Execute one requested graph node under declared-read commitment policies.
Ready commitments sample `commitValueLaw` and then use the actual reachable
graph step. Ready internal nodes use the canonical available graph event. A
non-ready request is an explicit no-op, avoiding any fabricated typed value. -/
def policyNodeStep [Fintype Player] {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G)
    (policies : CommitPolicyProfile G)
    (state : ReachableConfig G) (node : Fin G.nodeCount) :
    FinDist (ReachableConfig G) := by
  classical
  if hready : Ready G state.1 node then
    exact (policyValueLaw hwf hguards policies state node hready).map fun write =>
      ⟨state.1.completeNode write.event.node write.written,
        Reachable.step state.2 write.event write.supported⟩
  else
    exact FinDist.pure state

/-- Erasing reachability evidence exposes `policyNodeStep` as the pushforward
of its supported typed-write law through the actual graph update. -/
theorem map_val_policyNodeStep_of_ready [Fintype Player]
    {G : Graph Player L} (hwf : G.WF) (hguards : GuardLive G)
    (policies : CommitPolicyProfile G) (state : ReachableConfig G)
    (node : Fin G.nodeCount) (hready : Ready G state.1 node) :
    (policyNodeStep hwf hguards policies state node).map Subtype.val =
      (policyValueLaw hwf hguards policies state node hready).map fun write =>
        state.1.completeNode node write.written := by
  unfold policyNodeStep
  rw [dif_pos hready, FinDist.map_comp]
  apply FinDist.map_congr_of_eq_on_support
  intro write _
  simp [write.event_node]

/-- Execute a finite requested node order with the actual policy-driven graph
step. Legal topological schedules never take the no-op branch. -/
def runPolicyNodes [Fintype Player] {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G)
    (policies : CommitPolicyProfile G) :
    ReachableConfig G → List (Fin G.nodeCount) → FinDist (ReachableConfig G)
  | state, [] => FinDist.pure state
  | state, node :: rest =>
      (policyNodeStep hwf hguards policies state node).bind fun next =>
        runPolicyNodes hwf hguards policies next rest

@[simp] theorem runPolicyNodes_nil [Fintype Player] {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G)
    (policies : CommitPolicyProfile G) (state : ReachableConfig G) :
    runPolicyNodes hwf hguards policies state [] = FinDist.pure state := rfl

@[simp] theorem runPolicyNodes_cons [Fintype Player] {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G)
    (policies : CommitPolicyProfile G) (state : ReachableConfig G)
    (node : Fin G.nodeCount) (rest : List (Fin G.nodeCount)) :
    runPolicyNodes hwf hguards policies state (node :: rest) =
      (policyNodeStep hwf hguards policies state node).bind fun next =>
        runPolicyNodes hwf hguards policies next rest := rfl

theorem runPolicyNodes_append [Fintype Player] {G : Graph Player L}
    (hwf : G.WF) (hguards : GuardLive G)
    (policies : CommitPolicyProfile G) (state : ReachableConfig G)
    (left right : List (Fin G.nodeCount)) :
    runPolicyNodes hwf hguards policies state (left ++ right) =
      (runPolicyNodes hwf hguards policies state left).bind fun after =>
        runPolicyNodes hwf hguards policies after right := by
  induction left generalizing state with
  | nil => simp
  | cons node rest ih =>
      simp only [List.cons_append, runPolicyNodes_cons, ih,
        FinDist.bind_bind]

theorem policyNodeStep_of_not_ready [Fintype Player]
    {G : Graph Player L} (hwf : G.WF) (hguards : GuardLive G)
    (policies : CommitPolicyProfile G) (state : ReachableConfig G)
    (node : Fin G.nodeCount) (hnot : ¬ Ready G state.1 node) :
    policyNodeStep hwf hguards policies state node = FinDist.pure state := by
  unfold policyNodeStep
  rw [dif_neg hnot]


end Vegas.EventGraph
