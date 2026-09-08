/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.Batch

/-!
# Sequential checkpoint scheduling

`primitiveDownsetCheckpointPolicy` is deliberately permissive: where several
nodes are ready it allows any of them to move next, so which node fires is a
scheduler degree of freedom.  On a public runtime that freedom is visible, and
a strategy may condition on it — the target strategy carrier becomes
`Info × Schedule → Action` rather than `Info → Action`.  This information
extension requires its own strategic analysis; it does not by itself prove
failure of a correlation-sensitive solution concept.

This module supplies the opposite endpoint.  Under `sequentialCheckpointPolicy`
exactly one node may fire at each checkpoint, the ready node of least index, so
the completed-node trajectory is a function of the graph alone
(`sequentialCheckpointPolicy_done_congr`): checkpoints agreeing on what has
completed advance to checkpoints agreeing on what has completed, whatever the
players and nature wrote on the way.  The scheduler has no choice left to
expose and a strategy has nothing to condition on beyond the history it already
observes.

Not yet connected to the compiled game: `toExecutionProtocol` builds the
strategic presentation directly and consumes no `CheckpointPolicy`, so these
results constrain the checkpoint layer alone.

The distinction being drawn is between *quotienting* order away in the model
and *enforcing* an order in the compiled artifact.  A runtime realizes this
policy by rejecting every call other than the canonical next one; the ordering
is then inert because the contract made it inert, not because the model
declined to look.

The permissive policy admits independently scheduled calls; the sequential
policy fixes their order.  This module proves the structural distinction,
not liveness or correlated-equilibrium preservation for either policy.
-/

namespace Vegas

namespace EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- `node` is the canonical next mover at `cfg`: it is ready, and every ready
node has at least its index. -/
def IsNextReady (G : Graph Player L) (cfg : Config G)
    (node : Fin G.nodeCount) : Prop :=
  Ready G cfg node ∧ ∀ other, Ready G cfg other → node ≤ other

/-- There is at most one canonical next mover. -/
theorem IsNextReady.unique {G : Graph Player L} {cfg : Config G}
    {left right : Fin G.nodeCount}
    (hleft : IsNextReady G cfg left) (hright : IsNextReady G cfg right) :
    left = right :=
  le_antisymm (hleft.2 right hright.1) (hright.2 left hleft.1)

/-- A canonical next mover is ready. -/
theorem IsNextReady.ready {G : Graph Player L} {cfg : Config G}
    {node : Fin G.nodeCount} (h : IsNextReady G cfg node) :
    Ready G cfg node :=
  h.1

/-- Readiness reads the configuration only through its completed-node set. -/
theorem Ready.congr_done {G : Graph Player L} {cfgLeft cfgRight : Config G}
    (hdone : cfgLeft.done = cfgRight.done) (node : Fin G.nodeCount) :
    Ready G cfgLeft node ↔ Ready G cfgRight node := by
  unfold Ready
  rw [hdone]

/-- So does the canonical next mover. -/
theorem IsNextReady.congr_done {G : Graph Player L}
    {cfgLeft cfgRight : Config G}
    (hdone : cfgLeft.done = cfgRight.done) (node : Fin G.nodeCount) :
    IsNextReady G cfgLeft node ↔ IsNextReady G cfgRight node := by
  unfold IsNextReady
  constructor
  · rintro ⟨hready, hleast⟩
    refine ⟨(Ready.congr_done hdone node).mp hready, ?_⟩
    intro other hother
    exact hleast other ((Ready.congr_done hdone other).mpr hother)
  · rintro ⟨hready, hleast⟩
    refine ⟨(Ready.congr_done hdone node).mpr hready, ?_⟩
    intro other hother
    exact hleast other ((Ready.congr_done hdone other).mp hother)

/-- Every nonterminal configuration has a canonical next mover: the ready set
is nonempty and finitely indexed, so it has a least element. -/
theorem exists_isNextReady (G : Graph Player L) (cfg : Config G)
    (hterminal : ¬ Terminal G cfg) :
    ∃ node : Fin G.nodeCount, IsNextReady G cfg node := by
  classical
  obtain ⟨start, hstart⟩ := exists_ready_of_not_terminal G cfg hterminal
  set ready : Finset (Fin G.nodeCount) :=
    Finset.univ.filter (Ready G cfg) with hready
  have hstartMem : start ∈ ready := by
    simp [hready, hstart]
  have hnonempty : ready.Nonempty := ⟨start, hstartMem⟩
  refine ⟨ready.min' hnonempty, ?_, ?_⟩
  · have hmem := ready.min'_mem hnonempty
    simpa [hready] using hmem
  · intro other hother
    exact ready.min'_le other (by simp [hready, hother])

/-- Sequential checkpoint policy: only the canonical next mover may fire.

Contrast `primitiveDownsetCheckpointPolicy`, which allows every realizable
downset advance. -/
def sequentialCheckpointPolicy (G : Graph Player L) : CheckpointPolicy G where
  allowed src dst :=
    ∃ event : AvailableEvent G src.1,
      IsNextReady G src.1 event.node ∧
        dst.1 ∈ (stepAvailableEvent G src.1 event).support
  realizable := by
    rintro src dst ⟨event, _, hstep⟩
    have hbatch :
        BatchStep G src ⟨dst.1, Reachable.step src.2 event hstep⟩ :=
      BatchStep.singleton src event hstep
    have hdst :
        (⟨dst.1, Reachable.step src.2 event hstep⟩ : ReachableConfig G) = dst :=
      Subtype.ext rfl
    exact ⟨hdst ▸ hbatch⟩
  advances := by
    rintro src dst ⟨event, hnext, hstep⟩
    obtain ⟨written, hwritten⟩ :=
      stepAvailableEvent_support_completeNode event hstep
    rw [hwritten]
    exact Config.done_ssubset_completeNode hnext.ready.1 written

/-- **The sequential schedule carries no information.**

Two checkpoints that have completed the same nodes advance to checkpoints that
have completed the same nodes — whatever values were written on the way, and
whichever run each came from.  Since readiness reads the configuration only
through `done`, the completed-node trajectory of a sequential run is a function
of the graph alone: it is neither a random variable nor a strategic variable,
so there is no scheduler degree of freedom for a strategy to condition on.

This is precisely the property `primitiveDownsetCheckpointPolicy` lacks, and
its absence there is what enlarges the target strategy carrier from
`Info → Action` to `Info × Schedule → Action`.

The values written still differ between runs.  That is the players' and
nature's choice, and it is the game's entire content; what is fixed is *which*
node moves, not what it writes. -/
theorem sequentialCheckpointPolicy_done_congr
    {G : Graph Player L}
    {srcLeft srcRight dstLeft dstRight : ReachableConfig G}
    (hsrc : srcLeft.1.done = srcRight.1.done)
    (hleft : (sequentialCheckpointPolicy G).allowed srcLeft dstLeft)
    (hright : (sequentialCheckpointPolicy G).allowed srcRight dstRight) :
    dstLeft.1.done = dstRight.1.done := by
  obtain ⟨eventLeft, hnextLeft, hstepLeft⟩ := hleft
  obtain ⟨eventRight, hnextRight, hstepRight⟩ := hright
  obtain ⟨writtenLeft, hwrittenLeft⟩ :=
    stepAvailableEvent_support_completeNode eventLeft hstepLeft
  obtain ⟨writtenRight, hwrittenRight⟩ :=
    stepAvailableEvent_support_completeNode eventRight hstepRight
  have hnode : eventLeft.node = eventRight.node :=
    IsNextReady.unique
      ((IsNextReady.congr_done hsrc eventLeft.node).mp hnextLeft) hnextRight
  rw [hwrittenLeft, hwrittenRight]
  simp [Config.completeNode, hnode, hsrc]

/-- Every checkpoint the sequential policy allows from one source completes the
same node.  The single-source case of `sequentialCheckpointPolicy_done_congr`. -/
theorem sequentialCheckpointPolicy_done_determined
    {G : Graph Player L} {src dstLeft dstRight : ReachableConfig G}
    (hleft : (sequentialCheckpointPolicy G).allowed src dstLeft)
    (hright : (sequentialCheckpointPolicy G).allowed src dstRight) :
    dstLeft.1.done = dstRight.1.done :=
  sequentialCheckpointPolicy_done_congr rfl hleft hright

/-- The node completed by an allowed sequential checkpoint is exactly the
canonical next mover of the source. -/
theorem sequentialCheckpointPolicy_done_eq
    {G : Graph Player L} {src dst : ReachableConfig G}
    {node : Fin G.nodeCount}
    (hallowed : (sequentialCheckpointPolicy G).allowed src dst)
    (hnext : IsNextReady G src.1 node) :
    dst.1.done = insert node src.1.done := by
  obtain ⟨event, hnextEvent, hstep⟩ := hallowed
  obtain ⟨written, hwritten⟩ :=
    stepAvailableEvent_support_completeNode event hstep
  have hnode : event.node = node := IsNextReady.unique hnextEvent hnext
  rw [hwritten]
  simp [Config.completeNode, hnode]

/-- **The permissive policy really does leak the schedule.**

Wherever two distinct nodes are simultaneously ready,
`primitiveDownsetCheckpointPolicy` allows two checkpoints from the same source
whose completed-node sets differ.  So the contrast with
`sequentialCheckpointPolicy_done_congr` is a genuine separation rather than an
artefact of how the sequential policy is phrased: under the permissive policy
the completed-node successor is a scheduler choice, and on a public runtime
that choice is observable. -/
theorem primitiveDownsetCheckpointPolicy_done_not_determined
    {G : Graph Player L} (hwf : G.WF) (hguards : GuardLive G)
    {src : ReachableConfig G} {left right : Fin G.nodeCount}
    (hne : left ≠ right)
    (hleft : Ready G src.1 left) (hright : Ready G src.1 right) :
    ∃ dstLeft dstRight : ReachableConfig G,
      (primitiveDownsetCheckpointPolicy G).allowed src dstLeft ∧
        (primitiveDownsetCheckpointPolicy G).allowed src dstRight ∧
          dstLeft.1.done ≠ dstRight.1.done := by
  obtain ⟨eventLeft, hnodeLeft⟩ :=
    exists_availableEvent_of_ready hwf hguards hleft
  obtain ⟨eventRight, hnodeRight⟩ :=
    exists_availableEvent_of_ready hwf hguards hright
  obtain ⟨cfgLeft, hcfgLeft⟩ :=
    (stepAvailableEvent G src.1 eventLeft).support_nonempty
  obtain ⟨cfgRight, hcfgRight⟩ :=
    (stepAvailableEvent G src.1 eventRight).support_nonempty
  obtain ⟨writtenLeft, hwrittenLeft⟩ :=
    stepAvailableEvent_support_completeNode eventLeft hcfgLeft
  obtain ⟨writtenRight, hwrittenRight⟩ :=
    stepAvailableEvent_support_completeNode eventRight hcfgRight
  refine
    ⟨⟨cfgLeft, Reachable.step src.2 eventLeft hcfgLeft⟩,
      ⟨cfgRight, Reachable.step src.2 eventRight hcfgRight⟩,
      ⟨?_, ⟨BatchStep.singleton src eventLeft hcfgLeft⟩⟩,
      ⟨?_, ⟨BatchStep.singleton src eventRight hcfgRight⟩⟩, ?_⟩
  · have hnotDone : eventLeft.node ∉ src.1.done := by
      rw [hnodeLeft]
      exact hleft.1
    change src.1.done ⊂ cfgLeft.done
    rw [hwrittenLeft]
    exact Config.done_ssubset_completeNode hnotDone writtenLeft
  · have hnotDone : eventRight.node ∉ src.1.done := by
      rw [hnodeRight]
      exact hright.1
    change src.1.done ⊂ cfgRight.done
    rw [hwrittenRight]
    exact Config.done_ssubset_completeNode hnotDone writtenRight
  · change cfgLeft.done ≠ cfgRight.done
    rw [hwrittenLeft, hwrittenRight]
    simp only [Config.completeNode, hnodeLeft, hnodeRight]
    intro hcontra
    have hmem : left ∈ insert right src.1.done := by
      rw [← hcontra]
      exact Finset.mem_insert_self left src.1.done
    rcases Finset.mem_insert.mp hmem with heq | hdone
    · exact hne heq
    · exact hleft.1 hdone

/-- Sequential progress.

This obligation is strictly stronger than the permissive one: it is not enough
that *some* node can fire, the *canonical* node must be able to.  That is what
`exists_availableEvent_of_ready` supplies, and it is the price of enforcing a
schedule rather than quotienting one away. -/
def sequentialCheckpointPresentation (G : Graph Player L)
    (hwf : G.WF) (hguards : GuardLive G) : CheckpointPresentation G where
  policy := sequentialCheckpointPolicy G
  nonterminal_exists_allowed := by
    intro state hterminal
    obtain ⟨node, hnext⟩ := exists_isNextReady G state.1 hterminal
    obtain ⟨event, hnode⟩ :=
      exists_availableEvent_of_ready hwf hguards hnext.ready
    obtain ⟨dstCfg, hdst⟩ :=
      (stepAvailableEvent G state.1 event).support_nonempty
    refine ⟨⟨dstCfg, Reachable.step state.2 event hdst⟩, event, ?_, hdst⟩
    rw [hnode]
    exact hnext

end EventGraph

end Vegas
