/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.Frontier

/-!
# Source-order observation boundaries

These lemmas combine source-order prerequisites with closure of reachable
completed-node sets.  They state the observation boundary needed when relating
a ready compiled commitment to the written-order source semantics.
-/

namespace Vegas.EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- While a source-earlier commit remains ready, no source-later internal node
can already be complete.  Thus a later sample or reveal cannot publish a value
into the ready commit's observation. -/
theorem ReadyCommitNode.later_internal_not_done
    {G : Graph Player L} {cfg : Config G} {who : Player}
    {commit internal : Fin G.nodeCount}
    {internalRow : EventNode Player L}
    (hreachable : Reachable G cfg)
    (hcommit : ReadyCommitNode G cfg who commit)
    (hinternalRow : G.nodes[internal]? = some internalRow)
    (hlt : (commit : Nat) < (internal : Nat))
    (hinternal : NodeSem.isInternal internalRow.sem = true) :
    internal ∉ cfg.done := by
  rcases hcommit with ⟨commitRow, guard, hcommitRow, hcommitSem, hready⟩
  intro hdone
  have hprereq : commit ∈ G.prereqs internal :=
    G.prior_commit_mem_prereqs_of_internal hinternalRow hcommitRow hlt
      hinternal (by simp [hcommitSem, NodeSem.isCommit])
  have hcommitDone := reachable_donePrereqs hreachable hdone hprereq
  exact hready.1 hcommitDone

/-- A source-later sample cannot have run while an earlier source commit is
still ready. -/
theorem ReadyCommitNode.later_sample_not_done
    {G : Graph Player L} {cfg : Config G} {who : Player}
    {commit sample : Fin G.nodeCount}
    {sampleRow : EventNode Player L}
    {dist : EventDist L}
    (hreachable : Reachable G cfg)
    (hcommit : ReadyCommitNode G cfg who commit)
    (hsampleRow : G.nodes[sample]? = some sampleRow)
    (hlt : (commit : Nat) < (sample : Nat))
    (hsample : sampleRow.sem = .sample dist) :
    sample ∉ cfg.done := by
  apply hcommit.later_internal_not_done hreachable hsampleRow hlt
  simp [hsample, NodeSem.isInternal]

/-- A source-later reveal cannot have run while an earlier source commit is
still ready. -/
theorem ReadyCommitNode.later_reveal_not_done
    {G : Graph Player L} {cfg : Config G} {who : Player}
    {commit reveal : Fin G.nodeCount}
    {revealRow : EventNode Player L}
    {source : Nat}
    (hreachable : Reachable G cfg)
    (hcommit : ReadyCommitNode G cfg who commit)
    (hrevealRow : G.nodes[reveal]? = some revealRow)
    (hlt : (commit : Nat) < (reveal : Nat))
    (hreveal : revealRow.sem = .reveal source) :
    reveal ∉ cfg.done := by
  apply hcommit.later_internal_not_done hreachable hrevealRow hlt
  simp [hreveal, NodeSem.isInternal]

/-- A later commit whose choice footprint contains an earlier ready commit's
target cannot already be complete.  The statement applies in particular to a
later commit by the same player. -/
theorem ReadyCommitNode.later_commit_reading_target_not_done
    {G : Graph Player L} {cfg : Config G} {who : Player}
    {commit later : Fin G.nodeCount}
    {laterRow : EventNode Player L}
    {laterGuard : EventGuard L}
    (hreachable : Reachable G cfg)
    (hcommit : ReadyCommitNode G cfg who commit)
    (hlaterRow : G.nodes[later]? = some laterRow)
    (hlaterSem : laterRow.sem = .commit who laterGuard)
    (hlt : (commit : Nat) < (later : Nat))
    (hread : G.nodeTarget commit ∈ FieldRef.fields laterGuard.choiceReads) :
    later ∉ cfg.done := by
  rcases hcommit with ⟨commitRow, _commitGuard, hcommitRow, _hcommitSem, hready⟩
  intro hdone
  have hsemanticRead : G.nodeTarget commit ∈ laterRow.sem.reads := by
    simpa [hlaterSem, NodeSem.reads] using hread
  have hprereq : commit ∈ G.prereqs later :=
    G.nodeTarget_mem_prereqs_of_read hlaterRow hcommitRow hlt hsemanticRead
  have hcommitDone := reachable_donePrereqs hreachable hdone hprereq
  exact hready.1 hcommitDone

end Vegas.EventGraph
