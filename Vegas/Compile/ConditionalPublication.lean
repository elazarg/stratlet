/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.SealedMessages
import Interaction.ConditionalPublication

/-! # Atomic choice and publication from graph metadata

An adjacent source choice and reveal can be implemented by one application
transaction. Its readiness test includes prerequisites of both graph nodes,
except for the choice-to-publication edge discharged inside that transaction.
The operational correspondence uses the existing two primitive graph kernels.
It does not equate their intermediate observations with atomic execution.
-/

namespace Vegas.EventGraph

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}

namespace Graph

/-- External dependencies of a choice followed by its publication. In
particular, earlier commitments required only by the reveal remain present. -/
def publicationPrerequisites (G : Graph Player L)
    (choice publication : Fin G.nodeCount) : List Nat :=
  (G.messagePrerequisites choice ++ G.messagePrerequisites publication).filter
    (fun prior => prior != choice.val)

theorem mem_publicationPrerequisites (G : Graph Player L)
    (choice publication prior : Fin G.nodeCount) :
    prior.val ∈ G.publicationPrerequisites choice publication ↔
      prior ≠ choice ∧ (prior ∈ G.prereqs choice ∨ prior ∈ G.prereqs publication) := by
  simp only [publicationPrerequisites, List.mem_filter, List.mem_append,
    mem_messagePrerequisites, bne_iff_ne]
  rw [Fin.val_injective.ne_iff]
  exact and_comm

/-- Emit public validation metadata. A compiler additionally supplies the
row, binding, and guard correspondence for these nodes. -/
def conditionalPublication (G : Graph Player L) (owner : Player) (sourceSlot : Nat)
    (choice publication : Fin G.nodeCount) (deadline : Nat) :
    Interaction.ConditionalPublication Player where
  owner := owner
  sourceSlot := sourceSlot
  choiceNode := choice.val
  publicationNode := publication.val
  requires := G.publicationPrerequisites choice publication
  deadline := deadline

/-- A successful public readiness check supplies both the first graph
readiness and all external prerequisites of the second graph event. -/
theorem conditionalPublication_ready (G : Graph Player L) (cfg : Config G)
    (owner : Player) (sourceSlot : Nat) (choice publication : Fin G.nodeCount)
    (deadline : Nat) (accepted : Option (CommitmentHandle Player Nat))
    (done : Nat → Bool)
    (hcompleted : ∀ node : Fin G.nodeCount, done node.val = true ↔ node ∈ cfg.done)
    (hready : (G.conditionalPublication owner sourceSlot choice publication deadline).ready
      accepted done = true) :
    Ready G cfg choice ∧ publication ∉ cfg.done ∧
      G.prereqs publication ⊆ insert choice cfg.done := by
  simp only [ConditionalPublication.ready, conditionalPublication, Bool.and_eq_true,
    beq_iff_eq, Bool.not_eq_true'] at hready
  obtain ⟨⟨⟨_, hchoice⟩, hpublication⟩, hrequires⟩ := hready
  have hdone (prior : Fin G.nodeCount) (hne : prior ≠ choice)
      (hprior : prior ∈ G.prereqs choice ∨ prior ∈ G.prereqs publication) :
      prior ∈ cfg.done := by
    apply (hcompleted prior).mp
    apply List.all_eq_true.mp hrequires prior.val
    exact (G.mem_publicationPrerequisites choice publication prior).mpr ⟨hne, hprior⟩
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro hmem
    have := (hcompleted choice).mpr hmem
    simp_all
  · intro prior hprior
    exact hdone prior (fun heq => by
      have hlt := G.prereq_lt hprior
      subst prior
      exact Nat.lt_irrefl _ hlt) (Or.inl hprior)
  · intro hmem
    have := (hcompleted publication).mpr hmem
    simp_all
  · intro prior hprior
    by_cases heq : prior = choice
    · exact Finset.mem_insert.mpr (Or.inl heq)
    · exact Finset.mem_insert_of_mem (hdone prior heq (Or.inr hprior))

end Graph

/-- The choice completes precisely the one internal prerequisite omitted from
the public transaction's readiness test. -/
theorem publication_ready_after_choice {G : Graph Player L} (cfg : Config G)
    (choice publication : Fin G.nodeCount) (value : TypedValue L)
    (hne : publication ≠ choice) (hnotDone : publication ∉ cfg.done)
    (hrequires : G.prereqs publication ⊆ insert choice cfg.done) :
    Ready G (cfg.completeNode choice value) publication := by
  exact ⟨by simpa [Config.completeNode] using And.intro hne hnotDone, hrequires⟩

/-- The second event reads exactly the value just written by the first one. -/
def publicationAfterChoice {G : Graph Player L} (cfg : Config G)
    (choice publication : Fin G.nodeCount)
    (value : L.Val (G.nodeRow publication).ty)
    (hsem : (G.nodeRow publication).sem = .reveal (G.nodeTarget choice))
    (hready : Ready G
      (cfg.completeNode choice ⟨(G.nodeRow publication).ty, value⟩) publication) :
    InternalStep G (cfg.completeNode choice ⟨(G.nodeRow publication).ty, value⟩)
      ⟨publication⟩ :=
  .reveal (G.nodeRow publication) (G.nodeTarget choice)
    (G.nodes_get?_nodeRow publication) hsem hready value
    (by simp [Config.completeNode, Store.getAs, TypedValue.as?])

/-- The macro has the exact effects of a legal commitment and its
deterministic reveal, using the existing primitive kernels. -/
theorem choice_publication_laws {G : Graph Player L} (cfg : Config G)
    (owner : Player) (choice publication : Fin G.nodeCount)
    (value : L.Val (G.nodeRow publication).ty)
    (step : CommitStep G cfg owner ⟨choice, ⟨(G.nodeRow publication).ty, value⟩⟩)
    (hsem : (G.nodeRow publication).sem = .reveal (G.nodeTarget choice))
    (hready : Ready G
      (cfg.completeNode choice ⟨(G.nodeRow publication).ty, value⟩) publication) :
    stepCommit G cfg step =
      FinDist.pure (cfg.completeNode choice ⟨(G.nodeRow publication).ty, value⟩) ∧
    stepInternal G _ (publicationAfterChoice cfg choice publication value hsem hready) =
      FinDist.pure ((cfg.completeNode choice ⟨(G.nodeRow publication).ty, value⟩).completeNode
        publication ⟨(G.nodeRow publication).ty, value⟩) := by
  constructor
  · simp only [stepCommit, step.written_eq_action]
  · rfl

/-- A macro accepted at a represented reachable state produces another
reachable graph state. No intermediate graph event is invented or skipped. -/
theorem reachable_choice_publication {G : Graph Player L} (cfg : Config G)
    (owner : Player) (choice publication : Fin G.nodeCount)
    (value : L.Val (G.nodeRow publication).ty)
    (step : CommitStep G cfg owner ⟨choice, ⟨(G.nodeRow publication).ty, value⟩⟩)
    (hsem : (G.nodeRow publication).sem = .reveal (G.nodeTarget choice))
    (hready : Ready G
      (cfg.completeNode choice ⟨(G.nodeRow publication).ty, value⟩) publication)
    (hreachable : Reachable G cfg) :
    Reachable G ((cfg.completeNode choice ⟨(G.nodeRow publication).ty, value⟩).completeNode
      publication ⟨(G.nodeRow publication).ty, value⟩) := by
  have hlaws := choice_publication_laws cfg owner choice publication value step hsem hready
  have hmid : Reachable G (cfg.completeNode choice ⟨(G.nodeRow publication).ty, value⟩) :=
    Reachable.step hreachable (.commit owner _ step) (by
      change _ ∈ (stepCommit G cfg step).support
      rw [hlaws.1]
      exact FinDist.mem_support_pure.mpr rfl)
  exact Reachable.step hmid
    (.internal ⟨publication⟩ (publicationAfterChoice cfg choice publication value hsem hready))
    (by
      change _ ∈ (stepInternal G _
        (publicationAfterChoice cfg choice publication value hsem hready)).support
      rw [hlaws.2]
      exact FinDist.mem_support_pure.mpr rfl)

end Vegas.EventGraph
