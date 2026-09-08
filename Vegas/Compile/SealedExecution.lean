/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.SealedMessages

/-! # Primitive execution laws for sealed-message fragments -/

namespace Vegas.EventGraph

open Interaction GameTheory.Math.Probability

universe uValue

variable {Player : Type} [DecidableEq Player] {Value : Type uValue} {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty}

namespace SealedFragment

/-- A supported commitment row accepts an arbitrary value of the fragment's
common type at any configuration where that node is ready. -/
noncomputable def commitStep (supported : SealedFragment G ty)
    (cfg : Config G) (node : Fin G.nodeCount) (who : Player)
    (guard : EventGuard L)
    (hsem : (G.nodeRow node).sem = .commit who guard)
    (hready : Ready G cfg node) (value : L.Val ty) :
    CommitStep G cfg who ⟨node, ⟨ty, value⟩⟩ := by
  have hguardTy : guard.ty = ty := supported.commitType node who guard hsem
  have hreads : guard.choiceReads = ∅ := supported.commitReads node who guard hsem
  have available : ∀ ref, ref ∈ guard.choiceReads →
      ∃ stored, Store.getAs cfg.store ref.field ref.ty = some stored := by
    intro ref href
    rw [hreads] at href
    simp at href
  let env : ReadEnv L guard.choiceReads :=
    ReadEnv.ofStore cfg.store guard.choiceReads available
  have henv : ReadEnv.ofStore? cfg.store guard.choiceReads = some env := by
    unfold ReadEnv.ofStore?
    rw [dif_pos available]
  refine
    { row := G.nodeRow node
      guard := guard
      row_get := G.nodes_get?_nodeRow node
      sem_eq := hsem
      ready := hready
      value := cast (congrArg L.Val hguardTy.symm) value
      value_ok := ?_
      env := env
      env_ok := henv
      guard_ok := supported.commitGuard node who guard hsem _ env }
  subst ty
  simp [TypedValue.as?]

/-- The commitment witness executes as the exact pure graph write supplied by
the caller. -/
theorem stepCommit_commitStep (supported : SealedFragment G ty)
    (cfg : Config G) (node : Fin G.nodeCount) (who : Player)
    (guard : EventGuard L)
    (hsem : (G.nodeRow node).sem = .commit who guard)
    (hready : Ready G cfg node) (value : L.Val ty) :
    stepCommit G cfg (supported.commitStep cfg node who guard hsem hready value) =
      FinDist.pure (cfg.completeNode node ⟨ty, value⟩) := by
  unfold stepCommit
  rw [CommitStep.written_eq_action
    (supported.commitStep cfg node who guard hsem hready value)]

/-- A supported reveal whose source is present has an internal-step witness. -/
def revealStep (supported : SealedFragment G ty)
    (cfg : Config G) (node : Fin G.nodeCount) (source : Nat)
    (hsem : (G.nodeRow node).sem = .reveal source)
    (hready : Ready G cfg node) (value : L.Val ty)
    (hsource : Store.getAs cfg.store source ty = some value) :
    InternalStep G cfg ⟨node⟩ := by
  have hrowTy : (G.nodeRow node).ty = ty := supported.rowType node
  subst ty
  exact .reveal (G.nodeRow node) source (G.nodes_get?_nodeRow node)
    hsem hready value hsource

/-- The reveal witness deterministically writes the claimed source value. -/
theorem stepInternal_revealStep (supported : SealedFragment G ty)
    (cfg : Config G) (node : Fin G.nodeCount) (source : Nat)
    (hsem : (G.nodeRow node).sem = .reveal source)
    (hready : Ready G cfg node) (value : L.Val ty)
    (hsource : Store.getAs cfg.store source ty = some value) :
    stepInternal G cfg
        (supported.revealStep cfg node source hsem hready value hsource) =
      FinDist.pure (cfg.completeNode node ⟨ty, value⟩) := by
  have hrowTy : (G.nodeRow node).ty = ty := supported.rowType node
  subst ty
  rfl

end SealedFragment

/-- Public application completion and prerequisite checks imply graph
readiness when the event log represents the graph's completed-node set. -/
theorem ready_of_messagePrerequisites
    (events : List (SealedProgram.Event Player Value)) (cfg : Config G)
    (node : Fin G.nodeCount)
    (hcompleted : ∀ query : Fin G.nodeCount,
      SealedProgram.done events query.val = true ↔ query ∈ cfg.done)
    (hnotDone : SealedProgram.done events node.val = false)
    (hrequires : (G.messagePrerequisites node).all
      (SealedProgram.done events) = true) :
    Ready G cfg node := by
  constructor
  · intro hdone
    have : SealedProgram.done events node.val = true := (hcompleted node).2 hdone
    rw [hnotDone] at this
    contradiction
  · intro prior hprior
    apply (hcompleted prior).1
    apply List.all_eq_true.mp hrequires prior.val
    exact (G.mem_messagePrerequisites node prior).2 hprior

end Vegas.EventGraph
