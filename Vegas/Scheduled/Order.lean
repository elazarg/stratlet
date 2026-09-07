/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.Frontier
import Mathlib.Data.Finset.Sort

/-!
# Executable ordering for compiled strategic frontiers

This module contains only the data-level public activity test and deterministic
ordering policy.  In particular, it is outside a `noncomputable section`: a
backend with a finite linearly ordered player representation can execute
`fixedOrder` directly.
-/

namespace Vegas.EventGraph

open EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- Readiness computed solely from the public completed-node set. -/
def ReadyAtView (G : Graph Player L) (seen : PublicObservation G)
    (node : Fin G.nodeCount) : Prop :=
  node ∉ seen.done ∧ G.prereqs node ⊆ seen.done

instance instDecidableReadyAtView (G : Graph Player L)
    (seen : PublicObservation G) (node : Fin G.nodeCount) :
    Decidable (ReadyAtView G seen node) := by
  unfold ReadyAtView
  infer_instance

/-- A ready public node is a commit owned by `who`. -/
def ReadyCommitAtView (G : Graph Player L) (seen : PublicObservation G)
    (who : Player) (node : Fin G.nodeCount) : Prop :=
  ReadyAtView G seen node ∧
    match (G.nodeRow node).sem with
    | .commit owner _ => owner = who
    | _ => False

instance instDecidableReadyCommitAtView (G : Graph Player L)
    (seen : PublicObservation G) (who : Player)
    (node : Fin G.nodeCount) :
    Decidable (ReadyCommitAtView G seen who node) := by
  unfold ReadyCommitAtView
  split <;> infer_instance

/-- A ready public node is automatic (sample or reveal). -/
def ReadyInternalAtView (G : Graph Player L) (seen : PublicObservation G)
    (node : Fin G.nodeCount) : Prop :=
  ReadyAtView G seen node ∧
    match (G.nodeRow node).sem with
    | .sample _ => True
    | .reveal _ => True
    | .commit _ _ => False

instance instDecidableReadyInternalAtView (G : Graph Player L)
    (seen : PublicObservation G) (node : Fin G.nodeCount) :
    Decidable (ReadyInternalAtView G seen node) := by
  unfold ReadyInternalAtView
  split <;> infer_instance

/-- The public activity predicate used by executable ordering. -/
def ActiveAtPublicView (G : Graph Player L) (seen : PublicObservation G)
    (who : Player) : Prop :=
  (∃ node : Fin G.nodeCount, node ∉ seen.done) ∧
    (∀ node : Fin G.nodeCount, ¬ ReadyInternalAtView G seen node) ∧
    ∃ node : Fin G.nodeCount, ReadyCommitAtView G seen who node

instance instDecidableActiveAtPublicView (G : Graph Player L)
    (seen : PublicObservation G) (who : Player) :
    Decidable (ActiveAtPublicView G seen who) := by
  unfold ActiveAtPublicView
  infer_instance

/-- Sort the publicly active players by the backend's concrete player order. -/
def fixedOrder [Fintype Player] [LinearOrder Player]
    (G : Graph Player L)
    (seen : PublicObservation G) : List Player :=
  ((Finset.univ : Finset Player).filter
    (ActiveAtPublicView G seen)).sort (· ≤ ·)

end Vegas.EventGraph
