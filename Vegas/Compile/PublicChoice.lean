/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.PublicChoice
import Vegas.Compile.ConditionalPublication

/-! # Public choice endpoints from graph metadata

The emitted endpoint consumes public completion flags, an executable validator,
and an authenticated request. The represented graph configuration occurs only
in its correctness proofs. Matching the public validator to the source guard
is a separate obligation; this module does not grant access to private fields.
The endpoint implements a choice and its immediate reveal atomically, with no
claim that their intermediate observations are strategically interchangeable.
-/

namespace Vegas.EventGraph

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}

namespace Graph

/-- Emit an ordinary public choice endpoint for a compiled choice/reveal pair.
Source occurrence evidence supplies the owner and the two node identifiers. -/
def publicChoice (G : Graph Player L) (owner : Player)
    (choice publication : Fin G.nodeCount) : Interaction.PublicChoice Player where
  owner := owner
  choiceNode := choice.val
  publicationNode := publication.val
  requires := G.publicationPrerequisites choice publication

theorem publicChoice_ready (G : Graph Player L) (cfg : Config G)
    (owner : Player) (choice publication : Fin G.nodeCount) (done : Nat → Bool)
    (hcompleted : ∀ node : Fin G.nodeCount, done node.val = true ↔ node ∈ cfg.done)
    (hready : (G.publicChoice owner choice publication).ready done = true) :
    Ready G cfg choice ∧ publication ∉ cfg.done ∧
      G.prereqs publication ⊆ insert choice cfg.done := by
  simp only [PublicChoice.ready, publicChoice, Bool.and_eq_true, Bool.not_eq_true'] at hready
  exact G.publication_ready cfg choice publication done hcompleted
    hready.1.1 hready.1.2 hready.2

end Graph

end Vegas.EventGraph
