/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.DisclosureTrace

/-! # Publication ordering at the optional-disclosure site -/

noncomputable section

namespace VegasTests.OptionalDisclosure

open Vegas EventGraph

/-- At the actual optional-disclosure site, readiness of the private choice
already supplies every external prerequisite of its adjacent publication. -/
theorem opening_ready_publication_prerequisites (state : Config graph)
    (hready : Ready graph state (node 4)) :
    graph.prereqs (node 5) ⊆ insert (node 4) state.done := by
  intro prior hprior
  have hstructural : graph.prereqs (node 5) ⊆
      insert (node 4) (graph.prereqs (node 4)) := by decide
  rcases Finset.mem_insert.mp (hstructural hprior) with heq | hchoice
  · exact Finset.mem_insert.mpr (Or.inl heq)
  · exact Finset.mem_insert_of_mem (hready.2 hchoice)

/-- Once the ready choice is written, its adjacent publication is ready
without waiting for another external graph event. -/
theorem opening_publication_ready_after_choice (state : Config graph)
    (opening : Option Bool) (hchoice : Ready graph state (node 4))
    (hpublication : node 5 ∉ state.done) :
    Ready graph (state.completeNode (node 4) ⟨.option .bool, opening⟩) (node 5) := by
  constructor
  · simp only [Config.completeNode, Finset.mem_insert]
    exact fun h => h.elim (by decide) hpublication
  · exact opening_ready_publication_prerequisites state hchoice

/-- The responder's choice cannot become ready before publication completes. -/
theorem response_ready_requires_publication (state : Config graph)
    (hready : Ready graph state (node 6)) : node 5 ∈ state.done :=
  hready.2 response_after_opening

/-- The adjacent graph writes leave the selected optional value in its public
field. -/
theorem opening_macro_field (state : Config graph) (opening : Option Bool) :
    Store.getAs
      ((state.completeNode (node 4) ⟨.option .bool, opening⟩).completeNode
        (node 5) ⟨.option .bool, opening⟩).store 5 (.option .bool) = some opening := by
  simp only [Config.completeNode]
  rw [show graph.nodeTarget (node 5) = 5 from rfl]
  simp [Store.getAs, TypedValue.as?]

/-- Completing the optional publication does not expose the retained original
binding to the responder. -/
theorem opening_macro_original_hidden (state : Config graph) (opening : Option Bool)
    (index : Fin graph.nodeCount) :
    (observe graph
      ((state.completeNode (node 4) ⟨.option .bool, opening⟩).completeNode
        (node 5) ⟨.option .bool, opening⟩) (1 : TestPlayer)).fieldValue? index 0 = none :=
  original_absent_from_response _ index

end VegasTests.OptionalDisclosure
