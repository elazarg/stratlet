/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.PublicChoiceSourceCoupling
import Vegas.Compile.SourceExecutionOutcome
import VegasTests.ApplicationImage

/-! # A generated publication preserves its written-source continuation

The guarded first publication of the mixed-type application executes through
the real inclusion handler. The resulting state is related to the exact source
continuation, with both source bindings and the advanced compiler prefix.
-/

noncomputable section

namespace VegasTests.PublicChoiceSourceCoupling

open Vegas Vegas.EventGraph Vegas.ToEventGraph
open VegasTests.ApplicationImage

def checkpoint : CoupledAt ApplicationImage.compiled.graph compilerInitial :=
  compiledInitialCoupled source

def nextBuild :=
  (((compilerInitial.addCommitEvent 1 0 firstGuard source.fresh.1).1).addRevealEvent
    2 0 .here source.fresh.2.1).1

theorem included_source_successor :
    ∃ next : CoupledAt ApplicationImage.compiled.graph nextBuild,
      next.current.source = (source.env.cons true).cons true ∧
      firstIncluded.application.Refines next.current.graph.1 := by
  exact PublicChoiceSite.include_source_coupling (P := Fin 2) (L := simpleExpr)
    (Γ := InitialContext) (name := 1) (publicName := 2) (who := 0) (ty := .bool)
    firstGuard firstTail source.fresh
    compilerInitial checkpoint image firstSubmitted (Vegas.ApplicationImage.State.initial_refines _)
    first_publicly_validatable firstAddress 0 image_lookup_first true (by rfl) (by rfl)

/-- A second owner's differently typed choice uses the first inclusion's
coupled continuation in the same final graph, rather than reinitializing it. -/
theorem final_source_successor :
    ∃ next : CoupledAt ApplicationImage.compiled.graph
        (((nextBuild.addCommitEvent 3 1 secondGuard source.fresh.2.2.1).1).addRevealEvent
          4 1 .here source.fresh.2.2.2.1).1,
      next.current.source =
        (((source.env.cons true).cons true).cons (some false)).cons (some false) ∧
      finalExecution.application.Refines next.current.graph.1 := by
  obtain ⟨first, hsource, hrefines⟩ := included_source_successor
  obtain ⟨next, hnextSource, hnextRefines⟩ := PublicChoiceSite.include_source_coupling
    (P := Fin 2) (L := simpleExpr) (Γ := FirstPublishedContext)
    (name := 3) (publicName := 4) (who := 1) (ty := .option .bool)
    secondGuard secondTail source.fresh.2.2 nextBuild first image secondSubmitted hrefines
    second_publicly_validatable secondAddress 0 image_lookup_second (some false)
    (by rfl) (by rfl)
  exact ⟨next, hnextSource.trans (by rw [hsource]), hnextRefines⟩

end VegasTests.PublicChoiceSourceCoupling

/-- info: 'VegasTests.PublicChoiceSourceCoupling.included_source_successor' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.PublicChoiceSourceCoupling.included_source_successor

/-- info: 'VegasTests.PublicChoiceSourceCoupling.final_source_successor' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.PublicChoiceSourceCoupling.final_source_successor
