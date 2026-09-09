/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.BindingSourceCoupling
import Vegas.Compile.SourceExecutionOutcome
import VegasTests.GeneratedBindingPolicy

/-! # Generated opaque-binding source successor

The persistent-disclosure fixture's actual pending binding is included through
the shared application handler.  Its privately prepared bit becomes both the
accepted snapshot and the value of the exact one-node source continuation.
-/

noncomputable section

namespace VegasTests.BindingSourceCoupling

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction
open VegasTests.PersistentDisclosure
open VegasTests.GeneratedPersistentDisclosure
open VegasTests.GeneratedBindingPolicy

def checkpoint : CoupledAt GeneratedPersistentDisclosure.compiled.graph compilerInitial :=
  compiledInitialCoupled source

def nextBuild : BuildState TestPlayer simpleExpr [(0, .sealed 0 .bool)] :=
  (compilerInitial.addCommitEvent (actionName := 0) (actionTy := BaseTy.bool)
    0 0 (.constBool true) source.fresh.1).1

private theorem image_lookup_binding : image.lookup 0 = some (.bind code) := by
  have hmem : (ApplicationInstruction.bind code) ∈
      applicationPlan.instructions (fun _ => 10) := by
    change _ ∈ [ApplicationInstruction.bind code, _, _, _, _, _]
    simp
  exact applicationPlan.image_lookup_of_mem (fun _ => 10) _ hmem

/-- The real canonical inclusion fixes the source continuation to the cached
secret and retains complete native refinement and snapshot provenance. -/
theorem included_source_successor (secret : Bool) :
    ∃ next : CoupledAt GeneratedPersistentDisclosure.compiled.graph nextBuild,
      next.current.source = source.env.cons secret ∧
      (included secret).native.application.Refines next.current.graph.1 ∧
      ApplicationImage.AcceptedSnapshot (L := simpleExpr) 0 (0, 0)
        (some ⟨.bool, secret⟩) (included secret).native.application := by
  have hrefines : (submitted secret).native.application.Refines
      checkpoint.current.graph.1 := by
    exact (ApplicationImage.State.initial_refines
      GeneratedPersistentDisclosure.compiled.graph).register
      0 0 ⟨.bool, secret⟩
  obtain ⟨next, hsource, hrefinesNext, hsnapshot⟩ :=
    SourceDecisionSite.include_binding_source_coupling
      (P := TestPlayer) (L := simpleExpr)
      (.constBool true) _ source.fresh compilerInitial checkpoint image
      (submitted secret).native hrefines 0 0 image_lookup_binding secret
      (by rfl) (by rfl) (by rfl)
  have hcheckpointSource : checkpoint.current.source = source.env := rfl
  have hincludedNative : (included secret).native =
      image.application.includePending (submitted secret).native (0, 0) := rfl
  refine ⟨next, ?_, ?_, ?_⟩
  · rw [← hcheckpointSource]
    exact hsource
  · rw [hincludedNative]
    exact hrefinesNext
  · rw [hincludedNative]
    change ApplicationImage.AcceptedSnapshot (L := simpleExpr) 0 (0, 0)
      (some ⟨.bool, secret⟩)
      (image.application.includePending (submitted secret).native (0, 0)).application
      at hsnapshot
    exact hsnapshot

end VegasTests.BindingSourceCoupling

/-- info: 'VegasTests.BindingSourceCoupling.included_source_successor' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.BindingSourceCoupling.included_source_successor
