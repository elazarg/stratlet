/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.PublicChoiceValidation
import VegasTests.DisclosureAccounting
import VegasTests.DisclosureTrace

/-! # Generated public endpoint for the disclosure response

The source occurrence identifies the responder's adjacent choice and reveal.
The executable public endpoint receives compiler-derived ownership and
readiness metadata. Its native application integration retains the existing
raw message pool and public-service behavior.
-/

noncomputable section

namespace VegasTests.OptionalDisclosure

open Vegas EventGraph Interaction

def responseOccurrence : PublicChoiceSite source.prog where
  context := ResponseContext
  choiceName := 6
  publicName := 7
  owner := 1
  ty := .bool
  guard := .constBool true
  tail := .ret [(0, payoff)]
  decision := .commit (.commit (.reveal (.sample (.commit (.reveal (.here _ _))))))
  adjacent := rfl

def responseCompilerInitial : ToEventGraph.BuildState TestPlayer simpleExpr source.Γ :=
  ToEventGraph.BuildState.fromInitial
    (ToEventGraph.initialState source.Γ source.env source.wctx)

/-- The runtime endpoint is emitted from the actual source occurrence. -/
def responseEndpoint : PublicChoice TestPlayer :=
  responseOccurrence.runtimeSite source.fresh responseCompilerInitial

/-- Retained guard code from the same source decision as the endpoint. -/
def responseGuard : EventGuard simpleExpr :=
  responseOccurrence.compiledGuard source.fresh responseCompilerInitial

theorem responseGuard_no_reads : responseGuard.validationReads = ∅ :=
  responseGuard.validationReads_eq_empty rfl

theorem responseGuard_public : responseGuard.PubliclyValidatable graph := by
  intro ref href
  rw [responseGuard_no_reads] at href
  exact False.elim (Finset.notMem_empty _ href)

/-- This source guard needs no stored values, so the native validator uses
an empty public store. It does not reconstruct an owner view or graph state. -/
def responseValidator (value : Bool) : Bool :=
  responseOccurrence.validator source.fresh responseCompilerInitial (fun _ => none) value

@[simp] theorem responseValidator_true (value : Bool) : responseValidator value = true := by
  have available : ∀ ref, ref ∈ responseGuard.validationReads →
      (Store.getAs (fun _ => none) ref.field ref.ty).isSome := by
    simp [responseGuard_no_reads]
  change responseGuard.validate (fun _ => none) value = true
  unfold EventGuard.validate ReadEnv.ofStoreExec?
  rw [dif_pos available]
  rfl

theorem responseEndpoint_graph :
    responseEndpoint = graph.publicChoice 1 (node 6) (node 7) := rfl

@[simp] theorem responseEndpoint_owner : responseEndpoint.owner = 1 := rfl

@[simp] theorem responseEndpoint_choiceNode : responseEndpoint.choiceNode = 6 := rfl

@[simp] theorem responseEndpoint_publicationNode : responseEndpoint.publicationNode = 7 := rfl

@[simp] theorem responseEndpoint_requires :
    responseEndpoint.requires = graph.publicationPrerequisites (node 6) (node 7) := rfl

end VegasTests.OptionalDisclosure
