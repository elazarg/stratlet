/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationPlanCoverage

/-! # Field allocation of generated application instructions

Generated instructions retain the compiler's node-to-field allocation. Opaque
service slots use the original source field, including at conditional openings.
These address facts do not assert that the image contains a preceding binding
instruction for every conditional source field, that such a binding is accepted,
or that a private snapshot represents a legal source value.
-/

noncomputable section

namespace Vegas

open EventGraph ToEventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

namespace ApplicationInstruction

/-- Fields allocated to an instruction, including private binding storage.
An original field consulted by a conditional opening is not allocated again. -/
def allocatedFields : ApplicationInstruction P L → List Nat
  | .sample code => [code.outputField]
  | .bind code => [code.sourceField]
  | .publicChoice code => [code.choiceField, code.publicationField]
  | .conditional code => [code.choiceField, code.publicationField]

/-- Compatibility with the compiler's canonical field and private-slot scheme.
This is an allocation property, not a behavioral correctness certificate. -/
def AllocatedAt (initialFields : Nat) : ApplicationInstruction P L → Prop
  | .sample code => code.outputField = initialFields + code.node
  | .bind code =>
      code.sourceField = initialFields + code.node ∧ code.sourceSlot = code.sourceField
  | .publicChoice code =>
      code.choiceField = initialFields + code.endpoint.choiceNode ∧
        code.publicationField = initialFields + code.endpoint.publicationNode
  | .conditional code =>
      code.choiceField = initialFields + code.endpoint.choiceNode ∧
        code.publicationField = initialFields + code.endpoint.publicationNode ∧
        code.endpoint.sourceSlot = code.sourceField

omit [DecidableEq P] in
theorem allocatedFields_eq_map (instruction : ApplicationInstruction P L)
    (initialFields : Nat) (hallocated : instruction.AllocatedAt initialFields) :
    instruction.allocatedFields = instruction.coveredNodes.map (initialFields + ·) := by
  cases instruction <;> simp_all [AllocatedAt, allocatedFields, coveredNodes]

end ApplicationInstruction

namespace ApplicationPlan

/-- Every emitted instruction uses the same compiler allocation, without an
external field-coherence premise. -/
theorem instructions_allocated
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} (plan : ApplicationPlan accounted fresh state)
    (deadlineOf : Nat → Nat) :
    ∀ instruction ∈ plan.instructions deadlineOf,
      instruction.AllocatedAt state.initialFields.length := by
  induction plan with
  | ret => simp [instructions]
  | sample next ih =>
      simp only [instructions, List.mem_cons]
      intro instruction hmem
      rcases hmem with rfl | hmem
      · simp [ApplicationInstruction.AllocatedAt, headSampleCode,
          Graph.sampleCode, compiledNext, compileCore, Graph.nodeTarget,
          BuildResult.graph, compileCore_initialFields]
      · simpa using ih instruction hmem
  | binding unrestricted next ih =>
      simp only [instructions, List.mem_cons]
      intro instruction hmem
      rcases hmem with rfl | hmem
      · simp [ApplicationInstruction.AllocatedAt, SourceDecisionSite.bindingCode,
          SourceDecisionSite.compiledNode, decisionSiteState, Graph.nodeTarget,
          BuildResult.graph, BuildState.nextField, BuildState.nextNode]
      · simpa using ih instruction hmem
  | publicChoice publicGuard next ih =>
      simp only [instructions, List.mem_cons]
      intro instruction hmem
      rcases hmem with rfl | hmem
      · simp [ApplicationInstruction.AllocatedAt, PublicChoiceSite.code,
          PublicChoiceSite.runtimeSite, Graph.publicChoice, Graph.nodeTarget,
          BuildResult.graph]
      · simpa using ih instruction hmem
  | conditional publicGuard next ih | conditionalCopy spec publicGuard next ih =>
      simp only [instructions, List.mem_cons]
      intro instruction hmem
      rcases hmem with rfl | hmem
      · simp [ApplicationInstruction.AllocatedAt, ConditionalPublicationSite.code,
          ConditionalPublicationSite.runtimeSite, Graph.conditionalPublication,
          Graph.nodeTarget, BuildResult.graph]
      · simpa using ih instruction hmem

/-- Exact field allocation follows from exact node coverage. -/
theorem allocatedFields_eq_map
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} (plan : ApplicationPlan accounted fresh state)
    (deadlineOf : Nat → Nat) :
    (plan.instructions deadlineOf).flatMap ApplicationInstruction.allocatedFields =
      ((plan.instructions deadlineOf).flatMap ApplicationInstruction.coveredNodes).map
        (state.initialFields.length + ·) := by
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro instruction hmem
  exact instruction.allocatedFields_eq_map state.initialFields.length
    (plan.instructions_allocated deadlineOf instruction hmem)

/-- Distinct generated source events cannot allocate the same field. -/
theorem allocatedFields_nodup
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} (plan : ApplicationPlan accounted fresh state)
    (deadlineOf : Nat → Nat) :
    ((plan.instructions deadlineOf).flatMap ApplicationInstruction.allocatedFields).Nodup := by
  rw [plan.allocatedFields_eq_map deadlineOf]
  exact (plan.coveredNodes_nodup deadlineOf).map (by
    intro a b hab
    exact Nat.add_left_cancel hab)

end ApplicationPlan

end Vegas

/-- info: 'Vegas.ApplicationPlan.instructions_allocated' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.instructions_allocated

/-- info: 'Vegas.ApplicationPlan.allocatedFields_nodup' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.allocatedFields_nodup
