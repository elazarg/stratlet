/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationPlan

/-! # Node coverage of generated application plans

Each emitted instruction names the exact compiler node or adjacent node pair
that it implements. Flattening those blocks recovers every newly compiled
graph node, in order and exactly once.
-/

noncomputable section

namespace Vegas

open EventGraph ToEventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

namespace ApplicationInstruction

/-- Compiler nodes implemented by one emitted instruction. Public and
conditional publication instructions implement their adjacent choice/reveal
pair atomically. -/
def coveredNodes : ApplicationInstruction P L → List Nat
  | .sample code => [code.node]
  | .bind code => [code.node]
  | .publicChoice code => [code.endpoint.choiceNode, code.endpoint.publicationNode]
  | .conditional code => [code.endpoint.choiceNode, code.endpoint.publicationNode]

omit [DecidableEq P] in
@[simp] theorem address_mem_coveredNodes (instruction : ApplicationInstruction P L) :
    instruction.address ∈ instruction.coveredNodes := by
  cases instruction <;> simp [address, coveredNodes]

end ApplicationInstruction

namespace ApplicationPlan

/-- The emitted instruction blocks are exactly the consecutive graph nodes
added after the incoming compiler cursor. The prefix formulation avoids any
truncated-subtraction side condition. -/
theorem coveredNodes_eq_range
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} (plan : ApplicationPlan accounted fresh state)
    (deadlineOf : Nat → Nat) :
    List.range state.nodes.length ++
        (plan.instructions deadlineOf).flatMap ApplicationInstruction.coveredNodes =
      List.range (compileCore prog fresh state).nodes.length := by
  induction plan with
  | ret => simp [instructions, compileCore]
  | sample next ih =>
      simpa [instructions, headSampleCode, ApplicationInstruction.coveredNodes,
        Graph.sampleCode, compiledNext, compileCore,
        BuildState.addSampleEvent_nodes, List.range_succ, List.append_assoc] using ih
  | binding unrestricted next ih =>
      simpa [instructions, ApplicationInstruction.coveredNodes, compileCore,
        SourceDecisionSite.bindingCode, SourceDecisionSite.compiledNode,
        decisionSiteState, BuildState.addCommitEvent_nodes, List.range_succ,
        List.append_assoc] using ih
  | publicChoice publicGuard next ih =>
      simpa [instructions, ApplicationInstruction.coveredNodes, compileCore,
        PublicChoiceSite.atHead,
        PublicChoiceSite.code, PublicChoiceSite.runtimeSite, Graph.publicChoice,
        PublicChoiceSite.siteState, decisionSiteState,
        BuildState.addCommitEvent_nodes, BuildState.addRevealEvent_nodes,
        List.range_succ, List.append_assoc, Nat.add_assoc] using ih
  | conditional publicGuard next ih =>
      simpa [instructions, ApplicationInstruction.coveredNodes, compileCore,
        CommitmentAccounting.OpeningSite.code,
        CommitmentAccounting.OpeningSite.runtimeSite, Graph.conditionalPublication,
        CommitmentAccounting.OpeningSite.choiceNode,
        CommitmentAccounting.OpeningSite.publicationNode,
        CommitmentAccounting.OpeningSite.data, decisionSiteState,
        BuildState.addCommitEvent_nodes, BuildState.addRevealEvent_nodes,
        List.range_succ, List.append_assoc, Nat.add_assoc] using ih

/-- No generated graph node is covered twice. -/
theorem coveredNodes_nodup
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} (plan : ApplicationPlan accounted fresh state)
    (deadlineOf : Nat → Nat) :
    (plan.instructions deadlineOf).flatMap
      ApplicationInstruction.coveredNodes |>.Nodup := by
  have hcoverage := plan.coveredNodes_eq_range deadlineOf
  have hnodup : (List.range state.nodes.length ++
      (plan.instructions deadlineOf).flatMap
        ApplicationInstruction.coveredNodes).Nodup := by
    rw [hcoverage]
    exact List.nodup_range
  exact (List.nodup_append.mp hnodup).2.1

omit [DecidableEq P] in
private theorem instructionAddresses_sublist
    (instructions : List (ApplicationInstruction P L)) :
    List.Sublist (instructions.map ApplicationInstruction.address)
      (instructions.flatMap ApplicationInstruction.coveredNodes) := by
  induction instructions with
  | nil => exact List.Sublist.slnil
  | cons instruction tail ih =>
      cases instruction with
      | sample code =>
          simpa [ApplicationInstruction.address,
            ApplicationInstruction.coveredNodes] using
              List.Sublist.cons_cons code.node ih
      | bind code =>
          simpa [ApplicationInstruction.address,
            ApplicationInstruction.coveredNodes] using
              List.Sublist.cons_cons code.node ih
      | publicChoice code =>
          simpa [ApplicationInstruction.address,
            ApplicationInstruction.coveredNodes] using
              (List.Sublist.cons_cons code.endpoint.publicationNode ih).cons
                code.endpoint.choiceNode
      | conditional code =>
          simpa [ApplicationInstruction.address,
            ApplicationInstruction.coveredNodes] using
              (List.Sublist.cons_cons code.endpoint.publicationNode ih).cons
                code.endpoint.choiceNode

/-- Dispatch addresses are unique because they form a sublist of the exact
node coverage. -/
theorem instructionAddresses_nodup
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} (plan : ApplicationPlan accounted fresh state)
    (deadlineOf : Nat → Nat) :
    (plan.instructions deadlineOf |>.map ApplicationInstruction.address).Nodup :=
  (plan.coveredNodes_nodup deadlineOf).sublist
    (instructionAddresses_sublist (plan.instructions deadlineOf))

omit [DecidableEq P] in
private theorem lookup_eq_some_of_mem_of_addresses_nodup
    (instructions : List (ApplicationInstruction P L))
    (instruction : ApplicationInstruction P L)
    (hnodup : (instructions.map ApplicationInstruction.address).Nodup)
    (hmem : instruction ∈ instructions) :
    (ApplicationImage.lookup ⟨instructions⟩ instruction.address) = some instruction := by
  induction instructions with
  | nil => simp at hmem
  | cons head tail ih =>
      have hnodup' := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hmem with heq | htail
      · subst instruction
        simp [ApplicationImage.lookup]
      · have haddress : head.address ≠ instruction.address := by
          intro heq
          apply hnodup'.1
          exact List.mem_map.mpr ⟨instruction, htail, heq.symm⟩
        simpa [ApplicationImage.lookup, haddress] using ih hnodup'.2 htail

/-- Membership in the generated instruction list gives the exact dispatcher
lookup result, with no externally supplied uniqueness premise. -/
theorem image_lookup_of_mem
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} (plan : ApplicationPlan accounted fresh state)
    (deadlineOf : Nat → Nat) (instruction : ApplicationInstruction P L)
    (hmem : instruction ∈ plan.instructions deadlineOf) :
    (plan.image deadlineOf).lookup instruction.address = some instruction := by
  exact lookup_eq_some_of_mem_of_addresses_nodup (plan.instructions deadlineOf)
    instruction (plan.instructionAddresses_nodup deadlineOf) hmem

/-- A source-head sample is dispatched at the compiler cursor with its
retained distribution code. No search through the emitted suffix is needed. -/
theorem image_lookup_sample
    {Γ : VCtx P L} {pending : Finset VarId} {name : VarId} {ty : L.Ty}
    {dist : L.DistExpr (erasePubVCtx Γ) ty}
    {tail : VegasCore P L ((name, .pub ty) :: Γ)}
    {accounted : CommitmentAccounting pending tail}
    {fresh : FreshBindings (.sample name dist tail)} {state : BuildState P L Γ}
    (next : ApplicationPlan accounted fresh.2
      (state.addSampleEvent name dist fresh.1).1) (deadlineOf : Nat → Nat) :
    ((ApplicationPlan.sample (fresh := fresh) next).image deadlineOf).lookup state.nodes.length =
      some (.sample (headSampleCode fresh state)) := by
  change ((ApplicationPlan.sample (fresh := fresh) next).image deadlineOf).lookup
    (ApplicationInstruction.sample (P := P) (headSampleCode fresh state)).address = _
  apply (ApplicationPlan.sample (fresh := fresh) next).image_lookup_of_mem deadlineOf
  exact List.mem_cons_self

end ApplicationPlan

end Vegas

/-- info: 'Vegas.ApplicationPlan.coveredNodes_eq_range' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.coveredNodes_eq_range

/-- info: 'Vegas.ApplicationPlan.image_lookup_of_mem' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.image_lookup_of_mem
