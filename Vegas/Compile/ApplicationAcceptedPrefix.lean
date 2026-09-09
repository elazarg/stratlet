/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationBindingOrigins
import Vegas.Compile.ApplicationImageBindingInclusion
import Vegas.Compile.ApplicationPlanCoverage

/-! # Accepted bindings before a source cursor

The source-ordered application proof needs one dynamic fact not contained in
graph refinement: a binding instruction already passed by the source cursor
was actually accepted under its canonical owner and private slot.  Snapshot
values are deliberately absent here.  Registration provenance and graph
agreement recover those values only when a later conditional opening needs
them.
-/

noncomputable section

namespace Vegas.ApplicationImage

open EventGraph ToEventGraph Interaction Interaction.MessageApplication

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Every generated binding strictly before `bound` has its canonical opaque
handle in the actual application state.  Membership is taken in the ambient
image, while the bound is the proof-side source compiler cursor. -/
def AcceptedBindingPrefix (image : ApplicationImage P L) (bound : Nat)
    (state : State P L) : Prop :=
  ∀ code, .bind code ∈ image.instructions → code.node < bound →
    state.memory.accepted code.sourceField = some (code.owner, code.sourceSlot)

namespace AcceptedBindingPrefix

omit [DecidableEq P] in
/-- Before the first generated node there are no binding obligations. -/
theorem zero (image : ApplicationImage P L) (state : State P L) :
    image.AcceptedBindingPrefix 0 state := by
  intro code _ hnode
  omega

omit [DecidableEq P] in
/-- Advance a source cursor across an interval containing no generated binding
node.  The interval premise is static compiler metadata; all dynamic handle
facts below the old cursor are reused from the existing prefix. -/
theorem advance_of_noBinding
    (image : ApplicationImage P L) (lower upper : Nat) (state : State P L)
    (hprefix : image.AcceptedBindingPrefix lower state)
    (hclear : ∀ code, .bind code ∈ image.instructions →
      lower ≤ code.node → code.node < upper → False) :
    image.AcceptedBindingPrefix upper state := by
  intro code hcode hnode
  by_cases hbefore : code.node < lower
  · exact hprefix code hcode hbefore
  · exact False.elim (hclear code hcode (Nat.le_of_not_gt hbefore) hnode)

/-- Exact generated-node coverage advances the prefix across a nonbinding
instruction block.  Any binding in the same node interval would duplicate a
covered node, contradicting the plan's compiler-derived coverage theorem. -/
theorem advance_of_coveredNonbinding
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {build : BuildState P L Γ}
    (plan : ApplicationPlan accounted fresh build) (deadlineOf : Nat → Nat)
    (lower upper : Nat) (state : State P L)
    (instruction : ApplicationInstruction P L)
    (hprefix : (plan.image deadlineOf).AcceptedBindingPrefix lower state)
    (hinstruction : instruction ∈ plan.instructions deadlineOf)
    (hnonbinding : ∀ code, instruction ≠ .bind code)
    (hinterval : ∀ node, lower ≤ node → node < upper →
      node ∈ instruction.coveredNodes) :
    (plan.image deadlineOf).AcceptedBindingPrefix upper state := by
  apply advance_of_noBinding (plan.image deadlineOf) lower upper state hprefix
  intro code hcode hlower hupper
  have hpairwise := (List.nodup_flatMap.mp
    (plan.coveredNodes_nodup deadlineOf)).2
  let : Std.Symm (fun a b : ApplicationInstruction P L =>
      List.Disjoint a.coveredNodes b.coveredNodes) :=
    ⟨fun _ _ hdisjoint => hdisjoint.symm⟩
  have hdisjoint : List.Disjoint instruction.coveredNodes
      (ApplicationInstruction.bind code : ApplicationInstruction P L).coveredNodes := by
    exact hpairwise.forall hinstruction hcode (hnonbinding code)
  exact (List.disjoint_left.mp hdisjoint) (hinterval code.node hlower hupper)
    (by simp [ApplicationInstruction.coveredNodes])

/-- Canonical accepted handles persist through arbitrary supported player and
environment policies over the same image. -/
theorem runPolicies
    (image : ApplicationImage P L) (bound : Nat)
    (players : P → image.application.PlayerPolicy)
    (environment : image.application.EnvironmentPolicy)
    (schedule : List (@Invocation P))
    (execution next : image.application.PolicyExecution)
    (hprefix : image.AcceptedBindingPrefix bound execution.native.application)
    (hnext : next ∈ (image.application.runPolicies players environment schedule
      execution).support) :
    image.AcceptedBindingPrefix bound next.native.application := by
  intro code hcode hnode
  have haccepted := hprefix code hcode hnode
  have hsnapshot : AcceptedSnapshot code.sourceField
      (code.owner, code.sourceSlot)
      (execution.native.application.frozen code.sourceField)
      execution.native.application := ⟨haccepted, rfl⟩
  exact (image.runPolicies_acceptedSnapshot code.sourceField
    (code.owner, code.sourceSlot)
    (execution.native.application.frozen code.sourceField)
    players environment schedule execution next hsnapshot hnext).1

/-- A genuinely accepted generated head binding extends the dynamic prefix by
one node.  Uniqueness comes from the generated plan's exact dispatch-address
coverage, rather than an assumption on an arbitrary image. -/
theorem extend
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {build : BuildState P L Γ}
    (plan : ApplicationPlan accounted fresh build) (deadlineOf : Nat → Nat)
    (bound : Nat) (state : State P L) (code : BindingCode P)
    (hprefix : (plan.image deadlineOf).AcceptedBindingPrefix bound state)
    (hcode : .bind code ∈ plan.instructions deadlineOf)
    (hnode : code.node = bound)
    (snapshot : Option (TypedValue L))
    (haccepted : AcceptedSnapshot code.sourceField
      (code.owner, code.sourceSlot) snapshot state) :
    (plan.image deadlineOf).AcceptedBindingPrefix (bound + 1) state := by
  intro other hother hotherNode
  by_cases hbefore : other.node < bound
  · exact hprefix other hother hbefore
  · have hotherEq : other.node = bound := by omega
    have hotherLookup := plan.image_lookup_of_mem deadlineOf (.bind other) hother
    have hcodeLookup := plan.image_lookup_of_mem deadlineOf (.bind code) hcode
    have hotherLookup' : (plan.image deadlineOf).lookup bound = some (.bind other) := by
      simpa only [ApplicationInstruction.address, hotherEq] using hotherLookup
    have hcodeLookup' : (plan.image deadlineOf).lookup bound = some (.bind code) := by
      simpa only [ApplicationInstruction.address, hnode] using hcodeLookup
    have hinstruction :
        (ApplicationInstruction.bind other : ApplicationInstruction P L) = .bind code := by
      exact Option.some.inj (hotherLookup'.symm.trans hcodeLookup')
    cases hinstruction
    exact haccepted.1

omit [DecidableEq P] in
/-- A conditional instruction whose choice node is the current source cursor
uses the canonical handle of its statically certified earlier binding.  This
is the handle-existence step; frozen-value agreement remains a separate
registration/refinement consequence. -/
theorem conditionalHandle
    {image : ApplicationImage P L} {bound : Nat} {state : State P L}
    (hprefix : image.AcceptedBindingPrefix bound state)
    (horigins : image.HasBindingOrigins)
    (conditional : ConditionalCode P L)
    (hconditional : .conditional conditional ∈ image.instructions)
    (hboundary : conditional.endpoint.choiceNode = bound) :
    state.memory.accepted conditional.sourceField =
      some (conditional.endpoint.owner, conditional.endpoint.sourceSlot) := by
  obtain ⟨before, binding, after, himage, _, horigin⟩ :=
    horigins.origin_of_mem conditional hconditional
  have hbinding : .bind binding ∈ image.instructions := by
    rw [himage]
    simp
  have hnode : binding.node < bound := by
    rw [← hboundary]
    exact horigin.2.2.2
  have haccepted := hprefix binding hbinding hnode
  simpa only [horigin.1, horigin.2.1, horigin.2.2.1] using haccepted

end AcceptedBindingPrefix

end Vegas.ApplicationImage

/-- info: 'Vegas.ApplicationImage.AcceptedBindingPrefix.runPolicies' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.AcceptedBindingPrefix.runPolicies

/-- info: 'Vegas.ApplicationImage.AcceptedBindingPrefix.extend' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.AcceptedBindingPrefix.extend

/-- info:
'Vegas.ApplicationImage.AcceptedBindingPrefix.advance_of_coveredNonbinding' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.AcceptedBindingPrefix.advance_of_coveredNonbinding

/-- info: 'Vegas.ApplicationImage.AcceptedBindingPrefix.conditionalHandle' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.AcceptedBindingPrefix.conditionalHandle
