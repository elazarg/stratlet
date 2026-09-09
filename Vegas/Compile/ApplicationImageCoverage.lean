/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationPlanAllocation
import Vegas.Compile.ApplicationImageBindings
import Vegas.Compile.ApplicationImageSamples
import Interaction.MessageApplicationPolicyInvariant

/-! # Native coverage of completed generated fields

Allocation relates instruction outputs to completed event flags. Actual message
handling and chance transitions preserve a stored value or accepted canonical
handle at every completed event field. These safety statements quantify arbitrary
player and environment policies; they do not assume source-strategy lifting or
provide typed private values. Owner-local reconstruction additionally uses typed
registration provenance and native-to-graph refinement.
-/

noncomputable section

namespace Vegas.ApplicationImage

open EventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A completed generated event has either a stored value or an accepted
canonical opaque binding at its compiler-allocated field. -/
def Memory.Covers (initialFields : Nat) (memory : Memory P L) : Prop :=
  ∀ node, memory.done node = true →
    (memory.store (initialFields + node)).isSome ∨
      ∃ owner, memory.accepted (initialFields + node) =
        some (owner, initialFields + node)

omit [DecidableEq P] in
theorem Memory.covers_of_done_false (memory : Memory P L) (initialFields : Nat)
    (hdone : ∀ node, memory.done node = false) : memory.Covers initialFields := by
  intro node hcompleted
  rw [hdone node] at hcompleted
  contradiction

theorem State.register_covers (state : State P L) (initialFields : Nat)
    (hcovers : state.memory.Covers initialFields) (who : P) (slot : Nat)
    (value : TypedValue L) :
    (state.register who slot value).memory.Covers initialFields := hcovers

omit [DecidableEq P] in
theorem State.advance_covers (state : State P L) (initialFields clock : Nat)
    (hcovers : state.memory.Covers initialFields) :
    (state.advance clock).memory.Covers initialFields := hcovers

private theorem store_isSome_set (store : Store L) (field : Nat)
    (value : TypedValue L) (query : Nat) (hvalue : (store query).isSome) :
    (store.set field value query).isSome := by
  by_cases heq : query = field
  · subst query
    simp
  · rwa [Store.set_ne store heq]

omit [DecidableEq P] in
theorem State.sample_covers (state : State P L) (code : SampleCode L)
    (initialFields : Nat)
    (hallocated :
      (ApplicationInstruction.sample (P := P) code).AllocatedAt initialFields)
    (value : L.Val code.dist.ty) (hcovers : state.memory.Covers initialFields) :
    (state.sample code value).memory.Covers initialFields := by
  intro node hdone
  change code.outputField = initialFields + code.node at hallocated
  simp only [State.sample, Bool.or_eq_true, beq_iff_eq] at hdone
  rcases hdone with hnode | hold
  · left
    subst node
    rw [← hallocated]
    change (state.memory.store.set code.outputField ⟨code.dist.ty, value⟩
      code.outputField).isSome = true
    simp
  · rcases hcovers node hold with hstored | ⟨owner, howner⟩
    · left
      exact store_isSome_set state.memory.store code.outputField
        ⟨code.dist.ty, value⟩ (initialFields + node) hstored
    · exact Or.inr ⟨owner, howner⟩

omit [DecidableEq P] in
theorem State.publish_covers (state : State P L) (code : PublicChoiceCode P L)
    (initialFields : Nat)
    (hallocated : (ApplicationInstruction.publicChoice code).AllocatedAt initialFields)
    (value : L.Val code.guard.ty) (hcovers : state.memory.Covers initialFields) :
    (state.publish code value).memory.Covers initialFields := by
  intro node hdone
  change code.choiceField = initialFields + code.endpoint.choiceNode ∧
    code.publicationField = initialFields + code.endpoint.publicationNode at hallocated
  simp only [State.publish, Memory.publish, Bool.or_eq_true, beq_iff_eq] at hdone
  rcases hdone with (hchoice | hpublication) | hold
  · left
    subst node
    rw [← hallocated.1]
    apply store_isSome_set
    simp
  · left
    subst node
    rw [← hallocated.2]
    change (((state.memory.store.set code.choiceField ⟨code.guard.ty, value⟩).set
      code.publicationField ⟨code.guard.ty, value⟩) code.publicationField).isSome = true
    simp
  · rcases hcovers node hold with hstored | ⟨owner, howner⟩
    · left
      apply store_isSome_set
      exact store_isSome_set state.memory.store code.choiceField
        ⟨code.guard.ty, value⟩ (initialFields + node) hstored
    · exact Or.inr ⟨owner, howner⟩

omit [DecidableEq P] in
theorem State.publishConditional_covers (state : State P L)
    (code : ConditionalCode P L) (initialFields : Nat)
    (hallocated : (ApplicationInstruction.conditional code).AllocatedAt initialFields)
    (result : Option (L.Val code.secretTy)) (hcovers : state.memory.Covers initialFields) :
    (state.publishConditional code result).memory.Covers initialFields := by
  intro node hdone
  change code.choiceField = initialFields + code.endpoint.choiceNode ∧
    code.publicationField = initialFields + code.endpoint.publicationNode ∧
      code.endpoint.sourceSlot = code.sourceField at hallocated
  simp only [State.publishConditional, Bool.or_eq_true, beq_iff_eq] at hdone
  rcases hdone with (hchoice | hpublication) | hold
  · left
    subst node
    rw [← hallocated.1]
    apply store_isSome_set
    simp
  · left
    subst node
    rw [← hallocated.2.1]
    change (((state.memory.store.set code.choiceField _).set
      code.publicationField _) code.publicationField).isSome = true
    simp
  · rcases hcovers node hold with hstored | ⟨owner, howner⟩
    · left
      apply store_isSome_set
      exact store_isSome_set state.memory.store code.choiceField _
        (initialFields + node) hstored
    · exact Or.inr ⟨owner, howner⟩

omit [DecidableEq P] in
theorem State.bind_covers (state : State P L) (code : BindingCode P)
    (initialFields : Nat)
    (hallocated : (ApplicationInstruction.bind (L := L) code).AllocatedAt initialFields)
    (handle : CommitmentHandle P Nat) (hhandle : handle = (code.owner, code.sourceSlot))
    (hcovers : state.memory.Covers initialFields) :
    (state.bind code handle).memory.Covers initialFields := by
  intro node hdone
  change code.sourceField = initialFields + code.node ∧
    code.sourceSlot = code.sourceField at hallocated
  simp only [State.bind, Bool.or_eq_true, beq_iff_eq] at hdone
  rcases hdone with hnode | hold
  · right
    subst node
    refine ⟨code.owner, ?_⟩
    simp [State.bind, hallocated, hhandle]
  · rcases hcovers node hold with hstored | ⟨owner, howner⟩
    · exact Or.inl hstored
    · right
      by_cases hfield : initialFields + node = code.sourceField
      · exact ⟨code.owner, by simp [State.bind, hfield, hhandle, hallocated]⟩
      · exact ⟨owner, by simpa [State.bind, hfield] using howner⟩

theorem handle_covers (image : ApplicationImage P L) (initialFields : Nat)
    (hallocated : ∀ instruction ∈ image.instructions,
      instruction.AllocatedAt initialFields)
    (state next : State P L) (message : Message P (Payload P L))
    (hcovers : state.memory.Covers initialFields)
    (hnext : image.handle state message = some next) :
    next.memory.Covers initialFields := by
  rcases message with ⟨id, payload⟩
  cases payload with
  | malformed data => simp [ApplicationImage.handle] at hnext
  | choice address typed =>
      cases hlookup : image.lookup address with
      | none => simp [ApplicationImage.handle, hlookup] at hnext
      | some instruction =>
          have hmem := List.mem_of_find?_eq_some hlookup
          cases instruction with
          | sample code => simp [ApplicationImage.handle, hlookup] at hnext
          | bind code => simp [ApplicationImage.handle, hlookup] at hnext
          | conditional code => simp [ApplicationImage.handle, hlookup] at hnext
          | publicChoice code =>
              simp only [ApplicationImage.handle, hlookup, Option.bind_eq_bind,
                Option.bind_some] at hnext
              cases htyped : typed.as? code.guard.ty with
              | none => simp [htyped] at hnext
              | some value =>
                  simp only [htyped, Option.bind_some] at hnext
                  cases hresolved : code.endpoint.resolve? state.memory.done
                      (code.guard.validate state.memory.store) ⟨id, value⟩ with
                  | none => simp [hresolved] at hnext
                  | some accepted =>
                      simp only [hresolved, Option.bind_some] at hnext
                      cases hnext
                      exact state.publish_covers code initialFields
                        (hallocated _ hmem) accepted hcovers
  | binding address handle =>
      cases hlookup : image.lookup address with
      | none => simp [ApplicationImage.handle, hlookup] at hnext
      | some instruction =>
          have hmem := List.mem_of_find?_eq_some hlookup
          cases instruction with
          | sample code => simp [ApplicationImage.handle, hlookup] at hnext
          | publicChoice code => simp [ApplicationImage.handle, hlookup] at hnext
          | conditional code => simp [ApplicationImage.handle, hlookup] at hnext
          | bind code =>
              simp only [ApplicationImage.handle, hlookup, Option.bind_eq_bind,
                Option.bind_some] at hnext
              split at hnext
              · rename_i hadmitted
                cases hnext
                exact state.bind_covers code initialFields (hallocated _ hmem) handle
                  hadmitted.2.1 hcovers
              · contradiction
  | conditional address payload =>
      cases hlookup : image.lookup address with
      | none => simp [ApplicationImage.handle, hlookup] at hnext
      | some instruction =>
          have hmem := List.mem_of_find?_eq_some hlookup
          cases instruction with
          | sample code => simp [ApplicationImage.handle, hlookup] at hnext
          | publicChoice code => simp [ApplicationImage.handle, hlookup] at hnext
          | bind code => simp [ApplicationImage.handle, hlookup] at hnext
          | conditional code =>
              simp only [ApplicationImage.handle, hlookup, Option.bind_eq_bind,
                Option.bind_some] at hnext
              cases hdecoded : code.decode payload with
              | none => simp [hdecoded] at hnext
              | some decoded =>
                  simp only [hdecoded, Option.bind_some] at hnext
                  cases hresolved : code.endpoint.resolve? state.memory.clock
                      (state.verify code) (state.memory.accepted code.sourceField)
                      state.memory.done (code.canOpen state.memory.store)
                      ⟨id, decoded⟩ with
                  | none => simp [hresolved] at hnext
                  | some result =>
                      simp only [hresolved, Option.bind_some] at hnext
                      cases hnext
                      exact state.publishConditional_covers code initialFields
                        (hallocated _ hmem) result hcovers

theorem environmentStep_covers (image : ApplicationImage P L) (initialFields : Nat)
    (hallocated : ∀ instruction ∈ image.instructions,
      instruction.AllocatedAt initialFields)
    (state next : State P L) (command : EnvironmentCommand)
    (hcovers : state.memory.Covers initialFields)
    (hnext : next ∈ (image.application.environmentStep state command).support) :
    next.memory.Covers initialFields := by
  cases command with
  | advance clock =>
      simp only [ApplicationImage.application, FinDist.mem_support_pure] at hnext
      subst next
      exact state.advance_covers initialFields clock hcovers
  | sample address =>
      change next ∈ (image.sample state address).support at hnext
      rcases image.sample_support state address next hnext with rfl | hsampled
      · exact hcovers
      · obtain ⟨code, reads, value, hcode, _, _, _, _, rfl⟩ := hsampled
        exact state.sample_covers code initialFields
          (hallocated _ (List.mem_of_find?_eq_some hcode)) value hcovers

theorem run_memory_covers (image : ApplicationImage P L) (initialFields : Nat)
    (hallocated : ∀ instruction ∈ image.instructions,
      instruction.AllocatedAt initialFields)
    (state next : image.application.State) (actions : List image.application.Action)
    (hcovers : state.application.memory.Covers initialFields)
    (hnext : next ∈ (image.application.run actions state).support) :
    next.application.memory.Covers initialFields := by
  apply image.application.run_application_invariant
    (fun native => native.memory.Covers initialFields)
    (fun native who command h => by cases command; exact native.register_covers _ h _ _ _)
    (fun native message result h hresult =>
      image.handle_covers initialFields hallocated native result message h hresult)
    (fun native command result h hresult =>
      image.environmentStep_covers initialFields hallocated native result command h hresult)
    state next actions hcovers hnext

theorem runPolicies_memory_covers (image : ApplicationImage P L) (initialFields : Nat)
    (hallocated : ∀ instruction ∈ image.instructions,
      instruction.AllocatedAt initialFields)
    (players : P → image.application.PlayerPolicy)
    (environment : image.application.EnvironmentPolicy)
    (schedule : List (@Invocation P))
    (execution next : image.application.PolicyExecution)
    (hcovers : execution.native.application.memory.Covers initialFields)
    (hnext : next ∈ (image.application.runPolicies players environment schedule
      execution).support) : next.native.application.memory.Covers initialFields := by
  exact image.application.runPolicies_application_invariant
    (fun native => native.memory.Covers initialFields)
    (fun native who command h => by cases command; exact native.register_covers _ h _ _ _)
    (fun native message result h hresult =>
      image.handle_covers initialFields hallocated native result message h hresult)
    (fun native command result h hresult =>
      image.environmentStep_covers initialFields hallocated native result command h hresult)
    players environment schedule execution next hcovers hnext

theorem runPolicies_initial_memory_covers (image : ApplicationImage P L)
    (initialFields : Nat)
    (hallocated : ∀ instruction ∈ image.instructions,
      instruction.AllocatedAt initialFields)
    (players : P → image.application.PlayerPolicy)
    (environment : image.application.EnvironmentPolicy)
    (schedule : List (@Invocation P)) (memory : Memory P L)
    (hdone : ∀ node, memory.done node = false)
    (next : image.application.PolicyExecution)
    (hnext : next ∈ (image.application.runPolicies players environment schedule
      (PolicyExecution.initial image.application
        (MessageApplication.State.initial image.application (State.initial memory)))).support) :
    next.native.application.memory.Covers initialFields := by
  exact image.runPolicies_memory_covers initialFields hallocated players environment schedule
    _ next (memory.covers_of_done_false initialFields hdone) hnext

end Vegas.ApplicationImage

namespace Vegas.ApplicationPlan

open EventGraph ToEventGraph Interaction Interaction.MessageApplication

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A structurally generated image covers every completed event field in every
supported policy execution from its canonical public-memory initialization. -/
theorem runPolicies_memory_covers
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} (plan : ApplicationPlan accounted fresh state)
    (deadlineOf : Nat → Nat)
    (players : P → (plan.image deadlineOf).application.PlayerPolicy)
    (environment : (plan.image deadlineOf).application.EnvironmentPolicy)
    (schedule : List (@Invocation P))
    (next : (plan.image deadlineOf).application.PolicyExecution)
    (hnext : next ∈ ((plan.image deadlineOf).application.runPolicies
      players environment schedule
      (PolicyExecution.initial (plan.image deadlineOf).application
        (MessageApplication.State.initial (plan.image deadlineOf).application
          (ApplicationImage.State.initial
            (ApplicationImage.Memory.initial (compileCore prog fresh state).graph))))).support) :
    next.native.application.memory.Covers state.initialFields.length := by
  apply (plan.image deadlineOf).runPolicies_initial_memory_covers
    state.initialFields.length
    (memory := ApplicationImage.Memory.initial (compileCore prog fresh state).graph)
  · intro instruction hmem
    exact plan.instructions_allocated deadlineOf instruction hmem
  · intro node
    rfl
  · exact hnext

end Vegas.ApplicationPlan

/-- info: 'Vegas.ApplicationPlan.runPolicies_memory_covers' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.runPolicies_memory_covers
