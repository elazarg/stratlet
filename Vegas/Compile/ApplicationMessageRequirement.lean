/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationPlanCoverage
import Vegas.Compile.ApplicationImageSamples

/-! # Completion that requires an owner-authored message

Opaque bindings and ordinary public choices have authenticated entry points.
Their generated node blocks are disjoint from every other instruction's
effects. Consequently neither clock advancement, chance invocation, nor a
message authored by another principal can complete one of these nodes.

Conditional publication is deliberately excluded: its permissionless expiry
entry point can complete its node pair without an owner-authored request.
-/

noncomputable section

namespace Vegas.ApplicationImage

open EventGraph Interaction

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- An inspectable property of emitted code: every instruction that can write
this completion flag requires a message authored by the designated principal.
It is not a scheduling or player-policy assumption. -/
def RequiresSubmission (image : ApplicationImage P L) (node : Nat) (who : P) : Prop :=
  ∀ instruction ∈ image.instructions, node ∈ instruction.coveredNodes →
    match instruction with
    | .bind code => code.owner = who
    | .publicChoice code => code.endpoint.owner = who
    | .sample _ | .conditional _ => False

theorem RequiresSubmission.privateStep
    {image : ApplicationImage P L} {node : Nat} (state : State P L)
    (actor : P) (command : image.application.PrivateCommand)
    (hnotDone : state.memory.done node = false) :
    (image.application.privateStep state actor command).memory.done node = false := by
  cases command
  exact hnotDone

/-- Arbitrary clock advances and supported chance draws cannot execute an
authenticated player-choice instruction. -/
theorem RequiresSubmission.environmentStep
    {image : ApplicationImage P L} {node : Nat} {who : P}
    (required : image.RequiresSubmission node who)
    (state : State P L) (command : image.application.EnvironmentCommand)
    (next : State P L) (hnotDone : state.memory.done node = false)
    (hnext : next ∈ (image.application.environmentStep state command).support) :
    next.memory.done node = false := by
  cases command with
  | advance clock =>
      simp only [application, GameTheory.Math.Probability.FinDist.mem_support_pure] at hnext
      subst next
      exact hnotDone
  | sample address =>
      rcases image.sample_support state address next hnext with rfl |
        ⟨code, reads, value, hcode, _, _, _, _, rfl⟩
      · exact hnotDone
      · have hne : node ≠ code.node := by
          intro heq
          exact required (.sample code) (List.mem_of_find?_eq_some hcode)
            (by simp [ApplicationInstruction.coveredNodes, heq])
        simp [State.sample, hne, hnotDone]

/-- A successfully included message from another principal cannot complete
this node. Rejection is handled by the shared transactional interpreter. -/
theorem RequiresSubmission.handle
    {image : ApplicationImage P L} {node : Nat} {who : P}
    (required : image.RequiresSubmission node who)
    (state : State P L) (message : Message P (Payload P L)) (next : State P L)
    (hnotDone : state.memory.done node = false) (hsender : message.sender ≠ who)
    (hnext : image.handle state message = some next) :
    next.memory.done node = false := by
  obtain ⟨id, payload⟩ := message
  cases payload with
  | malformed data => simp [ApplicationImage.handle] at hnext
  | binding address handle =>
      cases hlookup : image.lookup address with
      | none => simp [ApplicationImage.handle, hlookup] at hnext
      | some instruction =>
          cases instruction with
          | sample code | publicChoice code | conditional code =>
              simp [ApplicationImage.handle, hlookup] at hnext
          | bind code =>
              simp only [ApplicationImage.handle, hlookup, Option.bind_eq_bind,
                Option.bind_some] at hnext
              split at hnext
              · rename_i hadmitted
                cases hnext
                have hne : node ≠ code.node := by
                  intro heq
                  have howner := required (.bind code)
                    (List.mem_of_find?_eq_some hlookup)
                    (by simp [ApplicationInstruction.coveredNodes, heq])
                  exact hsender (hadmitted.1.trans howner)
                simp [State.bind, hne, hnotDone]
              · contradiction
  | choice address typed =>
      cases hlookup : image.lookup address with
      | none => simp [ApplicationImage.handle, hlookup] at hnext
      | some instruction =>
          cases instruction with
          | sample code | bind code | conditional code =>
              simp [ApplicationImage.handle, hlookup] at hnext
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
                      have hne : node ∉
                          (ApplicationInstruction.publicChoice code).coveredNodes := by
                        intro hnode
                        have howner := required (.publicChoice code)
                          (List.mem_of_find?_eq_some hlookup) hnode
                        exact hsender (((code.endpoint.resolve_iff _ _ _ _).mp
                          hresolved).2.1.trans howner)
                      simp [ApplicationInstruction.coveredNodes] at hne
                      simp [State.publish, Memory.publish, hne.1, hne.2, hnotDone]
  | conditional address payload =>
      cases hlookup : image.lookup address with
      | none => simp [ApplicationImage.handle, hlookup] at hnext
      | some instruction =>
          cases instruction with
          | sample code | bind code | publicChoice code =>
              simp [ApplicationImage.handle, hlookup] at hnext
          | conditional code =>
              simp only [ApplicationImage.handle, hlookup, Option.bind_eq_bind,
                Option.bind_some] at hnext
              cases hdecoded : code.decode payload with
              | none => simp [hdecoded] at hnext
              | some decoded =>
                  simp only [hdecoded, Option.bind_some] at hnext
                  cases hresolved : code.endpoint.resolve? state.memory.clock
                      (state.verify code) (state.memory.accepted code.sourceField)
                      state.memory.done (code.canOpen state.memory.store) ⟨id, decoded⟩ with
                  | none => simp [hresolved] at hnext
                  | some result =>
                      simp only [hresolved, Option.bind_some] at hnext
                      cases hnext
                      have hne : node ∉
                          (ApplicationInstruction.conditional code).coveredNodes :=
                        required (.conditional code) (List.mem_of_find?_eq_some hlookup)
                      simp [ApplicationInstruction.coveredNodes] at hne
                      simp [State.publishConditional, hne.1, hne.2, hnotDone]

end Vegas.ApplicationImage

namespace Vegas.ApplicationPlan

open EventGraph ToEventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Generated node-block disjointness makes the authenticated entry point
the only instruction capable of completing any node in its block. -/
theorem requiresSubmission
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} (plan : ApplicationPlan accounted fresh state)
    (deadlineOf : Nat → Nat) (instruction : ApplicationInstruction P L)
    (hinstruction : instruction ∈ plan.instructions deadlineOf)
    (node : Nat) (hnode : node ∈ instruction.coveredNodes) (who : P)
    (hauthor : match instruction with
      | .bind code => code.owner = who
      | .publicChoice code => code.endpoint.owner = who
      | .sample _ | .conditional _ => False) :
    (plan.image deadlineOf).RequiresSubmission node who := by
  intro other hother hcovered
  by_cases heq : instruction = other
  · subst other
    cases instruction <;> exact hauthor
  · have hpairwise := (List.nodup_flatMap.mp (plan.coveredNodes_nodup deadlineOf)).2
    let : Std.Symm (fun a b : ApplicationInstruction P L =>
        List.Disjoint a.coveredNodes b.coveredNodes) :=
      ⟨fun _ _ hdisjoint => hdisjoint.symm⟩
    exact False.elim ((List.disjoint_left.mp
      (hpairwise.forall hinstruction hother heq)) hnode hcovered)

end Vegas.ApplicationPlan

/-- info: 'Vegas.ApplicationPlan.requiresSubmission' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.requiresSubmission
