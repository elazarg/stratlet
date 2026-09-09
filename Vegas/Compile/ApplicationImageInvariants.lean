/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationImageSamples
import Interaction.MessageApplicationLaws
import Interaction.MessageApplicationPolicyLaws

/-! # Application-image snapshot invariants

An accepted binding fixes both its public handle and its private frozen
snapshot. This is field-local and requires no well-formedness relation between
the instructions in an image.
-/

noncomputable section

namespace Vegas.ApplicationImage

open EventGraph Interaction GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- The accepted handle and frozen verifier captured at one source field. The
snapshot may be absent or dynamically ill-typed. -/
def AcceptedSnapshot (field : Nat) (handle : CommitmentHandle P Nat)
    (snapshot : Option (TypedValue L)) (state : State P L) : Prop :=
  state.memory.accepted field = some handle ∧ state.frozen field = snapshot

theorem privateStep_acceptedSnapshot (image : ApplicationImage P L)
    (field : Nat) (handle : CommitmentHandle P Nat)
    (snapshot : Option (TypedValue L)) (state : State P L) (who : P)
    (command : image.application.PrivateCommand)
    (hstate : AcceptedSnapshot field handle snapshot state) :
    AcceptedSnapshot field handle snapshot
      (image.application.privateStep state who command) := by
  cases command
  exact hstate

theorem environmentStep_acceptedSnapshot (image : ApplicationImage P L)
    (field : Nat) (handle : CommitmentHandle P Nat)
    (snapshot : Option (TypedValue L)) (state : State P L)
    (command : image.application.EnvironmentCommand) (next : State P L)
    (hstate : AcceptedSnapshot field handle snapshot state)
    (hnext : next ∈ (image.application.environmentStep state command).support) :
    AcceptedSnapshot field handle snapshot next := by
  cases command with
  | advance clock =>
      simp only [application, FinDist.mem_support_pure] at hnext
      subst next
      exact hstate
  | sample address =>
      change next ∈ (image.sample state address).support at hnext
      rcases image.sample_support state address next hnext with rfl |
        ⟨code, reads, value, _, _, _, _, _, rfl⟩
      · exact hstate
      · exact hstate

theorem handle_acceptedSnapshot (image : ApplicationImage P L)
    (field : Nat) (acceptedHandle : CommitmentHandle P Nat)
    (snapshot : Option (TypedValue L)) (state : State P L)
    (message : Message P (Payload P L)) (next : State P L)
    (hstate : AcceptedSnapshot field acceptedHandle snapshot state)
    (hnext : image.application.handle state message = some next) :
    AcceptedSnapshot field acceptedHandle snapshot next := by
  change image.handle state message = some next at hnext
  rcases hstate with ⟨haccepted, hfrozen⟩
  cases message with
  | mk id payload =>
      cases payload with
      | malformed data => simp [ApplicationImage.handle] at hnext
      | choice address typed =>
          cases hlookup : image.lookup address with
          | none => simp [ApplicationImage.handle, hlookup] at hnext
          | some instruction =>
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
                          exact ⟨haccepted, hfrozen⟩
      | binding address bindingHandle =>
          cases hlookup : image.lookup address with
          | none => simp [ApplicationImage.handle, hlookup] at hnext
          | some instruction =>
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
                    have hne : code.sourceField ≠ field := by
                      intro heq
                      have hempty : state.memory.accepted code.sourceField = none :=
                        hadmitted.2.2.1
                      rw [heq, haccepted] at hempty
                      contradiction
                    have hne' : field ≠ code.sourceField := Ne.symm hne
                    exact ⟨by simpa [State.bind, hne'] using haccepted,
                      by simpa [State.bind, hne'] using hfrozen⟩
                  · contradiction
      | conditional address payload =>
          cases hlookup : image.lookup address with
          | none => simp [ApplicationImage.handle, hlookup] at hnext
          | some instruction =>
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
                          exact ⟨haccepted, hfrozen⟩

/-- Accepted snapshots persist through every supported native action list. -/
theorem run_acceptedSnapshot (image : ApplicationImage P L)
    (field : Nat) (handle : CommitmentHandle P Nat)
    (snapshot : Option (TypedValue L))
    (state next : image.application.State) (actions : List image.application.Action)
    (hstate : AcceptedSnapshot field handle snapshot state.application)
    (hnext : next ∈ (image.application.run actions state).support) :
    AcceptedSnapshot field handle snapshot next.application := by
  exact image.application.run_application_invariant
    (AcceptedSnapshot field handle snapshot)
    (privateStep_acceptedSnapshot image field handle snapshot)
    (handle_acceptedSnapshot image field handle snapshot)
    (environmentStep_acceptedSnapshot image field handle snapshot)
    state next actions hstate hnext

/-- Accepted snapshots persist under arbitrary players, environments, and
policy schedules over the same application image. -/
theorem runPolicies_acceptedSnapshot (image : ApplicationImage P L)
    (field : Nat) (handle : CommitmentHandle P Nat)
    (snapshot : Option (TypedValue L))
    (players : P → image.application.PlayerPolicy)
    (environment : image.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation P))
    (execution next : image.application.PolicyExecution)
    (hstate : AcceptedSnapshot field handle snapshot execution.native.application)
    (hnext : next ∈ (image.application.runPolicies players environment schedule
      execution).support) :
    AcceptedSnapshot field handle snapshot next.native.application := by
  exact image.application.runPolicies_application_invariant
    (AcceptedSnapshot field handle snapshot)
    (privateStep_acceptedSnapshot image field handle snapshot)
    (handle_acceptedSnapshot image field handle snapshot)
    (environmentStep_acceptedSnapshot image field handle snapshot)
    players environment schedule execution next hstate hnext

end Vegas.ApplicationImage

/-- info: 'Vegas.ApplicationImage.run_acceptedSnapshot' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.run_acceptedSnapshot

/-- info: 'Vegas.ApplicationImage.runPolicies_acceptedSnapshot' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.runPolicies_acceptedSnapshot
