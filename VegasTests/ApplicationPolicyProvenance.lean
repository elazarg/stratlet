/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationPolicyProvenance
import VegasTests.GeneratedApplicationPolicy

/-! # Provenance controls for generated application policies

The positive regression applies the general lifted-policy theorem to an actual
multistage supported execution. The negative regression admits the same raw
binding before preparation and demonstrates why the lifted-owner premise is
essential.
-/

noncomputable section

namespace VegasTests.ApplicationPolicyProvenance

open Vegas Vegas.EventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability
open VegasTests.PersistentDisclosure
open VegasTests.GeneratedPersistentDisclosure
open VegasTests.GeneratedBindingPolicy (initial)
open VegasTests.GeneratedApplicationPolicy

/-- Every supported execution in the concrete through-chance law has the
registration-to-snapshot agreement required by owner-local source readout. -/
theorem through_chance_registrationMatches
    (profile : SourceBehavioralProfile source.prog)
    (next : image.application.PolicyExecution)
    (hnext : next ∈ (image.application.runPolicies
      (applicationPlan.liftProfile (fun _ => 10) profile) service
      [.player 0, .player 0, .environment, .player 0, .environment, .environment]
      initial).support) :
    image.RegistrationMatches 0 (next.principalHistory 0) next.native.application := by
  apply ApplicationImage.RegisteredBindings.registrationMatches
  apply applicationPlan.runPolicies_lifted_registeredBindings (fun _ => 10) profile 0
    (applicationPlan.liftProfile (fun _ => 10) profile) rfl service
    (ApplicationImage.Memory.initial GeneratedPersistentDisclosure.compiled.graph)
    (fun _ => rfl)
    [.player 0, .player 0, .environment, .player 0, .environment, .environment]
    next
  exact hnext

def prematurePlayer : TestPlayer → image.application.PlayerPolicy := fun who history _ =>
  if who = 0 then
    if history.isEmpty then FinDist.pure (.submit (.binding 0 (0, 0)))
    else FinDist.pure (.privateCommand (.register 0 ⟨.bool, false⟩))
  else FinDist.pure .wait

def prematureEnvironment : image.application.EnvironmentPolicy :=
  fun _ _ => FinDist.pure (.include (0, 0))

def prematureSubmitted : image.application.PolicyExecution :=
  { initial with
    native := { initial.native with
      pool := (initial.native.pool.submit 0 (.binding 0 (0, 0))).2 }
    principalHistory := fun who => if who = 0 then
      [⟨MessageApplication.State.observe image.application initial.native 0,
        .submit (.binding 0 (0, 0))⟩] else []
    nativeTrace := [.submit 0 (.binding 0 (0, 0))] }

def prematureIncluded : image.application.PolicyExecution :=
  { prematureSubmitted with
    native := image.application.includePending prematureSubmitted.native (0, 0)
    environmentHistory :=
      [⟨MessageApplication.State.environmentView image.application
        prematureSubmitted.native, .include (0, 0)⟩]
    nativeTrace := prematureSubmitted.nativeTrace ++ [.include (0, 0)] }

def prematureFinal : image.application.PolicyExecution :=
  { prematureIncluded with
    native := { prematureIncluded.native with application :=
      prematureIncluded.native.application.register 0 0 ⟨.bool, false⟩ }
    principalHistory := fun who => if who = 0 then
      prematureIncluded.principalHistory 0 ++
        [⟨MessageApplication.State.observe image.application prematureIncluded.native 0,
          .privateCommand (.register 0 ⟨.bool, false⟩)⟩]
      else prematureIncluded.principalHistory who
    nativeTrace := prematureIncluded.nativeTrace ++
      [.privateCommand 0 (.register 0 ⟨.bool, false⟩)] }

/-- The unrestricted shared runtime really permits bind-before-registration:
the subsequent registration enters owner history, but the accepted snapshot
remains permanently absent. -/
theorem premature_binding_run :
    image.application.runPolicies prematurePlayer prematureEnvironment
      [.player 0, .environment, .player 0] initial = FinDist.pure prematureFinal := by
  simp only [prematurePlayer, prematureEnvironment, prematureFinal,
    prematureIncluded, prematureSubmitted, GeneratedBindingPolicy.initial,
    PolicyExecution.initial,
    MessageApplication.runPolicies, MessageApplication.invoke,
    MessageApplication.playerStep, MessageApplication.environmentPolicyStep,
    PlayerCommand.toAction, EnvironmentPolicyCommand.toAction,
    MessageApplication.advance, MessageApplication.step, List.isEmpty_nil, if_pos,
    FinDist.pure_bind, List.isEmpty_cons, Bool.false_eq_true, if_false, List.nil_append]
  rfl

theorem premature_binding_breaks_registrationMatches :
    ¬ image.RegistrationMatches 0 (prematureFinal.principalHistory 0)
      prematureFinal.native.application := by
  intro hmatches
  have hfrozen := hmatches 0 ⟨.bool, false⟩ (by rfl) (by rfl) (by rfl)
  cases hfrozen

end VegasTests.ApplicationPolicyProvenance

/-- info: 'VegasTests.ApplicationPolicyProvenance.through_chance_registrationMatches'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  VegasTests.ApplicationPolicyProvenance.through_chance_registrationMatches

/-- info: 'VegasTests.ApplicationPolicyProvenance.premature_binding_run' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ApplicationPolicyProvenance.premature_binding_run

/-- info: 'VegasTests.ApplicationPolicyProvenance.premature_binding_breaks_registrationMatches'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  VegasTests.ApplicationPolicyProvenance.premature_binding_breaks_registrationMatches
