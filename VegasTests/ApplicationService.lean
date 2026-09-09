/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationService
import VegasTests.GeneratedBindingPolicy

/-! # The reference service on a generated mixed-feature image

The fixture emits binding, public choices, chance, conditional opening, and
conditional copy. The randomized binding test uses the shared policy runner
and the generated service instead of an independently specified inclusion.
-/

noncomputable section

namespace VegasTests.ApplicationService

open Vegas Vegas.EventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability
open VegasTests.PersistentDisclosure VegasTests.GeneratedPersistentDisclosure
  VegasTests.GeneratedBindingPolicy

theorem generated_script : image.serviceInvocations =
    [.player 0, .player 0, .environment,
      .player 0, .environment, .environment,
      .player 0, .environment, .player 1, .environment,
      .player 0, .environment] := rfl

/-- The generated service selects the submitted opaque binding at either
private value. The premise is an actual supported player step. -/
theorem serves_binding_submission (secret : Bool) :
    image.serialService (submitted secret).environmentHistory
        (MessageApplication.State.environmentView image.application
          (submitted secret).native) = FinDist.pure (.include (0, 0)) := by
  apply image.serialService_after_submit (registered secret) (submitted secret)
    (.bind code) 0 (.binding 0 (0, 0))
  · rfl
  · rfl
  · rfl
  · simp only [MessageApplication.playerStep, PlayerCommand.toAction,
      MessageApplication.advance, MessageApplication.step,
      FinDist.pure_bind, FinDist.mem_support_pure]
    rfl

/-- Arbitrary source randomization survives actual private registration,
public submission, and the observation-local reference service. -/
theorem binding_service_law (law : FinDist Bool) :
    image.application.runPolicies (players law) image.serialService
      [.player 0, .player 0, .environment] initial = law.map included := by
  have hsubmission : image.application.runPolicies (players law) image.serialService
      [.player 0, .player 0] initial = law.map submitted := by
    exact binding_submission_source_law law
  rw [show ([.player 0, .player 0, .environment] : List (@Invocation TestPlayer)) =
    [.player 0, .player 0] ++ [.environment] from rfl,
    MessageApplication.runPolicies_append, hsubmission, FinDist.bind_map,
    FinDist.map_eq_bind]
  apply FinDist.bind_congr
  intro secret _
  simp only [MessageApplication.runPolicies, MessageApplication.invoke,
    serves_binding_submission, FinDist.pure_bind,
    MessageApplication.environmentPolicyStep, EnvironmentPolicyCommand.toAction,
    MessageApplication.advance, MessageApplication.step]
  rfl

/-- Chance is invoked at the emitted address; its outcome is not an argument
of the service command, even for arbitrary environment observations. -/
theorem serves_sample (history : List image.application.EnvironmentEntry)
    (view : image.application.EnvironmentObservation) (hindex : history.length = 2) :
    image.serialService history view = FinDist.pure (.application (.sample 3)) := by
  unfold ApplicationImage.serialService
  rw [hindex]
  rfl

/-- Missing submissions produce a recorded wait. There is no implied retry
or timeout in this finite reference service. -/
theorem missing_binding_waits :
    image.application.invoke (players (FinDist.pure false)) image.serialService
        initial .environment =
      image.application.environmentPolicyStep initial .wait := by
  change (FinDist.pure _).bind _ = _
  rw [FinDist.pure_bind]
  rfl

private def newerAlreadyIncluded : image.application.State :=
  let first := { initial.native with
    pool := (initial.native.pool.submit 0 (.malformed [0])).2 }
  let second := { first with pool := (first.pool.submit 0 (.malformed [1])).2 }
  image.application.includePending second (0, 1)

/-- If the newest submission has already been included, the service waits
even when an older submission is still pending. It does not search backwards. -/
theorem no_older_message_fallback :
    newerAlreadyIncluded.pool.lookup (0, 0) = some ⟨(0, 0), .malformed [0]⟩ ∧
      image.serialService [] (MessageApplication.State.environmentView
        image.application newerAlreadyIncluded) = FinDist.pure .wait := by
  exact ⟨rfl, rfl⟩

/-- At a message instruction the service also permits inclusion of malformed
traffic. The application, not the service policy, rejects it. -/
theorem malformed_submission_is_serviced
    (submitted : image.application.PolicyExecution)
    (hsubmitted : submitted ∈
      (image.application.playerStep 0 initial (.submit (.malformed [7]))).support) :
    image.serialService submitted.environmentHistory
        (MessageApplication.State.environmentView image.application submitted.native) =
      FinDist.pure (.include (0, 0)) ∧
      image.handle submitted.native.application ⟨(0, 0), .malformed [7]⟩ = none := by
  refine ⟨?_, rfl⟩
  exact image.serialService_after_submit initial submitted (.bind code) 0
    (.malformed [7]) rfl rfl rfl hsubmitted

end VegasTests.ApplicationService

/-- info: 'VegasTests.ApplicationService.binding_service_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ApplicationService.binding_service_law

/-- info: 'VegasTests.ApplicationService.malformed_submission_is_serviced' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ApplicationService.malformed_submission_is_serviced
