/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationPlan
import Interaction.MessageApplicationPolicies
import Interaction.MessagePoolFreshness

/-! # A source-ordered reference service

This environment policy supports source-ordered forward realization and is
paired with the emitted image's invocation list. Its instruction index is the length of
its own actual history, including unsuccessful invocations. It reads only the
emitted instructions and the message pool in its environment observation;
source environments, compiler cursors, and private commitment tables are absent.

The service includes the current instruction owner's most recently submitted
message when it remains pending, without inspecting its payload, or invokes
the current chance kernel. It does not search for an older pending message.
The application remains responsible for validation and chance readiness. A
missing submission produces a wait and still advances the service history.
Consequently this is neither a retry policy nor a fairness or completion
guarantee against arbitrary player deviations or additional invocations.
-/

noncomputable section

namespace Vegas

open Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {P : Type} {L : IExpr}

namespace ApplicationInstruction

/-- The author of the message used by this instruction; chance is invoked
directly by the environment. -/
def submitter : ApplicationInstruction P L → Option P
  | .sample _ => none
  | .bind code => some code.owner
  | .publicChoice code => some code.endpoint.owner
  | .conditional code => some code.endpoint.owner

/-- A finite invocation phase for the reference source-ordered service.
Binding uses a private registration followed by its public submission. -/
def serviceInvocations : ApplicationInstruction P L → List (@Invocation P)
  | .sample _ => [.environment]
  | .bind code => [.player code.owner, .player code.owner, .environment]
  | .publicChoice code => [.player code.endpoint.owner, .environment]
  | .conditional code => [.player code.endpoint.owner, .environment]

@[simp] theorem serviceInvocations_environment_count (code : ApplicationInstruction P L) :
    code.serviceInvocations.countP Invocation.isEnvironment = 1 := by
  cases code <;> simp [serviceInvocations, Invocation.isEnvironment]

end ApplicationInstruction

namespace ApplicationImage

/-- The canonical script is derived from emitted instructions, without a
second source interpreter or a proof-side cursor. -/
def serviceInvocations (image : ApplicationImage P L) : List (@Invocation P) :=
  image.instructions.flatMap ApplicationInstruction.serviceInvocations

@[simp] theorem serviceInvocations_environment_count (image : ApplicationImage P L) :
    image.serviceInvocations.countP Invocation.isEnvironment = image.instructions.length := by
  obtain ⟨instructions⟩ := image
  induction instructions with
  | nil => rfl
  | cons code rest ih =>
      change (code.serviceInvocations ++
        rest.flatMap ApplicationInstruction.serviceInvocations).countP _ = rest.length + 1
      rw [List.countP_append, ApplicationInstruction.serviceInvocations_environment_count]
      change 1 + (serviceInvocations ⟨rest⟩).countP _ = rest.length + 1
      rw [ih, Nat.add_comm]

variable [DecidableEq P]

private def latestSubmission (image : ApplicationImage P L) (who : P)
    (view : image.application.EnvironmentObservation) :
    image.application.EnvironmentPolicyCommand :=
  match view.pool.nextSerial who with
  | 0 => .wait
  | serial + 1 =>
      if (view.pool.lookup (who, serial)).isSome then .include (who, serial) else .wait

/-- One service command depends only on the current instruction and the
environment observation. No payload inspection or validator oracle is used. -/
def serviceCommand (image : ApplicationImage P L) (code : ApplicationInstruction P L)
    (view : image.application.EnvironmentObservation) :
    image.application.EnvironmentPolicyCommand :=
  match code with
  | .sample code => .application (.sample code.node)
  | .bind code => image.latestSubmission code.owner view
  | .publicChoice code => image.latestSubmission code.endpoint.owner view
  | .conditional code => image.latestSubmission code.endpoint.owner view

/-- The environment advances once per invocation, using its own recorded
history. The exact forward law must pair this policy with `serviceInvocations`
and canonical empty environment history. -/
def serialService (image : ApplicationImage P L) : image.application.EnvironmentPolicy :=
  fun history view => FinDist.pure <|
    match image.instructions[history.length]? with
    | none => .wait
    | some code => image.serviceCommand code view

theorem serialService_at (image : ApplicationImage P L)
    (history : List image.application.EnvironmentEntry)
    (view : image.application.EnvironmentObservation) (code : ApplicationInstruction P L)
    (hcode : image.instructions[history.length]? = some code) :
    image.serialService history view = FinDist.pure (image.serviceCommand code view) := by
  simp only [serialService, hcode]

/-- The actual environment-history length selects the head of an emitted
suffix. The source compiler cursor is used only to prove the static split. -/
theorem serialService_at_suffix (image : ApplicationImage P L)
    (history : List image.application.EnvironmentEntry)
    (view : image.application.EnvironmentObservation)
    (before after : List (ApplicationInstruction P L)) (code : ApplicationInstruction P L)
    (himage : image.instructions = before ++ code :: after)
    (hindex : history.length = before.length) :
    image.serialService history view = FinDist.pure (image.serviceCommand code view) := by
  apply image.serialService_at history view code
  rw [himage, hindex]
  simp

/-- The most recent submission, if still pending, is selected exactly. The successor premise
rules out both an empty submission history and natural-number underflow. -/
theorem serialService_include (image : ApplicationImage P L)
    (history : List image.application.EnvironmentEntry)
    (view : image.application.EnvironmentObservation) (code : ApplicationInstruction P L)
    (who : P) (serial : Nat) (message : Message P (Payload P L))
    (hcode : image.instructions[history.length]? = some code)
    (howner : code.submitter = some who)
    (hserial : view.pool.nextSerial who = serial + 1)
    (hpending : view.pool.lookup (who, serial) = some message) :
    image.serialService history view = FinDist.pure (.include (who, serial)) := by
  rw [image.serialService_at history view code hcode]
  cases code with
  | sample code => simp [ApplicationInstruction.submitter] at howner
  | bind code | publicChoice code | conditional code =>
      simp only [ApplicationInstruction.submitter, Option.some.injEq] at howner
      simp only [serviceCommand, latestSubmission, howner, hserial, hpending,
        Option.isSome_some, ↓reduceIte]

/-- An actual fresh submission supplies the service premise used by the local
source-phase laws. Its payload may be arbitrary: acceptance is a separate fact. -/
theorem serialService_after_submit (image : ApplicationImage P L)
    (execution submitted : image.application.PolicyExecution)
    (code : ApplicationInstruction P L) (who : P) (payload : Payload P L)
    (hcode : image.instructions[execution.environmentHistory.length]? = some code)
    (howner : code.submitter = some who)
    (hfresh : execution.native.pool.lookup (who, execution.native.pool.nextSerial who) = none)
    (hsubmitted : submitted ∈
      (image.application.playerStep who execution (.submit payload)).support) :
    image.serialService submitted.environmentHistory
        (MessageApplication.State.environmentView image.application submitted.native) =
      FinDist.pure (.include (who, execution.native.pool.nextSerial who)) := by
  have hhistory := image.application.playerStep_environmentHistory who execution
    (.submit payload) submitted hsubmitted
  have hnative : submitted.native ∈
      ((image.application.playerStep who execution (.submit payload)).map
        PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨submitted, hsubmitted, rfl⟩
  rw [image.application.playerStep_native] at hnative
  simp only [PlayerCommand.toAction, MessageApplication.step, FinDist.mem_support_pure]
    at hnative
  apply image.serialService_include submitted.environmentHistory _ code who
    (execution.native.pool.nextSerial who)
    ⟨(who, execution.native.pool.nextSerial who), payload⟩
  · simpa only [hhistory] using hcode
  · exact howner
  · simp only [MessageApplication.State.environmentView, hnative,
      MessagePool.submit, ↓reduceIte]
  · exact hnative ▸ execution.native.pool.lookup_submit_fresh who payload hfresh

/-- A private preparation followed by a fresh submission uses the same service
index and envelope identifier as the phase's initial execution. Private
application commands do not create messages or environment-history entries. -/
theorem serialService_after_private_submit (image : ApplicationImage P L)
    (execution prepared submitted : image.application.PolicyExecution)
    (code : ApplicationInstruction P L) (who : P)
    (command : image.application.PrivateCommand) (payload : Payload P L)
    (hcode : image.instructions[execution.environmentHistory.length]? = some code)
    (howner : code.submitter = some who)
    (hfresh : execution.native.pool.lookup (who, execution.native.pool.nextSerial who) = none)
    (hprepared : prepared ∈
      (image.application.playerStep who execution (.privateCommand command)).support)
    (hsubmitted : submitted ∈
      (image.application.playerStep who prepared (.submit payload)).support) :
    image.serialService submitted.environmentHistory
        (MessageApplication.State.environmentView image.application submitted.native) =
      FinDist.pure (.include (who, execution.native.pool.nextSerial who)) := by
  have hhistory := image.application.playerStep_environmentHistory who execution
    (.privateCommand command) prepared hprepared
  have hnative : prepared.native ∈
      ((image.application.playerStep who execution (.privateCommand command)).map
        PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨prepared, hprepared, rfl⟩
  rw [image.application.playerStep_native] at hnative
  simp only [PlayerCommand.toAction, MessageApplication.step, FinDist.mem_support_pure]
    at hnative
  have hpool : prepared.native.pool = execution.native.pool := congrArg (·.pool) hnative
  have hservice := image.serialService_after_submit prepared submitted code who payload
    (by simpa only [hhistory] using hcode) howner
    (by simpa only [hpool] using hfresh) hsubmitted
  simpa only [hpool] using hservice

/-- The service's history index advances by the number of emitted instructions
in a serviced segment, independently of the random choices and message results. -/
theorem runPolicies_service_history_length (image segment : ApplicationImage P L)
    (players : P → image.application.PlayerPolicy)
    (execution next : image.application.PolicyExecution)
    (hnext : next ∈ (image.application.runPolicies players image.serialService
      segment.serviceInvocations execution).support) :
    next.environmentHistory.length =
      execution.environmentHistory.length + segment.instructions.length := by
  simpa only [serviceInvocations_environment_count] using
    image.application.runPolicies_environmentHistory_length players image.serialService
      segment.serviceInvocations execution next hnext

end ApplicationImage
end Vegas

/-- info: 'Vegas.ApplicationImage.serialService_after_submit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.serialService_after_submit

/-- info: 'Vegas.ApplicationImage.serialService_after_private_submit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.serialService_after_private_submit

/-- info: 'Vegas.ApplicationImage.runPolicies_service_history_length' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.runPolicies_service_history_length
