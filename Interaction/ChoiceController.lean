/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPolicies

/-! # Sample-once message-application choice controllers

An endpoint-specific codec recognizes the submissions belonging to one choice
endpoint.  The controller samples only when no recognized submission is present
in its own history.  The first submitted command therefore serves as the
controller's persistent memory; retries reuse that recorded value.
-/

noncomputable section

namespace Interaction.MessageApplication

open GameTheory.Math.Probability

universe uPrincipal uValue uInput uPayload

/-- Encoding for one submission endpoint.  `decode` must reject payloads for
other endpoints; endpoint identity is consequently part of the wire codec. -/
structure SubmissionCodec (Value : Type uValue) (Payload : Type uPayload) where
  encode : Value → Payload
  decode : Payload → Option Value
  decode_encode : ∀ value, decode (encode value) = some value

variable {Principal : Type uPrincipal} (app : MessageApplication Principal)

namespace SubmissionCodec

variable {Value : Type uValue}

/-- The value in the earliest chronological submission recognized by this
endpoint's codec. -/
def cachedValue (codec : SubmissionCodec Value app.Payload) :
    List app.PlayerEntry → Option Value
  | [] => none
  | entry :: rest =>
      match entry.command with
      | .submit payload =>
          match codec.decode payload with
          | some value => some value
          | none => cachedValue codec rest
      | _ => cachedValue codec rest

@[simp]
theorem cachedValue_nil (codec : SubmissionCodec Value app.Payload) :
    codec.cachedValue app [] = none := rfl

@[simp]
theorem cachedValue_cons_private (codec : SubmissionCodec Value app.Payload)
    (view : app.View) (command : app.PrivateCommand)
    (history : List app.PlayerEntry) :
    codec.cachedValue app (⟨view, .privateCommand command⟩ :: history) =
      codec.cachedValue app history := rfl

@[simp]
theorem cachedValue_cons_submit (codec : SubmissionCodec Value app.Payload)
    (view : app.View) (payload : app.Payload) (history : List app.PlayerEntry) :
    codec.cachedValue app (⟨view, .submit payload⟩ :: history) =
      match codec.decode payload with
      | some value => some value
      | none => codec.cachedValue app history := rfl

@[simp]
theorem cachedValue_cons_replay (codec : SubmissionCodec Value app.Payload)
    (view : app.View) (id : MessageId Principal)
    (history : List app.PlayerEntry) :
    codec.cachedValue app (⟨view, .replay id⟩ :: history) =
      codec.cachedValue app history := rfl

@[simp]
theorem cachedValue_cons_wait (codec : SubmissionCodec Value app.Payload)
    (view : app.View) (history : List app.PlayerEntry) :
    codec.cachedValue app (⟨view, .wait⟩ :: history) =
      codec.cachedValue app history := rfl

theorem cachedValue_append_of_none (codec : SubmissionCodec Value app.Payload)
    (history suffix : List app.PlayerEntry)
    (hcache : codec.cachedValue app history = none) :
    codec.cachedValue app (history ++ suffix) = codec.cachedValue app suffix := by
  induction history with
  | nil => rfl
  | cons entry history ih =>
      rcases entry with ⟨before, command⟩
      cases command with
      | privateCommand command =>
          simp only [cachedValue] at hcache ⊢
          exact ih hcache
      | submit payload =>
          cases hdecode : codec.decode payload with
          | none =>
              rw [cachedValue_cons_submit, hdecode] at hcache
              change codec.cachedValue app
                (⟨before, .submit payload⟩ :: (history ++ suffix)) =
                  codec.cachedValue app suffix
              rw [cachedValue_cons_submit, hdecode]
              exact ih hcache
          | some value =>
              rw [cachedValue_cons_submit, hdecode] at hcache
              contradiction
      | replay id =>
          simp only [cachedValue] at hcache ⊢
          exact ih hcache
      | wait =>
          simp only [cachedValue] at hcache ⊢
          exact ih hcache

theorem cachedValue_append_of_some (codec : SubmissionCodec Value app.Payload)
    (history suffix : List app.PlayerEntry) (value : Value)
    (hcache : codec.cachedValue app history = some value) :
    codec.cachedValue app (history ++ suffix) = some value := by
  induction history with
  | nil => simp at hcache
  | cons entry history ih =>
      rcases entry with ⟨before, command⟩
      cases command with
      | privateCommand command =>
          simp only [cachedValue] at hcache ⊢
          exact ih hcache
      | submit payload =>
          cases hdecode : codec.decode payload with
          | none =>
              rw [cachedValue_cons_submit, hdecode] at hcache
              change codec.cachedValue app
                (⟨before, .submit payload⟩ :: (history ++ suffix)) = some value
              rw [cachedValue_cons_submit, hdecode]
              exact ih hcache
          | some cached =>
              rw [cachedValue_cons_submit, hdecode] at hcache
              change codec.cachedValue app
                (⟨before, .submit payload⟩ :: (history ++ suffix)) = some value
              rw [cachedValue_cons_submit, hdecode]
              exact hcache
      | replay id =>
          simp only [cachedValue] at hcache ⊢
          exact ih hcache
      | wait =>
          simp only [cachedValue] at hcache ⊢
          exact ih hcache

theorem cachedValue_append_encoded_of_none
    (codec : SubmissionCodec Value app.Payload)
    (history : List app.PlayerEntry) (view : app.View) (value : Value)
    (hcache : codec.cachedValue app history = none) :
    codec.cachedValue app
      (history ++ [⟨view, .submit (codec.encode value)⟩]) = some value := by
  rw [codec.cachedValue_append_of_none app history _ hcache]
  simp [cachedValue, codec.decode_encode]

end SubmissionCodec

/-- A behavioral choice controller whose first real submission records its
sample.  Readout may use both the principal's own history and its current view. -/
structure ChoiceController (Value : Type uValue) (Input : Type uInput) where
  codec : SubmissionCodec Value app.Payload
  ready : app.View → Bool
  resolved : app.View → Bool
  readout? : List app.PlayerEntry → app.View → Option Input
  kernel : Input → FinDist Value
  retry : List app.PlayerEntry → app.View → Bool

namespace ChoiceController

variable {Value : Type uValue} {Input : Type uInput}

/-- Sample once, then optionally retry the exact value recorded by the earliest
recognized submission. -/
def policy (controller : ChoiceController app Value Input) : app.PlayerPolicy :=
  fun history view =>
    if controller.resolved view then
      FinDist.pure .wait
    else
      match controller.codec.cachedValue app history with
      | some value =>
          if controller.ready view && controller.retry history view then
            FinDist.pure (.submit (controller.codec.encode value))
          else
            FinDist.pure .wait
      | none =>
          if controller.ready view then
            match controller.readout? history view with
            | some input =>
                (controller.kernel input).map fun value =>
                  .submit (controller.codec.encode value)
            | none => FinDist.pure .wait
          else
            FinDist.pure .wait

theorem policy_of_resolved (controller : ChoiceController app Value Input)
    (history : List app.PlayerEntry) (view : app.View)
    (hresolved : controller.resolved view = true) :
    controller.policy app history view = FinDist.pure .wait := by
  simp [policy, hresolved]

theorem policy_of_cached (controller : ChoiceController app Value Input)
    (history : List app.PlayerEntry) (view : app.View) (value : Value)
    (hresolved : controller.resolved view = false)
    (hcache : controller.codec.cachedValue app history = some value) :
    controller.policy app history view =
      if controller.ready view && controller.retry history view then
        FinDist.pure (.submit (controller.codec.encode value))
      else
        FinDist.pure .wait := by
  simp [policy, hresolved, hcache]

theorem policy_of_uncached_ready (controller : ChoiceController app Value Input)
    (history : List app.PlayerEntry) (view : app.View) (input : Input)
    (hresolved : controller.resolved view = false)
    (hcache : controller.codec.cachedValue app history = none)
    (hready : controller.ready view = true)
    (hreadout : controller.readout? history view = some input) :
    controller.policy app history view =
      (controller.kernel input).map fun value =>
        .submit (controller.codec.encode value) := by
  simp [policy, hresolved, hcache, hready, hreadout]

theorem policy_of_uncached_not_ready
    (controller : ChoiceController app Value Input)
    (history : List app.PlayerEntry) (view : app.View)
    (hresolved : controller.resolved view = false)
    (hcache : controller.codec.cachedValue app history = none)
    (hready : controller.ready view = false) :
    controller.policy app history view = FinDist.pure .wait := by
  simp [policy, hresolved, hcache, hready]

theorem policy_of_uncached_no_readout
    (controller : ChoiceController app Value Input)
    (history : List app.PlayerEntry) (view : app.View)
    (hresolved : controller.resolved view = false)
    (hcache : controller.codec.cachedValue app history = none)
    (hready : controller.ready view = true)
    (hreadout : controller.readout? history view = none) :
    controller.policy app history view = FinDist.pure .wait := by
  simp [policy, hresolved, hcache, hready, hreadout]

/-- Every recognized retry supported after a cached value carries that exact
value.  A wait branch makes the submission premises impossible. -/
theorem supported_submit_of_cached
    (controller : ChoiceController app Value Input)
    (history : List app.PlayerEntry) (view : app.View)
    (cached decoded : Value) (command : app.PlayerCommand) (payload : app.Payload)
    (hresolved : controller.resolved view = false)
    (hcache : controller.codec.cachedValue app history = some cached)
    (hcommand : command ∈ (controller.policy app history view).support)
    (hsubmit : command = .submit payload)
    (hdecode : controller.codec.decode payload = some decoded) :
    decoded = cached := by
  rw [controller.policy_of_cached app history view cached hresolved hcache] at hcommand
  cases hreplay : controller.ready view && controller.retry history view with
  | false =>
      simp only [hreplay, Bool.false_eq_true, if_false,
        FinDist.mem_support_pure] at hcommand
      have : PlayerCommand.submit payload = (PlayerCommand.wait : app.PlayerCommand) :=
        hsubmit.symm.trans hcommand
      contradiction
  | true =>
      simp only [hreplay, ↓reduceIte, FinDist.mem_support_pure] at hcommand
      have hpayload : payload = controller.codec.encode cached :=
        PlayerCommand.submit.inj (hsubmit.symm.trans hcommand)
      subst payload
      rw [controller.codec.decode_encode] at hdecode
      exact (Option.some.inj hdecode).symm

/-- A recognized first submission supported by an uncached ready controller is
exactly the encoding of a value in the source kernel's support. -/
theorem supported_submit_of_uncached
    (controller : ChoiceController app Value Input)
    (history : List app.PlayerEntry) (view : app.View) (input : Input)
    (decoded : Value) (command : app.PlayerCommand) (payload : app.Payload)
    (hresolved : controller.resolved view = false)
    (hcache : controller.codec.cachedValue app history = none)
    (hready : controller.ready view = true)
    (hreadout : controller.readout? history view = some input)
    (hcommand : command ∈ (controller.policy app history view).support)
    (hsubmit : command = .submit payload)
    (hdecode : controller.codec.decode payload = some decoded) :
    decoded ∈ (controller.kernel input).support := by
  rw [controller.policy_of_uncached_ready app history view input
    hresolved hcache hready hreadout, FinDist.support_map] at hcommand
  obtain ⟨sample, hsample, hsampleCommand⟩ := hcommand
  have hpayload : controller.codec.encode sample = payload :=
    PlayerCommand.submit.inj (hsampleCommand.trans hsubmit)
  have hencoded := controller.codec.decode_encode sample
  rw [hpayload] at hencoded
  have hvalue : decoded = sample := Option.some.inj (hdecode.symm.trans hencoded)
  rw [hvalue]
  exact hsample

end ChoiceController

end Interaction.MessageApplication
