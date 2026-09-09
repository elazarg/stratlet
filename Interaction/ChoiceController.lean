/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPolicies

/-! # Sample-once message-application choice controllers

A choice encoding identifies the canonical wire representation of one choice.
The controller samples only when no recognized command is present in its own
history. The first encoded command therefore serves as persistent memory;
retries reuse that recorded value.

Canonical decoding does not by itself separate different endpoints. Distinct
endpoint images or explicit dispatch tags remain application/compiler
obligations.
-/

noncomputable section

namespace Interaction.MessageApplication

open GameTheory.Math.Probability

universe uPrincipal uValue uInput uWire

/-- A canonical partial encoding of choice values into a wire representation. -/
structure ChoiceEncoding (Value : Type uValue) (Wire : Type uWire) where
  encode : Value → Wire
  decode : Wire → Option Value
  decode_encode : ∀ value, decode (encode value) = some value
  decode_sound : ∀ wire value, decode wire = some value → wire = encode value

variable {Principal : Type uPrincipal} (app : MessageApplication Principal)

namespace ChoiceEncoding

variable {Value : Type uValue}

/-- Lift a payload encoding to actual submission commands. Every other player
command is outside the lifted decoding domain. -/
def submission (encoding : ChoiceEncoding Value app.Payload) :
    ChoiceEncoding Value app.PlayerCommand where
  encode value := .submit (encoding.encode value)
  decode
    | .submit payload => encoding.decode payload
    | _ => none
  decode_encode := encoding.decode_encode
  decode_sound command value hdecode := by
    cases command with
    | submit payload =>
        exact congrArg PlayerCommand.submit
          (encoding.decode_sound payload value hdecode)
    | privateCommand command | replay id | wait => contradiction

/-- Lift a private-command encoding to actual private commands. Every other
player command is outside the lifted decoding domain. -/
def privateCommand (encoding : ChoiceEncoding Value app.PrivateCommand) :
    ChoiceEncoding Value app.PlayerCommand where
  encode value := .privateCommand (encoding.encode value)
  decode
    | .privateCommand command => encoding.decode command
    | _ => none
  decode_encode := encoding.decode_encode
  decode_sound command value hdecode := by
    cases command with
    | privateCommand command =>
        exact congrArg PlayerCommand.privateCommand
          (encoding.decode_sound command value hdecode)
    | submit payload | replay id | wait => contradiction

@[simp]
theorem submission_decode_submit (encoding : ChoiceEncoding Value app.Payload)
    (payload : app.Payload) :
    (encoding.submission app).decode (.submit payload) = encoding.decode payload := rfl

@[simp]
theorem submission_decode_private (encoding : ChoiceEncoding Value app.Payload)
    (command : app.PrivateCommand) :
    (encoding.submission app).decode (.privateCommand command) = none := rfl

@[simp]
theorem submission_decode_replay (encoding : ChoiceEncoding Value app.Payload)
    (id : MessageId Principal) :
    (encoding.submission app).decode (.replay id) = none := rfl

@[simp]
theorem submission_decode_wait (encoding : ChoiceEncoding Value app.Payload) :
    (encoding.submission app).decode .wait = none := rfl

@[simp]
theorem privateCommand_decode_private
    (encoding : ChoiceEncoding Value app.PrivateCommand)
    (command : app.PrivateCommand) :
    (encoding.privateCommand app).decode (.privateCommand command) =
      encoding.decode command := rfl

@[simp]
theorem privateCommand_decode_submit
    (encoding : ChoiceEncoding Value app.PrivateCommand) (payload : app.Payload) :
    (encoding.privateCommand app).decode (.submit payload) = none := rfl

@[simp]
theorem privateCommand_decode_replay
    (encoding : ChoiceEncoding Value app.PrivateCommand) (id : MessageId Principal) :
    (encoding.privateCommand app).decode (.replay id) = none := rfl

@[simp]
theorem privateCommand_decode_wait
    (encoding : ChoiceEncoding Value app.PrivateCommand) :
    (encoding.privateCommand app).decode .wait = none := rfl

/-- The value in the earliest chronological command recognized by this
encoding. -/
def cachedValue (encoding : ChoiceEncoding Value app.PlayerCommand) :
    List app.PlayerEntry → Option Value
  | [] => none
  | entry :: rest =>
      match encoding.decode entry.command with
      | some value => some value
      | none => cachedValue encoding rest

@[simp]
theorem cachedValue_nil (encoding : ChoiceEncoding Value app.PlayerCommand) :
    encoding.cachedValue app [] = none := rfl

@[simp]
theorem cachedValue_cons (encoding : ChoiceEncoding Value app.PlayerCommand)
    (view : app.View) (command : app.PlayerCommand)
    (history : List app.PlayerEntry) :
    encoding.cachedValue app (⟨view, command⟩ :: history) =
      match encoding.decode command with
      | some value => some value
      | none => encoding.cachedValue app history := rfl

theorem cachedValue_append_of_none
    (encoding : ChoiceEncoding Value app.PlayerCommand)
    (history suffix : List app.PlayerEntry)
    (hcache : encoding.cachedValue app history = none) :
    encoding.cachedValue app (history ++ suffix) = encoding.cachedValue app suffix := by
  induction history with
  | nil => rfl
  | cons entry history ih =>
      rcases entry with ⟨view, command⟩
      cases hdecode : encoding.decode command with
      | none =>
          rw [cachedValue_cons, hdecode] at hcache
          change encoding.cachedValue app
            (⟨view, command⟩ :: (history ++ suffix)) =
              encoding.cachedValue app suffix
          rw [cachedValue_cons, hdecode]
          exact ih hcache
      | some value =>
          rw [cachedValue_cons, hdecode] at hcache
          contradiction

theorem cachedValue_append_of_some
    (encoding : ChoiceEncoding Value app.PlayerCommand)
    (history suffix : List app.PlayerEntry) (value : Value)
    (hcache : encoding.cachedValue app history = some value) :
    encoding.cachedValue app (history ++ suffix) = some value := by
  induction history with
  | nil => simp at hcache
  | cons entry history ih =>
      rcases entry with ⟨view, command⟩
      cases hdecode : encoding.decode command with
      | none =>
          rw [cachedValue_cons, hdecode] at hcache
          change encoding.cachedValue app
            (⟨view, command⟩ :: (history ++ suffix)) = some value
          rw [cachedValue_cons, hdecode]
          exact ih hcache
      | some cached =>
          rw [cachedValue_cons, hdecode] at hcache
          change encoding.cachedValue app
            (⟨view, command⟩ :: (history ++ suffix)) = some value
          rw [cachedValue_cons, hdecode]
          exact hcache

theorem cachedValue_append_encoded_of_none
    (encoding : ChoiceEncoding Value app.PlayerCommand)
    (history : List app.PlayerEntry) (view : app.View) (value : Value)
    (hcache : encoding.cachedValue app history = none) :
    encoding.cachedValue app
      (history ++ [⟨view, encoding.encode value⟩]) = some value := by
  rw [encoding.cachedValue_append_of_none app history _ hcache]
  simp [cachedValue, encoding.decode_encode]

end ChoiceEncoding

/-- A behavioral choice controller whose first encoded command records its
sample. Readout may use both the principal's own history and current view. -/
structure ChoiceController (Value : Type uValue) (Input : Type uInput) where
  codec : ChoiceEncoding Value app.PlayerCommand
  ready : app.View → Bool
  resolved : app.View → Bool
  readout? : List app.PlayerEntry → app.View → Option Input
  kernel : Input → FinDist Value
  retry : List app.PlayerEntry → app.View → Bool

namespace ChoiceController

variable {Value : Type uValue} {Input : Type uInput}

/-- Sample once, then optionally retry the exact command recorded by the
earliest recognized history entry. -/
def policy (controller : ChoiceController app Value Input) : app.PlayerPolicy :=
  fun history view =>
    if controller.resolved view then
      FinDist.pure .wait
    else
      match controller.codec.cachedValue app history with
      | some value =>
          if controller.ready view && controller.retry history view then
            FinDist.pure (controller.codec.encode value)
          else
            FinDist.pure .wait
      | none =>
          if controller.ready view then
            match controller.readout? history view with
            | some input => (controller.kernel input).map controller.codec.encode
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
        FinDist.pure (controller.codec.encode value)
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
      (controller.kernel input).map controller.codec.encode := by
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

/-- Every non-wait recognized command supported after a cached value carries
that exact value. -/
theorem supported_command_of_cached
    (controller : ChoiceController app Value Input)
    (history : List app.PlayerEntry) (view : app.View)
    (cached decoded : Value) (command : app.PlayerCommand)
    (hresolved : controller.resolved view = false)
    (hcache : controller.codec.cachedValue app history = some cached)
    (hcommand : command ∈ (controller.policy app history view).support)
    (hactive : command ≠ .wait)
    (hdecode : controller.codec.decode command = some decoded) :
    decoded = cached := by
  rw [controller.policy_of_cached app history view cached hresolved hcache] at hcommand
  cases hreplay : controller.ready view && controller.retry history view with
  | false =>
      simp only [hreplay, Bool.false_eq_true, if_false,
        FinDist.mem_support_pure] at hcommand
      exact False.elim (hactive hcommand)
  | true =>
      simp only [hreplay, ↓reduceIte, FinDist.mem_support_pure] at hcommand
      subst command
      rw [controller.codec.decode_encode] at hdecode
      exact (Option.some.inj hdecode).symm

/-- A recognized command supported by an uncached ready controller is exactly
the encoding of a value in the source kernel's support. -/
theorem supported_command_of_uncached
    (controller : ChoiceController app Value Input)
    (history : List app.PlayerEntry) (view : app.View) (input : Input)
    (decoded : Value) (command : app.PlayerCommand)
    (hresolved : controller.resolved view = false)
    (hcache : controller.codec.cachedValue app history = none)
    (hready : controller.ready view = true)
    (hreadout : controller.readout? history view = some input)
    (hcommand : command ∈ (controller.policy app history view).support)
    (hdecode : controller.codec.decode command = some decoded) :
    decoded ∈ (controller.kernel input).support := by
  rw [controller.policy_of_uncached_ready app history view input
    hresolved hcache hready hreadout, FinDist.support_map] at hcommand
  obtain ⟨sample, hsample, hsampleCommand⟩ := hcommand
  have hcanonical : command = controller.codec.encode decoded :=
    controller.codec.decode_sound command decoded hdecode
  have hencoded := congrArg controller.codec.decode
    (hsampleCommand.trans hcanonical)
  rw [controller.codec.decode_encode, controller.codec.decode_encode] at hencoded
  have hvalue : sample = decoded := Option.some.inj hencoded
  rwa [← hvalue]

end ChoiceController

end Interaction.MessageApplication
