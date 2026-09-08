/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedPolicyLaws
import Interaction.SealedProgramLaws

/-! # Public-view controllers for sealed-message openings -/

noncomputable section

namespace Interaction.SealedProgram

open GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}

def openingCommand [DecidableEq Principal] (program : SealedProgram Principal)
    (owner : Principal) (revealNode : Nat) (value : Value)
    (view : View Principal Value) : PlayerCommand Principal Value :=
  match openingRequest? program view.events owner revealNode value with
  | some payload => .submit payload
  | none => .wait

theorem openingCommand_allowed [DecidableEq Principal] (rebroadcast : Bool)
    (program : SealedProgram Principal) (owner : Principal) (revealNode : Nat)
    (value : Value) (view : View Principal Value) :
    (openingCommand program owner revealNode value view).allowed rebroadcast := by
  unfold openingCommand
  split <;> trivial

def openingPolicy [DecidableEq Principal] (rebroadcast : Bool)
    (program : SealedProgram Principal) (owner : Principal) (revealNode : Nat)
    (value : Value) : PlayerPolicy Principal Value rebroadcast :=
  fun _ view => FinDist.pure
    ⟨openingCommand program owner revealNode value view,
      openingCommand_allowed rebroadcast program owner revealNode value view⟩

/-- The owner's complete local controller: privately register, publish the
opaque commitment, then use the public-view opening controller. -/
def commitOpenPolicy [DecidableEq Principal] (rebroadcast : Bool)
    (program : SealedProgram Principal) (owner : Principal)
    (commitNode revealNode : Nat) (value : Value) :
    PlayerPolicy Principal Value rebroadcast :=
  fun history view =>
    match history.length with
    | 0 => FinDist.pure ⟨.register commitNode value, by trivial⟩
    | 1 => FinDist.pure
        ⟨.submit (.commitment commitNode (owner, commitNode)), by trivial⟩
    | _ + 2 => openingPolicy rebroadcast program owner revealNode value history view

theorem openingCommand_eq_wait_of_handle_eq_none [DecidableEq Principal]
    (program : SealedProgram Principal) (owner : Principal) (revealNode : Nat)
    (value : Value) (view : View Principal Value)
    (hready : openingHandle? program view.events owner revealNode = none) :
    openingCommand program owner revealNode value view = .wait := by
  simp [openingCommand, openingRequest?, hready]

/-- Public readiness is exactly the condition under which the opening
controller submits, for every chosen value. -/
theorem openingCommand_ne_wait_iff_ready [DecidableEq Principal]
    (program : SealedProgram Principal) (owner : Principal) (revealNode : Nat)
    (value : Value) (view : View Principal Value) :
    openingCommand program owner revealNode value view ≠ .wait ↔
      openingReady program view.events owner revealNode = true := by
  cases hhandle : openingHandle? program view.events owner revealNode <;>
    simp [openingCommand, openingRequest?, openingReady, hhandle]

theorem openingCommand_submit_sound [DecidableEq Principal]
    (program : SealedProgram Principal) (owner : Principal) (node source : Nat)
    (value : Value) (view : View Principal Value)
    (hcommand : openingCommand program owner node value view =
      .submit (.opening node (owner, source) value)) :
    ∃ requires,
      program.rules[node]? = some { kind := .reveal owner source, requires } ∧
      done view.events node = false ∧
      requires.all (done view.events) = true ∧
      accepted? view.events source = some (owner, source) := by
  unfold openingCommand at hcommand
  split at hcommand
  next payload hrequest =>
    have hpayload : payload = .opening node (owner, source) value := by
      simpa using hcommand
    subst payload
    exact openingRequest?_sound program view.events owner node source value hrequest
  next => contradiction

theorem openingCommand_ne_wait_sound [DecidableEq Principal]
    (program : SealedProgram Principal) (owner : Principal) (node : Nat)
    (value : Value) (view : View Principal Value)
    (hnonwait : openingCommand program owner node value view ≠ .wait) :
    ∃ source requires,
      openingCommand program owner node value view =
          .submit (.opening node (owner, source) value) ∧
        program.rules[node]? = some { kind := .reveal owner source, requires } ∧
        done view.events node = false ∧
        requires.all (done view.events) = true ∧
        accepted? view.events source = some (owner, source) := by
  unfold openingCommand at hnonwait ⊢
  cases hrequest : openingRequest? program view.events owner node value with
  | none => simp [hrequest] at hnonwait
  | some payload =>
      have hshape : ∃ source, payload = .opening node (owner, source) value := by
        unfold openingRequest? at hrequest
        cases hhandle : openingHandle? program view.events owner node with
        | none => simp [hhandle] at hrequest
        | some handle =>
            rw [hhandle] at hrequest
            have hpayload : payload = .opening node handle value := by
              simpa using (Option.some.inj hrequest).symm
            subst payload
            obtain ⟨source, rfl⟩ :=
              openingHandle?_eq_some_owner program view.events owner node handle hhandle
            exact ⟨source, rfl⟩
      obtain ⟨source, rfl⟩ := hshape
      refine ⟨source, ?_⟩
      obtain ⟨requires, hrule, hdone, hrequires, haccepted⟩ :=
        openingRequest?_sound program view.events owner node source value hrequest
      exact ⟨requires, rfl, hrule, hdone, hrequires, haccepted⟩

theorem submitOpening?_eq_playerStep_openingCommand
    [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal) (execution : PolicyExecution Principal Value)
    (owner : Principal) (node : Nat) (value : Value)
    (handle : CommitmentHandle Principal Nat)
    (hready : openingHandle? program execution.native.events owner node = some handle) :
    (submitOpening? program execution.native owner node value).map Prod.snd =
      some (playerStep program owner execution
        (openingCommand program owner node value (execution.native.observe owner))).native := by
  have hrequest : openingRequest? program execution.native.events owner node value =
      some (.opening node handle value) := by
    simp [openingRequest?, hready]
  rw [submitOpening?_eq_step program execution.native owner node value _ hrequest]
  simp [openingCommand, State.observe_events, hrequest, playerStep, applyNative,
    PlayerCommand.toAction]

end Interaction.SealedProgram
