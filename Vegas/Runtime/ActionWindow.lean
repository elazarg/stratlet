/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Runtime.DeviationAdequacy
import GameTheory.Protocol.Strategic
import GameTheory.Core.Mixed

/-! # Request windows implementing source actions

A timeout selects an action already present in the source menu. It does not
create an additional outcome or impose an incentive condition. The decoder
rejects malformed requests; a valid request can realize every source action.
The complete list of attempts is returned, including rejected requests.
-/

noncomputable section

namespace Vegas.Runtime.ActionWindow

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

variable {Info Request : Type} {Choice : Info → Type}

structure Gate (Info : Type) (Choice : Info → Type) (Request : Type) where
  timeoutAction : (info : Info) → Choice info
  decode : (info : Info) → Request → Option (Choice info)
  encode : (info : Info) → Choice info → Request
  decode_encode : ∀ info choice, decode info (encode info choice) = some choice

abbrev Attempts (Request : Type) := List (Option Request)

/-- Most recent decision first; each entry retains the information at that
decision and every attempted request, most recent request first. -/
abbrev Memory (Info Request : Type) := List (Info × Attempts Request)

/-- A deterministic controller can use all its prior request histories.
Finite private randomization over these controllers is supplied by the game. -/
abbrev Policy (Info Request : Type) :=
  Info → Memory Info Request → Attempts Request → Option Request

def accepted (gate : Gate Info Choice Request) (info : Info) :
    Option Request → Option (Choice info)
  | none => none
  | some request => gate.decode info request

def execute (gate : Gate Info Choice Request) (policy : Policy Info Request)
    (info : Info) (memory : Memory Info Request) :
    Nat → Attempts Request → Choice info × Attempts Request
  | 0, attempts => (gate.timeoutAction info, attempts)
  | slots + 1, attempts =>
      let request := policy info memory attempts
      match accepted gate info request with
      | some choice => (choice, request :: attempts)
      | none => execute gate policy info memory slots (request :: attempts)

def compile (gate : Gate Info Choice Request) (policy : (info : Info) → Choice info) :
    Policy Info Request :=
  fun info _ _ => some (gate.encode info (policy info))

@[simp] theorem execute_compile (gate : Gate Info Choice Request)
    (policy : (info : Info) → Choice info) (info : Info)
    (memory : Memory Info Request) (slots : Nat) (attempts : Attempts Request) :
    execute gate (compile gate policy) info memory (slots + 1) attempts =
      (policy info, some (gate.encode info (policy info)) :: attempts) := by
  simp [execute, compile, accepted, gate.decode_encode]

theorem silence_timeout (gate : Gate Info Choice Request) (info : Info)
    (memory : Memory Info Request) (slots : Nat) (attempts : Attempts Request) :
    (execute gate (fun _ _ _ => none) info memory slots attempts).1 = gate.timeoutAction info := by
  induction slots generalizing attempts with
  | zero => rfl
  | succ slots ih => exact ih (none :: attempts)

end Vegas.Runtime.ActionWindow
