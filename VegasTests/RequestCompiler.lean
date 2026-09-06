/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.Request

/-! # Request validation, retry memory, and source-designated timeout tests -/

noncomputable section

namespace VegasTests.RequestCompiler

open Vegas.Runtime

/-- Requests 0 and 1 are source actions; every other packet is malformed. -/
def gate : ActionWindow.Gate Nat (fun _ => Bool) Nat where
  timeoutAction := fun _ => false
  decode := fun _ request => match request with
    | 0 => some false
    | 1 => some true
    | _ => none
  encode := fun _ choice => if choice then 1 else 0
  decode_encode := by intro info choice; cases choice <;> rfl

/-- A controller deliberately sends a malformed first packet. At its next
decision, it uses the retained rejection to choose a different source action. -/
def rememberRejection : ActionWindow.Policy Nat Nat := fun info memory attempts =>
  if info = 0 then if attempts = [] then some 2 else some 1
  else if memory = [(0, [some 1, some 2])] then some 0 else some 1

example : ActionWindow.execute gate rememberRejection 0 [] 2 [] =
    (true, [some 1, some 2]) := by decide

example : ActionWindow.execute gate rememberRejection 1
    [(0, [some 1, some 2])] 2 [] = (false, [some 0]) := by decide

example : ActionWindow.execute gate rememberRejection 1 [] 2 [] =
    (true, [some 1]) := by decide

example : ActionWindow.execute gate rememberRejection 0 [] 1 [] =
    (false, [some 2]) := by decide

example : ActionWindow.execute gate (fun _ _ _ => none) 0 [] 3 [] =
    (false, [none, none, none]) := by decide

/-- Zero delivery slots cannot implement the non-timeout action. -/
example (controller : ActionWindow.Policy Nat Nat) :
    (ActionWindow.execute gate controller 0 [] 0 []).1 ≠ true := by
  change false ≠ true
  decide

/-- A valid compiled action needs no special treatment of prior retry memory. -/
example (info : Nat) (memory : ActionWindow.Memory Nat Nat) (slots : Nat) :
    (ActionWindow.execute gate (ActionWindow.compile gate (fun _ => true))
      info memory (slots + 1) []).1 = true := by
  rw [ActionWindow.execute_compile]

/-- Neither finiteness of request types nor finite global information carriers
are required for the whole-protocol pure and mixed certificates. -/
example {Player : Type} [Fintype Player] [DecidableEq Player]
    {E : GameTheory.Protocol.ExecutionProtocol Player}
    (M : GameTheory.Protocol.InformationModel E) (recall : M.PerfectRecall)
    (timeoutAction : (who : Player) → M.Policy who)
    (slots : (who : Player) → M.InfoState who → Nat)
    (horizon : Nat) (utility : E.History → Player → ℝ) :
    Nonempty (DeviationAdequacy (RequestCompiler.sourceGame M horizon utility).mixed
      (RequestCompiler.targetGame M (RequestCompiler.menuInterface M timeoutAction slots)
        horizon utility).mixed) :=
  ⟨RequestCompiler.mixedAdequacy M _ recall horizon utility⟩

end VegasTests.RequestCompiler
