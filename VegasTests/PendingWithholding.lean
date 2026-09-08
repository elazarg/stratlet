/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedPersistence
import VegasTests.PendingRelease

/-! # Informed withholding after the compiled release boundary

This deterministic control uses the actual checked pending-choice program.
Player one binds `some false` before release, but after observing player zero's
included opening submits its own opening only when that value is `some false`.
The other branch remains pending; it is not reinterpreted as source `none`.
-/

namespace VegasTests.PendingWithholding

open Interaction Interaction.SealedProgram GameTheory GameTheory.Math.Probability
open VegasTests.PendingSource VegasTests.PendingExecution

noncomputable section

def withholding : PlayerPolicy Player Value true := fun history view =>
  match history.length with
  | 0 => FinDist.pure ⟨.register 1 (some false), trivial⟩
  | 1 => FinDist.pure ⟨.submit (.commitment 1 (1, 1)), trivial⟩
  | _ + 2 =>
      match view.messages.inbox with
      | ⟨_, .opening 2 (0, 0) (some false)⟩ :: _ =>
          FinDist.pure ⟨.submit (.opening 3 (1, 1) (some false)), trivial⟩
      | _ => FinDist.pure ⟨.wait, trivial⟩

def profile (value : Value) : Profile (policySignature Player Value true) :=
  Profile.update (fun _ => withholding) 0 (commitOpenPolicy true program 0 0 2 value)

def environment : EnvironmentPolicy Player Value := fun history _ =>
  match history.length with
  | 0 => FinDist.pure (.include (0, 0))
  | 1 => FinDist.pure (.include (1, 0))
  | 2 => FinDist.pure (.deliver 1 (0, 1))
  | 3 => FinDist.pure (.include (0, 1))
  | 4 => FinDist.pure (.include (1, 1))
  | _ => FinDist.pure .wait

def schedule : List (Invocation Player) :=
  [.player 0, .player 0, .player 1, .player 1,
   .environment, .environment, .player 0, .environment,
   .environment, .player 1, .environment]

def law (value : Value) : FinDist (PolicyExecution Player Value) :=
  (policyGame true program environment schedule initial).play (profile value)

def responseCommand : Value → PlayerCommand Player Value
  | some false => .submit (.opening 3 (1, 1) (some false))
  | _ => .wait

def s0 : PolicyExecution Player Value := PolicyExecution.initial initial
def s1 (v : Value) := playerStep program 0 s0 (.register 0 v)
def s2 (v : Value) := playerStep program 0 (s1 v) (.submit (.commitment 0 (0, 0)))
def s3 (v : Value) := playerStep program 1 (s2 v) (.register 1 (some false))
def s4 (v : Value) := playerStep program 1 (s3 v) (.submit (.commitment 1 (1, 1)))
def s5 (v : Value) := environmentStep program (s4 v) (.include (0, 0))
def s6 (v : Value) := environmentStep program (s5 v) (.include (1, 0))
def s7 (v : Value) := playerStep program 0 (s6 v) (.submit (.opening 2 (0, 0) v))
def s8 (v : Value) := environmentStep program (s7 v) (.deliver 1 (0, 1))
def s9 (v : Value) := environmentStep program (s8 v) (.include (0, 1))
def s10 (v : Value) := playerStep program 1 (s9 v) (responseCommand v)
def s11 (v : Value) := environmentStep program (s10 v) (.include (1, 1))

private theorem allowedTrue (command : PlayerCommand Player Value) : command.allowed true := by
  cases command <;> trivial

private theorem invokePlayerPure (v : Value) (execution : PolicyExecution Player Value)
    (who : Player) (command : PlayerCommand Player Value)
    (hpolicy : profile v who (execution.principalHistory who) (execution.native.observe who) =
      FinDist.pure ⟨command, allowedTrue command⟩) :
    invoke true program (profile v) environment execution (.player who) =
      FinDist.pure (playerStep program who execution command) := by
  simp only [invoke, hpolicy, FinDist.map_pure]

private theorem invokeEnvironmentPure (v : Value) (execution : PolicyExecution Player Value)
    (command : EnvironmentCommand Player)
    (hpolicy : environment execution.environmentHistory execution.native.environmentView =
      FinDist.pure command) :
    invoke true program (profile v) environment execution .environment =
      FinDist.pure (environmentStep program execution command) := by
  simp only [invoke, hpolicy, FinDist.map_pure]

private theorem i0 (v : Value) : invoke true program (profile v) environment s0 (.player 0) =
    FinDist.pure (s1 v) := by apply invokePlayerPure; cases v <;> rfl
private theorem i1 (v : Value) : invoke true program (profile v) environment (s1 v) (.player 0) =
    FinDist.pure (s2 v) := by apply invokePlayerPure; cases v <;> rfl
private theorem i2 (v : Value) : invoke true program (profile v) environment (s2 v) (.player 1) =
    FinDist.pure (s3 v) := by apply invokePlayerPure; cases v <;> rfl
private theorem i3 (v : Value) : invoke true program (profile v) environment (s3 v) (.player 1) =
    FinDist.pure (s4 v) := by apply invokePlayerPure; cases v <;> rfl
private theorem i4 (v : Value) : invoke true program (profile v) environment (s4 v) .environment =
    FinDist.pure (s5 v) := by apply invokeEnvironmentPure; cases v <;> rfl
private theorem i5 (v : Value) : invoke true program (profile v) environment (s5 v) .environment =
    FinDist.pure (s6 v) := by apply invokeEnvironmentPure; cases v <;> rfl
private theorem i6 (v : Value) : invoke true program (profile v) environment (s6 v) (.player 0) =
    FinDist.pure (s7 v) := by apply invokePlayerPure; rcases v with _ | (_ | _) <;> rfl
private theorem i7 (v : Value) : invoke true program (profile v) environment (s7 v) .environment =
    FinDist.pure (s8 v) := by apply invokeEnvironmentPure; cases v <;> rfl
private theorem i8 (v : Value) : invoke true program (profile v) environment (s8 v) .environment =
    FinDist.pure (s9 v) := by apply invokeEnvironmentPure; cases v <;> rfl
private theorem i9 (v : Value) : invoke true program (profile v) environment (s9 v) (.player 1) =
    FinDist.pure (s10 v) := by
  apply invokePlayerPure
  rcases v with _ | (_ | _) <;> rfl
private theorem i10 (v : Value) : invoke true program (profile v) environment (s10 v) .environment =
    FinDist.pure (s11 v) := by apply invokeEnvironmentPure; cases v <;> rfl

theorem law_eq_final (v : Value) : law v = FinDist.pure (s11 v) := by
  change runPolicies true program (profile v) environment schedule s0 = _
  simp only [schedule, runPolicies, i0, i1, i2, i3, i4, i5, i6,
    i7, i8, i9, i10, FinDist.pure_bind]

theorem false_events : (law (some false)).map (fun execution => execution.native.events) =
    FinDist.pure [.accepted 0 (0, 0), .accepted 1 (1, 1),
      .opened 2 (some false), .opened 3 (some false)] := by
  rw [law_eq_final, FinDist.map_pure]
  rfl

theorem true_events : (law (some true)).map (fun execution => execution.native.events) =
    FinDist.pure [.accepted 0 (0, 0), .accepted 1 (1, 1), .opened 2 (some true)] := by
  rw [law_eq_final, FinDist.map_pure]
  rfl

/-- Player one's earlier binding remains `some false` in both worlds, including
the branch where it later withholds its opening. -/
theorem bound_lookup (v : Value) :
    (law v).map (fun execution => execution.native.service.lookup (1, 1)) =
      FinDist.pure (some (some false)) := by
  rw [law_eq_final, FinDist.map_pure]
  rcases v with _ | (_ | _) <;> rfl

def hasPlayerOneOpening : List (Event Player Value) → Bool
  | [] => false
  | .opened 3 (some false) :: _ => true
  | _ :: rest => hasPlayerOneOpening rest

def hasPlayerZeroTrueOpening : List (Event Player Value) → Bool
  | [] => false
  | .opened 2 (some true) :: _ => true
  | _ :: rest => hasPlayerZeroTrueOpening rest

theorem false_opens :
    (law (some false)).map (fun execution =>
      hasPlayerOneOpening execution.native.events) = FinDist.pure true := by
  rw [law_eq_final, FinDist.map_pure]
  rfl

/-- Withholding leaves reveal node three incomplete even though both commitment
nodes and player zero's opening are present. -/
theorem true_withholds :
    (law (some true)).map (fun execution =>
      (done execution.native.events 0, done execution.native.events 1,
        hasPlayerZeroTrueOpening execution.native.events,
        hasPlayerOneOpening execution.native.events)) =
      FinDist.pure (true, true, true, false) := by
  rw [law_eq_final, FinDist.map_pure]
  rfl

theorem disclosure_differs :
    (law (some false)).map (fun execution => hasPlayerOneOpening
      execution.native.events) ≠
    (law (some true)).map (fun execution => hasPlayerOneOpening
      execution.native.events) := by
  rw [false_opens]
  have htrue : (law (some true)).map (fun execution => hasPlayerOneOpening
      execution.native.events) = FinDist.pure false := by
    rw [law_eq_final, FinDist.map_pure]
    rfl
  rw [htrue]
  intro heq
  have hmem : true ∈ (FinDist.pure false : FinDist Bool).support := by
    rw [← heq]
    exact FinDist.mem_support_pure.mpr rfl
  exact Bool.noConfusion (FinDist.mem_support_pure.mp hmem)

end

end VegasTests.PendingWithholding
