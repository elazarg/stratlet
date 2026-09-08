/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.PendingRelease

/-! # Concrete release-boundary traces

This deterministic fixture executes the complete native policy schedule.  The
first-release readout stops observing immediately after both commitments are
accepted, while the underlying execution continues through delivery and
inclusion of the protected opening.
-/

namespace VegasTests.PendingReleaseExamples

open Interaction Interaction.SealedProgram GameTheory GameTheory.Math.Probability
open VegasTests.PendingSource VegasTests.PendingExecution
open VegasTests.PendingPolicies VegasTests.PendingRelease

noncomputable section

def opponent : PlayerPolicy Player Value true :=
  commitOpenPolicy true program 1 1 3 none

def players : Profile (policySignature Player Value true) := fun _ => opponent

def environment : EnvironmentPolicy Player Value := fun history _ =>
  match history.length with
  | 0 => FinDist.pure (.include (0, 0))
  | 1 => FinDist.pure (.include (1, 0))
  | 2 => FinDist.pure (.deliver 1 (0, 1))
  | 3 => FinDist.pure (.include (0, 1))
  | _ => FinDist.pure .wait

def schedule : List (Invocation Player) :=
  [.player 0, .player 1, .player 1, .environment, .player 0,
   .environment, .player 0, .environment, .environment, .player 0]

def law (value : Value) : FinDist (PolicyTrace Player Value) :=
  controllerTraceLaw true value players environment schedule

def profile (value : Value) : Player → PlayerPolicy Player Value true := fun who =>
  controllerProfile true value players who

def s0 : PolicyExecution Player Value := PolicyExecution.initial initial
def s1 (v : Value) := playerStep program 0 s0 (.register 0 v)
def s2 (v : Value) := playerStep program 0 (s1 v) (.submit (.commitment 0 (0, 0)))
def s3 (v : Value) := playerStep program 0 (s2 v) .wait
def s4 (v : Value) := playerStep program 1 (s3 v) (.register 1 none)
def s5 (v : Value) := playerStep program 1 (s4 v) (.submit (.commitment 1 (1, 1)))
def s6 (v : Value) := environmentStep program (s5 v) (.include (0, 0))
def s7 (v : Value) := playerStep program 0 (s6 v) .wait
def s8 (v : Value) := environmentStep program (s7 v) (.include (1, 0))
def s9 (v : Value) := playerStep program 0 (s8 v) (.submit (.opening 2 (0, 0) v))
def s10 (v : Value) := environmentStep program (s9 v) (.deliver 1 (0, 1))
def s11 (v : Value) := environmentStep program (s10 v) (.include (0, 1))
def s12 (v : Value) := playerStep program 0 (s11 v) .wait

def expectedTrace (v : Value) : PolicyTrace Player Value :=
  .step s0 (.step (s1 v) (.step (s2 v) (.step (s3 v) (.step (s4 v)
    (.step (s5 v) (.step (s6 v) (.step (s7 v) (.step (s8 v) (.step (s9 v)
      (.step (s10 v) (.step (s11 v) (.finish (s12 v)))))))))))))

private theorem allowedTrue (command : PlayerCommand Player Value) : command.allowed true := by
  cases command <;> trivial

private theorem invokePlayerPure (v : Value) (e : PolicyExecution Player Value)
    (who : Player) (command : PlayerCommand Player Value)
    (h : profile v who (e.principalHistory who) (e.native.observe who) =
      FinDist.pure ⟨command, allowedTrue command⟩) :
    invoke true program (profile v) environment e (.player who) =
      FinDist.pure (playerStep program who e command) := by
  simp only [invoke, h, FinDist.map_pure]

private theorem invokeEnvironmentPure (v : Value) (e : PolicyExecution Player Value)
    (command : EnvironmentCommand Player)
    (h : environment e.environmentHistory e.native.environmentView = FinDist.pure command) :
    invoke true program (profile v) environment e .environment =
      FinDist.pure (environmentStep program e command) := by
  simp only [invoke, h, FinDist.map_pure]

private theorem i0 (v : Value) :
    invoke true program (profile v) environment s0 (.player 0) = FinDist.pure (s1 v) := by
  apply invokePlayerPure
  cases v <;> rfl
private theorem i1 (v : Value) :
    invoke true program (profile v) environment (s1 v) (.player 0) = FinDist.pure (s2 v) := by
  apply invokePlayerPure
  cases v <;> rfl
private theorem i2 (v : Value) :
    invoke true program (profile v) environment (s2 v) (.player 0) = FinDist.pure (s3 v) := by
  apply invokePlayerPure
  cases v <;> rfl
private theorem i3 (v : Value) :
    invoke true program (profile v) environment (s3 v) (.player 1) = FinDist.pure (s4 v) := by
  apply invokePlayerPure
  cases v <;> rfl
private theorem i4 (v : Value) :
    invoke true program (profile v) environment (s4 v) (.player 1) = FinDist.pure (s5 v) := by
  apply invokePlayerPure
  cases v <;> rfl
private theorem i5 (v : Value) :
    invoke true program (profile v) environment (s5 v) .environment = FinDist.pure (s6 v) := by
  apply invokeEnvironmentPure
  cases v <;> rfl
private theorem i6 (v : Value) :
    invoke true program (profile v) environment (s6 v) (.player 0) = FinDist.pure (s7 v) := by
  apply invokePlayerPure
  cases v <;> rfl
private theorem i7 (v : Value) :
    invoke true program (profile v) environment (s7 v) .environment = FinDist.pure (s8 v) := by
  apply invokeEnvironmentPure
  cases v <;> rfl
private theorem i8 (v : Value) :
    invoke true program (profile v) environment (s8 v) (.player 0) = FinDist.pure (s9 v) := by
  apply invokePlayerPure
  cases v <;> rfl
private theorem i9 (v : Value) :
    invoke true program (profile v) environment (s9 v) .environment = FinDist.pure (s10 v) := by
  apply invokeEnvironmentPure
  cases v <;> rfl
private theorem i10 (v : Value) :
    invoke true program (profile v) environment (s10 v) .environment = FinDist.pure (s11 v) := by
  apply invokeEnvironmentPure
  cases v <;> rfl
private theorem i11 (v : Value) :
    invoke true program (profile v) environment (s11 v) (.player 0) = FinDist.pure (s12 v) := by
  apply invokePlayerPure
  rcases v with _ | (_ | _) <;> rfl

theorem law_eq_trace (v : Value) : law v = FinDist.pure (expectedTrace v) := by
  change tracePolicies true program (profile v) environment
    (.player 0 :: .player 0 :: schedule) s0 = _
  simp only [schedule, tracePolicies, i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10,
    i11, FinDist.pure_bind, FinDist.map_pure]
  rfl

def cutEvents (value : Value) : FinDist (List (Event Player Value)) :=
  (law value).map fun trace => (trace.firstRelease release).native.events

def finalEvents (value : Value) : FinDist (List (Event Player Value)) :=
  (law value).map fun trace => trace.last.native.events

theorem cut_observations_hide :
    ((law (some false)).map (PolicyTrace.firstRelease release)).map
        (PolicyExecution.observations 0) =
      ((law (some true)).map (PolicyTrace.firstRelease release)).map
        (PolicyExecution.observations 0) :=
  controllerTraceLaw_hiding true (some false) (some true) players environment schedule

theorem cutEvents_eq (v : Value) : cutEvents v =
    FinDist.pure [.accepted 0 (0, 0), .accepted 1 (1, 1)] := by
  rw [cutEvents, law_eq_trace]
  rw [FinDist.map_pure]
  congr 1

theorem finalEvents_eq (v : Value) : finalEvents v =
    FinDist.pure [.accepted 0 (0, 0), .accepted 1 (1, 1), .opened 2 v] := by
  rw [finalEvents, law_eq_trace]
  rw [FinDist.map_pure]
  congr 1
  rcases v with _ | (_ | _) <;> rfl

theorem cut_ready (v : Value) : (cutEvents v).map release = FinDist.pure true := by
  rw [cutEvents_eq]
  rw [FinDist.map_pure]
  congr 1

theorem final_not_ready (v : Value) : (finalEvents v).map release = FinDist.pure false := by
  rw [finalEvents_eq]
  rw [FinDist.map_pure]
  congr 1

/-- Submission already exposes the protected value to the complete wire-pool
observer, before the opening is included by the application. -/
theorem s9_opening_visible (v : Value) :
    (s9 v).native.pool.sent 0 =
      [⟨(0, 0), .commitment 0 (0, 0)⟩, ⟨(0, 1), .opening 2 (0, 0) v⟩] := by
  rcases v with _ | (_ | _) <;> rfl

/-- Delivery exposes that same opening to player one while the application
still contains only the two accepted commitments. -/
theorem s10_delivered_before_inclusion (v : Value) :
    (s10 v).native.pool.inbox 1 = [⟨(0, 1), .opening 2 (0, 0) v⟩] ∧
      (s10 v).native.events = [.accepted 0 (0, 0), .accepted 1 (1, 1)] := by
  rcases v with _ | (_ | _) <;> exact ⟨rfl, rfl⟩

theorem full_events_disclose : finalEvents (some false) ≠ finalEvents (some true) := by
  rw [finalEvents_eq, finalEvents_eq]
  intro heq
  have hmem : [.accepted 0 (0, 0), .accepted 1 (1, 1), .opened 2 (some false)] ∈
      (FinDist.pure [.accepted 0 (0, 0), .accepted 1 (1, 1), .opened 2 (some true)] :
        FinDist (List (Event Player Value))).support := by
    rw [← heq]
    exact FinDist.mem_support_pure.mpr rfl
  have hlist := FinDist.mem_support_pure.mp hmem
  simp at hlist

end

end VegasTests.PendingReleaseExamples
