/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.PendingOutcome

/-! # Replayed messages in the compiled nullable protocol

These transcripts use the actual compiled program. A broadcaster copies an
observed envelope with its original author intact. Application idempotence
does not imply that the ledger is unchanged, or that a previously rejected
opening can never become valid after other nodes complete.
-/

namespace VegasTests.PendingReplay

open Interaction Interaction.SealedProgram
open Vegas EventGraph
open VegasTests.PendingSource VegasTests.PendingExecution

/-- One submitted commitment is pending but has not reached player 1. -/
def hiddenCommitment : RuntimeState :=
  program.run initial [.register 0 0 (some false),
    .submit 0 (.commitment 0 (0, 0))]

theorem cannot_replay_unobserved :
    program.step hiddenCommitment (.replay 1 (0, 0)) = hiddenCommitment := by
  rfl

/-- The recipient can copy a delivered commitment, retaining player 0 as its
author and retaining the original message id. Both copies remain pending. -/
def copiedCommitment : RuntimeState :=
  program.run hiddenCommitment [.deliver 1 (0, 0), .replay 1 (0, 0)]

theorem copied_original_envelope :
    copiedCommitment.pool.pending =
      [⟨(0, 0), .commitment 0 (0, 0)⟩, ⟨(0, 0), .commitment 0 (0, 0)⟩] ∧
    copiedCommitment.pool.nextSerial 0 = 1 ∧
    copiedCommitment.pool.nextSerial 1 = 0 := by
  exact ⟨rfl, rfl, rfl⟩

def includedTwice : RuntimeState :=
  program.run copiedCommitment [.include (0, 0), .include (0, 0)]

theorem copied_commitment_executes_once :
    includedTwice.events = [.accepted 0 (0, 0)] ∧
    includedTwice.pool.ledger =
      [⟨(0, 0), .commitment 0 (0, 0)⟩, ⟨(0, 0), .commitment 0 (0, 0)⟩] := by
  exact ⟨rfl, rfl⟩

def completed : RuntimeState := honestRun (some false) (some true) false

/-- Player 1 rebroadcasts player 0's commitment and opening after completion. -/
def replayCompletedActions : List (Action PendingSource.Player Value) :=
  [.replay 1 (0, 0), .include (0, 0), .replay 1 (0, 1), .include (0, 1)]

def replayCompleted : RuntimeState := program.run completed replayCompletedActions

theorem completed_application_unchanged :
    replayCompleted.events = completed.events ∧
    replayCompleted.service = completed.service := by
  exact ⟨rfl, rfl⟩

theorem completed_ledger_extended :
    replayCompleted.pool.ledger = completed.pool.ledger ++
      [⟨(0, 0), .commitment 0 (0, 0)⟩, ⟨(0, 1), .opening 2 (0, 0) (some false)⟩] := by
  rfl

theorem completed_replay_observable :
    replayCompleted.observe 0 ≠ completed.observe 0 := by
  intro heq
  have hlength := congrArg (fun view => view.messages.ledger.length) heq
  change 6 = 4 at hlength
  contradiction

/-- An opening was published before its second commitment prerequisite was
included. It is visible, but has not executed an application reveal. -/
def premature : RuntimeState :=
  program.run initial
    [.register 0 0 (some false), .submit 0 (.commitment 0 (0, 0)), .include (0, 0),
     .register 1 1 (some true), .submit 1 (.commitment 1 (1, 1)),
     .submit 0 (.opening 2 (0, 0) (some false)), .deliver 1 (0, 1), .include (0, 1)]

theorem premature_opening_rejected :
    premature.events = [.accepted 0 (0, 0)] ∧
    premature.pool.ledger =
      [⟨(0, 0), .commitment 0 (0, 0)⟩, ⟨(0, 1), .opening 2 (0, 0) (some false)⟩] := by
  exact ⟨rfl, rfl⟩

/-- After the premature opening, the transcript contains only inclusion and
player 1's replay. The observed opening succeeds once its prerequisites hold. -/
def enabledReplay : RuntimeState :=
  program.run premature [.include (1, 0), .replay 1 (0, 1), .include (0, 1)]

theorem rejected_opening_can_execute_later :
    enabledReplay.events =
      [.accepted 0 (0, 0), .accepted 1 (1, 1), .opened 2 (some false)] := by
  rfl

/-- Explicit replay is covered by the same native-to-source theorem. -/
theorem completed_replay_source :
    ∃ terminalEnv : Vegas.VEnv Vegas.simpleExpr compiled.terminalCtx,
      Vegas.SmallStep.Star
        { ctx := source.core.Γ, env := source.core.env, cont := source.core.prog }
        { ctx := compiled.terminalCtx, env := terminalEnv,
          cont := .ret compiled.sourcePayoffs } ∧
      evalPayoffs? compiled.payoffs
          (VegasTests.PendingOutcome.expected (some false) (some true)).store =
        some (Vegas.evalPayoffs compiled.sourcePayoffs terminalEnv) ∧
      ∀ {name bindTy} (h : Vegas.VHasVar compiled.terminalCtx name bindTy),
        Store.getAs
          (VegasTests.PendingOutcome.expected (some false) (some true)).store
          (compiled.terminalState.fieldOf h) bindTy.base = some (terminalEnv.get h) := by
  obtain ⟨cfg, hdecode, _, hsource⟩ := source.sealed_run_source
    (.option .bool) sealedFragment
    (VegasTests.PendingOutcome.honestActions (some false) (some true) false ++
      replayCompletedActions)
  change graph.decodeSealed (.option .bool)
      (program.run initial
        (VegasTests.PendingOutcome.honestActions (some false) (some true) false ++
          replayCompletedActions)) = some cfg at hdecode
  rw [SealedProgram.run_append, ← VegasTests.PendingOutcome.honestRun_eq_run] at hdecode
  change graph.decodeSealed (.option .bool) replayCompleted = some cfg at hdecode
  have heq : graph.decodeSealed (.option .bool) replayCompleted =
      some (VegasTests.PendingOutcome.expected (some false) (some true)) := by
    change VegasTests.PendingOutcome.decoded completed = _
    exact VegasTests.PendingOutcome.decode_honestRun (some false) (some true) false
  have hcfg := Option.some.inj (hdecode.symm.trans heq)
  subst cfg
  exact hsource (VegasTests.PendingOutcome.expected_terminal (some false) (some true))

#guard replayCompleted.events.length == 4
#guard replayCompleted.pool.ledger.length == 6
#guard enabledReplay.events.length == 3

end VegasTests.PendingReplay

/-- info: 'VegasTests.PendingReplay.completed_replay_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.PendingReplay.completed_replay_source
