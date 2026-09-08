/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Game.SealedTimeout
import VegasTests.PendingOutcome

/-! # A complete timed run reaches the nullable source

Checkpoint completion is not used as a terminality criterion. This regression
includes both openings, decodes all four graph nodes, and proves terminality of
that decoded configuration separately.
-/

noncomputable section

namespace VegasTests.PendingTimeoutSource

open Interaction Vegas EventGraph
open VegasTests.PendingSource VegasTests.PendingExecution VegasTests.PendingOutcome

abbrev Value := Option Bool

def timed : SealedTimeout PendingSource.Player := ⟨sealedFragment.compile, 3, 5⟩

def timedAction : SealedProgram.Action PendingSource.Player Value →
    SealedTimeout.Action PendingSource.Player Value
  | .register owner slot value => .register owner slot value
  | .submit author payload => .submit author (.protocol payload)
  | .replay broadcaster id => .replay broadcaster id
  | .deliver observer id => .deliver observer id
  | .include id => .include id

def timedActions (left right : Value) (reverse : Bool) :
    List (SealedTimeout.Action PendingSource.Player Value) :=
  .advance 6 :: (honestActions left right reverse).map timedAction

def result (left right : Value) (reverse : Bool) :
    SealedTimeout.State PendingSource.Player Value :=
  timed.run (SealedTimeout.State.empty PendingSource.Player Value)
    (timedActions left right reverse)

theorem result_application (left right : Value) (reverse : Bool) :
    (result left right reverse).application.service =
        (honestRun left right reverse).service ∧
      (result left right reverse).application.events =
        (honestRun left right reverse).events ∧
      (result left right reverse).application.resolution = .completed := by
  fin_cases left <;> fin_cases right <;> cases reverse <;> exact ⟨rfl, rfl, rfl⟩

theorem decode_result (left right : Value) (reverse : Bool) :
    graph.decodeSealedFrom (.option .bool)
      (result left right reverse).application.service (Config.initial graph)
      (result left right reverse).application.events =
        some (expected left right) := by
  rw [(result_application left right reverse).1,
    (result_application left right reverse).2.1]
  exact decode_honestRun left right reverse

theorem result_terminal (left right : Value) (reverse : Bool) :
    ∃ cfg : Config graph,
      graph.decodeSealedFrom (.option .bool) (result left right reverse).application.service
        (Config.initial graph) (result left right reverse).application.events = some cfg ∧
      Reachable graph cfg ∧ Terminal graph cfg := by
  obtain ⟨cfg, hdecode, hreachable⟩ :=
    sealedFragment.sealed_timeout_run_refines 3 5 (timedActions left right reverse)
  have hcfg : cfg = expected left right :=
    Option.some.inj (hdecode.symm.trans (decode_result left right reverse))
  subst cfg
  exact ⟨expected left right, decode_result left right reverse, hreachable,
    expected_terminal left right⟩

theorem complete_timed_run_source (left right : Value) (reverse : Bool) :
    ∃ terminalEnv : VEnv simpleExpr compiled.terminalCtx,
      SmallStep.Star
        { ctx := source.core.Γ, env := source.core.env, cont := source.core.prog }
        { ctx := compiled.terminalCtx, env := terminalEnv,
          cont := .ret compiled.sourcePayoffs } ∧
      evalPayoffs? compiled.payoffs (expected left right).store =
        some (evalPayoffs compiled.sourcePayoffs terminalEnv) ∧
      ∀ {name bindTy} (h : VHasVar compiled.terminalCtx name bindTy),
        Store.getAs (expected left right).store
          (compiled.terminalState.fieldOf h) bindTy.base = some (terminalEnv.get h) := by
  obtain ⟨cfg, hdecode, _hreachable, hsource⟩ :=
    source.sealed_timeout_run_source (.option .bool) sealedFragment 3 5
      (timedActions left right reverse)
  have hcfg : cfg = expected left right :=
    Option.some.inj (hdecode.symm.trans (decode_result left right reverse))
  subst cfg
  exact hsource (expected_terminal left right)

end VegasTests.PendingTimeoutSource

/-- info: 'Vegas.EventGraph.SealedFragment.sealed_timeout_run_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.sealed_timeout_run_refines

/-- info: 'Vegas.WFProgram.sealed_timeout_run_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WFProgram.sealed_timeout_run_source

/-- info: 'Vegas.WFProgram.sealed_timeout_policy_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WFProgram.sealed_timeout_policy_source
