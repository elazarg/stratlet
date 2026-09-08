/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.SealedSource
import VegasTests.PendingExecution

/-! # Decoded outcome of the nullable pending-message transcript -/

noncomputable section

namespace VegasTests.PendingOutcome

open Interaction Interaction.SealedProgram
open Vegas EventGraph
open VegasTests.PendingSource VegasTests.PendingExecution

def expected (left right : Value) : Config graph :=
  ((((Config.initial graph).completeNode (node 0) ⟨.option .bool, left⟩)
    |>.completeNode (node 1) ⟨.option .bool, right⟩)
    |>.completeNode (node 2) ⟨.option .bool, left⟩)
    |>.completeNode (node 3) ⟨.option .bool, right⟩

def honestActions (left right : Value) (reverse : Bool) :
    List (Action PendingSource.Player Value) :=
  commitActions left right reverse ++ openingActions left right

theorem honestRun_eq_run (left right : Value) (reverse : Bool) :
    honestRun left right reverse = program.run initial (honestActions left right reverse) := by
  simp [honestRun, afterCommits, honestActions, SealedProgram.run, List.foldl_append]

def decoded (state : RuntimeState) : Option (Config graph) :=
  Graph.decodeSealed graph (.option .bool) state

private theorem decodeEvents
    (service : IdealCommitments PendingSource.Player Nat Value) (cfg : Config graph)
    (first second third fourth : Fin graph.nodeCount)
    (firstHandle secondHandle : CommitmentHandle PendingSource.Player Nat)
    (a b c d : Value)
    (ha : service.lookup firstHandle = some a) (hb : service.lookup secondHandle = some b) :
    graph.decodeSealedFrom (.option .bool) service cfg
        [.accepted first.val firstHandle, .accepted second.val secondHandle,
          .opened third.val c, .opened fourth.val d] =
      some (cfg.completeNodes
        [(first, ⟨.option .bool, a⟩), (second, ⟨.option .bool, b⟩),
          (third, ⟨.option .bool, c⟩), (fourth, ⟨.option .bool, d⟩)]) := by
  simp only [Graph.decodeSealedFrom]
  rw [graph.decodeSealedEvent_accepted (.option .bool) service first firstHandle,
    graph.decodeSealedEvent_accepted (.option .bool) service second secondHandle,
    graph.decodeSealedEvent_opened (.option .bool) service third c,
    graph.decodeSealedEvent_opened (.option .bool) service fourth d,
    ha, hb]
  rfl

theorem decode_honestRun (left right : Value) (reverse : Bool) :
    decoded (honestRun left right reverse) = some (expected left right) := by
  cases reverse
  · unfold decoded Graph.decodeSealed
    rw [honest_forward_events]
    exact decodeEvents _ _ (node 0) (node 1) (node 2) (node 3) (0, 0) (1, 1)
      left right left right (honest_service_left left right false)
      (honest_service_right left right false)
  · unfold decoded Graph.decodeSealed
    rw [honest_reverse_events]
    have h := decodeEvents (honestRun left right true).service (Config.initial graph)
      (node 1) (node 0) (node 2) (node 3) (1, 1) (0, 0) right left left right
      (honest_service_right left right true) (honest_service_left left right true)
    simp only [Config.completeNodes_cons, Config.completeNodes_nil] at h
    rw [Config.completeNode_comm (left := node 1) (right := node 0)
      (hne := by decide)] at h
    exact h

theorem expected_terminal (left right : Value) : Terminal graph (expected left right) := by
  intro candidate
  have hmem : candidate = node 3 ∨ candidate = node 2 ∨
      candidate = node 1 ∨ candidate = node 0 := by
    fin_cases candidate
    · exact Or.inr (Or.inr (Or.inr (Fin.ext rfl)))
    · exact Or.inr (Or.inr (Or.inl (Fin.ext rfl)))
    · exact Or.inr (Or.inl (Fin.ext rfl))
    · exact Or.inl (Fin.ext rfl)
  simpa only [expected, Config.completeNode, Finset.mem_insert, Config.initial,
    Finset.notMem_empty, or_false] using hmem

theorem honestRun_terminal (left right : Value) (reverse : Bool) :
    ∃ cfg : Config graph,
      decoded (honestRun left right reverse) = some cfg ∧
      Reachable graph cfg ∧ Terminal graph cfg := by
  obtain ⟨cfg, hdecode, hreachable⟩ :=
    Vegas.EventGraph.SealedFragment.run_refines sealedFragment (honestActions left right reverse)
  change decoded (program.run initial (honestActions left right reverse)) = some cfg at hdecode
  rw [← honestRun_eq_run] at hdecode
  have hcfg : cfg = expected left right := by
    exact Option.some.inj (hdecode.symm.trans (decode_honestRun left right reverse))
  subst cfg
  exact ⟨expected left right, decode_honestRun left right reverse,
    hreachable, expected_terminal left right⟩

/-- The executable transcript reaches the written source semantics, with all
terminal bindings preserved. This does not identify withholding with a source
nullable choice: the transcript submits and opens each chosen value. -/
theorem honestRun_source (left right : Value) (reverse : Bool) :
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
  obtain ⟨cfg, hdecode, _, hsource⟩ := source.sealed_run_source
    (.option .bool) sealedFragment (honestActions left right reverse)
  change decoded (program.run initial (honestActions left right reverse)) = some cfg at hdecode
  rw [← honestRun_eq_run] at hdecode
  have hcfg : cfg = expected left right :=
    Option.some.inj (hdecode.symm.trans (decode_honestRun left right reverse))
  subst cfg
  exact hsource (expected_terminal left right)

end VegasTests.PendingOutcome

/-- info: 'Vegas.WFProgram.sealed_run_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WFProgram.sealed_run_source
