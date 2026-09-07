/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasEVM.Contract.Validator

/-!
# Logical contract execution

The logical executor repeats the finite request checks and, when they pass,
returns the exact semantic law over raw graph configurations.  For an encoded
proof-carrying command, that law is definitionally the primitive event law and
therefore exactly the projection of `Machine.Program.step`.

This is a semantic reference executor, not an extracted random sampler:
GameTheory's canonical `FinDist` is a noncomputable PMF-based analysis object.
A concrete backend must lower retained `EventDist` code to its entropy or
sampling mechanism and prove the resulting law correct.
-/

noncomputable section

namespace Vegas.Machine.Contract

open EventGraph
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}

namespace Request

variable {program : Program Player L}

/-- Validate and execute one logical request against a raw graph
configuration. Invalid requests return `none`; valid requests return their
exact next-configuration law. -/
def executeConfig? (cfg : Config program.graph) :
    Request Player L → Option (FinDist (Config program.graph))
  | { node := rawNode, authority := authority, payload := payload } =>
      if hnode : rawNode < program.graph.nodeCount then
        let node : Fin program.graph.nodeCount := ⟨rawNode, hnode⟩
        let row := program.graph.nodeRow node
        match row.sem with
        | .commit who guard =>
            match authority, payload with
            | .player actor, .value supplied =>
                if actor = who then
                  match supplied.as? guard.ty with
                  | none => none
                  | some value =>
                      match ReadEnv.ofStoreExec? cfg.store
                          guard.choiceReads with
                      | none => none
                      | some env =>
                          if Ready program.graph cfg node then
                            if guard.eval value env = true then
                              some <| FinDist.pure <|
                                cfg.completeNode node
                                  { ty := guard.ty, value := value }
                            else
                              none
                          else
                            none
                else
                  none
            | _, _ => none
        | .sample dist =>
            match authority, payload with
            | .internal, .none =>
                match ReadEnv.ofStoreExec? cfg.store dist.reads with
                | none => none
                | some env =>
                    if Ready program.graph cfg node then
                      some <| (dist.eval env).map fun value =>
                        cfg.completeNode node { ty := dist.ty, value := value }
                    else
                      none
            | _, _ => none
        | .reveal source =>
            match authority, payload with
            | .internal, .none =>
                match Store.getAs cfg.store source row.ty with
                | none => none
                | some value =>
                    if Ready program.graph cfg node then
                      some <| FinDist.pure <|
                        cfg.completeNode node { ty := row.ty, value := value }
                    else
                      none
            | _, _ => none
      else
        none

/-- Logical execution succeeds exactly when Boolean request validation does.
-/
theorem executeConfig?_isSome
    (cfg : Config program.graph) (request : Request Player L) :
    (executeConfig? cfg request).isSome = acceptsConfig cfg request := by
  rcases request with ⟨rawNode, authority, payload⟩
  by_cases hnode : rawNode < program.graph.nodeCount
  · let node : Fin program.graph.nodeCount := ⟨rawNode, hnode⟩
    let row := program.graph.nodeRow node
    cases hsem : row.sem <;> cases authority <;> cases payload <;>
      simp only [executeConfig?, acceptsConfig, hnode, ↓reduceDIte,
        node, row, hsem]
    all_goals try rfl
    all_goals
      repeat' split <;> simp_all
  · simp [executeConfig?, acceptsConfig, hnode]

/-- Executing the envelope of a valid proof-carrying command recovers exactly
the primitive raw-configuration transition law. -/
theorem executeConfig?_encode
    (state : program.State) (command : program.Command state) :
    executeConfig? state.1 (encode command) =
      some (stepAvailableEvent program.graph state.1 command) := by
  cases command with
  | commit who action step =>
      change executeConfig? state.1
        { node := action.node
          authority := .player who
          payload := .value action.value } = _
      have hrow : program.graph.nodeRow action.node = step.row := by
        have hget :
            program.graph.nodes[(action.node : Nat)]? = some step.row :=
          step.row_get
        rw [program.graph.nodes_get?_nodeRow action.node] at hget
        exact Option.some.inj hget
      have hsem :
          (program.graph.nodeRow action.node).sem =
            .commit who step.guard := by
        rw [hrow]
        exact step.sem_eq
      have hexecSome :=
        ReadEnv.ofStoreExec?_isSome_of_ofStore?_eq_some step.env_ok
      rcases Option.isSome_iff_exists.mp hexecSome with ⟨execEnv, hexec⟩
      have hproofEnv :=
        ReadEnv.ofStore?_eq_some_of_ofStoreExec?_eq_some hexec
      have henv : execEnv = step.env := by
        rw [step.env_ok] at hproofEnv
        exact (Option.some.inj hproofEnv).symm
      have hguard : step.guard.eval step.value execEnv = true := by
        rw [henv]
        exact step.guard_ok
      simp [executeConfig?, action.node.isLt, hsem, step.value_ok,
        hexec, step.ready, hguard, stepAvailableEvent, stepCommit]
  | internal event step =>
      cases step with
      | sample row dist row_get sem_eq ready env env_ok =>
          change executeConfig? state.1
            { node := event.node
              authority := .internal
              payload := .none } = _
          have hrow : program.graph.nodeRow event.node = row := by
            have hget :
                program.graph.nodes[(event.node : Nat)]? = some row := row_get
            rw [program.graph.nodes_get?_nodeRow event.node] at hget
            exact Option.some.inj hget
          have hsem :
              (program.graph.nodeRow event.node).sem = .sample dist := by
            rw [hrow]
            exact sem_eq
          have hexecSome :=
            ReadEnv.ofStoreExec?_isSome_of_ofStore?_eq_some env_ok
          rcases Option.isSome_iff_exists.mp hexecSome with
            ⟨execEnv, hexec⟩
          have hproofEnv :=
            ReadEnv.ofStore?_eq_some_of_ofStoreExec?_eq_some hexec
          have henv : execEnv = env := by
            rw [env_ok] at hproofEnv
            exact (Option.some.inj hproofEnv).symm
          simp [executeConfig?, event.node.isLt, hsem, hexec, ready,
            henv, stepAvailableEvent, stepInternal]
      | reveal row source row_get sem_eq ready value value_ok =>
          change executeConfig? state.1
            { node := event.node
              authority := .internal
              payload := .none } = _
          have hrow : program.graph.nodeRow event.node = row := by
            have hget :
                program.graph.nodes[(event.node : Nat)]? = some row := row_get
            rw [program.graph.nodes_get?_nodeRow event.node] at hget
            exact Option.some.inj hget
          subst row
          simp [executeConfig?, event.node.isLt, sem_eq, value_ok, ready,
            stepAvailableEvent, stepInternal]

/-- The logical executor law is exactly the reachability-erased machine-step
law. -/
theorem executeConfig?_encode_eq_map_step
    (state : program.State) (command : program.Command state) :
    executeConfig? state.1 (encode command) =
      some (FinDist.map Subtype.val (program.step state command)) := by
  rw [executeConfig?_encode, Program.step]
  rw [EventGraph.map_val_stepAvailable]

end Request

end Vegas.Machine.Contract
