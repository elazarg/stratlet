/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasEVM.Contract.ABI

/-!
# Executable logical request validation

This module checks raw logical ABI requests by finite computation: node
bounds, authority and payload shape, graph readiness, typed decoding, read
availability, and commit guards.  `accepts` is a computable Boolean, while its
adequacy theorem relates that Boolean boundary to the proof-carrying semantic
command relation.

The validator still runs over semantic machine state and language values.  A
backend must separately prove that decoding concrete calldata and storage
reconstructs those inputs.
-/

namespace Vegas.Machine.Contract

open EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr}

namespace Request

variable {program : Program Player L}

/-- Execute the finite logical request checks against a raw graph
configuration. Reachability is not needed to run the checks. -/
def acceptsConfig (cfg : Config program.graph) : Request Player L → Bool
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
                  | none => false
                  | some value =>
                      match ReadEnv.ofStoreExec? cfg.store
                          guard.choiceReads with
                      | none => false
                      | some env =>
                          if Ready program.graph cfg node then
                            guard.eval value env
                          else
                            false
                else
                  false
            | _, _ => false
        | .sample dist =>
            match authority, payload with
            | .internal, .none =>
                match ReadEnv.ofStoreExec? cfg.store dist.reads with
                | none => false
                | some _env => decide (Ready program.graph cfg node)
            | _, _ => false
        | .reveal source =>
            match authority, payload with
            | .internal, .none =>
                match Store.getAs cfg.store source row.ty with
                | none => false
                | some _value => decide (Ready program.graph cfg node)
            | _, _ => false
      else
        false

/-- Executably decide whether a logical request denotes a currently available
primitive command in a reachable machine state. -/
def accepts (state : program.State) (request : Request Player L) : Bool :=
  acceptsConfig state.1 request

/-- Erasing a proof-carrying valid command always passes executable
validation. -/
theorem accepts_encode
    {state : program.State} (command : program.Command state) :
    accepts state (encode command) = true := by
  cases command with
  | commit who action step =>
      change accepts state
        { node := action.node
          authority := .player who
          payload := .value action.value } = true
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
      simp [accepts, acceptsConfig, action.node.isLt, hsem, step.value_ok, hexec,
        step.ready, hguard]
  | internal event step =>
      cases step with
      | sample row dist row_get sem_eq ready env env_ok =>
          change accepts state
            { node := event.node
              authority := .internal
              payload := .none } = true
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
          simp [accepts, acceptsConfig, event.node.isLt, hsem, hexec, ready]
      | reveal row source row_get sem_eq ready value value_ok =>
          change accepts state
            { node := event.node
              authority := .internal
              payload := .none } = true
          have hrow : program.graph.nodeRow event.node = row := by
            have hget :
                program.graph.nodes[(event.node : Nat)]? = some row := row_get
            rw [program.graph.nodes_get?_nodeRow event.node] at hget
            exact Option.some.inj hget
          have hsem :
              (program.graph.nodeRow event.node).sem = .reveal source := by
            rw [hrow]
            exact sem_eq
          have hvalueCanonical :=
            Store.getAs_cast state.1.store source
              (congrArg EventNode.ty hrow.symm) value_ok
          simp [accepts, acceptsConfig, event.node.isLt, hsem,
            hvalueCanonical, ready]

/-- Every request accepted by executable validation reconstructs a valid
proof-carrying semantic command. -/
theorem represents_of_accepts_eq_true
    {state : program.State} {request : Request Player L}
    (haccepts : accepts state request = true) :
    Represents state request := by
  rcases request with ⟨rawNode, authority, payload⟩
  by_cases hnode : rawNode < program.graph.nodeCount
  · let node : Fin program.graph.nodeCount := ⟨rawNode, hnode⟩
    let row := program.graph.nodeRow node
    have hrowGet : program.graph.nodes[(node : Nat)]? = some row :=
      program.graph.nodes_get?_nodeRow node
    cases hsem : row.sem with
    | commit who guard =>
        cases authority with
        | internal =>
            simp [accepts, acceptsConfig, hnode, node, row, hsem] at haccepts
        | player actor =>
            cases payload with
            | none =>
                simp [accepts, acceptsConfig, hnode, node, row, hsem]
                  at haccepts
            | value supplied =>
                by_cases hactor : actor = who
                · subst actor
                  cases hvalue : supplied.as? guard.ty with
                  | none =>
                      simp [accepts, acceptsConfig, hnode, node, row, hsem,
                        hvalue]
                        at haccepts
                  | some value =>
                      cases henv :
                          ReadEnv.ofStoreExec? state.1.store
                            guard.choiceReads with
                      | none =>
                          simp [accepts, acceptsConfig, hnode, node, row, hsem,
                            hvalue, henv] at haccepts
                      | some env =>
                          by_cases hready : Ready program.graph state.1 node
                          · have hguard : guard.eval value env = true := by
                              simpa [accepts, acceptsConfig, hnode, node, row, hsem,
                                hvalue, henv, hready] using haccepts
                            have envOk :=
                              ReadEnv.ofStore?_eq_some_of_ofStoreExec?_eq_some
                                henv
                            refine
                              ⟨.commit who
                                { node := node, value := supplied }
                                { row := row
                                  guard := guard
                                  row_get := hrowGet
                                  sem_eq := hsem
                                  ready := hready
                                  value := value
                                  value_ok := hvalue
                                  env := env
                                  env_ok := envOk
                                  guard_ok := hguard }, ?_⟩
                            rfl
                          · simp [accepts, acceptsConfig, hnode, node, row, hsem,
                              hvalue, henv, hready] at haccepts
                · simp [accepts, acceptsConfig, hnode, node, row, hsem, hactor]
                    at haccepts
    | sample dist =>
        cases authority with
        | player actor =>
            cases payload <;>
              simp [accepts, acceptsConfig, hnode, node, row, hsem] at haccepts
        | internal =>
            cases payload with
            | value supplied =>
                simp [accepts, acceptsConfig, hnode, node, row, hsem]
                  at haccepts
            | none =>
                cases henv :
                    ReadEnv.ofStoreExec? state.1.store dist.reads with
                | none =>
                    simp [accepts, acceptsConfig, hnode, node, row, hsem, henv]
                      at haccepts
                | some env =>
                    have hready : Ready program.graph state.1 node := by
                      simpa [accepts, acceptsConfig, hnode, node, row, hsem,
                        henv]
                        using haccepts
                    have envOk :=
                      ReadEnv.ofStore?_eq_some_of_ofStoreExec?_eq_some henv
                    exact
                      ⟨.internal
                        { node := node }
                        (.sample row dist hrowGet hsem hready env envOk),
                        rfl⟩
    | reveal source =>
        cases authority with
        | player actor =>
            cases payload <;>
              simp [accepts, acceptsConfig, hnode, node, row, hsem] at haccepts
        | internal =>
            cases payload with
            | value supplied =>
                simp [accepts, acceptsConfig, hnode, node, row, hsem]
                  at haccepts
            | none =>
                cases hvalue : Store.getAs state.1.store source row.ty with
                | none =>
                    simp [accepts, acceptsConfig, hnode, node, row, hsem,
                      hvalue]
                      at haccepts
                | some value =>
                    have hready : Ready program.graph state.1 node := by
                      simpa [accepts, acceptsConfig, hnode, node, row, hsem,
                        hvalue]
                        using haccepts
                    exact
                      ⟨.internal
                        { node := node }
                        (.reveal row source hrowGet hsem hready value hvalue),
                        rfl⟩
  · simp [accepts, acceptsConfig, hnode] at haccepts

/-- Executable validation accepts exactly the logical requests represented by
currently valid machine commands. -/
theorem accepts_eq_true_iff
    (state : program.State) (request : Request Player L) :
    accepts state request = true ↔ Represents state request := by
  constructor
  · exact represents_of_accepts_eq_true
  · rintro ⟨command, rfl⟩
    exact accepts_encode command

/-- The executable Boolean and the classical reference decoder have exactly
the same acceptance boundary. -/
theorem accepts_iff_decode_isSome
    (state : program.State) (request : Request Player L) :
    accepts state request = true ↔ (decode state request).isSome := by
  rw [accepts_eq_true_iff, decode_isSome_iff]

end Request

end Vegas.Machine.Contract
