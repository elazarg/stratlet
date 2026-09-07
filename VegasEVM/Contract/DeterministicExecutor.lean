/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasEVM.Contract.Calldata
import VegasEVM.Contract.InternalCalldata

/-!
# Deterministic non-chance execution

Player commitments and graph reveals are deterministic once calldata and
storage are fixed.  This module exposes their direct executor rather than
wrapping point laws in `FinDist`.  Sample requests are rejected here and are
handled exclusively by `OracleProtocol`.
-/

noncomputable section

namespace Vegas.Machine.Contract

open EventGraph

variable {Player Address : Type}
variable [DecidableEq Player] [DecidableEq Address]
variable {L : IExpr} {program : Program Player L}

namespace Request

/-- Execute only deterministic logical rows.  Source chance is deliberately
absent from this surface. -/
def executeDeterministicConfig? (cfg : Config program.graph) :
    Request Player L → Option (Config program.graph)
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
                              some <| cfg.completeNode node
                                { ty := guard.ty, value := value }
                            else
                              none
                          else
                            none
                else
                  none
            | _, _ => none
        | .sample _ => none
        | .reveal source =>
            match authority, payload with
            | .internal, .none =>
                match Store.getAs cfg.store source row.ty with
                | none => none
                | some value =>
                    if Ready program.graph cfg node then
                      some <| cfg.completeNode node
                        { ty := row.ty, value := value }
                    else
                      none
            | _, _ => none
      else
        none

/-- A valid commit envelope executes to its unique raw successor. -/
theorem executeDeterministicConfig?_encode_commit
    (state : program.State) (who : Player)
    (action : CommitAction program.graph who)
    (step : CommitStep program.graph state.1 who action) :
    executeDeterministicConfig? state.1
        (Request.encode (.commit who action step)) =
      some (state.1.completeNode action.node
        { ty := step.guard.ty, value := step.value }) := by
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
  simp [executeDeterministicConfig?, Request.encode, action.node.isLt, hsem,
    step.value_ok, hexec, step.ready, hguard]

/-- A valid reveal envelope executes to its unique raw successor. -/
theorem executeDeterministicConfig?_encode_reveal
    (state : program.State) (event : InternalEvent program.graph)
    (row : EventNode Player L) (source : Nat)
    (rowGet : program.graph.nodes[event.node]? = some row)
    (semEq : row.sem = .reveal source)
    (ready : Ready program.graph state.1 event.node)
    (value : L.Val row.ty)
    (valueOk : Store.getAs state.1.store source row.ty = some value) :
    executeDeterministicConfig? state.1
        (Request.encode
          (.internal event
            (.reveal row source rowGet semEq ready value valueOk))) =
      some (state.1.completeNode event.node
        { ty := row.ty, value := value }) := by
  have hrow : program.graph.nodeRow event.node = row := by
    have hget :
        program.graph.nodes[(event.node : Nat)]? = some row := rowGet
    rw [program.graph.nodes_get?_nodeRow event.node] at hget
    exact Option.some.inj hget
  subst row
  simp [executeDeterministicConfig?, Request.encode, event.node.isLt, semEq,
    valueOk, ready]

/-- Execute deterministic logical rows against canonical raw storage. -/
def executeDeterministicStore? (codec : StorageCodec program)
    (store : RawStore codec) (request : Request Player L) :
    Option (RawStore codec) :=
  match RawStore.decodeSnapshot (program := program) codec store with
  | none => none
  | some snapshot =>
      (executeDeterministicConfig? snapshot.toConfig request).map fun next =>
        RawStore.encodeSnapshot codec (StateSnapshot.ofConfig next)

/-- Stored execution of a valid commitment is its unique canonical encoded
successor. -/
theorem executeDeterministicStore?_encodeState_commit
    (codec : StorageCodec program) (state : program.State) (who : Player)
    (action : CommitAction program.graph who)
    (step : CommitStep program.graph state.1 who action) :
    executeDeterministicStore? codec (RawStore.encodeState codec state)
        (Request.encode (.commit who action step)) =
      some (RawStore.encodeSnapshot codec
        (StateSnapshot.ofConfig
          (state.1.completeNode action.node
            { ty := step.guard.ty, value := step.value }))) := by
  have hcanonical :=
    StateSnapshot.canonical_reachable program.graphWF state.2
  unfold executeDeterministicStore?
  rw [RawStore.decodeSnapshot_encodeState]
  change
    (executeDeterministicConfig?
      (StateSnapshot.ofConfig state.1).toConfig
      (Request.encode (.commit who action step))).map _ = _
  rw [hcanonical]
  rw [executeDeterministicConfig?_encode_commit]
  rfl

/-- Stored execution of a valid reveal is its unique canonical encoded
successor. -/
theorem executeDeterministicStore?_encodeState_reveal
    (codec : StorageCodec program) (state : program.State)
    (event : InternalEvent program.graph)
    (row : EventNode Player L) (source : Nat)
    (rowGet : program.graph.nodes[event.node]? = some row)
    (semEq : row.sem = .reveal source)
    (ready : Ready program.graph state.1 event.node)
    (value : L.Val row.ty)
    (valueOk : Store.getAs state.1.store source row.ty = some value) :
    executeDeterministicStore? codec (RawStore.encodeState codec state)
        (Request.encode
          (.internal event
            (.reveal row source rowGet semEq ready value valueOk))) =
      some (RawStore.encodeSnapshot codec
        (StateSnapshot.ofConfig
          (state.1.completeNode event.node
            { ty := row.ty, value := value }))) := by
  have hcanonical :=
    StateSnapshot.canonical_reachable program.graphWF state.2
  unfold executeDeterministicStore?
  rw [RawStore.decodeSnapshot_encodeState]
  change
    (executeDeterministicConfig?
      (StateSnapshot.ofConfig state.1).toConfig
      (Request.encode
        (.internal event
          (.reveal row source rowGet semEq ready value valueOk)))).map _ = _
  rw [hcanonical]
  rw [executeDeterministicConfig?_encode_reveal]
  rfl

end Request

namespace PlayerCalldata

/-- Deterministically decode, authenticate, and execute a player commitment. -/
def executeDeterministicStore?
    (registry : PlayerRegistry Player Address)
    (codec : StorageCodec program) (store : RawStore codec)
    (calldata : PlayerCalldata Player Address codec.Word) :
    Option (RawStore codec) :=
  match decode program codec calldata with
  | none => none
  | some call =>
      if PlayerCall.authenticated registry call then
        Request.executeDeterministicStore? codec store call.request
      else
        none

/-- A valid authenticated commitment reaches its unique deterministic stored
successor. -/
theorem executeDeterministicStore?_encodeCommit
    (registry : PlayerRegistry Player Address)
    (codec : StorageCodec program) (state : program.State) (who : Player)
    (action : CommitAction program.graph who)
    (step : CommitStep program.graph state.1 who action) :
    executeDeterministicStore? registry codec
        (RawStore.encodeState codec state)
        (encodeCommit registry codec action step) =
      some (RawStore.encodeSnapshot codec
        (StateSnapshot.ofConfig
          (state.1.completeNode action.node
            { ty := step.guard.ty, value := step.value }))) := by
  have hvalue :=
    TypedValue.eq_mk_of_as?_eq_some
      action.value step.guard.ty step.value step.value_ok
  let call : PlayerCall Player Address L :=
    { caller := registry.address who
      player := who
      node := action.node
      value := { ty := step.guard.ty, value := step.value } }
  have hrequest :
      call.request = Request.encode (.commit who action step) := by
    simp [call, PlayerCall.request, Request.encode, ← hvalue]
  unfold executeDeterministicStore?
  rw [show decode program codec (encodeCommit registry codec action step) =
      some call from decode_encodeCommit registry codec action step]
  dsimp only
  rw [if_pos (by simp [call, PlayerCall.authenticated])]
  rw [hrequest]
  exact Request.executeDeterministicStore?_encodeState_commit
    codec state who action step

end PlayerCalldata

namespace InternalCalldata

/-- Deterministically execute an authorized reveal.  Sample rows decode but
are rejected by the deterministic executor and must use `OracleProtocol`. -/
def executeDeterministicStore? (policy : TriggerPolicy Address)
    (codec : StorageCodec program) (store : RawStore codec)
    (calldata : InternalCalldata Address) : Option (RawStore codec) :=
  if policy.allows calldata.caller calldata.node then
    match decode (Player := Player) program calldata with
    | none => none
    | some request => Request.executeDeterministicStore? codec store request
  else
    none

omit [DecidableEq Address] in
/-- A valid authorized reveal reaches its unique deterministic stored
successor. -/
theorem executeDeterministicStore?_encodeReveal
    (policy : TriggerPolicy Address) (codec : StorageCodec program)
    (caller : Address) (state : program.State)
    (event : InternalEvent program.graph)
    (row : EventNode Player L) (source : Nat)
    (rowGet : program.graph.nodes[event.node]? = some row)
    (semEq : row.sem = .reveal source)
    (ready : Ready program.graph state.1 event.node)
    (value : L.Val row.ty)
    (valueOk : Store.getAs state.1.store source row.ty = some value)
    (authorized : policy.allows caller event.node = true) :
    executeDeterministicStore? (program := program) policy codec
        (RawStore.encodeState codec state) (encode caller event) =
      some (RawStore.encodeSnapshot codec
        (StateSnapshot.ofConfig
          (state.1.completeNode event.node
            { ty := row.ty, value := value }))) := by
  let step : InternalStep program.graph state.1 event :=
    .reveal row source rowGet semEq ready value valueOk
  unfold executeDeterministicStore?
  change
    (if policy.allows caller event.node then
      match decode (Player := Player) program (encode caller event) with
      | none => none
      | some request =>
          Request.executeDeterministicStore? codec
            (RawStore.encodeState codec state) request
    else none) = _
  rw [if_pos authorized]
  rw [decode_encode caller event step]
  exact Request.executeDeterministicStore?_encodeState_reveal codec state event
    row source rowGet semEq ready value valueOk

end InternalCalldata

end Vegas.Machine.Contract
