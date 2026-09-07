/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasEVM.Contract.StoredExecutor

/-!
# Internal-action calldata

An internal trigger carries a physical caller and one graph node. Decoding
accepts only sample or reveal rows and erases the trigger to the existing
logical internal request. A separate policy says which target callers may
submit such triggers.

This layer executes exactly one primitive semantic machine step. It does not
select a scheduler, close all available internal work, implement sample
entropy, or prove that caller-controlled transaction ordering preserves game
information. Those are separate lowering and strategic-proof obligations.
-/

noncomputable section

namespace Vegas.Machine.Contract

open EventGraph

variable {Player Address : Type}
variable [DecidableEq Player]
variable {L : IExpr} {program : Program Player L}

/-- Target-level authorization for submitting internal-action triggers.
Authorization may vary by graph node, so sample nodes can use a designated
oracle while reveal nodes remain permissionless. The policy does not choose or
execute an event. -/
structure TriggerPolicy (Address : Type) where
  allows : Address → Nat → Bool

namespace TriggerPolicy

/-- Every caller may submit an internal trigger. -/
def permissionless : TriggerPolicy Address where
  allows _ _ := true

end TriggerPolicy

/-- Caller-bearing calldata for one internal graph node. -/
structure InternalCalldata (Address : Type) where
  caller : Address
  node : Nat

namespace InternalCalldata

/-- Decode a graph-directed internal trigger to the logical request boundary.
Player commit rows cannot be reached through this entry point. -/
def decode (program : Program Player L)
    (calldata : InternalCalldata Address) : Option (Request Player L) :=
  if hnode : calldata.node < program.graph.nodeCount then
    let node : Fin program.graph.nodeCount := ⟨calldata.node, hnode⟩
    match (program.graph.nodeRow node).sem with
    | .commit _ _ => none
    | .sample _ | .reveal _ =>
        some
          { node := calldata.node
            authority := .internal
            payload := .none }
  else
    none

/-- Encode one internal graph event for submission by a target caller. -/
def encode (caller : Address) (event : InternalEvent program.graph) :
    InternalCalldata Address where
  caller := caller
  node := event.node

/-- A valid semantic internal event round-trips through graph-directed
calldata decoding to exactly its logical request. -/
@[simp] theorem decode_encode
    (caller : Address) {state : program.State}
    (event : InternalEvent program.graph)
    (step : InternalStep program.graph state.1 event) :
    decode (Player := Player) program (encode caller event) =
      some (Request.encode (.internal event step)) := by
  cases step with
  | sample row dist row_get sem_eq ready env env_ok =>
      have hrow : program.graph.nodeRow event.node = row := by
        have hget :
            program.graph.nodes[(event.node : Nat)]? = some row := row_get
        rw [program.graph.nodes_get?_nodeRow event.node] at hget
        exact Option.some.inj hget
      have hsem :
          (program.graph.nodeRow event.node).sem = .sample dist := by
        rw [hrow]
        exact sem_eq
      simp [decode, encode, event.node.isLt, hsem, Request.encode]
  | reveal row source row_get sem_eq ready value value_ok =>
      have hrow : program.graph.nodeRow event.node = row := by
        have hget :
            program.graph.nodes[(event.node : Nat)]? = some row := row_get
        rw [program.graph.nodes_get?_nodeRow event.node] at hget
        exact Option.some.inj hget
      have hsem :
          (program.graph.nodeRow event.node).sem = .reveal source := by
        rw [hrow]
        exact sem_eq
      simp [decode, encode, event.node.isLt, hsem, Request.encode]

/-- Authenticate and validate one internal trigger against canonical raw
storage. -/
def acceptsStore (policy : TriggerPolicy Address)
    (codec : StorageCodec program) (store : RawStore codec)
    (calldata : InternalCalldata Address) : Bool :=
  policy.allows calldata.caller calldata.node &&
    match decode (Player := Player) program calldata with
    | none => false
    | some request =>
        Request.acceptsStore (program := program) codec store request

/-- An authorized encoding of a valid semantic internal event is accepted on
the encoded reachable state. -/
theorem acceptsStore_encodeState_encode
    (policy : TriggerPolicy Address) (codec : StorageCodec program)
    (caller : Address) {state : program.State}
    (event : InternalEvent program.graph)
    (step : InternalStep program.graph state.1 event)
    (hauthorized : policy.allows caller event.node = true) :
    acceptsStore (program := program) policy codec
        (RawStore.encodeState codec state) (encode caller event) = true := by
  unfold acceptsStore
  change (policy.allows caller event.node &&
      (match decode (Player := Player) program (encode caller event) with
       | none => false
       | some request =>
          Request.acceptsStore (program := program) codec
            (RawStore.encodeState codec state) request)) = true
  rw [hauthorized]
  simp only [Bool.true_and]
  rw [decode_encode caller event step]
  simp only
  rw [Request.acceptsStore_encodeState]
  exact Request.accepts_encode (.internal event step)

/-- Decode, authorize, and semantically execute one internal trigger against
canonical raw storage. -/
def executeStore? (policy : TriggerPolicy Address)
    (codec : StorageCodec program) (store : RawStore codec)
    (calldata : InternalCalldata Address) :
    Option (GameTheory.Math.Probability.FinDist (RawStore codec)) :=
  if policy.allows calldata.caller calldata.node then
    match decode (Player := Player) program calldata with
    | none => none
    | some request =>
        Request.executeStore? (program := program) codec store request
  else
    none

/-- Internal-trigger execution succeeds exactly when validation accepts. -/
theorem executeStore?_isSome
    (policy : TriggerPolicy Address) (codec : StorageCodec program)
    (store : RawStore codec) (calldata : InternalCalldata Address) :
    (executeStore? (program := program) policy codec store calldata).isSome =
      acceptsStore (program := program) policy codec store calldata := by
  unfold executeStore? acceptsStore
  by_cases hauthorized : policy.allows calldata.caller calldata.node
  · simp only [hauthorized, ↓reduceIte, Bool.true_and]
    cases decode (Player := Player) program calldata with
    | none => rfl
    | some request => exact Request.executeStore?_isSome codec store request
  · simp [hauthorized]

/-- End-to-end internal-trigger law: for an authorized caller and a valid
semantic internal event, decoding, authorization, stored execution, and
successor encoding produce exactly the machine step law transported through
canonical raw storage. -/
theorem executeStore?_encodeState_encode
    (policy : TriggerPolicy Address) (codec : StorageCodec program)
    (caller : Address) {state : program.State}
    (event : InternalEvent program.graph)
    (step : InternalStep program.graph state.1 event)
    (hauthorized : policy.allows caller event.node = true) :
    executeStore? (program := program) policy codec
        (RawStore.encodeState codec state) (encode caller event) =
      some ((program.step state (.internal event step)).map
        (RawStore.encodeState codec)) := by
  unfold executeStore?
  change
    (if policy.allows caller event.node then
      match decode (Player := Player) program (encode caller event) with
      | none => none
      | some request =>
          Request.executeStore? (program := program) codec
            (RawStore.encodeState codec state) request
    else none) = _
  rw [if_pos hauthorized]
  rw [decode_encode caller event step]
  exact Request.executeStore?_encodeState_encode
    codec state (.internal event step)

/-- Every internal trigger accepted against encoded reachable storage executes
as some valid semantic machine command. Per-node authorization and graph
decoding therefore cannot produce a transition outside the canonical reachable
state image. -/
theorem executeStore?_encodeState_of_accepts
    (policy : TriggerPolicy Address) (codec : StorageCodec program)
    (state : program.State) (calldata : InternalCalldata Address)
    (haccept :
      acceptsStore (program := program) policy codec
        (RawStore.encodeState codec state) calldata = true) :
    ∃ command : program.Command state,
      executeStore? (program := program) policy codec
          (RawStore.encodeState codec state) calldata =
        some ((program.step state command).map
          (RawStore.encodeState codec)) := by
  unfold acceptsStore at haccept
  have hparts :
      policy.allows calldata.caller calldata.node = true ∧
        (match decode (Player := Player) program calldata with
         | none => false
         | some request =>
            Request.acceptsStore (program := program) codec
              (RawStore.encodeState codec state) request) = true := by
    simpa only [Bool.and_eq_true] using haccept
  have hauthorized := hparts.1
  have hdecoded := hparts.2
  cases hdecode : decode (Player := Player) program calldata with
  | none => simp [hdecode] at hdecoded
  | some request =>
      simp only [hdecode] at hdecoded
      rcases Request.executeStore?_encodeState_of_accepts
          codec state request hdecoded with
        ⟨command, _hencode, hexecute⟩
      refine ⟨command, ?_⟩
      unfold executeStore?
      rw [if_pos hauthorized, hdecode]
      exact hexecute

end InternalCalldata

end Vegas.Machine.Contract
