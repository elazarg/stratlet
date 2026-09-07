/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasEVM.Contract.Authentication
import VegasEVM.Contract.StoredExecutor

/-!
# Player commit calldata

A player call on a word-oriented target carries a physical caller, claimed
semantic player, node id, and one target word.  Decoding inspects the graph row,
requires a commit owned by the claimed player, and decodes the word at the
guard's language type. Caller authentication remains the adjacent certified
registry check.

This is a logical word-level ABI, not byte serialization, gas accounting, or a
specific chain calling convention.
-/

namespace Vegas.Machine.Contract

open EventGraph

variable {Player Address : Type}
variable [DecidableEq Player] [DecidableEq Address]
variable {L : IExpr} {program : Program Player L}

namespace StorageCodec

/-- Every commit guard type used by the program is supported because the
corresponding node output type is supported and graph well-formedness equates
the two types. -/
theorem commitSupported (codec : StorageCodec program)
    (node : Fin program.graph.nodeCount) {who : Player}
    {guard : EventGuard L}
    (hsem : (program.graph.nodeRow node).sem = .commit who guard) :
    codec.Supported guard.ty := by
  have hwf :=
    program.graphWF (node : Nat) (program.graph.nodeRow node)
      (program.graph.nodes_get?_nodeRow node)
  unfold Graph.nodeWFAt at hwf
  rw [hsem] at hwf
  exact hwf.2.1 ▸ codec.node_supported node

/-- The guard type of a proof-carrying commit step is supported by the
program-indexed codec. -/
theorem commitStepSupported (codec : StorageCodec program)
    {state : program.State} {who : Player}
    (action : CommitAction program.graph who)
    (step : CommitStep program.graph state.1 who action) :
    codec.Supported step.guard.ty := by
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
  exact codec.commitSupported action.node hsem

end StorageCodec

/-- Word-level player commit calldata. -/
structure PlayerCalldata (Player Address Word : Type) where
  caller : Address
  player : Player
  node : Nat
  value : Word

namespace PlayerCalldata

/-- Decode word-level calldata to the typed authenticated-call boundary. -/
def decode (program : Program Player L) (codec : StorageCodec program)
    (calldata : PlayerCalldata Player Address codec.Word) :
    Option (PlayerCall Player Address L) :=
  if hnode : calldata.node < program.graph.nodeCount then
    let node : Fin program.graph.nodeCount := ⟨calldata.node, hnode⟩
    match (program.graph.nodeRow node).sem with
    | .commit who guard =>
        if calldata.player = who then
          match codec.decodeValue guard.ty calldata.value with
          | none => none
          | some value =>
              some
                { caller := calldata.caller
                  player := calldata.player
                  node := calldata.node
                  value := { ty := guard.ty, value := value } }
        else
          none
    | .sample _ | .reveal _ => none
  else
    none

/-- Encode one valid semantic commit as caller-bearing target words. -/
def encodeCommit (registry : PlayerRegistry Player Address)
    (codec : StorageCodec program) {state : program.State} {who : Player}
    (action : CommitAction program.graph who)
    (step : CommitStep program.graph state.1 who action) :
    PlayerCalldata Player Address codec.Word where
  caller := registry.address who
  player := who
  node := action.node
  value := codec.encodeValue step.guard.ty step.value

omit [DecidableEq Address] in
/-- Valid semantic commits round-trip through word-level calldata decoding. -/
@[simp] theorem decode_encodeCommit
    (registry : PlayerRegistry Player Address)
    (codec : StorageCodec program) {state : program.State} {who : Player}
    (action : CommitAction program.graph who)
    (step : CommitStep program.graph state.1 who action) :
    decode program codec (encodeCommit registry codec action step) =
      some
        { caller := registry.address who
          player := who
          node := action.node
          value := { ty := step.guard.ty, value := step.value } } := by
  have hrow : program.graph.nodeRow action.node = step.row := by
    have hget :
        program.graph.nodes[(action.node : Nat)]? = some step.row :=
      step.row_get
    rw [program.graph.nodes_get?_nodeRow action.node] at hget
    exact Option.some.inj hget
  have hsem :
      (program.graph.nodeRow action.node).sem = .commit who step.guard := by
    rw [hrow]
    exact step.sem_eq
  cases hcase : (program.graph.nodeRow action.node).sem with
  | sample dist =>
      rw [hcase] at hsem
      cases hsem
  | reveal source =>
      rw [hcase] at hsem
      cases hsem
  | commit actor guard =>
      have heq :
          NodeSem.commit actor guard = NodeSem.commit who step.guard :=
        hcase.symm.trans hsem
      cases heq
      unfold decode encodeCommit
      simp [action.node.isLt, hcase,
        codec.decode_encode_value _ (codec.commitStepSupported action step)]

omit [DecidableEq Address] in
/-- The decoded call of a valid commit erases to exactly the original logical
request. -/
theorem request_of_decode_encodeCommit
    (registry : PlayerRegistry Player Address)
    (codec : StorageCodec program) {state : program.State} {who : Player}
    (action : CommitAction program.graph who)
    (step : CommitStep program.graph state.1 who action) :
    ∃ call : PlayerCall Player Address L,
      decode program codec (encodeCommit registry codec action step) =
        some call ∧
      call.request = Request.encode (.commit who action step) := by
  let call : PlayerCall Player Address L :=
    { caller := registry.address who
      player := who
      node := action.node
      value := { ty := step.guard.ty, value := step.value } }
  refine ⟨call, decode_encodeCommit registry codec action step, ?_⟩
  have hvalue :=
    TypedValue.eq_mk_of_as?_eq_some
      action.value step.guard.ty step.value step.value_ok
  simp [call, PlayerCall.request, Request.encode, ← hvalue]

/-- Decode, authenticate, and validate word-level calldata against canonical
raw storage. -/
def acceptsStore (registry : PlayerRegistry Player Address)
    (codec : StorageCodec program) (store : RawStore codec)
    (calldata : PlayerCalldata Player Address codec.Word) : Bool :=
  match decode program codec calldata with
  | none => false
  | some call =>
      PlayerCall.acceptsStore (program := program) registry codec store call

/-- Encoding a valid semantic commit produces accepted word-level calldata on
the encoded reachable state. -/
theorem acceptsStore_encodeState_encodeCommit
    (registry : PlayerRegistry Player Address)
    (codec : StorageCodec program) {state : program.State} {who : Player}
    (action : CommitAction program.graph who)
    (step : CommitStep program.graph state.1 who action) :
    acceptsStore (program := program) registry codec
        (RawStore.encodeState codec state)
        (encodeCommit registry codec action step) = true := by
  have hvalue :=
    TypedValue.eq_mk_of_as?_eq_some
      action.value step.guard.ty step.value step.value_ok
  unfold acceptsStore
  rw [decode_encodeCommit]
  dsimp only
  unfold PlayerCall.acceptsStore
  rw [Request.acceptsStore_encodeState]
  have hvalid :=
    Request.accepts_encode (AvailableEvent.commit who action step)
  simpa [PlayerCall.authenticated, PlayerCall.request, Request.encode,
    ← hvalue]
    using hvalid

/-- Decode, authenticate, and semantically execute word-level player calldata
against canonical raw storage. -/
noncomputable def executeStore?
    (registry : PlayerRegistry Player Address)
    (codec : StorageCodec program) (store : RawStore codec)
    (calldata : PlayerCalldata Player Address codec.Word) :
    Option (GameTheory.Math.Probability.FinDist (RawStore codec)) :=
  match decode program codec calldata with
  | none => none
  | some call =>
      if PlayerCall.authenticated registry call then
        Request.executeStore? (program := program) codec store call.request
      else
        none

/-- Word-level execution succeeds exactly when word-level validation accepts.
-/
theorem executeStore?_isSome
    (registry : PlayerRegistry Player Address)
    (codec : StorageCodec program) (store : RawStore codec)
    (calldata : PlayerCalldata Player Address codec.Word) :
    (executeStore? (program := program) registry codec store calldata).isSome =
      acceptsStore (program := program) registry codec store calldata := by
  unfold executeStore? acceptsStore
  cases hdecode : decode program codec calldata with
  | none => rfl
  | some call =>
      by_cases hauth : PlayerCall.authenticated registry call
      · simp [hauth, PlayerCall.acceptsStore, Request.executeStore?_isSome]
      · simp [hauth, PlayerCall.acceptsStore]

/-- End-to-end word-call law for a valid semantic commit: calldata decoding,
authentication, stored execution, and successor encoding produce exactly the
machine step law transported through canonical raw storage. -/
theorem executeStore?_encodeState_encodeCommit
    (registry : PlayerRegistry Player Address)
    (codec : StorageCodec program) {state : program.State} {who : Player}
    (action : CommitAction program.graph who)
    (step : CommitStep program.graph state.1 who action) :
    executeStore? (program := program) registry codec
        (RawStore.encodeState codec state)
        (encodeCommit registry codec action step) =
      some ((program.step state (.commit who action step)).map
        (RawStore.encodeState codec)) := by
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
  unfold executeStore?
  rw [show decode program codec (encodeCommit registry codec action step) =
      some call from decode_encodeCommit registry codec action step]
  dsimp only
  rw [if_pos (by simp [call, PlayerCall.authenticated])]
  rw [hrequest]
  exact Request.executeStore?_encodeState_encode
    codec state (.commit who action step)

/-- Every player wire call accepted against encoded reachable storage executes
as some valid semantic machine command. Thus accepted hostile player input
cannot leave the canonical image of reachable states. -/
theorem executeStore?_encodeState_of_accepts
    (registry : PlayerRegistry Player Address)
    (codec : StorageCodec program) (state : program.State)
    (calldata : PlayerCalldata Player Address codec.Word)
    (haccept :
      acceptsStore (program := program) registry codec
        (RawStore.encodeState codec state) calldata = true) :
    ∃ command : program.Command state,
      executeStore? (program := program) registry codec
          (RawStore.encodeState codec state) calldata =
        some ((program.step state command).map
          (RawStore.encodeState codec)) := by
  unfold acceptsStore at haccept
  cases hdecode : decode program codec calldata with
  | none => simp [hdecode] at haccept
  | some call =>
      simp only [hdecode] at haccept
      unfold PlayerCall.acceptsStore at haccept
      have hparts :
          PlayerCall.authenticated registry call = true ∧
            Request.acceptsStore (program := program) codec
              (RawStore.encodeState codec state) call.request = true := by
        simpa only [Bool.and_eq_true] using haccept
      have hauth := hparts.1
      have hrequest := hparts.2
      rcases Request.executeStore?_encodeState_of_accepts
          codec state call.request hrequest with
        ⟨command, _hencode, hexecute⟩
      refine ⟨command, ?_⟩
      unfold executeStore?
      rw [hdecode]
      simp only
      rw [if_pos hauth]
      exact hexecute

end PlayerCalldata

end Vegas.Machine.Contract
