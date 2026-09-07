/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasEVM.Contract.ClassicalEVMCalldata
import VegasEVM.Contract.State

/-!
# Total EVM storage for classical contract state

EVM storage is a total map whose missing keys read as zero, whereas the
earlier contract state uses a sparse map so an absent field is distinct from a
field containing the zero word. This pass resolves that mismatch explicitly:
every graph field receives a value word and a presence bit. Completion bits
remain canonical Booleans, and the asynchronous oracle phase receives a
pending bit and pending-node word.

The dense layout is collision-free and bounded. Encoding and decoding a
`ClassicalSnapshot` round-trip exactly through total 256-bit storage for every
program whose value and node codecs are lossless. This is the state format a
handler compiler may address with `SLOAD` and `SSTORE`.
-/

noncomputable section

namespace Vegas.Machine.Contract.EVM

open EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} {program : Program Player L}

/-- Logical cells in the complete deterministic classical EVM state. -/
inductive ClassicalStorageSlot (program : Program Player L) where
  | fieldValue (field : Fin program.graph.fieldCount)
  | fieldPresent (field : Fin program.graph.fieldCount)
  | completed (node : Fin program.graph.nodeCount)
  | pendingFlag
  | pendingNode

/-- Collision-free bounded layout for complete classical EVM state. -/
structure ClassicalStorageLayout (program : Program Player L) where
  slotCount : Nat
  address : ClassicalStorageSlot program → Nat
  address_lt : ∀ slot, address slot < slotCount
  injective : Function.Injective address

namespace ClassicalStorageLayout

/-- Dense layout: values, presence bits, completion bits, then the two oracle
phase cells. -/
def canonicalAddress : ClassicalStorageSlot program → Nat
  | .fieldValue field => field
  | .fieldPresent field => program.graph.fieldCount + field
  | .completed node => 2 * program.graph.fieldCount + node
  | .pendingFlag =>
      2 * program.graph.fieldCount + program.graph.nodeCount
  | .pendingNode =>
      2 * program.graph.fieldCount + program.graph.nodeCount + 1

/-- Number of storage cells reserved by the dense classical layout. -/
def canonicalSlotCount (program : Program Player L) : Nat :=
  2 * program.graph.fieldCount + program.graph.nodeCount + 2

theorem canonicalAddress_lt (slot : ClassicalStorageSlot program) :
    canonicalAddress slot < canonicalSlotCount program := by
  cases slot with
  | fieldValue field =>
      simp [canonicalAddress, canonicalSlotCount]
      omega
  | fieldPresent field =>
      simp [canonicalAddress, canonicalSlotCount]
      omega
  | completed node =>
      simp [canonicalAddress, canonicalSlotCount]
      omega
  | pendingFlag =>
      simp [canonicalAddress, canonicalSlotCount]
  | pendingNode =>
      simp [canonicalAddress, canonicalSlotCount]

theorem canonicalAddress_injective :
    Function.Injective
      (canonicalAddress (program := program)) := by
  intro left right heq
  cases left <;> cases right <;>
    simp only [canonicalAddress] at heq ⊢
  all_goals try { omega }
  all_goals congr 1; apply Fin.ext; omega

/-- Canonical classical EVM storage layout. -/
def canonical (program : Program Player L) :
    ClassicalStorageLayout program where
  slotCount := canonicalSlotCount program
  address := canonicalAddress
  address_lt := canonicalAddress_lt
  injective := canonicalAddress_injective

@[simp] theorem canonical_slotCount :
    (canonical program).slotCount =
      2 * program.graph.fieldCount + program.graph.nodeCount + 2 :=
  rfl

@[simp] theorem canonical_fieldValue
    (field : Fin program.graph.fieldCount) :
    (canonical program).address (.fieldValue field) = field :=
  rfl

@[simp] theorem canonical_fieldPresent
    (field : Fin program.graph.fieldCount) :
    (canonical program).address (.fieldPresent field) =
      program.graph.fieldCount + field :=
  rfl

@[simp] theorem canonical_completed
    (node : Fin program.graph.nodeCount) :
    (canonical program).address (.completed node) =
      2 * program.graph.fieldCount + node :=
  rfl

@[simp] theorem canonical_pendingFlag :
    (canonical program).address .pendingFlag =
      2 * program.graph.fieldCount + program.graph.nodeCount :=
  rfl

@[simp] theorem canonical_pendingNode :
    (canonical program).address .pendingNode =
      2 * program.graph.fieldCount + program.graph.nodeCount + 1 :=
  rfl

end ClassicalStorageLayout

/-- The complete classical layout fits the EVM's 256-bit storage-key space. -/
def ClassicalStorageFitsWord (program : Program Player L) : Prop :=
  (ClassicalStorageLayout.canonical program).slotCount ≤ 2 ^ 256

/-- Every certified classical storage address is represented exactly by a
256-bit storage key. -/
theorem classicalStorageAddress_lt_word
    (fits : ClassicalStorageFitsWord program)
    (slot : ClassicalStorageSlot program) :
    (ClassicalStorageLayout.canonical program).address slot < 2 ^ 256 :=
  ((ClassicalStorageLayout.canonical program).address_lt slot).trans_le fits

/-- Semantic snapshot represented by the total classical EVM layout. The
pending node is bounded at this layer because only graph sample nodes can be
pending in reachable protocol states. -/
structure ClassicalSnapshot (program : Program Player L) where
  graph : StateSnapshot program.graph
  pending : Option (Fin program.graph.nodeCount)

namespace ClassicalSnapshot

@[ext] theorem ext {left right : ClassicalSnapshot program}
    (hgraph : left.graph = right.graph)
    (hpending : left.pending = right.pending) : left = right := by
  cases left
  cases right
  simp_all

/-- Idle snapshot of one semantic graph configuration. -/
def idle (cfg : Config program.graph) : ClassicalSnapshot program where
  graph := StateSnapshot.ofConfig cfg
  pending := none

/-- Waiting snapshot of one semantic graph configuration. -/
def waiting (cfg : Config program.graph)
    (node : Fin program.graph.nodeCount) : ClassicalSnapshot program where
  graph := StateSnapshot.ofConfig cfg
  pending := some node

/-- Decode the earlier sparse classical protocol state and simultaneously
check the invariant that a pending node is in the graph. -/
def ofProtocolState? (codec : StorageCodec program)
    (state : OracleProtocol.State codec) : Option (ClassicalSnapshot program) :=
  match RawStore.decodeSnapshot codec state.store with
  | none => none
  | some graph =>
      match state.pending with
      | none => some { graph := graph, pending := none }
      | some node =>
          if hnode : node < program.graph.nodeCount then
            some { graph := graph, pending := some ⟨node, hnode⟩ }
          else
            none

@[simp] theorem ofProtocolState?_idleState
    (codec : StorageCodec program) (state : program.State) :
    ofProtocolState? codec (OracleProtocol.idleState codec state) =
      some (idle state.1) := by
  simp [ofProtocolState?, OracleProtocol.idleState, idle]

@[simp] theorem ofProtocolState?_waitingState
    (codec : StorageCodec program) (state : program.State)
    (event : InternalEvent program.graph) :
    ofProtocolState? codec (OracleProtocol.waitingState codec state event) =
      some (waiting state.1 event.node) := by
  simp [ofProtocolState?, OracleProtocol.waitingState, waiting,
    event.node.isLt]

end ClassicalSnapshot

/-- Concrete total EVM account storage. -/
abbrev TotalStorage := Nat → Word

/-- Read and validate a possibly absent typed field from total EVM storage. -/
def decodeClassicalField (codec : StorageCodec program)
    (words : WireCodec codec.Word Word) (storage : TotalStorage)
    (field : Fin program.graph.fieldCount) :
    Option (Option (L.Val (program.graph.fieldRow field).ty)) :=
  let layout := ClassicalStorageLayout.canonical program
  match decodeBool (storage (layout.address (.fieldPresent field))) with
  | none => none
  | some false => some none
  | some true =>
      match words.decode (storage (layout.address (.fieldValue field))) with
      | none => none
      | some raw =>
          (codec.decodeValue (program.graph.fieldRow field).ty raw).map some

/-- Read one canonical completion bit from total EVM storage. -/
def decodeClassicalCompleted (storage : TotalStorage)
    (node : Fin program.graph.nodeCount) : Option Bool :=
  decodeBool
    (storage
      ((ClassicalStorageLayout.canonical program).address (.completed node)))

/-- Read the bounded asynchronous-oracle marker. -/
def decodeClassicalPending
    (nodes : WireCodec (Fin program.graph.nodeCount) Word)
    (storage : TotalStorage) :
    Option (Option (Fin program.graph.nodeCount)) :=
  let layout := ClassicalStorageLayout.canonical program
  match decodeBool (storage (layout.address .pendingFlag)) with
  | none => none
  | some false => some none
  | some true => (nodes.decode (storage (layout.address .pendingNode))).map some

/-- Encode graph data, presence, completion, and oracle phase into total EVM
storage. Keys outside the certified layout receive zero. -/
def encodeClassicalSnapshot (codec : StorageCodec program)
    (words : WireCodec codec.Word Word)
    (nodes : WireCodec (Fin program.graph.nodeCount) Word)
    (snapshot : ClassicalSnapshot program) : TotalStorage :=
  fun key =>
    if hfieldValue : key < program.graph.fieldCount then
      let field : Fin program.graph.fieldCount := ⟨key, hfieldValue⟩
      match snapshot.graph.fieldValue? field with
      | none => 0
      | some value => words.encode
          (codec.encodeValue (program.graph.fieldRow field).ty value)
    else if hfieldPresent :
        key - program.graph.fieldCount < program.graph.fieldCount then
      let field : Fin program.graph.fieldCount :=
        ⟨key - program.graph.fieldCount, hfieldPresent⟩
      encodeBool (snapshot.graph.fieldValue? field).isSome
    else if hcompleted :
        key - 2 * program.graph.fieldCount < program.graph.nodeCount then
      let node : Fin program.graph.nodeCount :=
        ⟨key - 2 * program.graph.fieldCount, hcompleted⟩
      encodeBool (decide (node ∈ snapshot.graph.done))
    else if key =
        2 * program.graph.fieldCount + program.graph.nodeCount then
      encodeBool snapshot.pending.isSome
    else if key =
        2 * program.graph.fieldCount + program.graph.nodeCount + 1 then
      match snapshot.pending with
      | none => 0
      | some node => nodes.encode node
    else
      0

/-- Canonical snapshot storage has finite support inside the declared dense
layout. This is the exact support fact required by constructor generation. -/
theorem encodeClassicalSnapshot_eq_zero_of_ge_slotCount
    (codec : StorageCodec program) (words : WireCodec codec.Word Word)
    (nodes : WireCodec (Fin program.graph.nodeCount) Word)
    (snapshot : ClassicalSnapshot program) (key : Nat)
    (hkey : ClassicalStorageLayout.canonicalSlotCount program ≤ key) :
    encodeClassicalSnapshot codec words nodes snapshot key = 0 := by
  unfold ClassicalStorageLayout.canonicalSlotCount at hkey
  unfold encodeClassicalSnapshot
  split <;> try omega
  split <;> try omega
  split <;> try omega
  split <;> try omega
  split <;> try omega
  rfl

@[simp] theorem encodeClassicalSnapshot_fieldValue
    (codec : StorageCodec program) (words : WireCodec codec.Word Word)
    (nodes : WireCodec (Fin program.graph.nodeCount) Word)
    (snapshot : ClassicalSnapshot program)
    (field : Fin program.graph.fieldCount) :
    encodeClassicalSnapshot codec words nodes snapshot
        ((ClassicalStorageLayout.canonical program).address
          (.fieldValue field)) =
      match snapshot.graph.fieldValue? field with
      | none => 0
      | some value => words.encode
          (codec.encodeValue (program.graph.fieldRow field).ty value) := by
  simp [encodeClassicalSnapshot, ClassicalStorageLayout.canonical,
    ClassicalStorageLayout.canonicalAddress, field.isLt]

@[simp] theorem encodeClassicalSnapshot_fieldPresent
    (codec : StorageCodec program) (words : WireCodec codec.Word Word)
    (nodes : WireCodec (Fin program.graph.nodeCount) Word)
    (snapshot : ClassicalSnapshot program)
    (field : Fin program.graph.fieldCount) :
    encodeClassicalSnapshot codec words nodes snapshot
        ((ClassicalStorageLayout.canonical program).address
          (.fieldPresent field)) =
      encodeBool (snapshot.graph.fieldValue? field).isSome := by
  have hnotValue :
      ¬program.graph.fieldCount + (field : Nat) <
        program.graph.fieldCount := by omega
  have hpresent :
      program.graph.fieldCount + (field : Nat) -
          program.graph.fieldCount < program.graph.fieldCount := by
    rw [Nat.add_sub_cancel_left]
    exact field.isLt
  have hfieldIndex :
      (⟨program.graph.fieldCount + (field : Nat) -
          program.graph.fieldCount, hpresent⟩ :
        Fin program.graph.fieldCount) = field := by
    apply Fin.ext
    simp
  simp only [ClassicalStorageLayout.canonical_fieldPresent]
  unfold encodeClassicalSnapshot
  rw [dif_neg hnotValue, dif_pos hpresent]
  rw [hfieldIndex]

@[simp] theorem encodeClassicalSnapshot_completed
    (codec : StorageCodec program) (words : WireCodec codec.Word Word)
    (nodes : WireCodec (Fin program.graph.nodeCount) Word)
    (snapshot : ClassicalSnapshot program)
    (node : Fin program.graph.nodeCount) :
    encodeClassicalSnapshot codec words nodes snapshot
        ((ClassicalStorageLayout.canonical program).address
          (.completed node)) =
      encodeBool (decide (node ∈ snapshot.graph.done)) := by
  have hnotValue :
      ¬2 * program.graph.fieldCount + (node : Nat) <
        program.graph.fieldCount := by omega
  have hnotPresent :
      ¬(2 * program.graph.fieldCount + (node : Nat) -
          program.graph.fieldCount < program.graph.fieldCount) := by omega
  have hcompleted :
      2 * program.graph.fieldCount + (node : Nat) -
          2 * program.graph.fieldCount < program.graph.nodeCount := by
    rw [Nat.add_sub_cancel_left]
    exact node.isLt
  have hnodeIndex :
      (⟨2 * program.graph.fieldCount + (node : Nat) -
          2 * program.graph.fieldCount, hcompleted⟩ :
        Fin program.graph.nodeCount) = node := by
    apply Fin.ext
    simp
  simp only [ClassicalStorageLayout.canonical_completed]
  unfold encodeClassicalSnapshot
  rw [dif_neg hnotValue, dif_neg hnotPresent, dif_pos hcompleted]
  rw [hnodeIndex]

@[simp] theorem encodeClassicalSnapshot_pendingFlag
    (codec : StorageCodec program) (words : WireCodec codec.Word Word)
    (nodes : WireCodec (Fin program.graph.nodeCount) Word)
    (snapshot : ClassicalSnapshot program) :
    encodeClassicalSnapshot codec words nodes snapshot
        ((ClassicalStorageLayout.canonical program).address .pendingFlag) =
      encodeBool snapshot.pending.isSome := by
  have hnotValue :
      ¬2 * program.graph.fieldCount + program.graph.nodeCount <
        program.graph.fieldCount := by omega
  have hnotPresent :
      ¬(2 * program.graph.fieldCount + program.graph.nodeCount -
          program.graph.fieldCount < program.graph.fieldCount) := by omega
  have hnotCompleted :
      ¬(2 * program.graph.fieldCount + program.graph.nodeCount -
          2 * program.graph.fieldCount < program.graph.nodeCount) := by omega
  simp only [ClassicalStorageLayout.canonical_pendingFlag]
  unfold encodeClassicalSnapshot
  rw [dif_neg hnotValue, dif_neg hnotPresent, dif_neg hnotCompleted,
    if_pos rfl]

@[simp] theorem encodeClassicalSnapshot_pendingNode
    (codec : StorageCodec program) (words : WireCodec codec.Word Word)
    (nodes : WireCodec (Fin program.graph.nodeCount) Word)
    (snapshot : ClassicalSnapshot program) :
    encodeClassicalSnapshot codec words nodes snapshot
        ((ClassicalStorageLayout.canonical program).address .pendingNode) =
      match snapshot.pending with
      | none => 0
      | some node => nodes.encode node := by
  have hnotValue :
      ¬2 * program.graph.fieldCount + program.graph.nodeCount + 1 <
        program.graph.fieldCount := by omega
  have hnotPresent :
      ¬(2 * program.graph.fieldCount + program.graph.nodeCount + 1 -
          program.graph.fieldCount < program.graph.fieldCount) := by omega
  have hnotCompleted :
      ¬(2 * program.graph.fieldCount + program.graph.nodeCount + 1 -
          2 * program.graph.fieldCount < program.graph.nodeCount) := by omega
  have hnotFlag :
      2 * program.graph.fieldCount + program.graph.nodeCount + 1 ≠
        2 * program.graph.fieldCount + program.graph.nodeCount := by omega
  simp only [ClassicalStorageLayout.canonical_pendingNode]
  unfold encodeClassicalSnapshot
  rw [dif_neg hnotValue, dif_neg hnotPresent, dif_neg hnotCompleted,
    if_neg hnotFlag, if_pos rfl]

/-- Setting the two pending cells is exactly the canonical encoding of the
same graph snapshot waiting for the supplied node. -/
theorem encodeClassicalSnapshot_setPending
    (codec : StorageCodec program) (words : WireCodec codec.Word Word)
    (nodes : WireCodec (Fin program.graph.nodeCount) Word)
    (snapshot : ClassicalSnapshot program)
    (node : Fin program.graph.nodeCount) :
    Function.update
        (Function.update (encodeClassicalSnapshot codec words nodes snapshot)
          ((ClassicalStorageLayout.canonical program).address .pendingFlag) 1)
        ((ClassicalStorageLayout.canonical program).address .pendingNode)
        (nodes.encode node) =
      encodeClassicalSnapshot codec words nodes
        { snapshot with pending := some node } := by
  funext key
  let flag :=
    (ClassicalStorageLayout.canonical program).address
      (ClassicalStorageSlot.pendingFlag : ClassicalStorageSlot program)
  let pendingNode :=
    (ClassicalStorageLayout.canonical program).address
      (ClassicalStorageSlot.pendingNode : ClassicalStorageSlot program)
  change
    Function.update
        (Function.update (encodeClassicalSnapshot codec words nodes snapshot)
          flag 1) pendingNode (nodes.encode node) key =
      encodeClassicalSnapshot codec words nodes
        { snapshot with pending := some node } key
  by_cases hkeyNode : key = pendingNode
  · subst key
    simp only [Function.update_self]
    change nodes.encode node =
      encodeClassicalSnapshot codec words nodes
        { graph := snapshot.graph, pending := some node }
        ((ClassicalStorageLayout.canonical program).address .pendingNode)
    rw [encodeClassicalSnapshot_pendingNode]
  by_cases hkeyFlag : key = flag
  · subst key
    have hne : flag ≠ pendingNode := by
      simp [flag, pendingNode]
    simp only [Function.update_of_ne hne, Function.update_self]
    change (1 : Word) =
      encodeClassicalSnapshot codec words nodes
        { graph := snapshot.graph, pending := some node }
        ((ClassicalStorageLayout.canonical program).address .pendingFlag)
    rw [encodeClassicalSnapshot_pendingFlag]
    rfl
  simp only [Function.update_of_ne hkeyNode,
    Function.update_of_ne hkeyFlag]
  unfold encodeClassicalSnapshot
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  split
  · rename_i heq
    exact False.elim (hkeyFlag (by simpa [flag] using heq))
  · split
    · rename_i heq
      exact False.elim (hkeyNode (by simpa [pendingNode] using heq))
    · rfl

/-- Clearing both pending cells is exactly the canonical idle encoding. -/
theorem encodeClassicalSnapshot_clearPending
    (codec : StorageCodec program) (words : WireCodec codec.Word Word)
    (nodes : WireCodec (Fin program.graph.nodeCount) Word)
    (snapshot : ClassicalSnapshot program) :
    Function.update
        (Function.update (encodeClassicalSnapshot codec words nodes snapshot)
          ((ClassicalStorageLayout.canonical program).address .pendingFlag) 0)
        ((ClassicalStorageLayout.canonical program).address .pendingNode) 0 =
      encodeClassicalSnapshot codec words nodes
        { snapshot with pending := none } := by
  funext key
  let flag :=
    (ClassicalStorageLayout.canonical program).address
      (ClassicalStorageSlot.pendingFlag : ClassicalStorageSlot program)
  let pendingNode :=
    (ClassicalStorageLayout.canonical program).address
      (ClassicalStorageSlot.pendingNode : ClassicalStorageSlot program)
  change
    Function.update
        (Function.update (encodeClassicalSnapshot codec words nodes snapshot)
          flag 0) pendingNode 0 key =
      encodeClassicalSnapshot codec words nodes
        { snapshot with pending := none } key
  by_cases hkeyNode : key = pendingNode
  · subst key
    simp only [Function.update_self]
    change (0 : Word) =
      encodeClassicalSnapshot codec words nodes
        { graph := snapshot.graph, pending := none }
        ((ClassicalStorageLayout.canonical program).address .pendingNode)
    rw [encodeClassicalSnapshot_pendingNode]
  by_cases hkeyFlag : key = flag
  · subst key
    have hne : flag ≠ pendingNode := by
      simp [flag, pendingNode]
    simp only [Function.update_of_ne hne, Function.update_self]
    change (0 : Word) =
      encodeClassicalSnapshot codec words nodes
        { graph := snapshot.graph, pending := none }
        ((ClassicalStorageLayout.canonical program).address .pendingFlag)
    rw [encodeClassicalSnapshot_pendingFlag]
    rfl
  simp only [Function.update_of_ne hkeyNode,
    Function.update_of_ne hkeyFlag]
  unfold encodeClassicalSnapshot
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  split
  · rename_i heq
    exact False.elim (hkeyFlag (by simpa [flag] using heq))
  · split
    · rename_i heq
      exact False.elim (hkeyNode (by simpa [pendingNode] using heq))
    · rfl

/-- The canonical value cell of a completed Boolean node contains its literal
zero/one result word. -/
theorem encodeClassicalSnapshot_completeBool_fieldValue
    {program : Program Player simpleExpr}
    (usesBool : UsesOnlyBoolStorage program)
    (codec : StorageCodec program) (words : WireCodec codec.Word Word)
    (canonical : CanonicalRepresentation program codec words)
    (nodes : WireCodec (Fin program.graph.nodeCount) Word)
    (cfg : Config program.graph) (pending : Option (Fin program.graph.nodeCount))
    (node : Fin program.graph.nodeCount) (value : Bool) :
    encodeClassicalSnapshot codec words nodes
        { graph := StateSnapshot.ofConfig
            (cfg.completeNode node { ty := .bool, value := value })
          pending := pending }
        ((ClassicalStorageLayout.canonical program).address
          (.fieldValue
            ⟨program.graph.nodeTarget node,
              StateSnapshot.nodeTarget_lt_fieldCount program.graph node⟩)) =
      encodeBool value := by
  rw [encodeClassicalSnapshot_fieldValue]
  simp only [StateSnapshot.ofConfig, Config.completeNode, Store.getAs, Store.set,
    TypedValue.as?, usesBool.field_type, ↓reduceIte, ↓reduceDIte]
  convert canonical.encode_type_eq_bool
    (usesBool.field_type
      (⟨program.graph.nodeTarget node,
        StateSnapshot.nodeTarget_lt_fieldCount program.graph node⟩ :
        Fin program.graph.fieldCount)) value using 1
  congr 2
  apply eq_of_heq
  rw [cast_heq_iff_heq, eqRec_eq_cast, heq_cast_iff_heq]

/-- Completing a Boolean node makes its target-field presence cell true. -/
theorem encodeClassicalSnapshot_completeBool_fieldPresent
    {program : Program Player simpleExpr}
    (usesBool : UsesOnlyBoolStorage program)
    (codec : StorageCodec program) (words : WireCodec codec.Word Word)
    (nodes : WireCodec (Fin program.graph.nodeCount) Word)
    (cfg : Config program.graph) (pending : Option (Fin program.graph.nodeCount))
    (node : Fin program.graph.nodeCount) (value : Bool) :
    encodeClassicalSnapshot codec words nodes
        { graph := StateSnapshot.ofConfig
            (cfg.completeNode node { ty := .bool, value := value })
          pending := pending }
        ((ClassicalStorageLayout.canonical program).address
          (.fieldPresent
            ⟨program.graph.nodeTarget node,
              StateSnapshot.nodeTarget_lt_fieldCount program.graph node⟩)) =
      1 := by
  rw [encodeClassicalSnapshot_fieldPresent]
  simp [StateSnapshot.ofConfig, Config.completeNode, Store.getAs, Store.set,
    usesBool.field_type, TypedValue.as?, encodeBool]

/-- Completing a node makes its canonical completion cell true. -/
theorem encodeClassicalSnapshot_completeBool_completed
    {program : Program Player simpleExpr}
    (codec : StorageCodec program) (words : WireCodec codec.Word Word)
    (nodes : WireCodec (Fin program.graph.nodeCount) Word)
    (cfg : Config program.graph) (pending : Option (Fin program.graph.nodeCount))
    (node : Fin program.graph.nodeCount) (value : Bool) :
    encodeClassicalSnapshot codec words nodes
        { graph := StateSnapshot.ofConfig
            (cfg.completeNode node { ty := .bool, value := value })
          pending := pending }
        ((ClassicalStorageLayout.canonical program).address
          (.completed node)) = 1 := by
  rw [encodeClassicalSnapshot_completed]
  simp [StateSnapshot.ofConfig, Config.completeNode, encodeBool]

/-- A present Boolean graph field has its literal zero/one word at the
canonical value slot, independently of proof transports to the field type. -/
theorem encodeClassicalSnapshot_bool_fieldValue
    {program : Program Player simpleExpr}
    (usesBool : UsesOnlyBoolStorage program)
    (codec : StorageCodec program) (words : WireCodec codec.Word Word)
    (canonical : CanonicalRepresentation program codec words)
    (nodes : WireCodec (Fin program.graph.nodeCount) Word)
    (snapshot : ClassicalSnapshot program)
    (field : Fin program.graph.fieldCount) (value : Bool)
    (hvalue : snapshot.graph.fieldValue? field =
      some ((usesBool.field_type field).symm ▸ value)) :
    encodeClassicalSnapshot codec words nodes snapshot
        ((ClassicalStorageLayout.canonical program).address
          (.fieldValue field)) =
      encodeBool value := by
  rw [encodeClassicalSnapshot_fieldValue, hvalue]
  exact canonical.encode_type_eq_bool (usesBool.field_type field) value

/-- The three concrete writes emitted for a Boolean action are exactly the
canonical encoding of the graph successor produced by completing that node.
All other storage cells, including the pending-oracle phase, are unchanged. -/
theorem encodeClassicalSnapshot_completeBool
    {program : Program Player simpleExpr}
    (usesBool : UsesOnlyBoolStorage program)
    (codec : StorageCodec program) (words : WireCodec codec.Word Word)
    (canonical : CanonicalRepresentation program codec words)
    (nodes : WireCodec (Fin program.graph.nodeCount) Word)
    (cfg : Config program.graph) (pending : Option (Fin program.graph.nodeCount))
    (node : Fin program.graph.nodeCount) (value : Bool) :
    let target : Fin program.graph.fieldCount :=
      ⟨program.graph.nodeTarget node,
        StateSnapshot.nodeTarget_lt_fieldCount program.graph node⟩
    let layout := ClassicalStorageLayout.canonical program
    Function.update
        (Function.update
          (Function.update
            (encodeClassicalSnapshot codec words nodes
              { graph := StateSnapshot.ofConfig cfg, pending := pending })
            (layout.address (.fieldValue target)) (encodeBool value))
          (layout.address (.fieldPresent target)) 1)
        (layout.address (.completed node)) 1 =
      encodeClassicalSnapshot codec words nodes
        { graph := StateSnapshot.ofConfig
            (cfg.completeNode node { ty := .bool, value := value })
          pending := pending } := by
  dsimp only
  funext key
  let target : Fin program.graph.fieldCount :=
    ⟨program.graph.nodeTarget node,
      StateSnapshot.nodeTarget_lt_fieldCount program.graph node⟩
  let layout := ClassicalStorageLayout.canonical program
  let valueSlot := layout.address
    (ClassicalStorageSlot.fieldValue target)
  let presenceSlot := layout.address
    (ClassicalStorageSlot.fieldPresent target)
  let completionSlot := layout.address
    (ClassicalStorageSlot.completed node)
  change
    Function.update
        (Function.update
          (Function.update
            (encodeClassicalSnapshot codec words nodes
              { graph := StateSnapshot.ofConfig cfg, pending := pending })
            valueSlot (encodeBool value))
          presenceSlot 1)
        completionSlot 1 key =
      encodeClassicalSnapshot codec words nodes
        { graph := StateSnapshot.ofConfig
            (cfg.completeNode node { ty := .bool, value := value })
          pending := pending } key
  by_cases hcompletion : key = completionSlot
  · subst key
    simp only [Function.update_self]
    change (1 : Word) =
      encodeClassicalSnapshot codec words nodes
        { graph := StateSnapshot.ofConfig
            (cfg.completeNode node { ty := .bool, value := value })
          pending := pending }
        ((ClassicalStorageLayout.canonical program).address (.completed node))
    exact (encodeClassicalSnapshot_completeBool_completed codec words nodes
      cfg pending node value).symm
  by_cases hpresence : key = presenceSlot
  · subst key
    have hne : presenceSlot ≠ completionSlot := by
      intro heq
      have := (ClassicalStorageLayout.canonical program).injective heq
      cases this
    simp only [Function.update_of_ne hne, Function.update_self]
    change (1 : Word) =
      encodeClassicalSnapshot codec words nodes
        { graph := StateSnapshot.ofConfig
            (cfg.completeNode node { ty := .bool, value := value })
          pending := pending }
        ((ClassicalStorageLayout.canonical program).address
          (.fieldPresent target))
    exact (encodeClassicalSnapshot_completeBool_fieldPresent usesBool codec
      words nodes cfg pending node value).symm
  by_cases hvalue : key = valueSlot
  · subst key
    have hneCompletion : valueSlot ≠ completionSlot := by
      intro heq
      have := (ClassicalStorageLayout.canonical program).injective heq
      cases this
    have hnePresence : valueSlot ≠ presenceSlot := by
      intro heq
      have := (ClassicalStorageLayout.canonical program).injective heq
      cases this
    simp only [Function.update_of_ne hneCompletion,
      Function.update_of_ne hnePresence, Function.update_self]
    change encodeBool value =
      encodeClassicalSnapshot codec words nodes
        { graph := StateSnapshot.ofConfig
            (cfg.completeNode node { ty := .bool, value := value })
          pending := pending }
        ((ClassicalStorageLayout.canonical program).address
          (.fieldValue target))
    exact (encodeClassicalSnapshot_completeBool_fieldValue usesBool codec
      words canonical nodes cfg pending node value).symm
  simp only [Function.update_of_ne hcompletion,
    Function.update_of_ne hpresence, Function.update_of_ne hvalue]
  unfold encodeClassicalSnapshot
  by_cases hfieldValue : key < program.graph.fieldCount
  · rw [dif_pos hfieldValue, dif_pos hfieldValue]
    simp only [StateSnapshot.ofConfig, Config.completeNode]
    have hqueryNe : key ≠ program.graph.nodeTarget node := by
      intro heq
      apply hvalue
      simpa [valueSlot, layout, target] using heq
    rw [Store.getAs_set_ne cfg.store hqueryNe
      { ty := .bool, value := value }
      (program.graph.fieldRow ⟨key, hfieldValue⟩).ty]
  · rw [dif_neg hfieldValue, dif_neg hfieldValue]
    by_cases hfieldPresent :
        key - program.graph.fieldCount < program.graph.fieldCount
    · rw [dif_pos hfieldPresent, dif_pos hfieldPresent]
      simp only [StateSnapshot.ofConfig, Config.completeNode]
      have hqueryNe : key - program.graph.fieldCount ≠
          program.graph.nodeTarget node := by
        intro heq
        apply hpresence
        simp [presenceSlot, layout, target]
        omega
      rw [Store.getAs_set_ne cfg.store hqueryNe
        { ty := .bool, value := value }
        (program.graph.fieldRow
          ⟨key - program.graph.fieldCount, hfieldPresent⟩).ty]
    · rw [dif_neg hfieldPresent, dif_neg hfieldPresent]
      by_cases hcompleted :
          key - 2 * program.graph.fieldCount < program.graph.nodeCount
      · rw [dif_pos hcompleted, dif_pos hcompleted]
        have hnodeNe :
            (⟨key - 2 * program.graph.fieldCount, hcompleted⟩ :
              Fin program.graph.nodeCount) ≠ node := by
          intro heq
          apply hcompletion
          have hge : 2 * program.graph.fieldCount ≤ key := by omega
          have heqValue := Fin.ext_iff.mp heq
          change key - 2 * program.graph.fieldCount = (node : Nat) at heqValue
          change key = 2 * program.graph.fieldCount + (node : Nat)
          omega
        simp only [StateSnapshot.ofConfig, Config.completeNode]
        simp [hnodeNe]
      · rw [dif_neg hcompleted, dif_neg hcompleted]

@[simp] theorem decodeClassicalField_encodeClassicalSnapshot
    (codec : StorageCodec program) (words : WireCodec codec.Word Word)
    (nodes : WireCodec (Fin program.graph.nodeCount) Word)
    (snapshot : ClassicalSnapshot program)
    (field : Fin program.graph.fieldCount) :
    decodeClassicalField codec words
        (encodeClassicalSnapshot codec words nodes snapshot) field =
      some (snapshot.graph.fieldValue? field) := by
  unfold decodeClassicalField
  dsimp only
  rw [encodeClassicalSnapshot_fieldPresent,
    encodeClassicalSnapshot_fieldValue]
  cases hvalue : snapshot.graph.fieldValue? field with
  | none =>
      simp
  | some value =>
      simp [words.decode_encode,
        codec.decode_encode_value _ (codec.field_supported field)]

@[simp] theorem decodeClassicalCompleted_encodeClassicalSnapshot
    (codec : StorageCodec program) (words : WireCodec codec.Word Word)
    (nodes : WireCodec (Fin program.graph.nodeCount) Word)
    (snapshot : ClassicalSnapshot program)
    (node : Fin program.graph.nodeCount) :
    decodeClassicalCompleted
        (encodeClassicalSnapshot codec words nodes snapshot) node =
      some (decide (node ∈ snapshot.graph.done)) := by
  unfold decodeClassicalCompleted
  rw [encodeClassicalSnapshot_completed]
  exact decodeBool_encodeBool _

@[simp] theorem decodeClassicalPending_encodeClassicalSnapshot
    (codec : StorageCodec program) (words : WireCodec codec.Word Word)
    (nodes : WireCodec (Fin program.graph.nodeCount) Word)
    (snapshot : ClassicalSnapshot program) :
    decodeClassicalPending nodes
        (encodeClassicalSnapshot codec words nodes snapshot) =
      some snapshot.pending := by
  unfold decodeClassicalPending
  dsimp only
  rw [encodeClassicalSnapshot_pendingFlag,
    encodeClassicalSnapshot_pendingNode]
  cases hpending : snapshot.pending with
  | none =>
      simp
  | some node =>
      simp only [Option.isSome_some, decodeBool_encodeBool]
      rw [nodes.decode_encode]
      rfl

/-- Decode all finite cells, rejecting noncanonical Booleans or malformed
field/node words. -/
def decodeClassicalSnapshot (codec : StorageCodec program)
    (words : WireCodec codec.Word Word)
    (nodes : WireCodec (Fin program.graph.nodeCount) Word)
    (storage : TotalStorage) : Option (ClassicalSnapshot program) :=
  if hfields :
      ∀ field : Fin program.graph.fieldCount,
        (decodeClassicalField codec words storage field).isSome then
    if hcompleted :
        ∀ node : Fin program.graph.nodeCount,
          (decodeClassicalCompleted storage node).isSome then
      if hpending : (decodeClassicalPending nodes storage).isSome then
        some
          { graph :=
              { fieldValue? := fun field =>
                  (decodeClassicalField codec words storage field).get
                    (hfields field)
                done := Finset.univ.filter fun node =>
                  (decodeClassicalCompleted storage node).get
                    (hcompleted node) }
            pending := (decodeClassicalPending nodes storage).get hpending }
      else
        none
    else
      none
  else
    none

/-- Total EVM storage encoding is lossless for every classical snapshot. -/
@[simp] theorem decodeClassicalSnapshot_encodeClassicalSnapshot
    (codec : StorageCodec program) (words : WireCodec codec.Word Word)
    (nodes : WireCodec (Fin program.graph.nodeCount) Word)
    (snapshot : ClassicalSnapshot program) :
    decodeClassicalSnapshot codec words nodes
        (encodeClassicalSnapshot codec words nodes snapshot) =
      some snapshot := by
  have hfields :
      ∀ field : Fin program.graph.fieldCount,
        (decodeClassicalField codec words
          (encodeClassicalSnapshot codec words nodes snapshot) field).isSome := by
    intro field
    rw [decodeClassicalField_encodeClassicalSnapshot]
    cases snapshot.graph.fieldValue? field <;> rfl
  have hcompleted :
      ∀ node : Fin program.graph.nodeCount,
        (decodeClassicalCompleted
          (encodeClassicalSnapshot codec words nodes snapshot) node).isSome := by
    intro node
    rw [decodeClassicalCompleted_encodeClassicalSnapshot]
    rfl
  have hpending :
      (decodeClassicalPending nodes
        (encodeClassicalSnapshot codec words nodes snapshot)).isSome := by
    rw [decodeClassicalPending_encodeClassicalSnapshot]
    cases snapshot.pending <;> rfl
  unfold decodeClassicalSnapshot
  rw [dif_pos hfields, dif_pos hcompleted, dif_pos hpending]
  congr 1
  apply ClassicalSnapshot.ext
  · apply StateSnapshot.ext
    · ext node
      simp
    · intro field
      simp
  · simp

end Vegas.Machine.Contract.EVM
