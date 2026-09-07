/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.Machine
import VegasEVM.Compile.Classical
import VegasEVM.Contract.ClassicalEVMBytes
import VegasEVM.Contract.ClassicalEVMStorage
import VegasEVM.Contract.ClassicalEVMIR
import VegasEVM.Contract.EVMAddress

/-!
# Checked source to deterministic EVM-byte contract artifact

This module assembles the ordinary classical compiler with the complete
four-entry-point EVM calldata codec.  The result has EVM-sized selector/word
bytes, blockchain-supplied caller context, deterministic receive/revert
behavior, canonical storage, and ordered oracle request actions.

It is deliberately named a byte-calldata artifact, not a linked EVM runtime.
Retained expression code, checks, state updates, and authentication still need
lowering to handler instructions and a VM-level correctness theorem.
-/

noncomputable section

namespace Vegas.ClassicalCompiler

open Machine
open Machine.Contract
open Machine.Contract.Blockchain

variable {Player Address : Type}
variable [DecidableEq Player] [DecidableEq Address]
variable {L : IExpr}

/-- A deterministic contract paired with its complete EVM byte-calldata ABI. -/
structure EVMByteArtifact (source : WFProgram Player L) (Address : Type)
    [DecidableEq Address] where
  contract : ClassicalContract (Machine.compile source) Address
  abi : EVM.ClassicalABI (Machine.compile source) contract.codec.Word
  addresses : EVM.AddressCodec Address

namespace EVMByteArtifact

variable {source : WFProgram Player L}
variable (artifact : EVMByteArtifact source Address)

abbrev State := artifact.contract.State

/-- Canonical constructor state of the byte-calldata artifact. -/
def initial : artifact.State := artifact.contract.initial

/-- Semantic snapshot represented by the deployed EVM account storage. -/
def initialSnapshot : EVM.ClassicalSnapshot (Machine.compile source) :=
  let _contract := artifact.contract
  EVM.ClassicalSnapshot.idle (Machine.compile source).init.1

/-- Concrete total 256-bit storage installed at deployment. Absent source
fields are represented by false presence bits, not conflated with zero-valued
fields. -/
def initialStorage : EVM.TotalStorage :=
  EVM.encodeClassicalSnapshot artifact.contract.codec artifact.abi.values
    artifact.abi.nodes artifact.initialSnapshot

/-- The compiled constructor store has no nonzero cells outside the certified
dense layout. -/
theorem initialStorage_zero_outside (key : Nat)
    (hkey : EVM.ClassicalStorageLayout.canonicalSlotCount
      (Machine.compile source) ≤ key) :
    artifact.initialStorage key = 0 := by
  exact EVM.encodeClassicalSnapshot_eq_zero_of_ge_slotCount
    artifact.contract.codec artifact.abi.values artifact.abi.nodes
      artifact.initialSnapshot key hkey

/-- Finite routed handler inventory over the concrete EVM storage layout. -/
def handlerIR : EVM.ClassicalContractIR (Machine.compile source) :=
  EVM.compileClassicalIR (Machine.compile source)

/-- The concrete deployment storage decodes to exactly the compiled source
initial snapshot. -/
@[simp] theorem decode_initialStorage :
    EVM.decodeClassicalSnapshot artifact.contract.codec artifact.abi.values
        artifact.abi.nodes artifact.initialStorage =
      some artifact.initialSnapshot := by
  exact EVM.decodeClassicalSnapshot_encodeClassicalSnapshot _ _ _ _

/-- The earlier sparse constructor state and the new total EVM deployment
storage denote the same bounded classical snapshot. -/
@[simp] theorem sparse_initial_snapshot :
    EVM.ClassicalSnapshot.ofProtocolState? artifact.contract.codec
        artifact.initial =
      some artifact.initialSnapshot := by
  exact EVM.ClassicalSnapshot.ofProtocolState?_idleState
    artifact.contract.codec (Machine.compile source).init

/-- Deterministic byte-calldata receive function with the physical caller
supplied by blockchain context. -/
def receive (context : CallContext Address) (state : artifact.State)
    (calldata : EVM.ByteCalldata) :
    DeterministicResult artifact.State OracleProtocol.Request :=
  artifact.contract.receiveEVMBytes artifact.abi context state calldata

/-- Standard deterministic-contract packaging of the executable byte endpoint.
No entropy argument remains because chance is represented by oracle callback
calldata. -/
def toDeterministicContract :
    DeterministicContract Address EVM.ByteCalldata artifact.State
      OracleProtocol.Request Unit where
  initial := artifact.initial
  receive := fun _chain context state calldata _unit =>
    artifact.receive context state calldata

/-- Every encoded message reaches exactly the typed classical receive
function after caller contextualization. -/
@[simp] theorem receive_encode
    (context : CallContext Address) (state : artifact.State)
    (message :
      EVM.ClassicalMessage (Machine.compile source)
        artifact.contract.codec.Word) :
    artifact.receive context state (artifact.abi.encodeBytes message) =
      artifact.contract.receive state (message.contextualize context) := by
  exact artifact.contract.receiveEVMBytes_encode artifact.abi context state
    message

end EVMByteArtifact

/-- Backend choices needed to compile checked source to the executable
EVM-byte-calldata artifact. Node capacity is the concrete 256-bit bound;
address, value, and player codecs provide lossless EVM representations for
this deployment. -/
structure EVMByteBackend (source : WFProgram Player L) (Address : Type)
    [DecidableEq Address] where
  classical : Backend source Address
  selectors : EVM.ClassicalSelectors
  players : WireCodec Player EVM.Word
  playersCanonical : WireCodec.Canonical players
  nodesFit : EVM.NodesFitWord (Machine.compile source)
  storageFits : EVM.ClassicalStorageFitsWord (Machine.compile source)
  values : WireCodec classical.codec.Word EVM.Word
  addresses : EVM.AddressCodec Address

namespace EVMByteBackend

variable {source : WFProgram Player L}
variable (backend : EVMByteBackend source Address)

/-- Compile the checked source and all supplied representation choices to one
deterministic byte-calldata artifact. -/
def compile : EVMByteArtifact source Address where
  contract := backend.classical.compile
  abi :=
    { selectors := backend.selectors
      players := backend.players
      nodes := EVM.nodeWordCodec (Machine.compile source) backend.nodesFit
      values := backend.values }
  addresses := backend.addresses

@[simp] theorem compile_contract :
    backend.compile.contract = backend.classical.compile :=
  rfl

@[simp] theorem compile_initial :
    backend.compile.initial = backend.classical.compile.initial :=
  rfl

/-- The final ordinary compiler endpoint is a deterministic contract over raw
EVM-shaped byte calldata. -/
def artifact := backend.compile.toDeterministicContract

end EVMByteBackend

end Vegas.ClassicalCompiler
