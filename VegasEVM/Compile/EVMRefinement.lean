/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.Machine
import VegasEVM.Compile.BooleanEVM
import VegasEVM.Contract.EVMExecution

/-!
# Classical EVM refinement boundary

This module states the exact non-secure compiler-correctness obligation between
the deterministic classical byte-calldata artifact and generated EVM code.
It fixes the representation of protocol state, outbound oracle requests,
rollback, caller context, deployment, and per-call results.

`BooleanCompilationCorrect` is intentionally a proposition rather than an
assumption hidden inside the compiler result. Structural layout facts are
already proved by the preceding passes; instruction-level handler simulation
is the remaining classical proof.
-/

noncomputable section

namespace Vegas.ClassicalCompiler.EVMRefinement

open Machine
open Machine.Contract
open Machine.Contract.Blockchain

variable {Player Address : Type}
variable [DecidableEq Player] [DecidableEq Address]
variable {source : WFProgram Player simpleExpr}

/-- Concrete anonymous-log data for one classical oracle request. -/
def requestLog (request : OracleProtocol.Request) : List EVM.Byte :=
  (EVM.PushData.word (BitVec.ofNat 256 request.node)).bytes

/-- Ordered EVM logs representing the classical contract's ordered outbound
oracle requests. -/
def LogsRepresent (requests : List OracleProtocol.Request)
    (logs : List (List EVM.Byte)) : Prop :=
  logs = requests.map requestLog

/-- A total EVM store represents one typed classical protocol state through
the canonical bounded snapshot. -/
def StateRepresents (artifact : EVMByteArtifact source Address)
    (state : artifact.State) (storage : EVM.TotalStorage) : Prop :=
  ∃ snapshot,
    EVM.ClassicalSnapshot.ofProtocolState? artifact.contract.codec state =
        some snapshot ∧
      storage = EVM.encodeClassicalSnapshot artifact.contract.codec
        artifact.abi.values artifact.abi.nodes snapshot

/-- Deployment storage represents the classical artifact's initial state. -/
theorem initialStorage_represents
    (artifact : EVMByteArtifact source Address) :
    StateRepresents artifact artifact.initial artifact.initialStorage := by
  refine ⟨artifact.initialSnapshot, artifact.sparse_initial_snapshot, rfl⟩

/-- One rollback-aware VM result implements one deterministic classical call
result. Generated handlers return no data and use empty revert data. -/
def ResultRefines (artifact : EVMByteArtifact source Address)
    (classical : DeterministicResult artifact.State OracleProtocol.Request)
    (target : EVM.TransactionResult) : Prop :=
  match classical, target with
  | .success result, .success storage logs returnData =>
      StateRepresents artifact result.state storage ∧
        LogsRepresent result.actions logs ∧ returnData = []
  | .revert _, .revert data => data = []
  | _, _ => False

/-- Concrete execution environment for one runtime call. `caller` is the raw
160-bit value controlled by the invoking account, rather than an encoding
constructed from an abstract source context. The current backend does not
inspect `CALLVALUE`, so its word remains an explicit target input. -/
def runtimeEnv (artifact : EVMByteArtifact source Address)
    (runtime : EVM.RuntimeImage artifact.abi.selectors)
    (contractAddress : Address) (caller : EVM.AddressWord)
    (calldata : EVM.ByteCalldata)
    (callValue : EVM.Word) : EVM.ExecutionEnv where
  codeBytes := runtime.bytecode
  calldata := calldata.bytes
  caller := caller
  contractAddress := artifact.addresses.encode contractAddress
  callValue := callValue

/-- A linked runtime refines the complete deterministic classical byte
endpoint on every represented state, raw 160-bit caller, remaining context,
calldata value, and call value. Claiming whole-runtime refinement therefore
requires a total abstract representation of all EVM callers; a merely
lossless finite address codec is insufficient. The generated control flow is
acyclic, so the assembly instruction count plus one is the canonical fuel
bound. -/
def RuntimeRefines (artifact : EVMByteArtifact source Address)
    (runtime : EVM.RuntimeImage artifact.abi.selectors) : Prop :=
  ∃ representation : EVM.TotalAddressRepresentation artifact.addresses,
    ∀ (context : CallContext Address) (caller : EVM.AddressWord)
        (state : artifact.State) (storage : EVM.TotalStorage)
        (calldata : EVM.ByteCalldata) (callValue : EVM.Word),
      calldata.FitsWord → StateRepresents artifact state storage →
        ResultRefines artifact
          (artifact.receive
            { context with sender := representation.abstract caller }
            state calldata)
          (EVM.executeTransaction (runtime.assembly.length + 1)
            runtime.assembly
            (runtimeEnv artifact runtime context.contractAddress caller
              calldata callValue)
            storage)

/-- Complete ordinary deployment correctness: exact initial layout, exact
constructor behavior, and per-call runtime refinement. -/
def DeploymentRefines (artifact : EVMByteArtifact source Address)
    (deployment : EVM.DeploymentImage artifact.abi.selectors) : Prop :=
  deployment.slotCount =
      EVM.ClassicalStorageLayout.canonicalSlotCount (Machine.compile source) ∧
    deployment.initialStorage = artifact.initialStorage ∧
    deployment.execute.transactionResult =
      .success deployment.initialStorage [] deployment.runtime.bytecode ∧
    RuntimeRefines artifact deployment.runtime

/-- Successful source-level deployment compilation preserves the selected
runtime and fixes both constructor inputs to the canonical source layout. -/
theorem compiledDeployment_structure
    (backend : EVMByteBackend source Address)
    (limits : EVM.DeploymentLimits)
    (usesBool : EVM.UsesOnlyBoolStorage (Machine.compile source))
    (canonical : EVM.CanonicalRepresentation (Machine.compile source)
      backend.classical.codec backend.values)
    (permissionlessReveals :
      backend.classical.reveals = TriggerPolicy.permissionless)
    (permissionlessSampleRequests :
      backend.classical.sampleRequests = TriggerPolicy.permissionless)
    (deployment : EVM.DeploymentImage backend.selectors)
    (hcompile :
      backend.compileBooleanDeployment? limits usesBool canonical
          permissionlessReveals permissionlessSampleRequests =
        some deployment) :
    ∃ runtime,
      backend.compileBooleanRuntime? usesBool canonical
          permissionlessReveals permissionlessSampleRequests = some runtime ∧
      deployment.runtime = runtime ∧
      deployment.slotCount =
        EVM.ClassicalStorageLayout.canonicalSlotCount
          (Machine.compile source) ∧
      deployment.initialStorage = backend.compile.initialStorage := by
  unfold EVMByteBackend.compileBooleanDeployment? at hcompile
  cases hruntime :
      backend.compileBooleanRuntime? usesBool canonical
        permissionlessReveals permissionlessSampleRequests with
  | none => simp [hruntime] at hcompile
  | some runtime =>
      simp only [hruntime] at hcompile
      refine ⟨runtime, rfl, ?_, ?_, ?_⟩
      · exact EVM.DeploymentImage.build?_runtime hcompile
      · exact EVM.DeploymentImage.build?_slotCount hcompile
      · exact EVM.DeploymentImage.build?_initialStorage hcompile

/-- For a successfully compiled deployment, finite layout and constructor
execution are already discharged; ordinary compiler correctness is precisely
the linked runtime simulation obligation. -/
theorem compiledDeployment_refines_iff_runtime
    (backend : EVMByteBackend source Address)
    (limits : EVM.DeploymentLimits)
    (usesBool : EVM.UsesOnlyBoolStorage (Machine.compile source))
    (canonical : EVM.CanonicalRepresentation (Machine.compile source)
      backend.classical.codec backend.values)
    (permissionlessReveals :
      backend.classical.reveals = TriggerPolicy.permissionless)
    (permissionlessSampleRequests :
      backend.classical.sampleRequests = TriggerPolicy.permissionless)
    (deployment : EVM.DeploymentImage backend.selectors)
    (hcompile :
      backend.compileBooleanDeployment? limits usesBool canonical
          permissionlessReveals permissionlessSampleRequests =
        some deployment) :
    DeploymentRefines backend.compile deployment ↔
      RuntimeRefines backend.compile deployment.runtime := by
  rcases compiledDeployment_structure backend limits usesBool canonical
      permissionlessReveals permissionlessSampleRequests deployment hcompile with
    ⟨_runtime, _hruntime, _hselected, hslots, hstorage⟩
  constructor
  · intro hrefines
    exact hrefines.2.2.2
  · intro hruntimeRefines
    exact ⟨hslots, hstorage,
      EVM.DeploymentImage.execute_transactionResult deployment,
      hruntimeRefines⟩

/-- Exact proof obligation for the trusted-oracle Boolean compiler. This is
ordinary compiler correctness; it does not assert cryptographic secrecy,
oracle honesty, scheduling fairness, gas availability, or game preservation
under target-only observations. -/
def BooleanCompilationCorrect
    (backend : EVMByteBackend source Address)
    (limits : EVM.DeploymentLimits)
    (usesBool : EVM.UsesOnlyBoolStorage (Machine.compile source))
    (canonical : EVM.CanonicalRepresentation (Machine.compile source)
      backend.classical.codec backend.values)
    (permissionlessReveals :
      backend.classical.reveals = TriggerPolicy.permissionless)
    (permissionlessSampleRequests :
      backend.classical.sampleRequests = TriggerPolicy.permissionless) : Prop :=
  ∀ deployment,
    backend.compileBooleanDeployment? limits usesBool canonical
        permissionlessReveals permissionlessSampleRequests = some deployment →
      DeploymentRefines backend.compile deployment

end Vegas.ClassicalCompiler.EVMRefinement
