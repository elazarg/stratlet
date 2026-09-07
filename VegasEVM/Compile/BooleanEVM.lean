/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.Machine
import VegasEVM.Compile.ClassicalEVM
import VegasEVM.Contract.BooleanEVMRuntime
import VegasEVM.Contract.EVMDeployment

/-!
# Checked-source Boolean EVM runtime compiler

This is the checked Boolean source-to-EVM backend. The complete endpoint
supports trusted-oracle sample request/callback pairs; a specialized no-sample
endpoint remains useful for deterministic games. Both require Boolean graph
storage, permissionless internal triggers, and expressions accepted by the
concrete Boolean compiler. Handler generation, image-size checking, local-label
resolution, selector linking, constructor storage initialization, and opcode
emission are otherwise automatic.

The deployment endpoints return actual EVM creation bytecode whose constructor
initializes the compiled source snapshot and returns the linked runtime. A
VM-semantics correctness theorem remains separate; successful emission alone is
not a semantic or game-preservation result.
-/

namespace Vegas.ClassicalCompiler

open Machine
open Machine.Contract

noncomputable section

variable {Player Address : Type}
variable [DecidableEq Player] [DecidableEq Address]
variable {source : WFProgram Player simpleExpr}

namespace EVMByteBackend

/-- Compile the complete trusted-oracle Boolean classical surface to linked
EVM runtime bytes. Both internal trigger policies are permissionless in this
backend; restricted policies require a reified authorization compiler. -/
def compileBooleanRuntime?
    (backend : EVMByteBackend source Address)
    (usesBool : EVM.UsesOnlyBoolStorage (Machine.compile source))
    (_canonical : EVM.CanonicalRepresentation (Machine.compile source)
      backend.classical.codec backend.values)
    (_permissionlessReveals :
      backend.classical.reveals = TriggerPolicy.permissionless)
    (_permissionlessSampleRequests :
      backend.classical.sampleRequests = TriggerPolicy.permissionless) :
    Option (EVM.RuntimeImage backend.selectors) :=
  match EVM.compileBooleanClassicalHandlers? usesBool
      backend.classical.players backend.players backend.classical.oracle
      backend.addresses with
  | none => none
  | some handlers => EVM.RuntimeImage.linkLocalChecked?
      backend.selectors handlers

/-- Compile the complete trusted-oracle Boolean surface to deployable EVM
creation bytecode, including constructor initialization of the source state. -/
def compileBooleanDeployment?
    (backend : EVMByteBackend source Address)
    (limits : EVM.DeploymentLimits)
    (usesBool : EVM.UsesOnlyBoolStorage (Machine.compile source))
    (canonical : EVM.CanonicalRepresentation (Machine.compile source)
      backend.classical.codec backend.values)
    (permissionlessReveals :
      backend.classical.reveals = TriggerPolicy.permissionless)
    (permissionlessSampleRequests :
      backend.classical.sampleRequests = TriggerPolicy.permissionless) :
    Option (EVM.DeploymentImage backend.selectors) := do
  let runtime ← backend.compileBooleanRuntime? usesBool canonical
    permissionlessReveals permissionlessSampleRequests
  EVM.DeploymentImage.build? limits runtime
    (EVM.ClassicalStorageLayout.canonicalSlotCount (Machine.compile source))
    backend.storageFits
    backend.compile.initialStorage
    backend.compile.initialStorage_zero_outside

/-- Compile the supported Boolean/no-sample fragment all the way to linked EVM
runtime bytes. Unsupported guards, unresolved labels, or an oversized image
return `none`. -/
def compileBooleanNoSampleRuntime?
    (backend : EVMByteBackend source Address)
    (usesBool : EVM.UsesOnlyBoolStorage (Machine.compile source))
    (_canonical : EVM.CanonicalRepresentation (Machine.compile source)
      backend.classical.codec backend.values)
    (noSamples : EVM.HasNoSampleNodes (Machine.compile source))
    (_permissionlessReveals :
      backend.classical.reveals = TriggerPolicy.permissionless) :
    Option (EVM.RuntimeImage backend.selectors) :=
  match EVM.compileBooleanNoSampleHandlers? noSamples usesBool
      backend.classical.players backend.players backend.addresses with
  | none => none
  | some handlers => EVM.RuntimeImage.linkLocalChecked?
      backend.selectors handlers

/-- Compile the deterministic Boolean/no-sample specialization to deployable
creation bytecode. -/
def compileBooleanNoSampleDeployment?
    (backend : EVMByteBackend source Address)
    (limits : EVM.DeploymentLimits)
    (usesBool : EVM.UsesOnlyBoolStorage (Machine.compile source))
    (canonical : EVM.CanonicalRepresentation (Machine.compile source)
      backend.classical.codec backend.values)
    (noSamples : EVM.HasNoSampleNodes (Machine.compile source))
    (permissionlessReveals :
      backend.classical.reveals = TriggerPolicy.permissionless) :
    Option (EVM.DeploymentImage backend.selectors) := do
  let runtime ← backend.compileBooleanNoSampleRuntime? usesBool canonical noSamples
    permissionlessReveals
  EVM.DeploymentImage.build? limits runtime
    (EVM.ClassicalStorageLayout.canonicalSlotCount (Machine.compile source))
    backend.storageFits
    backend.compile.initialStorage
    backend.compile.initialStorage_zero_outside

end EVMByteBackend

end

end Vegas.ClassicalCompiler
