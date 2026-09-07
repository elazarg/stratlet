/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasEVM.Contract
import VegasEVM.Contract.Layout
import VegasEVM.Contract.ABI
import VegasEVM.Contract.Storage
import VegasEVM.Contract.Validator
import VegasEVM.Contract.State
import VegasEVM.Contract.StoredABI
import VegasEVM.Contract.Executor
import VegasEVM.Contract.StoredExecutor
import VegasEVM.Contract.Authentication
import VegasEVM.Contract.Calldata
import VegasEVM.Contract.InternalCalldata
import VegasEVM.Contract.Lifecycle
import VegasEVM.Contract.Configured
import VegasEVM.Contract.Wire
import VegasEVM.Contract.EVMWord
import VegasEVM.Contract.EVMAddress
import VegasEVM.Contract.Blockchain
import VegasEVM.Contract.EVMCalldata
import VegasEVM.Contract.EVMBytes
import VegasEVM.Contract.Entropy
import VegasEVM.Contract.UniformEntropy
import VegasEVM.Contract.OraclePolicy
import VegasEVM.Contract.OracleCalldata
import VegasEVM.Contract.OracleProtocol
import VegasEVM.Contract.DeterministicExecutor
import VegasEVM.Contract.Classical
import VegasEVM.Contract.IdealVisibility
import VegasEVM.Contract.ClassicalBatch
import VegasEVM.Contract.ClassicalEVMCalldata
import VegasEVM.Contract.ClassicalEVMBytes
import VegasEVM.Contract.ClassicalEVMStorage
import VegasEVM.Contract.ClassicalEVMIR
import VegasEVM.Contract.EVMAssembly
import VegasEVM.Contract.EVMLocalAssembly
import VegasEVM.Contract.EVMDeployment
import VegasEVM.Contract.EVMExecution
import VegasEVM.Contract.Imperative
import VegasEVM.Contract.ClassicalEVMCodegen
import VegasEVM.Contract.ClassicalEVMCodegenCorrect
import VegasEVM.Contract.SimpleEVMExpr
import VegasEVM.Contract.SimpleEVMExprCorrect
import VegasEVM.Contract.SimpleEVMActionCorrect
import VegasEVM.Contract.SimpleEVMAction
import VegasEVM.Contract.SimpleEVMDist
import VegasEVM.Contract.SimpleEVMSample
import VegasEVM.Contract.BooleanEVMRuntime
import VegasEVM.Contract.BooleanEVMRuntimeCorrect
import VegasEVM.Contract.Gas
import VegasEVM.Contract.Transaction
import VegasEVM.Compile.Classical
import VegasEVM.Compile.ClassicalEVM
import VegasEVM.Compile.BooleanEVM
import VegasEVM.Compile.EVMRefinement

/-! # Contract representations and EVM backend development

This library depends on the runtime-general core. Its checked local codegen
results do not discharge `Vegas.ClassicalCompiler.EVMRefinement.BooleanCompilationCorrect`.
The full default build checks this library alongside the core and paper audit;
importing `Vegas` alone does not import this backend.
-/
