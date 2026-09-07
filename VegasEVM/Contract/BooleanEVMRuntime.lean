/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasEVM.Contract.SimpleEVMSample

/-!
# Boolean classical EVM handlers

This backend generates all four handlers for Boolean-storage programs. It
validates exact calldata lengths, routes canonical node words, compiles player
commits and permissionless reveals, and implements the trusted-oracle sample
request/callback protocol. The result is symbolic local assembly ready for the
proved resolver and bytecode linker.

The no-sample specialization rejects both oracle entry points. The complete
surface instead logs the requested node, locks other graph actions until an
authenticated callback, and realizes the retained exact Boolean table from a
256-bit callback index.
-/

namespace Vegas.Machine.Contract.EVM

open EventGraph

noncomputable section

variable {Player Address : Type}
variable [DecidableEq Player] [DecidableEq Address]
variable {program : Program Player simpleExpr}

/-- Evidence that the program has no stochastic graph nodes. -/
def HasNoSampleNodes (program : Program Player simpleExpr) : Prop :=
  ∀ node : Fin program.graph.nodeCount,
    match (program.graph.nodeRow node).sem with
    | .sample _ => False
    | .commit _ _ | .reveal _ => True

/-- Stable plans assigned to one classical entry point. -/
def actionsForRoute (program : Program Player simpleExpr)
    (route : ClassicalRoute) : List (ClassicalActionIR program) :=
  (compileClassicalIR program).actions.filter fun action =>
    action.route = route

/-- Exact calldata-size assertion. -/
def compileCalldataSizeEq (expected : Nat) (reject : LocalLabel) :
    LocalAssembly :=
  [ .op .calldatasize,
    .op (.push (.nat256 expected)),
    .op .eq,
    .op .iszero,
    .jumpi reject ]

/-- Route one canonical node word to its action label. -/
def compileNodeRoute (nodeOffset : Nat) (node : Nat)
    (target : LocalLabel) : LocalAssembly :=
  LocalAssembly.ofAssembly (loadCalldataWord nodeOffset) ++
    [ .op (.push (.nat256 node)),
      .op .eq,
      .jumpi target ]

/-- Compile all node comparisons in stable action order. -/
def compileNodeRoutes (nodeOffset : Nat)
    (actions : List (ClassicalActionIR program)) : LocalAssembly :=
  actions.flatMap fun action =>
    compileNodeRoute nodeOffset action.node (action.node + 1)

/-- Compile completing action blocks while threading fresh expression labels.
-/
def compileCompletingBlocks?
    (reject : LocalLabel)
    (realize : ClassicalActionIR program → Nat → Option GeneratedLocalCode) :
    List (ClassicalActionIR program) → Nat →
      Option (LocalAssembly × Nat)
  | [], next => some ([], next)
  | action :: rest, next =>
      match realize action next with
      | none => none
      | some realized =>
          match compileCompletingBlocks? reject realize rest
              realized.nextLabel with
          | none => none
          | some (suffix, finalLabel) =>
              some
                ([.label (action.node + 1)] ++
                    compileClassicalStorageChecks reject action.checks ++
                    realized.code ++ compileClassicalActionWrites action ++
                    [.op .stop] ++ suffix,
                  finalLabel)

/-- Common exact-size/node-routing wrapper for completing calls. -/
def compileCompletingHandler?
    (calldataSize nodeOffset : Nat)
    (actions : List (ClassicalActionIR program))
    (realize : ClassicalActionIR program → Nat → Option GeneratedLocalCode) :
    Option LocalAssembly :=
  let reject := 0
  let firstBodyLabel := program.graph.nodeCount + 1
  match compileCompletingBlocks? reject realize actions firstBodyLabel with
  | none => none
  | some (blocks, _next) =>
      some <|
        compileCalldataSizeEq calldataSize reject ++
          compileNodeRoutes nodeOffset actions ++ [.jump reject] ++
          blocks ++ classicalRejectBlock reject

/-- Completing handler with source-independent checks performed once after
calldata-size validation and before node routing. -/
def compileCompletingHandlerWithPrefix?
    (calldataSize nodeOffset : Nat) (prelude : LocalAssembly)
    (actions : List (ClassicalActionIR program))
    (realize : ClassicalActionIR program → Nat → Option GeneratedLocalCode) :
    Option LocalAssembly :=
  let reject := 0
  let firstBodyLabel := program.graph.nodeCount + 1
  match compileCompletingBlocks? reject realize actions firstBodyLabel with
  | none => none
  | some (blocks, _next) =>
      some <|
        compileCalldataSizeEq calldataSize reject ++ prelude ++
          compileNodeRoutes nodeOffset actions ++ [.jump reject] ++
          blocks ++ classicalRejectBlock reject

/-- Complete player handler for the supported Boolean fragment. -/
def compileBooleanPlayerHandler?
    (usesBool : UsesOnlyBoolStorage program)
    (registry : PlayerRegistry Player Address)
    (players : WireCodec Player Word)
    (addresses : AddressCodec Address) : Option LocalAssembly :=
  compileCompletingHandler? 100 36 (actionsForRoute program .player)
    (fun action next =>
      compileSimplePlayerCommit? usesBool registry players addresses action
        0 next)

/-- Complete permissionless reveal handler for the supported Boolean fragment.
-/
def compileBooleanRevealHandler? : Option LocalAssembly :=
  compileCompletingHandler? (program := program) 36 4
    (actionsForRoute program .reveal) compileSimpleReveal?

/-- Immediate empty-data revert used for unavailable entry points. -/
def unavailableHandler : LocalAssembly :=
  [ .op (.push (.one (byte 0))),
    .op (.push (.one (byte 0))),
    .op .revert ]

/-- Compile request blocks. The handler-level prefix has already established
that no request is pending. -/
def compileSampleRequestBlocks (reject : LocalLabel) :
    List (ClassicalActionIR program) → LocalAssembly
  | [] => []
  | action :: rest =>
      [.label (action.node + 1)] ++
        compileClassicalStorageChecks reject action.checks ++
        compileSimpleSampleRequestEffect action ++
        compileSampleRequestBlocks reject rest

/-- Complete permissionless sample-request handler. -/
def compileBooleanSampleRequestHandler : LocalAssembly :=
  let reject := 0
  let actions := actionsForRoute program .sampleRequest
  compileCalldataSizeEq 36 reject ++
    compilePendingFlagEq (program := program) false reject ++
    compileNodeRoutes 4 actions ++ [.jump reject] ++
    compileSampleRequestBlocks reject actions ++ classicalRejectBlock reject

/-- Compile callback blocks while threading distribution-expression labels. -/
def compileSampleCallbackBlocks?
    (usesBool : UsesOnlyBoolStorage program)
    (oracle : OracleRegistry Address) (addresses : AddressCodec Address)
    (reject : LocalLabel) :
    List (ClassicalActionIR program) → Nat → Option (LocalAssembly × Nat)
  | [], next => some ([], next)
  | action :: rest, next =>
      match compileSimpleSampleCallback? usesBool oracle addresses action
          reject next with
      | none => none
      | some realized =>
          match compileSampleCallbackBlocks? usesBool oracle addresses reject
              rest realized.nextLabel with
          | none => none
          | some (suffix, finalLabel) =>
              some
                ([.label (action.node + 1)] ++
                    compileClassicalStorageChecks reject action.checks ++
                    realized.code ++ compileClearPending program ++
                    compileClassicalActionWrites action ++ [.op .stop] ++
                    suffix,
                  finalLabel)

/-- Complete authenticated oracle-callback handler. -/
def compileBooleanSampleCallbackHandler?
    (usesBool : UsesOnlyBoolStorage program)
    (oracle : OracleRegistry Address) (addresses : AddressCodec Address) :
    Option LocalAssembly :=
  let reject := 0
  let actions := actionsForRoute program .oracleCallback
  let firstBodyLabel := program.graph.nodeCount + 1
  match compileSampleCallbackBlocks? usesBool oracle addresses reject actions
      firstBodyLabel with
  | none => none
  | some (blocks, _next) =>
      some <|
        compileCalldataSizeEq 68 reject ++ compileNodeRoutes 4 actions ++
          [.jump reject] ++ blocks ++ classicalRejectBlock reject

/-- Compile the complete permissionless-trigger Boolean classical surface,
including trusted-oracle request logs and authenticated callbacks. -/
def compileBooleanClassicalHandlers?
    (usesBool : UsesOnlyBoolStorage program)
    (registry : PlayerRegistry Player Address)
    (players : WireCodec Player Word)
    (oracle : OracleRegistry Address)
    (addresses : AddressCodec Address) : Option LocalClassicalHandlers :=
  match
      compileCompletingHandlerWithPrefix? 100 36
        (compilePendingFlagEq (program := program) false 0)
        (actionsForRoute program .player)
        (fun action next =>
          compileSimplePlayerCommit? usesBool registry players addresses action
            0 next),
      compileCompletingHandlerWithPrefix? 36 4
        (compilePendingFlagEq (program := program) false 0)
        (actionsForRoute program .reveal) compileSimpleReveal?,
      compileBooleanSampleCallbackHandler? usesBool oracle addresses with
  | some player, some reveal, some oracleCallback =>
      some
        { player := player
          reveal := reveal
          sampleRequest := compileBooleanSampleRequestHandler
            (program := program)
          oracleCallback := oracleCallback }
  | _, _, _ => none

/-- Compile every handler for a Boolean program with no sample nodes. Reveal
authorization is permissionless at this concrete backend; a restricted trigger
policy needs its own reified authorization compiler. -/
def compileBooleanNoSampleHandlers?
    (_noSamples : HasNoSampleNodes program)
    (usesBool : UsesOnlyBoolStorage program)
    (registry : PlayerRegistry Player Address)
    (players : WireCodec Player Word)
    (addresses : AddressCodec Address) : Option LocalClassicalHandlers :=
  match compileBooleanPlayerHandler? usesBool registry players addresses,
      compileBooleanRevealHandler? (program := program) with
  | some player, some reveal =>
      some
        { player := player
          reveal := reveal
          sampleRequest := unavailableHandler
          oracleCallback := unavailableHandler }
  | _, _ => none

end

end Vegas.Machine.Contract.EVM
