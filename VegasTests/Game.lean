/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.EventGraph.Fence
import Vegas.Game.Kuhn
import Vegas.Scheduled
import VegasEVM.Compile.Classical
import VegasEVM.Compile.ClassicalEVM
import VegasEVM.Compile.BooleanEVM
import VegasEVM.Contract.ClassicalBatch
import VegasEVM.Contract.ClassicalEVMBytes
import VegasEVM.Contract.ClassicalEVMStorage
import VegasEVM.Contract.ClassicalEVMIR
import VegasEVM.Contract.EVMAssembly
import VegasEVM.Contract.EVMLocalAssembly
import VegasEVM.Contract.ClassicalEVMCodegen
import VegasEVM.Contract.BooleanEVMRuntime
import VegasEVM.Contract.EVMExecution
import Vegas.Runtime.KnownMediator
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
import VegasEVM.Contract.Imperative
import VegasEVM.Contract.Gas
import VegasEVM.Contract.Transaction

namespace VegasTests

open Vegas

abbrev TestPlayer := Fin 2

abbrev InitialSecretContext : VCtx TestPlayer simpleExpr :=
  [(7, .sealed 0 .bool)]

noncomputable def unopenedInitialSecret :
    VegasCore TestPlayer simpleExpr InitialSecretContext :=
  .ret []

example :
    ¬ RevealComplete (SealedVars InitialSecretContext)
        unopenedInitialSecret := by
  decide

noncomputable def openedInitialSecret :
    VegasCore TestPlayer simpleExpr InitialSecretContext :=
  .reveal 8 0 7 .here (.ret [])

example :
    RevealComplete (SealedVars InitialSecretContext)
      openedInitialSecret := by
  decide

def fairCoin : RationalLaw Bool where
  entries := [(false, 1 / 2), (true, 1 / 2)]
  normalized := by norm_num

example : fairCoin.denote.prob true = 1 / 2 := by
  unfold fairCoin
  rw [RationalLaw.prob_denote]
  dsimp
  rw [Fin.sum_univ_two]
  norm_num

example :
    (Machine.Contract.EVM.compileBoolTable? fairCoin.entries 0 1).isSome =
      true := by
  rfl

example :
    simpleExpr.evalLaw
        (DistExpr.weighted (Γ := []) (b := .bool) fairCoin)
        (Env.empty Val) = fairCoin := rfl

noncomputable def coinCore : VegasCore TestPlayer simpleExpr [] :=
  .sample 0 (DistExpr.weighted (b := .bool) fairCoin)
    (.ret
      [ (0,
          Expr.ite (.var 0 .here) (.constInt 1) (.constInt (-1))),
        (1,
          Expr.ite (.var 0 .here) (.constInt (-1)) (.constInt 1)) ])

noncomputable def coinProgram : WFProgram TestPlayer simpleExpr where
  core :=
    { Γ := []
      prog := coinCore
      env := VEnv.empty simpleExpr
      wctx := by simp
      fresh := by simp [coinCore, FreshBindings, Fresh] }
  reveals := by simp [coinCore, RevealComplete, SealedVars]
  legal := by
    unfold coinCore
    change True
    trivial

noncomputable def coinGame : Vegas.BoundedGame TestPlayer :=
  coinProgram.boundedGame

noncomputable def coinMachine : Machine.Program TestPlayer simpleExpr :=
  Machine.compile coinProgram

theorem coinMachine_graph_nodeCount : coinMachine.graph.nodeCount = 1 := rfl

theorem coinMachine_graph_fieldCount : coinMachine.graph.fieldCount = 1 := rfl

/-- The compiled coin graph carries a readability fence for every player, and
`decide` discharges it.

This is the regression test for `Graph.instDecidableFence`: a `Decidable`
instance can typecheck while failing to reduce, so the claim that a fence is a
*checkable* precondition rather than an assumed one is only worth as much as an
actual kernel evaluation on a real compiled graph. -/
theorem coinMachine_fence : ∀ who : TestPlayer, coinMachine.graph.Fence who := by
  decide

theorem coinUsesOnlyBoolStorage :
    Machine.Contract.EVM.UsesOnlyBoolStorage coinMachine := by
  constructor
  · intro field
    fin_cases field
    rfl
  · intro node
    fin_cases node
    rfl

example : coinGame.execution.BoundedHorizon coinGame.horizon :=
  coinGame.bounded

noncomputable example : GameTheory.UtilityGame TestPlayer :=
  coinGame.pure

noncomputable example : GameTheory.UtilityGame TestPlayer :=
  coinGame.behavioral

noncomputable example : GameTheory.UtilityGame TestPlayer :=
  coinGame.mixedPure

noncomputable def emptyCore : VegasCore TestPlayer simpleExpr [] :=
  .ret []

noncomputable def emptyProgram : WFProgram TestPlayer simpleExpr where
  core :=
    { Γ := []
      prog := emptyCore
      env := VEnv.empty simpleExpr
      wctx := by simp
      fresh := by simp [emptyCore, FreshBindings] }
  reveals := by simp [emptyCore, RevealComplete, SealedVars]
  legal := by trivial

noncomputable def emptyMachine : Machine.Program TestPlayer simpleExpr :=
  Machine.compile emptyProgram

theorem emptyMachine_graph_nodeCount : emptyMachine.graph.nodeCount = 0 := by
  simp [emptyMachine, Machine.compile, Machine.ofCompiled, emptyProgram,
    emptyCore, ToEventGraph.compile, ToEventGraph.compileCore,
    ToEventGraph.BuildResult.graph, EventGraph.Graph.nodeCount]

theorem emptyMachine_graph_fieldCount : emptyMachine.graph.fieldCount = 0 := by
  simp [emptyMachine, Machine.compile, Machine.ofCompiled, emptyProgram,
    emptyCore, ToEventGraph.compile, ToEventGraph.compileCore,
    ToEventGraph.BuildResult.graph, EventGraph.Graph.nodeCount,
    EventGraph.Graph.fieldCount, ToEventGraph.initialState,
    ToEventGraph.InitialState.empty]

theorem emptyUsesOnlyBoolStorage :
    Machine.Contract.EVM.UsesOnlyBoolStorage emptyMachine := by
  constructor <;> intro index <;> exact Fin.elim0 index

theorem emptyHasNoSampleNodes :
    Machine.Contract.EVM.HasNoSampleNodes emptyMachine := by
  intro node
  exact Fin.elim0 node

/-! ## Hidden simultaneous commitments -/

def matchingPenniesSame :
    Expr [(3, BaseTy.bool), (2, BaseTy.bool)] .bool :=
  .eq (.var 2 (.there .here)) (.var 3 .here)

def matchingPenniesLeftPayoff :
    Expr [(3, BaseTy.bool), (2, BaseTy.bool)] .int :=
  .ite matchingPenniesSame (.constInt 1) (.constInt (-1))

def matchingPenniesRightPayoff :
    Expr [(3, BaseTy.bool), (2, BaseTy.bool)] .int :=
  .ite matchingPenniesSame (.constInt (-1)) (.constInt 1)

/-- Two source-sequential commits compile to one simultaneous initial
frontier because neither choice depends on the other. -/
noncomputable def matchingPenniesCore : VegasCore TestPlayer simpleExpr [] :=
  .commit 0 0 (.constBool true)
    (.commit 1 1 (.constBool true)
      (.reveal 2 0 0 (.there .here)
        (.reveal 3 1 1 (.there .here)
          (.ret
            [ (0, matchingPenniesLeftPayoff),
              (1, matchingPenniesRightPayoff) ]))))

noncomputable def matchingPenniesProgram :
    WFProgram TestPlayer simpleExpr where
  core :=
    { Γ := []
      prog := matchingPenniesCore
      env := VEnv.empty simpleExpr
      wctx := by simp
      fresh := by simp [matchingPenniesCore, FreshBindings, Fresh] }
  reveals := by decide
  legal := by
    unfold matchingPenniesCore
    constructor
    · intro _env
      exact ⟨false, rfl⟩
    · constructor
      · intro _env
        exact ⟨false, rfl⟩
      · trivial

noncomputable def matchingPenniesMachine :
    Machine.Program TestPlayer simpleExpr :=
  Machine.compile matchingPenniesProgram

theorem matchingPenniesMachine_graph_nodeCount :
    matchingPenniesMachine.graph.nodeCount = 4 := by
  simp [matchingPenniesMachine, Machine.compile, Machine.ofCompiled,
    matchingPenniesProgram, matchingPenniesCore, ToEventGraph.compile,
    ToEventGraph.compileCore, ToEventGraph.BuildResult.graph,
    EventGraph.Graph.nodeCount]

theorem matchingPenniesMachine_graph_fieldCount :
    matchingPenniesMachine.graph.fieldCount = 4 := by
  simp [matchingPenniesMachine, Machine.compile, Machine.ofCompiled,
    matchingPenniesProgram, matchingPenniesCore, ToEventGraph.compile,
    ToEventGraph.compileCore, ToEventGraph.BuildResult.graph,
    EventGraph.Graph.fieldCount, EventGraph.Graph.nodeCount,
    ToEventGraph.initialState,
    ToEventGraph.InitialState.empty]

noncomputable def matchingPenniesGame : Vegas.BoundedGame TestPlayer :=
  matchingPenniesMachine.boundedGame

example
    (profile : GameTheory.Profile matchingPenniesGame.pure.form.sig) :
    (Runtime.KnownMediator.adequacy matchingPenniesGame.pure).IsNashForReal
        (Runtime.KnownMediator.compileProfile matchingPenniesGame.pure
          profile) ↔
      GameTheory.IsNash matchingPenniesGame.pure.form
        (GameTheory.euPreference matchingPenniesGame.pure.utility) profile :=
  Runtime.KnownMediator.isNashForReal_iff matchingPenniesGame.pure profile

noncomputable def matchingPenniesManifest :
    Machine.Contract.Manifest matchingPenniesMachine :=
  Machine.Contract.compile matchingPenniesMachine

example : matchingPenniesManifest.actions.length =
    matchingPenniesMachine.graph.nodeCount := by
  exact Machine.Contract.Manifest.compile_actions_length
    matchingPenniesMachine

example (node : Fin matchingPenniesMachine.graph.nodeCount) :
    (⟨node⟩ : Machine.Contract.Action matchingPenniesMachine) ∈
      matchingPenniesManifest.actions := by
  exact Machine.Contract.Manifest.action_mem matchingPenniesMachine node

noncomputable def matchingPenniesLayout :
    Machine.Contract.Layout matchingPenniesMachine :=
  Machine.Contract.Layout.canonical matchingPenniesMachine

noncomputable def matchingPenniesImperativeIR :
    Machine.Contract.Imperative.ContractIR matchingPenniesMachine :=
  Machine.Contract.Imperative.compile matchingPenniesMachine
    matchingPenniesLayout

example : matchingPenniesImperativeIR.actions.length = 4 := by
  rw [show matchingPenniesImperativeIR.actions.length =
      matchingPenniesMachine.graph.nodeCount by
    exact Machine.Contract.Imperative.compile_actions_length
      matchingPenniesLayout]
  exact matchingPenniesMachine_graph_nodeCount

example (node : Fin matchingPenniesMachine.graph.nodeCount) :
    (Machine.Contract.Imperative.compileAction
      matchingPenniesLayout node).body.length = 3 := by
  exact Machine.Contract.Imperative.compileAction_body_length
    matchingPenniesLayout node

example (node : Fin matchingPenniesMachine.graph.nodeCount) :
    Machine.Contract.Imperative.outputSlot matchingPenniesLayout node ≠
      Machine.Contract.Imperative.completionSlot
        matchingPenniesLayout node := by
  exact Machine.Contract.Imperative.outputSlot_ne_completionSlot
    matchingPenniesLayout node

example (cfg : EventGraph.Config matchingPenniesMachine.graph)
    (node : Fin matchingPenniesMachine.graph.nodeCount) :
    Machine.Contract.Imperative.evaluateAll
        (Machine.Contract.Imperative.Requirement.evaluate cfg)
        (Machine.Contract.Imperative.requirements
          matchingPenniesMachine node) =
      decide (EventGraph.Ready matchingPenniesMachine.graph cfg node) :=
  Machine.Contract.Imperative.evaluateAll_requirements cfg node

example (state : matchingPenniesMachine.State)
    (node : Fin matchingPenniesMachine.graph.nodeCount) :
    (Machine.Contract.Imperative.runChecks
        (Machine.Contract.Imperative.StorageCheck.evaluate
          (Machine.Contract.Imperative.completionReader
            (Machine.Contract.StorageCodec.reference matchingPenniesMachine)
            (Machine.Contract.RawStore.encodeState
              (Machine.Contract.StorageCodec.reference matchingPenniesMachine)
              state)))
        (Machine.Contract.Imperative.compileAction
          matchingPenniesLayout node).checks).succeeded =
      decide (EventGraph.Ready matchingPenniesMachine.graph state.1 node) := by
  exact Machine.Contract.Imperative.compileAction_checks_correct
    matchingPenniesLayout state.1 _
      (Machine.Contract.Imperative.completionReader_encodeState_agrees
        (Machine.Contract.StorageCodec.reference matchingPenniesMachine)
        state) node

example (state : matchingPenniesMachine.State)
    (node : Fin matchingPenniesMachine.graph.nodeCount) :
    (Machine.Contract.Gas.runChecks
        (Machine.Contract.Gas.CheckCostModel.uniform
          Machine.Contract.Imperative.StorageCheck)
        (Machine.Contract.Imperative.StorageCheck.evaluate
          (Machine.Contract.Imperative.completionReader
            (Machine.Contract.StorageCodec.reference matchingPenniesMachine)
            (Machine.Contract.RawStore.encodeState
              (Machine.Contract.StorageCodec.reference matchingPenniesMachine)
              state)))
        (Machine.Contract.Imperative.compileAction
          matchingPenniesLayout node).checks).succeeded =
      decide (EventGraph.Ready matchingPenniesMachine.graph state.1 node) := by
  rw [Machine.Contract.Gas.MeteredCheckResult.succeeded,
    Machine.Contract.Gas.erase_runChecks]
  exact Machine.Contract.Imperative.compileAction_checks_correct
    matchingPenniesLayout state.1 _
      (Machine.Contract.Imperative.completionReader_encodeState_agrees
        (Machine.Contract.StorageCodec.reference matchingPenniesMachine)
        state) node

example : Function.Injective matchingPenniesLayout.address :=
  matchingPenniesLayout.injective

example
    (field : Fin matchingPenniesMachine.graph.fieldCount)
    (node : Fin matchingPenniesMachine.graph.nodeCount) :
    matchingPenniesLayout.address (.value field) ≠
      matchingPenniesLayout.address (.completed node) := by
  exact Machine.Contract.Layout.value_ne_completed
    matchingPenniesMachine field node

example (state : matchingPenniesMachine.State)
    (command : matchingPenniesMachine.Command state) :
    (Machine.Contract.Request.decode state
      (Machine.Contract.Request.encode command)).isSome := by
  exact Machine.Contract.Request.decode_encode_isSome command

example (state : matchingPenniesMachine.State)
    (command : matchingPenniesMachine.Command state) :
    Machine.Contract.Request.accepts state
      (Machine.Contract.Request.encode command) = true := by
  exact Machine.Contract.Request.accepts_encode command

theorem matchingPenniesUsesOnlyBoolStorage :
    Machine.Contract.EVM.UsesOnlyBoolStorage matchingPenniesMachine := by
  constructor
  · intro field
    fin_cases field <;> rfl
  · intro node
    fin_cases node <;> rfl

noncomputable def matchingPenniesStorageCodec :
    Machine.Contract.StorageCodec matchingPenniesMachine :=
  Machine.Contract.EVM.boolStorageCodec matchingPenniesMachine
    matchingPenniesUsesOnlyBoolStorage

example : matchingPenniesStorageCodec.Word = BitVec 256 := rfl

example :
    Machine.Contract.EVM.decodeBool
        (matchingPenniesStorageCodec.encodeValue .bool true) = some true := by
  rfl

example (node : Fin matchingPenniesMachine.graph.nodeCount) :
    Machine.Contract.RawStore.readCompleted
        (Machine.Contract.Layout.canonical matchingPenniesMachine)
        matchingPenniesStorageCodec
        (Machine.Contract.initialStore matchingPenniesMachine
          matchingPenniesStorageCodec) node = some false := by
  exact Machine.Contract.readCompleted_initialStore
    matchingPenniesMachine matchingPenniesStorageCodec node

def matchingPenniesRegistry :
    Machine.Contract.PlayerRegistry TestPlayer TestPlayer where
  address := id
  injective := Function.injective_id

example (state : matchingPenniesMachine.State)
    (call : Machine.Contract.PlayerCall TestPlayer TestPlayer simpleExpr) :
    Machine.Contract.PlayerCall.acceptsStore
        (program := matchingPenniesMachine) matchingPenniesRegistry
        matchingPenniesStorageCodec
        (Machine.Contract.RawStore.encodeState matchingPenniesStorageCodec state)
        call = true ↔
      call.caller = matchingPenniesRegistry.address call.player ∧
        Machine.Contract.Request.Represents state call.request := by
  exact
    Machine.Contract.PlayerCall.acceptsStore_encodeState_eq_true_iff
      matchingPenniesRegistry matchingPenniesStorageCodec state call

example {state : matchingPenniesMachine.State} {who : TestPlayer}
    (action : EventGraph.CommitAction matchingPenniesMachine.graph who)
    (step : EventGraph.CommitStep matchingPenniesMachine.graph state.1
      who action) :
    Machine.Contract.PlayerCalldata.acceptsStore
        (program := matchingPenniesMachine) matchingPenniesRegistry
        matchingPenniesStorageCodec
        (Machine.Contract.RawStore.encodeState matchingPenniesStorageCodec state)
        (Machine.Contract.PlayerCalldata.encodeCommit
          matchingPenniesRegistry matchingPenniesStorageCodec action step) =
      true := by
  exact
    Machine.Contract.PlayerCalldata.acceptsStore_encodeState_encodeCommit
      matchingPenniesRegistry matchingPenniesStorageCodec action step

example {state : matchingPenniesMachine.State} {who : TestPlayer}
    (action : EventGraph.CommitAction matchingPenniesMachine.graph who)
    (step : EventGraph.CommitStep matchingPenniesMachine.graph state.1
      who action) :
    Machine.Contract.PlayerCalldata.executeStore?
        (program := matchingPenniesMachine) matchingPenniesRegistry
        matchingPenniesStorageCodec
        (Machine.Contract.RawStore.encodeState
          matchingPenniesStorageCodec state)
        (Machine.Contract.PlayerCalldata.encodeCommit
          matchingPenniesRegistry matchingPenniesStorageCodec action step) =
      some ((matchingPenniesMachine.step state (.commit who action step)).map
        (Machine.Contract.RawStore.encodeState
          matchingPenniesStorageCodec)) := by
  exact
    Machine.Contract.PlayerCalldata.executeStore?_encodeState_encodeCommit
      matchingPenniesRegistry matchingPenniesStorageCodec action step

def permissionlessTriggers :
    Machine.Contract.TriggerPolicy TestPlayer :=
  Machine.Contract.TriggerPolicy.permissionless

noncomputable def matchingPenniesContract :
    Machine.Contract.ConfiguredContract matchingPenniesMachine TestPlayer where
  codec := matchingPenniesStorageCodec
  players := matchingPenniesRegistry
  triggers := permissionlessTriggers

noncomputable def matchingPenniesClassicalBackend :
    ClassicalCompiler.Backend matchingPenniesProgram TestPlayer where
  codec := matchingPenniesStorageCodec
  players := matchingPenniesRegistry
  reveals := permissionlessTriggers
  sampleRequests := permissionlessTriggers
  oracle := { address := 0 }

noncomputable def matchingPenniesClassicalContract :=
  matchingPenniesClassicalBackend.compile

example :
    matchingPenniesClassicalContract.initial =
      Machine.Contract.OracleProtocol.idleState matchingPenniesStorageCodec
        matchingPenniesMachine.init :=
  rfl

example (state : matchingPenniesMachine.State) :
    Machine.Contract.IdealVisibility.publicView?
        matchingPenniesStorageCodec
        (matchingPenniesClassicalContract.encodeState state) =
      some (matchingPenniesMachine.publicView state) := by
  change
    Machine.Contract.IdealVisibility.publicView?
        matchingPenniesStorageCodec
        (Machine.Contract.OracleProtocol.idleState
          matchingPenniesStorageCodec state) =
      some (matchingPenniesMachine.publicView state)
  exact Machine.Contract.IdealVisibility.publicView?_idleState
    matchingPenniesStorageCodec state

example {state : matchingPenniesMachine.State}
    (batch : Machine.Contract.FrontierBatch matchingPenniesMachine state) :
    (matchingPenniesMachine.execution.step state batch.command).map
        matchingPenniesClassicalContract.encodeState =
      GameTheory.Math.Probability.FinDist.pure
        (matchingPenniesClassicalContract.executeBatch batch) := by
  exact matchingPenniesClassicalContract.map_source_step_encodeState batch

example {state : matchingPenniesMachine.State} {who : TestPlayer}
    (action : EventGraph.CommitAction matchingPenniesMachine.graph who)
    (step : EventGraph.CommitStep matchingPenniesMachine.graph state.1
      who action) :
    matchingPenniesClassicalContract.receive
        (matchingPenniesClassicalContract.encodeState state)
        (.player
          (Machine.Contract.PlayerCalldata.encodeCommit
            matchingPenniesRegistry matchingPenniesStorageCodec action step)) =
      .success (Machine.Contract.Blockchain.CallSuccess.silent
        { store := Machine.Contract.RawStore.encodeSnapshot
            matchingPenniesStorageCodec
            (EventGraph.StateSnapshot.ofConfig
              (state.1.completeNode action.node
                { ty := step.guard.ty, value := step.value }))
          pending := none }) := by
  exact matchingPenniesClassicalContract.receive_encodeState_playerCommit
    state who action step

def matchingPenniesSelectors : Machine.Contract.EVM.Selectors where
  player := 0
  internal := 1
  player_ne_internal := by decide

noncomputable def matchingPenniesMessageABI :
    Machine.Contract.EVM.MessageABI matchingPenniesMachine
      matchingPenniesContract.codec.Word where
  selectors := matchingPenniesSelectors
  players := Machine.Contract.EVM.indexWordCodec 2 (by
    norm_num [Machine.Contract.EVM.IndexFitsWord])
  nodes := Machine.Contract.EVM.nodeWordCodec matchingPenniesMachine (by
    change matchingPenniesMachine.graph.nodeCount ≤ 2 ^ 256
    rw [matchingPenniesMachine_graph_nodeCount]
    norm_num)

noncomputable def matchingPenniesArgumentWords :
    Machine.Contract.WireCodec matchingPenniesContract.codec.Word
      Machine.Contract.EVM.Word :=
  Machine.Contract.WireCodec.identity Machine.Contract.EVM.Word

def matchingPenniesClassicalSelectors :
    Machine.Contract.EVM.ClassicalSelectors where
  player := 0
  reveal := 1
  sampleRequest := 2
  oracleCallback := 3
  player_ne_reveal := by decide
  player_ne_sampleRequest := by decide
  player_ne_oracleCallback := by decide
  reveal_ne_sampleRequest := by decide
  reveal_ne_oracleCallback := by decide
  sampleRequest_ne_oracleCallback := by decide

noncomputable def matchingPenniesClassicalABI :
    Machine.Contract.EVM.ClassicalABI
      (Machine.compile matchingPenniesProgram)
      matchingPenniesClassicalContract.codec.Word where
  selectors := matchingPenniesClassicalSelectors
  players := matchingPenniesMessageABI.players
  nodes := matchingPenniesMessageABI.nodes
  values := matchingPenniesArgumentWords

noncomputable def matchingPenniesEVMByteBackend :
    ClassicalCompiler.EVMByteBackend matchingPenniesProgram TestPlayer where
  classical := matchingPenniesClassicalBackend
  selectors := matchingPenniesClassicalSelectors
  players := Machine.Contract.EVM.indexWordCodec 2 (by
    norm_num [Machine.Contract.EVM.IndexFitsWord])
  playersCanonical := Machine.Contract.EVM.indexWordCodec_canonical 2 (by
    norm_num [Machine.Contract.EVM.IndexFitsWord])
  nodesFit := by
    change (Machine.compile matchingPenniesProgram).graph.nodeCount ≤ 2 ^ 256
    change matchingPenniesMachine.graph.nodeCount ≤ 2 ^ 256
    rw [matchingPenniesMachine_graph_nodeCount]
    norm_num
  storageFits := by
    change
      2 * matchingPenniesMachine.graph.fieldCount +
          matchingPenniesMachine.graph.nodeCount + 2 ≤ 2 ^ 256
    rw [matchingPenniesMachine_graph_fieldCount,
      matchingPenniesMachine_graph_nodeCount]
    norm_num
  values :=
    Machine.Contract.WireCodec.identity Machine.Contract.EVM.Word
  addresses := Machine.Contract.EVM.indexAddressCodec 2 (by
    norm_num [Machine.Contract.EVM.IndexFitsAddress])

noncomputable def emptyClassicalBackend :
    ClassicalCompiler.Backend emptyProgram TestPlayer where
  codec := Machine.Contract.EVM.boolStorageCodec emptyMachine
    emptyUsesOnlyBoolStorage
  players := matchingPenniesRegistry
  reveals := permissionlessTriggers
  sampleRequests := permissionlessTriggers
  oracle := { address := 0 }

noncomputable def emptyEVMByteBackend :
    ClassicalCompiler.EVMByteBackend emptyProgram TestPlayer where
  classical := emptyClassicalBackend
  selectors := matchingPenniesClassicalSelectors
  players := Machine.Contract.EVM.indexWordCodec 2 (by
    norm_num [Machine.Contract.EVM.IndexFitsWord])
  playersCanonical := Machine.Contract.EVM.indexWordCodec_canonical 2 (by
    norm_num [Machine.Contract.EVM.IndexFitsWord])
  nodesFit := by
    change emptyMachine.graph.nodeCount ≤ 2 ^ 256
    rw [emptyMachine_graph_nodeCount]
    norm_num
  storageFits := by
    change 2 * emptyMachine.graph.fieldCount +
      emptyMachine.graph.nodeCount + 2 ≤ 2 ^ 256
    rw [emptyMachine_graph_fieldCount, emptyMachine_graph_nodeCount]
    norm_num
  values := Machine.Contract.WireCodec.identity Machine.Contract.EVM.Word
  addresses := Machine.Contract.EVM.indexAddressCodec 2 (by
    norm_num [Machine.Contract.EVM.IndexFitsAddress])

theorem emptyCanonicalRepresentation :
    Machine.Contract.EVM.CanonicalRepresentation emptyMachine
      emptyEVMByteBackend.classical.codec emptyEVMByteBackend.values :=
  Machine.Contract.EVM.boolIdentityRepresentation emptyMachine
    emptyUsesOnlyBoolStorage

example :
    (emptyEVMByteBackend.compileBooleanNoSampleRuntime?
      emptyUsesOnlyBoolStorage emptyCanonicalRepresentation
      emptyHasNoSampleNodes rfl).isSome = true := by
  rfl

noncomputable def emptyEVMRuntimeImage :
    Machine.Contract.EVM.RuntimeImage matchingPenniesClassicalSelectors :=
  (emptyEVMByteBackend.compileBooleanNoSampleRuntime?
    emptyUsesOnlyBoolStorage emptyCanonicalRepresentation
    emptyHasNoSampleNodes rfl).get (by rfl)

theorem emptyEVMRuntimeImage_bytecode_length :
    emptyEVMRuntimeImage.bytecode.length = 190 := by
  rfl

theorem emptyEVMInitialization_byteLength :
    (Machine.Contract.EVM.compileStorageInitialization
      (Machine.Contract.EVM.ClassicalStorageLayout.canonicalSlotCount
        emptyMachine)
      emptyEVMByteBackend.compile.initialStorage).byteLength = 0 := by
  rfl

noncomputable def emptyEVMDeploymentImage :
    Machine.Contract.EVM.DeploymentImage matchingPenniesClassicalSelectors where
  limits := Machine.Contract.EVM.DeploymentLimits.ethereum
  runtime := emptyEVMRuntimeImage
  slotCount := Machine.Contract.EVM.ClassicalStorageLayout.canonicalSlotCount
    emptyMachine
  slotCount_fits := emptyEVMByteBackend.storageFits
  initialStorage := emptyEVMByteBackend.compile.initialStorage
  storage_zero_outside :=
    emptyEVMByteBackend.compile.initialStorage_zero_outside
  offset_fits := by
    change 21 < 2 ^ 32
    norm_num
  runtime_size_fits := by
    rw [emptyEVMRuntimeImage_bytecode_length]
    norm_num [Machine.Contract.EVM.DeploymentLimits.ethereum]
  initcode_size_fits := by
    rw [emptyEVMInitialization_byteLength,
      emptyEVMRuntimeImage_bytecode_length]
    norm_num [Machine.Contract.EVM.DeploymentLimits.ethereum]

example : emptyEVMDeploymentImage.runtimeOffset = 21 := by
  rfl

example : emptyEVMDeploymentImage.bytecode.length = 211 := by
  rw [Machine.Contract.EVM.DeploymentImage.bytecode_length]
  rw [show emptyEVMDeploymentImage.runtimeOffset = 21 by rfl]
  rw [show emptyEVMDeploymentImage.runtime = emptyEVMRuntimeImage by rfl]
  rw [emptyEVMRuntimeImage_bytecode_length]

def copyReturnExecution : Machine.Contract.EVM.ExecutionState :=
  let constructor := Machine.Contract.EVM.deploymentCopyReturn 21 2
  Machine.Contract.EVM.execute 20 constructor
    { codeBytes := constructor.emit ++
        [Machine.Contract.EVM.byte 0xaa, Machine.Contract.EVM.byte 0xbb]
      calldata := []
      caller := 0
      contractAddress := 0
      callValue := 0 }
    Machine.Contract.EVM.freshStorage

def arithmeticExecutionEnv : Machine.Contract.EVM.ExecutionEnv where
  codeBytes := []
  calldata := []
  caller := 0
  contractAddress := 0
  callValue := 0

def arithmeticExecutionState (stack : List Machine.Contract.EVM.Word) :
    Machine.Contract.EVM.ExecutionState :=
  { Machine.Contract.EVM.ExecutionState.initial
      Machine.Contract.EVM.freshStorage with stack := stack }

example : (Machine.Contract.EVM.stepInstruction [] arithmeticExecutionEnv .sub
    (arithmeticExecutionState [10, 3])).stack = [7] := by
  decide

example : (Machine.Contract.EVM.stepInstruction [] arithmeticExecutionEnv .div
    (arithmeticExecutionState [10, 3])).stack = [3] := by
  decide

example : (Machine.Contract.EVM.stepInstruction [] arithmeticExecutionEnv .mod
    (arithmeticExecutionState [10, 3])).stack = [1] := by
  decide

example : (Machine.Contract.EVM.stepInstruction [] arithmeticExecutionEnv .lt
    (arithmeticExecutionState [3, 10])).stack = [1] := by
  decide

example : (Machine.Contract.EVM.stepInstruction [] arithmeticExecutionEnv .gt
    (arithmeticExecutionState [10, 3])).stack = [1] := by
  decide

example : (Machine.Contract.EVM.stepInstruction [] arithmeticExecutionEnv .shl
    (arithmeticExecutionState [1, 3])).stack = [6] := by
  decide

example :
    copyReturnExecution.exit =
      some (.returned
        [Machine.Contract.EVM.byte 0xaa,
          Machine.Contract.EVM.byte 0xbb]) := by
  decide

def emptyHandlerInventory : Machine.Contract.EVM.ClassicalHandlers where
  player := []
  reveal := []
  sampleRequest := []
  oracleCallback := []

def unknownSelectorExecution :
    Machine.Contract.EVM.ExecutionState :=
  let program := Machine.Contract.EVM.classicalRuntimeAssembly
    matchingPenniesClassicalSelectors emptyHandlerInventory
  Machine.Contract.EVM.execute 100 program
    { codeBytes := program.emit
      calldata := [0, 0, 0, 4]
      caller := 0
      contractAddress := 0
      callValue := 0 }
    Machine.Contract.EVM.freshStorage

example :
    unknownSelectorExecution.exit = some (.reverted []) := by
  decide

example :
    (emptyEVMByteBackend.compileBooleanRuntime?
      emptyUsesOnlyBoolStorage emptyCanonicalRepresentation rfl rfl).isSome = true := by
  rfl

example :
    matchingPenniesEVMByteBackend.compile.initial =
      matchingPenniesClassicalBackend.compile.initial :=
  rfl

example :
    Machine.Contract.EVM.decodeClassicalSnapshot
        matchingPenniesStorageCodec matchingPenniesArgumentWords
        matchingPenniesClassicalABI.nodes
        matchingPenniesEVMByteBackend.compile.initialStorage =
      some matchingPenniesEVMByteBackend.compile.initialSnapshot := by
  exact matchingPenniesEVMByteBackend.compile.decode_initialStorage

example (state : matchingPenniesMachine.State)
    (node : Fin matchingPenniesMachine.graph.nodeCount) :
    Machine.Contract.Imperative.evaluateAll
        (Machine.Contract.EVM.ClassicalStorageCheck.evaluate
          (Machine.Contract.EVM.encodeClassicalSnapshot
            matchingPenniesStorageCodec matchingPenniesArgumentWords
            matchingPenniesClassicalABI.nodes
            (Machine.Contract.EVM.ClassicalSnapshot.idle state.1)))
        (Machine.Contract.EVM.classicalChecks matchingPenniesMachine node) =
      decide (EventGraph.Ready matchingPenniesMachine.graph state.1 node) := by
  exact Machine.Contract.EVM.classicalChecks_accept_iff_ready
    matchingPenniesStorageCodec matchingPenniesArgumentWords
    matchingPenniesClassicalABI.nodes state.1 none node

example
    (message : Machine.Contract.EVM.ClassicalMessage
      matchingPenniesMachine matchingPenniesStorageCodec.Word) :
    matchingPenniesClassicalABI.decodeBytes
        (matchingPenniesClassicalABI.encodeBytes message) = some message := by
  exact matchingPenniesClassicalABI.decodeBytes_encodeBytes message

example (node : Fin matchingPenniesMachine.graph.nodeCount) :
    (matchingPenniesClassicalABI.encodeBytes
      (.oracleCallback { node := node, choice := 0 })).byteLength = 68 :=
  rfl

def matchingPenniesStopHandlers :
    Machine.Contract.EVM.LinkableHandlers where
  handlers :=
    { player := [.stop]
      reveal := [.stop]
      sampleRequest := [.stop]
      oracleCallback := [.stop] }
  size_fits := by
    norm_num [Machine.Contract.EVM.classicalRuntimeSize,
      Machine.Contract.EVM.classicalDispatcherSize,
      Machine.Contract.EVM.ClassicalHandlers.blockSize,
      Machine.Contract.EVM.ClassicalHandlers.get,
      Machine.Contract.EVM.Assembly.byteLength,
      Machine.Contract.EVM.Instruction.byteLength]

def matchingPenniesRuntimeImage :
    Machine.Contract.EVM.RuntimeImage matchingPenniesClassicalSelectors :=
  Machine.Contract.EVM.RuntimeImage.link matchingPenniesClassicalSelectors
    matchingPenniesStopHandlers

example : matchingPenniesRuntimeImage.bytecode.length = 76 := by
  change
    (Machine.Contract.EVM.RuntimeImage.link
      matchingPenniesClassicalSelectors
      matchingPenniesStopHandlers).bytecode.length = 76
  rw [Machine.Contract.EVM.RuntimeImage.link_bytecode_length]
  norm_num [matchingPenniesStopHandlers,
    Machine.Contract.EVM.classicalRuntimeSize,
    Machine.Contract.EVM.classicalDispatcherSize,
    Machine.Contract.EVM.ClassicalHandlers.blockSize,
    Machine.Contract.EVM.ClassicalHandlers.get,
    Machine.Contract.EVM.Assembly.byteLength,
    Machine.Contract.EVM.Instruction.byteLength]

example : matchingPenniesRuntimeImage.bytecode.take 6 =
    [Machine.Contract.EVM.byte 0x60, Machine.Contract.EVM.byte 0x00,
      Machine.Contract.EVM.byte 0x35, Machine.Contract.EVM.byte 0x60,
      Machine.Contract.EVM.byte 0xe0, Machine.Contract.EVM.byte 0x1c] := by
  rfl

def localConditionalExample : Machine.Contract.EVM.LocalAssembly :=
  [ .op (.push (.one (Machine.Contract.EVM.byte 1))),
    .jumpi 0,
    .op .stop,
    .label 0,
    .op .stop ]

example :
    Machine.Contract.EVM.LocalAssembly.resolveAt 100 localConditionalExample =
      some
        [ .push (.one (Machine.Contract.EVM.byte 1)),
          .push (.nat32 109),
          .jumpi,
          .stop,
          .jumpdest,
          .stop ] := by
  rfl

def duplicateLocalLabelHandlers :
    Machine.Contract.EVM.LocalClassicalHandlers where
  player := [.label 0, .label 0]
  reveal := []
  sampleRequest := []
  oracleCallback := []

example : Machine.Contract.EVM.RuntimeImage.linkLocalChecked?
    matchingPenniesClassicalSelectors duplicateLocalLabelHandlers = none := by
  rfl

example (check : Machine.Contract.EVM.ClassicalStorageCheck) :
    (Machine.Contract.EVM.compileClassicalStorageCheck 0 check).byteLength =
      44 := by
  exact Machine.Contract.EVM.compileClassicalStorageCheck_byteLength 0 check

theorem matchingPenniesHasNoSampleNodes :
    Machine.Contract.EVM.HasNoSampleNodes matchingPenniesMachine := by
  intro node
  fin_cases node <;> trivial

def trueBooleanGuardCode : EventGraph.GuardCode simpleExpr .bool where
  actionName := 0
  Context := []
  expr := .constBool true
  fieldOf := fun binding => nomatch binding

example : Machine.Contract.EVM.compileSimpleGuardCode?
    trueBooleanGuardCode =
      some [.push (.one (Machine.Contract.EVM.byte 1))] := by
  simp [Machine.Contract.EVM.compileSimpleGuardCode?, trueBooleanGuardCode,
    Machine.Contract.EVM.stackLimit]

def rightNestedBooleanExpr : Expr [] .bool :=
  .andBool (.constBool true)
    (.andBool (.constBool true) (.constBool true))

example : Machine.Contract.EVM.compileBoolExpr? (Γ := []) 2
    (fun binding => nomatch binding) rightNestedBooleanExpr = none := by
  simp [Machine.Contract.EVM.compileBoolExpr?, rightNestedBooleanExpr,
    Machine.Contract.EVM.lowerBoolExpr?,
    Machine.Contract.EVM.BoolExprIR.stackHeight]

example (message : matchingPenniesContract.Message) :
    matchingPenniesMessageABI.decodeBytes matchingPenniesArgumentWords
        (matchingPenniesMessageABI.encodeBytes
          matchingPenniesArgumentWords message) =
      some message := by
  exact matchingPenniesMessageABI.decodeBytes_encodeBytes
    matchingPenniesArgumentWords message

noncomputable def matchingPenniesEntropyRealization :
    Machine.Contract.Blockchain.EntropyRealization
      matchingPenniesContract.toStochasticContract :=
  Machine.Contract.Blockchain.EntropyRealization.semantic
    matchingPenniesContract.toStochasticContract

example
    (chain : Machine.Contract.Blockchain.ChainView)
    (context : Machine.Contract.Blockchain.CallContext TestPlayer)
    (store : matchingPenniesContract.Store)
    (message : matchingPenniesContract.Message) :
    (matchingPenniesEntropyRealization.entropyLaw
        chain context store message).map
        (matchingPenniesEntropyRealization.receive
          chain context store message) =
      (matchingPenniesContract.receive chain context store message).outcomeLaw :=
  matchingPenniesEntropyRealization.law chain context store message

example
    (chain : Machine.Contract.Blockchain.ChainView)
    (context : Machine.Contract.Blockchain.CallContext TestPlayer)
    (store : matchingPenniesContract.Store)
    (message : matchingPenniesContract.Message) :
    (matchingPenniesEntropyRealization.entropyLaw
        chain context store message).map
        (fun entropy =>
          Machine.Contract.Blockchain.DeterministicResult.settle store
            (matchingPenniesEntropyRealization.receive
              chain context store message entropy)) =
      (matchingPenniesContract.receive chain context store message).settledLaw
        store := by
  exact matchingPenniesEntropyRealization.settled_law
    chain context store message

example :
    matchingPenniesMessageABI.decode
        { selector := 2, arguments := [] } = none := by
  rfl

example :
    matchingPenniesMessageABI.decode
        { selector := matchingPenniesSelectors.player
          arguments := [] } = none := by
  rfl

noncomputable def matchingPenniesWireCodec :
    matchingPenniesContract.TransactionWireCodec
      matchingPenniesContract.Calldata :=
  Machine.Contract.WireCodec.identity matchingPenniesContract.Calldata

example {state : matchingPenniesMachine.State} {who : TestPlayer}
    (action : EventGraph.CommitAction matchingPenniesMachine.graph who)
    (step : EventGraph.CommitStep matchingPenniesMachine.graph state.1
      who action) :
    matchingPenniesContract.execute?
        (Machine.Contract.RawStore.encodeState
          matchingPenniesContract.codec state)
        (.player
          (Machine.Contract.PlayerCalldata.encodeCommit
            matchingPenniesContract.players matchingPenniesContract.codec
            action step)) =
      some ((matchingPenniesMachine.step state (.commit who action step)).map
        (Machine.Contract.RawStore.encodeState
          matchingPenniesContract.codec)) := by
  exact matchingPenniesContract.execute?_encodeState_playerCommit action step

example
    (chain : Machine.Contract.Blockchain.ChainView)
    (context : Machine.Contract.Blockchain.CallContext TestPlayer)
    {state : matchingPenniesMachine.State} {who : TestPlayer}
    (action : EventGraph.CommitAction matchingPenniesMachine.graph who)
    (step : EventGraph.CommitStep matchingPenniesMachine.graph state.1
      who action)
    (hsender : context.sender = matchingPenniesContract.players.address who) :
    matchingPenniesContract.receive chain context
        (Machine.Contract.RawStore.encodeState
          matchingPenniesContract.codec state)
        (.player
          (Machine.Contract.Blockchain.PlayerMessage.encodeCommit
            matchingPenniesContract.codec action step)) =
      .success (Machine.Contract.Blockchain.CallSuccess.silentLaw Empty
        ((matchingPenniesMachine.step state (.commit who action step)).map
          (Machine.Contract.RawStore.encodeState
            matchingPenniesContract.codec))) := by
  exact matchingPenniesContract.receive_encodeState_playerCommit
    chain context action step hsender

example
    (chain : Machine.Contract.Blockchain.ChainView)
    (context : Machine.Contract.Blockchain.CallContext TestPlayer)
    {state : matchingPenniesMachine.State} {who : TestPlayer}
    (action : EventGraph.CommitAction matchingPenniesMachine.graph who)
    (step : EventGraph.CommitStep matchingPenniesMachine.graph state.1
      who action)
    (hsender : context.sender = matchingPenniesContract.players.address who) :
    matchingPenniesContract.receiveEVMBytes chain
        matchingPenniesMessageABI matchingPenniesArgumentWords context
        (Machine.Contract.RawStore.encodeState
          matchingPenniesContract.codec state)
        (matchingPenniesMessageABI.encodeBytes matchingPenniesArgumentWords
          (.player
            (Machine.Contract.Blockchain.PlayerMessage.encodeCommit
              matchingPenniesContract.codec action step))) =
      .success (Machine.Contract.Blockchain.CallSuccess.silentLaw Empty
        ((matchingPenniesMachine.step state (.commit who action step)).map
          (Machine.Contract.RawStore.encodeState
            matchingPenniesContract.codec))) := by
  rw [matchingPenniesContract.receiveEVMBytes_encode]
  exact matchingPenniesContract.receive_encodeState_playerCommit
    chain context action step hsender

example
    (chain : Machine.Contract.Blockchain.ChainView)
    (context : Machine.Contract.Blockchain.CallContext TestPlayer)
    {state : matchingPenniesMachine.State} {who : TestPlayer}
    (action : EventGraph.CommitAction matchingPenniesMachine.graph who)
    (step : EventGraph.CommitStep matchingPenniesMachine.graph state.1
      who action)
    (hsender : context.sender = matchingPenniesContract.players.address who) :
    matchingPenniesContract.receiveEVMCalldata chain
        matchingPenniesMessageABI context
        (Machine.Contract.RawStore.encodeState
          matchingPenniesContract.codec state)
        (matchingPenniesMessageABI.encode
          (.player
            (Machine.Contract.Blockchain.PlayerMessage.encodeCommit
              matchingPenniesContract.codec action step))) =
      .success (Machine.Contract.Blockchain.CallSuccess.silentLaw Empty
        ((matchingPenniesMachine.step state (.commit who action step)).map
          (Machine.Contract.RawStore.encodeState
            matchingPenniesContract.codec))) := by
  rw [matchingPenniesContract.receiveEVMCalldata_encode]
  exact matchingPenniesContract.receive_encodeState_playerCommit
    chain context action step hsender

example {state : matchingPenniesMachine.State} {who : TestPlayer}
    (action : EventGraph.CommitAction matchingPenniesMachine.graph who)
    (step : EventGraph.CommitStep matchingPenniesMachine.graph state.1
      who action) :
    matchingPenniesContract.executeWire? matchingPenniesWireCodec
        (Machine.Contract.RawStore.encodeState
          matchingPenniesContract.codec state)
        (matchingPenniesWireCodec.encode
          (.player
            (Machine.Contract.PlayerCalldata.encodeCommit
              matchingPenniesContract.players matchingPenniesContract.codec
              action step))) =
      some ((matchingPenniesMachine.step state (.commit who action step)).map
        (Machine.Contract.RawStore.encodeState
          matchingPenniesContract.codec)) := by
  exact matchingPenniesContract.executeWire?_encodeState_playerCommit
    matchingPenniesWireCodec action step

example (state : matchingPenniesMachine.State)
    (wire : matchingPenniesContract.Calldata)
    (haccept :
      matchingPenniesContract.acceptsWire matchingPenniesWireCodec
        (Machine.Contract.RawStore.encodeState
          matchingPenniesContract.codec state) wire = true) :
    ∃ command : matchingPenniesMachine.Command state,
      matchingPenniesContract.executeWire? matchingPenniesWireCodec
          (Machine.Contract.RawStore.encodeState
            matchingPenniesContract.codec state) wire =
        some ((matchingPenniesMachine.step state command).map
          (Machine.Contract.RawStore.encodeState
            matchingPenniesContract.codec)) := by
  exact matchingPenniesContract.executeWire?_encodeState_of_accepts
    matchingPenniesWireCodec state wire haccept

example {state : matchingPenniesMachine.State} (caller : TestPlayer)
    (event : EventGraph.InternalEvent matchingPenniesMachine.graph)
    (step : EventGraph.InternalStep matchingPenniesMachine.graph state.1
      event) :
    Machine.Contract.InternalCalldata.executeStore?
        (program := matchingPenniesMachine) permissionlessTriggers
        matchingPenniesStorageCodec
        (Machine.Contract.RawStore.encodeState
          matchingPenniesStorageCodec state)
        (Machine.Contract.InternalCalldata.encode caller event) =
      some ((matchingPenniesMachine.step state (.internal event step)).map
        (Machine.Contract.RawStore.encodeState
          matchingPenniesStorageCodec)) := by
  exact
    Machine.Contract.InternalCalldata.executeStore?_encodeState_encode
      permissionlessTriggers matchingPenniesStorageCodec caller event step rfl

example {state : matchingPenniesMachine.State} (caller : TestPlayer)
    (event : EventGraph.InternalEvent matchingPenniesMachine.graph)
    (step : EventGraph.InternalStep matchingPenniesMachine.graph state.1
      event) :
    matchingPenniesContract.execute?
        (Machine.Contract.RawStore.encodeState
          matchingPenniesContract.codec state)
        (.internal
          (Machine.Contract.InternalCalldata.encode caller event)) =
      some ((matchingPenniesMachine.step state (.internal event step)).map
        (Machine.Contract.RawStore.encodeState
          matchingPenniesContract.codec)) := by
  exact matchingPenniesContract.execute?_encodeState_internal
    caller event step rfl

example (snapshot : EventGraph.StateSnapshot matchingPenniesMachine.graph) :
    Machine.Contract.RawStore.decodeSnapshot matchingPenniesStorageCodec
        (Machine.Contract.RawStore.encodeSnapshot
          matchingPenniesStorageCodec snapshot) =
      some snapshot := by
  exact Machine.Contract.RawStore.decodeSnapshot_encodeSnapshot
    matchingPenniesStorageCodec snapshot

example : Function.Injective
    (Machine.Contract.RawStore.encodeState
      (program := matchingPenniesMachine) matchingPenniesStorageCodec) := by
  exact Machine.Contract.RawStore.encodeState_injective
    matchingPenniesStorageCodec

example (state : matchingPenniesMachine.State)
    (command : matchingPenniesMachine.Command state) :
    Machine.Contract.Request.acceptsStore
        (program := matchingPenniesMachine) matchingPenniesStorageCodec
        (Machine.Contract.RawStore.encodeState
          (program := matchingPenniesMachine)
          matchingPenniesStorageCodec state)
        (Machine.Contract.Request.encode command) = true := by
  rw [Machine.Contract.Request.acceptsStore_encodeState]
  exact Machine.Contract.Request.accepts_encode command

example (state : matchingPenniesMachine.State)
    (command : matchingPenniesMachine.Command state) :
    Machine.Contract.Request.executeConfig? state.1
        (Machine.Contract.Request.encode command) =
      some (GameTheory.Math.Probability.FinDist.map Subtype.val
        (matchingPenniesMachine.step state command)) := by
  exact Machine.Contract.Request.executeConfig?_encode_eq_map_step
    state command

example (state : matchingPenniesMachine.State)
    (command : matchingPenniesMachine.Command state) :
    Machine.Contract.Request.executeStore?
        (program := matchingPenniesMachine) matchingPenniesStorageCodec
        (Machine.Contract.RawStore.encodeState matchingPenniesStorageCodec state)
        (Machine.Contract.Request.encode command) =
      some ((matchingPenniesMachine.step state command).map
        (Machine.Contract.RawStore.encodeState
          matchingPenniesStorageCodec)) := by
  exact Machine.Contract.Request.executeStore?_encodeState_encode
    matchingPenniesStorageCodec state command

example (state : matchingPenniesMachine.State)
    (request : Machine.Contract.Request TestPlayer simpleExpr)
    (haccept :
      Machine.Contract.Request.acceptsStore
          (program := matchingPenniesMachine) matchingPenniesStorageCodec
          (Machine.Contract.RawStore.encodeState
            matchingPenniesStorageCodec state) request = true) :
    ∃ command : matchingPenniesMachine.Command state,
      Machine.Contract.Request.encode command = request ∧
        Machine.Contract.Request.executeStore?
            (program := matchingPenniesMachine) matchingPenniesStorageCodec
            (Machine.Contract.RawStore.encodeState
              matchingPenniesStorageCodec state) request =
          some ((matchingPenniesMachine.step state command).map
            (Machine.Contract.RawStore.encodeState
              matchingPenniesStorageCodec)) := by
  exact Machine.Contract.Request.executeStore?_encodeState_of_accepts
    matchingPenniesStorageCodec state request haccept

example
    (store : Machine.Contract.RawStore matchingPenniesStorageCodec)
    (field : Fin matchingPenniesMachine.graph.fieldCount)
    (value : simpleExpr.Val
      (matchingPenniesMachine.graph.fieldRow field).ty) :
    Machine.Contract.RawStore.readValue matchingPenniesLayout
        matchingPenniesStorageCodec
        (Machine.Contract.RawStore.writeValue matchingPenniesLayout
          matchingPenniesStorageCodec store field value) field =
      some value := by
  exact Machine.Contract.RawStore.readValue_writeValue
    matchingPenniesLayout matchingPenniesStorageCodec store field value

example
    (store : Machine.Contract.RawStore matchingPenniesStorageCodec)
    (field : Fin matchingPenniesMachine.graph.fieldCount)
    (node : Fin matchingPenniesMachine.graph.nodeCount)
    (completed : Bool) :
    Machine.Contract.RawStore.readValue matchingPenniesLayout
        matchingPenniesStorageCodec
        (Machine.Contract.RawStore.writeCompleted matchingPenniesLayout
          matchingPenniesStorageCodec store node completed) field =
      Machine.Contract.RawStore.readValue matchingPenniesLayout
        matchingPenniesStorageCodec store field := by
  exact Machine.Contract.RawStore.readValue_writeCompleted
    matchingPenniesLayout matchingPenniesStorageCodec
    store field node completed

example (state : matchingPenniesMachine.State)
    (hterminal : matchingPenniesMachine.terminal state) :
    ∃ sourceEnv :
        VEnv simpleExpr
          (ToEventGraph.compile matchingPenniesProgram.core).terminalCtx,
      EventGraph.evalPayoffs? matchingPenniesMachine.payoffs state.1.store =
        some (evalPayoffs
          (ToEventGraph.compile matchingPenniesProgram.core).sourcePayoffs
          sourceEnv) := by
  exact Machine.compile_sourcePayoffOfTerminal
    matchingPenniesProgram state hterminal

example (state : matchingPenniesMachine.State)
    (hterminal : matchingPenniesMachine.terminal state) :
    ∃ sourceEnv :
        VEnv simpleExpr
          (ToEventGraph.compile matchingPenniesProgram.core).terminalCtx,
      Machine.Contract.terminalPayout? matchingPenniesMachine
          matchingPenniesStorageCodec
          (Machine.Contract.RawStore.encodeState
            matchingPenniesStorageCodec state) =
        some (evalPayoffs
          (ToEventGraph.compile matchingPenniesProgram.core).sourcePayoffs
          sourceEnv) := by
  exact Machine.Contract.terminalPayout?_compile_encodeState
    matchingPenniesProgram matchingPenniesStorageCodec state hterminal

example (state : matchingPenniesMachine.State)
    (hterminal : matchingPenniesMachine.terminal state) :
    ∃ terminalEnv :
        VEnv simpleExpr
          (ToEventGraph.compile matchingPenniesProgram.core).terminalCtx,
      SmallStep.Star
        { ctx := matchingPenniesProgram.core.Γ,
          env := matchingPenniesProgram.core.env,
          cont := matchingPenniesProgram.core.prog }
        { ctx :=
            (ToEventGraph.compile matchingPenniesProgram.core).terminalCtx,
          env := terminalEnv,
          cont := .ret
            (ToEventGraph.compile matchingPenniesProgram.core).sourcePayoffs } ∧
      EventGraph.evalPayoffs? matchingPenniesMachine.payoffs state.1.store =
        some (evalPayoffs
          (ToEventGraph.compile matchingPenniesProgram.core).sourcePayoffs
          terminalEnv) := by
  rcases Machine.compile_sourceStar matchingPenniesProgram state hterminal with
    ⟨terminalEnv, hstar, hpayoff, _agreement⟩
  exact ⟨terminalEnv, hstar, hpayoff⟩

noncomputable instance matchingPenniesFiniteDomains :
    FiniteDomains matchingPenniesProgram where
  context := inferInstanceAs (FiniteVCtx ([] : VCtx TestPlayer simpleExpr))
  program :=
    { proof :=
        .commit inferInstance
          (.commit inferInstance
            (.reveal inferInstance
              (.reveal inferInstance .ret))) }

example : matchingPenniesMachine.information.PerfectRecall :=
  matchingPenniesMachine.perfectRecall

noncomputable example :
    Runtime.DeviationAdequacy matchingPenniesGame.behavioral
      matchingPenniesGame.mixedPure :=
  matchingPenniesProgram.behavioralToMixedPureAdequacy

noncomputable def matchingPenniesNode0 :
    Fin matchingPenniesMachine.graph.nodeCount :=
  ⟨0, by simp [matchingPenniesMachine, Machine.compile,
    Machine.ofCompiled, matchingPenniesProgram, matchingPenniesCore,
    ToEventGraph.compile, ToEventGraph.compileCore,
    ToEventGraph.BuildResult.graph, EventGraph.Graph.nodeCount]⟩

noncomputable def matchingPenniesNode1 :
    Fin matchingPenniesMachine.graph.nodeCount :=
  ⟨1, by simp [matchingPenniesMachine, Machine.compile,
    Machine.ofCompiled, matchingPenniesProgram, matchingPenniesCore,
    ToEventGraph.compile, ToEventGraph.compileCore,
    ToEventGraph.BuildResult.graph, EventGraph.Graph.nodeCount]⟩

noncomputable def matchingPenniesNode2 :
    Fin matchingPenniesMachine.graph.nodeCount :=
  ⟨2, by simp [matchingPenniesMachine, Machine.compile,
    Machine.ofCompiled, matchingPenniesProgram, matchingPenniesCore,
    ToEventGraph.compile, ToEventGraph.compileCore,
    ToEventGraph.BuildResult.graph, EventGraph.Graph.nodeCount]⟩

noncomputable def matchingPenniesNode3 :
    Fin matchingPenniesMachine.graph.nodeCount :=
  ⟨3, by simp [matchingPenniesMachine, Machine.compile,
    Machine.ofCompiled, matchingPenniesProgram, matchingPenniesCore,
    ToEventGraph.compile, ToEventGraph.compileCore,
    ToEventGraph.BuildResult.graph, EventGraph.Graph.nodeCount]⟩

theorem matchingPenniesNode0_prereqs :
    matchingPenniesMachine.graph.prereqs matchingPenniesNode0 = ∅ := by
  decide

theorem matchingPenniesNode1_prereqs :
    matchingPenniesMachine.graph.prereqs matchingPenniesNode1 = ∅ := by
  decide

theorem matchingPenniesNode2_prereqs_ne_empty :
    matchingPenniesMachine.graph.prereqs matchingPenniesNode2 ≠ ∅ := by
  decide

theorem matchingPenniesNode3_prereqs_ne_empty :
    matchingPenniesMachine.graph.prereqs matchingPenniesNode3 ≠ ∅ := by
  decide

theorem matchingPenniesNode0_commit :
    ∃ guard, (matchingPenniesMachine.graph.nodeRow matchingPenniesNode0).sem =
      .commit 0 guard := by
  simp [EventGraph.Graph.nodeRow, matchingPenniesNode0,
    matchingPenniesMachine, Machine.compile, Machine.ofCompiled,
    matchingPenniesProgram, matchingPenniesCore, ToEventGraph.compile,
    ToEventGraph.compileCore, ToEventGraph.BuildResult.graph,
    EventGraph.Graph.nodeCount]

theorem matchingPenniesNode1_commit :
    ∃ guard, (matchingPenniesMachine.graph.nodeRow matchingPenniesNode1).sem =
      .commit 1 guard := by
  simp [EventGraph.Graph.nodeRow, matchingPenniesNode1,
    matchingPenniesMachine, Machine.compile, Machine.ofCompiled,
    matchingPenniesProgram, matchingPenniesCore, ToEventGraph.compile,
    ToEventGraph.compileCore, ToEventGraph.BuildResult.graph,
    EventGraph.Graph.nodeCount]

private theorem not_readyInternalNode_of_commit
    {G : EventGraph.Graph TestPlayer simpleExpr}
    {cfg : EventGraph.Config G} {node : Fin G.nodeCount} {who : TestPlayer}
    (hcommit : ∃ guard, (G.nodeRow node).sem = .commit who guard) :
    ¬ EventGraph.ReadyInternalNode G cfg node := by
  rintro ⟨row, hrow, hinternal, _hready⟩
  have hcanonical := G.nodes_get?_nodeRow node
  have hrowEq : row = G.nodeRow node := by
    exact Option.some.inj (hrow.symm.trans hcanonical)
  subst row
  rcases hcommit with ⟨guard, hcommit⟩
  rw [hcommit] at hinternal
  exact hinternal

private theorem not_ready_initial_of_prereqs_ne_empty
    {node : Fin matchingPenniesMachine.graph.nodeCount}
    (hne : matchingPenniesMachine.graph.prereqs node ≠ ∅) :
    ¬ EventGraph.Ready matchingPenniesMachine.graph
      (EventGraph.Config.initial matchingPenniesMachine.graph) node := by
  intro hready
  apply hne
  apply Finset.Subset.antisymm hready.2
  exact Finset.empty_subset _

example : matchingPenniesGame.execution.BoundedHorizon 4 := by
  rw [← show matchingPenniesMachine.graph.nodeCount = 4 by
    exact matchingPenniesMachine_graph_nodeCount]
  exact matchingPenniesGame.bounded

/-! ## The serialized counterfactual, on a real compiled program

The graph serialization theorems apply to every well-formed live graph. The
checks below instantiate them with matching pennies, whose two players are
ready at the same frontier and admit two distinct execution orders. -/

/-- The runtime matching pennies would get if its frontier were serialized
rather than applied whole. -/
@[reducible] noncomputable def matchingPenniesSerialized : ScheduledSystem TestPlayer :=
  Vegas.EventGraph.serializedSystem matchingPenniesMachine.graph
    matchingPenniesMachine.graphWF matchingPenniesMachine.guardLive

/-- The fixed-order serialized implementation of the same graph. -/
@[reducible] noncomputable def matchingPenniesFixedSerialized :
    ScheduledSystem TestPlayer :=
  Vegas.EventGraph.fixedSerializedSystem matchingPenniesMachine.graph
    matchingPenniesMachine.graphWF matchingPenniesMachine.guardLive

/-- The actual serialized execution protocol, information model, history
utility, and bounded horizon packaged as a game. -/
noncomputable def matchingPenniesSerializedGame :
    Vegas.BoundedGame (Participant TestPlayer) :=
  matchingPenniesMachine.serializedBoundedGame (fun _ => 0)

example :
    matchingPenniesSerializedGame.information.PerfectRecall :=
  matchingPenniesMachine.serializedPerfectRecall

example :
    matchingPenniesSerializedGame.execution.BoundedHorizon
      matchingPenniesMachine.graph.nodeCount :=
  matchingPenniesMachine.serializedBoundedHorizon (fun _ => 0)

/-- Actual serialized histories, not an auxiliary signal game, preserve
source information and payoffs after erasure. -/
theorem matchingPennies_serializedHistory_has_source
    (target : matchingPenniesMachine.serializedExecution.History) :
    ∃ source : matchingPenniesMachine.execution.History,
      source.state = target.state.base ∧
      (∀ who, matchingPenniesMachine.information.infoOf who source.trace =
        matchingPenniesMachine.eraseSerializedPlayerInformation who
          (matchingPenniesMachine.serializedInformation.infoOf
            (.player who) target.trace)) ∧
      ∀ who, matchingPenniesMachine.utility source who =
        matchingPenniesMachine.serializedUtility (fun _ => 0) target (.player who) :=
  matchingPenniesMachine.serializedHistory_has_source target (fun _ => 0)

/-- The real randomized runtime round expands into atomic source histories
with its exact joint law of state and erased player information. -/
theorem matchingPennies_serializedBehavioralRound_expands
    (policies : (who : Participant TestPlayer) →
      matchingPenniesMachine.serializedInformation.BehavioralPolicy who)
    (hterm : ¬ matchingPenniesMachine.serializedExecution.terminal
      matchingPenniesMachine.serializedExecution.init) :
    (matchingPenniesMachine.serializedInformation.runBehavioralFrom policies 1
        matchingPenniesMachine.serializedExecution.initHistory).map
          matchingPenniesMachine.serializedHistorySummary =
      ((matchingPenniesMachine.serializedInformation.behavioralJoint policies
          matchingPenniesMachine.serializedExecution.initHistory.trace hterm).bind
        fun command => matchingPenniesMachine.expandRound
          matchingPenniesMachine.execution.initHistory
          (fun who => command.1 (.player who))
          (matchingPenniesMachine.serializedPlayers_legal command)).map
            matchingPenniesMachine.historySummary :=
  matchingPenniesMachine.serializedBehavioralRound_expands
    matchingPenniesMachine.execution.initHistory []
    matchingPenniesMachine.serializedExecution.initHistory.trace
    (fun _ => rfl) policies hterm

/-- The compiled scheduler may use the complete public matching-pennies state,
but every actual player sees that same state.  It has no private fact to reveal
through the order. -/
example : matchingPenniesSerialized.SchedulerHasNoExtraInformation :=
  Vegas.EventGraph.serializedSystem_schedulerHasNoExtraInformation
    matchingPenniesMachine.graph matchingPenniesMachine.graphWF
    matchingPenniesMachine.guardLive

/-- Replay uses actual matching-pennies runtime policies, not the auxiliary
independent-signal game. Each player's observation projects to the complete
public graph state, so even data-dependent scheduler policies are covered. -/
theorem matchingPennies_randomScheduler_replay
    (schedulers : GameTheory.Math.Probability.FinDist
      (matchingPenniesSerialized.revealingInformation.Policy .scheduler))
    (profile : (who : Participant TestPlayer) →
      matchingPenniesSerialized.revealingInformation.BehavioralPolicy who)
    (fuel : Nat) :
    (schedulers.bind fun scheduler =>
      matchingPenniesSerialized.revealingInformation.runBehavioral
        (matchingPenniesSerialized.fixScheduler scheduler profile) fuel) =
      schedulers.bind fun scheduler =>
        matchingPenniesSerialized.revealingInformation.runBehavioral
          (matchingPenniesSerialized.replayBehavioralProfile scheduler
            (fun _ => Prod.fst) profile) fuel :=
  matchingPenniesSerialized.runMixedScheduler_replay
    schedulers (fun _ => Prod.fst) (fun _ _ => rfl) profile fuel

/-- Both participants really are required to submit at the initial compiled
frontier. -/
theorem matchingPenniesInitial_active (who : TestPlayer) :
    Vegas.EventGraph.ActiveAt matchingPenniesMachine.graph
      (EventGraph.Config.initial matchingPenniesMachine.graph) who := by
  classical
  constructor
  · intro hterminal
    exact (by simpa [EventGraph.Config.initial] using
      hterminal matchingPenniesNode0)
  constructor
  · apply Finset.eq_empty_iff_forall_notMem.mpr
    intro node hnode
    have hinternal := (Finset.mem_filter.mp hnode).2
    fin_cases node
    · apply not_readyInternalNode_of_commit matchingPenniesNode0_commit
      simpa only [matchingPenniesNode0] using hinternal
    · apply not_readyInternalNode_of_commit matchingPenniesNode1_commit
      simpa only [matchingPenniesNode1] using hinternal
    · apply not_ready_initial_of_prereqs_ne_empty
        matchingPenniesNode2_prereqs_ne_empty
      rcases hinternal with ⟨_row, _hrow, _hkind, hready⟩
      simpa only [matchingPenniesNode2] using hready
    · apply not_ready_initial_of_prereqs_ne_empty
        matchingPenniesNode3_prereqs_ne_empty
      rcases hinternal with ⟨_row, _hrow, _hkind, hready⟩
      simpa only [matchingPenniesNode3] using hready
  · unfold EventGraph.activePlayers
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ who, ?_⟩
    fin_cases who
    · refine ⟨matchingPenniesNode0, ?_⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases matchingPenniesNode0_commit with ⟨guard, hsem⟩
      exact ⟨matchingPenniesMachine.graph.nodeRow matchingPenniesNode0,
        guard, matchingPenniesMachine.graph.nodes_get?_nodeRow matchingPenniesNode0,
        hsem, by simp [EventGraph.Ready, EventGraph.Config.initial,
          matchingPenniesNode0_prereqs]⟩
    · refine ⟨matchingPenniesNode1, ?_⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases matchingPenniesNode1_commit with ⟨guard, hsem⟩
      exact ⟨matchingPenniesMachine.graph.nodeRow matchingPenniesNode1,
        guard, matchingPenniesMachine.graph.nodes_get?_nodeRow matchingPenniesNode1,
        hsem, by simp [EventGraph.Ready, EventGraph.Config.initial,
          matchingPenniesNode1_prereqs]⟩

noncomputable def matchingPenniesInitialSchedulingView :
    EventGraph.PublicObservation matchingPenniesMachine.graph :=
  EventGraph.publicObserve matchingPenniesMachine.graph
    (EventGraph.Config.initial matchingPenniesMachine.graph)

theorem matchingPennies_zeroFirst_mem_schedules :
    [0, 1] ∈ matchingPenniesSerialized.schedules
      matchingPenniesInitialSchedulingView := by
  change [0, 1].Nodup ∧ ∀ who : TestPlayer,
    who ∈ [0, 1] ↔ Vegas.EventGraph.ActiveAtView
      matchingPenniesMachine.graph matchingPenniesInitialSchedulingView who
  refine ⟨by decide, ?_⟩
  intro who
  constructor
  · intro _
    exact (Vegas.EventGraph.activeAtView_iff _ _).mpr
      (matchingPenniesInitial_active who)
  · intro _
    fin_cases who <;> simp

theorem matchingPennies_oneFirst_mem_schedules :
    [1, 0] ∈ matchingPenniesSerialized.schedules
      matchingPenniesInitialSchedulingView := by
  change [1, 0].Nodup ∧ ∀ who : TestPlayer,
    who ∈ [1, 0] ↔ Vegas.EventGraph.ActiveAtView
      matchingPenniesMachine.graph matchingPenniesInitialSchedulingView who
  refine ⟨by decide, ?_⟩
  intro who
  constructor
  · intro _
    exact (Vegas.EventGraph.activeAtView_iff _ _).mpr
      (matchingPenniesInitial_active who)
  · intro _
    fin_cases who <;> simp

/-- **The bridge theorem is not vacuous.**

A real compiled Vegas program, serialized, has a scheduler with a genuine choice
to make -- while the same program's compiled protocol resolves its frontier as
one joint action with no scheduler coordinate at all
(`matchingPenniesMachine`'s `toExecutionProtocol`).  The gap the paper describes
is a gap between two runtimes for *this* program, not only between two abstract
possibilities. -/
theorem matchingPenniesSerialized_not_enforcesOrder :
    ¬ matchingPenniesSerialized.EnforcesOrder :=
  Vegas.EventGraph.serializedSystem_not_enforcesOrder
    matchingPenniesMachine.graph matchingPenniesMachine.graphWF
    matchingPenniesMachine.guardLive
    matchingPennies_zeroFirst_mem_schedules
    matchingPennies_oneFirst_mem_schedules (by decide)

/-- Both accepted matching-pennies orders have the same settled graph effect,
even though the public schedule log distinguishes them. -/
theorem matchingPenniesSerialized_effectsCommute :
    matchingPenniesSerialized.EffectsCommute :=
  Vegas.EventGraph.serializedSystem_effectsCommute
    matchingPenniesMachine.graph matchingPenniesMachine.graphWF
    matchingPenniesMachine.guardLive

/-- The compiled matching-pennies runtime genuinely accepts both orders, and
those adversarial choices have the same settled graph effect. -/
theorem matchingPenniesSerialized_adversarial_orders_commute :
    [0, 1] ∈ matchingPenniesSerialized.schedules
        matchingPenniesInitialSchedulingView ∧
      [1, 0] ∈ matchingPenniesSerialized.schedules
        matchingPenniesInitialSchedulingView ∧
      matchingPenniesSerialized.EffectsCommute :=
  ⟨matchingPennies_zeroFirst_mem_schedules,
    matchingPennies_oneFirst_mem_schedules,
    matchingPenniesSerialized_effectsCommute⟩

/-- On the actual compiled matching-pennies frontier, both adversarially
accepted player orders implement the atomic source successor exactly. -/
theorem matchingPennies_both_orders_implement_atomic
    (joint : ∀ who, Option
      (EventGraph.FrontierAction matchingPenniesMachine.graph who))
    (hlegal : matchingPenniesMachine.execution.Legal
      matchingPenniesMachine.execution.init joint) :
    Vegas.EventGraph.applySerializedOrder joint [0, 1]
        matchingPenniesMachine.execution.init =
          EventGraph.applyFrontier matchingPenniesMachine.graph
            matchingPenniesMachine.graphWF
            matchingPenniesMachine.execution.init joint ∧
      Vegas.EventGraph.applySerializedOrder joint [1, 0]
        matchingPenniesMachine.execution.init =
          EventGraph.applyFrontier matchingPenniesMachine.graph
            matchingPenniesMachine.graphWF
            matchingPenniesMachine.execution.init joint := by
  constructor
  · exact Vegas.EventGraph.applySerializedOrder_eq_applyFrontier
      matchingPenniesMachine.graph matchingPenniesMachine.graphWF
      matchingPenniesMachine.guardLive matchingPenniesMachine.execution.init
      joint hlegal matchingPennies_zeroFirst_mem_schedules
  · exact Vegas.EventGraph.applySerializedOrder_eq_applyFrontier
      matchingPenniesMachine.graph matchingPenniesMachine.graphWF
      matchingPenniesMachine.guardLive matchingPenniesMachine.execution.init
      joint hlegal matchingPennies_oneFirst_mem_schedules

/-- Treating an accepted order as an independent public signal does not alter
Nash equilibrium among the matching-pennies players.  Target deviations are
unrestricted functions of that order; the scheduler's utility is arbitrary and
outside the equilibrium assertion. -/
theorem matchingPennies_scheduleSignal_playerNash_iff
    (schedulerUtility :
      List TestPlayer × matchingPenniesGame.behavioral.form.sig.Outcome → ℝ)
    (order : List TestPlayer)
    (_horder : order ∈ matchingPenniesSerialized.schedules
      matchingPenniesInitialSchedulingView)
    (profile : GameTheory.Profile matchingPenniesGame.behavioral.form.sig) :
    Vegas.Participant.IsPlayerNash
        (Vegas.Participant.IndependentSignal.game
          matchingPenniesGame.behavioral (List TestPlayer) schedulerUtility)
        (Vegas.Participant.PlayerDeviationAdequacyOn.compileProfile
          (Vegas.Participant.IndependentSignal.playerDeviationAdequacy
            matchingPenniesGame.behavioral (List TestPlayer) schedulerUtility)
          order profile) ↔
      GameTheory.IsNash matchingPenniesGame.behavioral.form
        (GameTheory.euPreference matchingPenniesGame.behavioral.utility)
        profile :=
  Vegas.Participant.IndependentSignal.isPlayerNash_iff
    matchingPenniesGame.behavioral (List TestPlayer) schedulerUtility
      order profile

/-- Every signal value in the randomized theorem is an order the actual
matching-pennies serializer accepts at its sole strategic frontier. -/
abbrev MatchingPenniesAcceptedOrder :=
  { order : List TestPlayer //
    order ∈ matchingPenniesSerialized.schedules
      matchingPenniesInitialSchedulingView }

/-- In the auxiliary independent-signal game, randomized orders are harmless.
This is distinct from the actual runtime replay theorem. Target deviations may
choose a distinct complete source strategy for every sampled accepted order;
their payoff is an average of ordinary source-deviation payoffs. -/
theorem matchingPennies_randomScheduleSignal_playerNash_iff
    (schedulerUtility : MatchingPenniesAcceptedOrder ×
      matchingPenniesGame.behavioral.form.sig.Outcome → ℝ)
    (orderLaw : GameTheory.Math.Probability.FinDist
      MatchingPenniesAcceptedOrder)
    (profile : GameTheory.Profile matchingPenniesGame.behavioral.form.sig) :
    Vegas.Participant.IsPlayerNash
        (Vegas.Participant.RandomIndependentSignal.game
          matchingPenniesGame.behavioral MatchingPenniesAcceptedOrder
          schedulerUtility)
        (Vegas.Participant.RandomIndependentSignal.compiledProfile
          matchingPenniesGame.behavioral MatchingPenniesAcceptedOrder
          orderLaw profile) ↔
      GameTheory.IsNash matchingPenniesGame.behavioral.form
        (GameTheory.euPreference matchingPenniesGame.behavioral.utility)
        profile :=
  Vegas.Participant.RandomIndependentSignal.isPlayerNash_iff
    matchingPenniesGame.behavioral MatchingPenniesAcceptedOrder
      schedulerUtility orderLaw profile

theorem matchingPenniesFixedSerialized_enforcesOrder :
    matchingPenniesFixedSerialized.EnforcesOrder :=
  Vegas.EventGraph.fixedSerializedSystem_enforcesOrder
    matchingPenniesMachine.graph matchingPenniesMachine.graphWF
    matchingPenniesMachine.guardLive

/-- The paper-facing scheduling boundary instantiated on this compiled program. -/
example :
    (∀ (state : EventGraph.ReachableConfig matchingPenniesMachine.graph)
        (legal : { joint : ∀ who,
            Option (EventGraph.FrontierAction matchingPenniesMachine.graph who) //
          matchingPenniesMachine.execution.Legal state joint }),
        EventGraph.readyInternalNodes matchingPenniesMachine.graph state.1 = ∅ →
          matchingPenniesMachine.execution.step state legal =
            GameTheory.Math.Probability.FinDist.pure
              (EventGraph.applyFrontier matchingPenniesMachine.graph
                matchingPenniesMachine.graphWF state legal.1)) ∧
      (∀ (state : matchingPenniesSerialized.State)
          (legal : { joint //
            matchingPenniesSerialized.toExecutionProtocol.Legal state joint })
          (next : matchingPenniesSerialized.State),
        next ∈ (matchingPenniesSerialized.toExecutionProtocol.step
            state legal).support →
          EventGraph.readyInternalNodes matchingPenniesMachine.graph
            next.base.1 = ∅) ∧
      ¬ matchingPenniesSerialized.EnforcesOrder ∧
      matchingPenniesFixedSerialized.EnforcesOrder :=
  ⟨fun state legal noInternal =>
      EventGraph.toExecutionProtocol_step_eq_pure_applyFrontier
        matchingPenniesMachine.graph matchingPenniesMachine.graphWF
        matchingPenniesMachine.guardLive state legal noInternal,
    fun state legal _next hnext =>
      EventGraph.serializedSystem_step_support_no_internal
        matchingPenniesMachine.graph matchingPenniesMachine.graphWF
        matchingPenniesMachine.guardLive state legal hnext,
    EventGraph.serializedSystem_not_enforcesOrder
      matchingPenniesMachine.graph matchingPenniesMachine.graphWF
      matchingPenniesMachine.guardLive matchingPennies_zeroFirst_mem_schedules
      matchingPennies_oneFirst_mem_schedules (by decide),
    EventGraph.fixedSerializedSystem_enforcesOrder
      matchingPenniesMachine.graph matchingPenniesMachine.graphWF
      matchingPenniesMachine.guardLive⟩

end VegasTests
