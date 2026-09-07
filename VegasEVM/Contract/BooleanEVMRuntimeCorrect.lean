/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasEVM.Contract.BooleanEVMRuntime
import VegasEVM.Contract.ClassicalEVMCodegenCorrect
import VegasEVM.Contract.SimpleEVMActionCorrect

/-!
# Execution correctness of Boolean classical EVM handlers

This layer proves the source-facing handler wrappers against the executable
EVM semantics. The proofs are compositional over resolved local assembly, so
they apply unchanged after checked four-handler linking.
-/

namespace Vegas.Machine.Contract.EVM

noncomputable section

/-- Resolved exact-calldata-size check for a concrete rejection destination.
-/
def calldataSizeEqAssembly (expected rejectDestination : Nat) : Assembly :=
  [ .calldatasize,
    .push (.nat256 expected),
    .eq,
    .iszero,
    .push (.nat32 rejectDestination),
    .jumpi ]

@[simp] theorem calldataSizeEqAssembly_byteLength
    (expected rejectDestination : Nat) :
    (calldataSizeEqAssembly expected rejectDestination).byteLength = 42 := by
  simp [calldataSizeEqAssembly, Assembly.byteLength,
    Instruction.byteLength]

/-- Local-label resolution turns the generated size assertion into its exact
concrete instruction sequence. -/
theorem resolveFrom?_compileCalldataSizeEq
    (whole : LocalAssembly) (base expected reject offset : Nat)
    (hlabel : whole.labelOffset? reject = some offset) :
    whole.resolveFrom? base (compileCalldataSizeEq expected reject) =
      some (calldataSizeEqAssembly expected (base + offset)) := by
  simp [compileCalldataSizeEq, LocalAssembly.resolveFrom?,
    LocalAssembly.resolveItem?, hlabel, calldataSizeEqAssembly]

/-- Exact-size calldata falls through the generated assertion with its stack
and all effects unchanged. The rejection destination is not inspected on this
path. -/
theorem run_calldataSizeEq_accept
    (whole : Assembly) (env : ExecutionEnv) (state : ExecutionState)
    (expected rejectDestination : Nat)
    (hrunning : state.exit = none)
    (hsize : env.calldata.length = expected)
    (hcode : Assembly.CodeAt whole
      (calldataSizeEqAssembly expected rejectDestination) state.pc) :
    run 6 whole env state =
      { state with pc := state.pc + 42 } := by
  apply StraightRun.run_eq ?_ hcode
  simp [StraightRun, calldataSizeEqAssembly, stepInstruction, advance,
    hrunning, hsize, boolWord]
  norm_num [Instruction.byteLength]

/-- A word-addressable calldata value of any other size takes the generated
rejection jump without changing the caller-visible machine effects. -/
theorem run_calldataSizeEq_reject
    (whole : Assembly) (env : ExecutionEnv) (state : ExecutionState)
    (expected rejectDestination : Nat)
    (hrunning : state.exit = none)
    (hexpected : expected < 2 ^ 256)
    (hcalldata : env.calldata.length < 2 ^ 256)
    (hsize : env.calldata.length ≠ expected)
    (hdestination : rejectDestination < 2 ^ 32)
    (hcode : Assembly.CodeAt whole
      (calldataSizeEqAssembly expected rejectDestination) state.pc)
    (htarget : Assembly.CodeAt whole [.jumpdest] rejectDestination) :
    run 6 whole env state =
      { state with pc := rejectDestination } := by
  let setup : Assembly :=
    [ .calldatasize,
      .push (.nat256 expected),
      .eq,
      .iszero,
      .push (.nat32 rejectDestination) ]
  let beforeJump : ExecutionState :=
    { state with
      pc := state.pc + setup.byteLength
      stack := (PushData.nat32 rejectDestination).value :: 1 :: state.stack }
  have hwordNe :
      BitVec.ofNat 256 env.calldata.length ≠ BitVec.ofNat 256 expected := by
    intro heq
    have hnat := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_ofNat] at hnat
    rw [Nat.mod_eq_of_lt hcalldata,
      Nat.mod_eq_of_lt hexpected] at hnat
    exact hsize hnat
  have hdecomp : calldataSizeEqAssembly expected rejectDestination =
      setup ++ [.jumpi] := by
    rfl
  rw [hdecomp] at hcode
  have hsetup := hcode.left
  have hjump := hcode.right
  have hstraight : StraightRun whole env setup state beforeJump := by
    simp [StraightRun, setup, beforeJump, stepInstruction, advance,
      hrunning, hwordNe, boolWord]
    norm_num [Assembly.byteLength, Instruction.byteLength]
  have hrunSetup : run setup.length whole env state = beforeJump :=
    hstraight.run_eq hsetup
  have hbeforeRunning : beforeJump.exit = none := by
    simp [beforeJump, hrunning]
  have hjump' : Assembly.CodeAt whole [.jumpi] beforeJump.pc := by
    simpa [beforeJump] using hjump
  have hrunJump : run 1 whole env beforeJump =
      { state with pc := rejectDestination } := by
    simpa [beforeJump] using
      run_guardedJump rejectDestination state.stack hbeforeRunning
        hdestination (by simp [beforeJump]) hjump' htarget
  rw [show 6 = setup.length + 1 by simp [setup], run_add,
    hrunSetup, hrunJump]

/-- Resolved comparison for one canonical node route. -/
def nodeRouteAssembly (nodeOffset node rejectDestination : Nat) : Assembly :=
  loadCalldataWord nodeOffset ++
    [ .push (.nat256 node),
      .eq,
      .push (.nat32 rejectDestination),
      .jumpi ]

@[simp] theorem nodeRouteAssembly_byteLength
    (nodeOffset node rejectDestination : Nat) :
    (nodeRouteAssembly nodeOffset node rejectDestination).byteLength = 74 := by
  simp [nodeRouteAssembly, loadCalldataWord, Assembly.byteLength,
    Instruction.byteLength]

/-- Local-label resolution turns one generated node comparison into its
concrete absolute-jump sequence. -/
theorem resolveFrom?_compileNodeRoute
    (whole : LocalAssembly) (base nodeOffset node target offset : Nat)
    (hlabel : whole.labelOffset? target = some offset) :
    whole.resolveFrom? base (compileNodeRoute nodeOffset node target) =
      some (nodeRouteAssembly nodeOffset node (base + offset)) := by
  simp [compileNodeRoute, LocalAssembly.resolveFrom?_append,
    LocalAssembly.resolveFrom?, LocalAssembly.resolveItem?, hlabel,
    nodeRouteAssembly]

/-- A nonmatching node word falls through one generated routing comparison
without changing the stack or effects. -/
theorem run_nodeRoute_miss
    (whole : Assembly) (env : ExecutionEnv) (state : ExecutionState)
    (nodeOffset node destination : Nat)
    (hrunning : state.exit = none)
    (hoffset : nodeOffset < 2 ^ 256)
    (hmiss : calldataLoad env.calldata nodeOffset ≠
      BitVec.ofNat 256 node)
    (hcode : Assembly.CodeAt whole
      (nodeRouteAssembly nodeOffset node destination) state.pc) :
    run 6 whole env state =
      { state with pc := state.pc + 74 } := by
  have hoffsetMod : nodeOffset % 2 ^ 256 = nodeOffset :=
    Nat.mod_eq_of_lt hoffset
  norm_num at hoffsetMod
  apply StraightRun.run_eq ?_ hcode
  simp [StraightRun, nodeRouteAssembly, loadCalldataWord,
    stepInstruction, advance, hrunning,
    Nat.mod_eq_of_lt hoffsetMod, hmiss, boolWord]
  norm_num [Instruction.byteLength]

/-- A matching node word takes its valid local-label destination and consumes
all routing temporaries. -/
theorem run_nodeRoute_hit
    (whole : Assembly) (env : ExecutionEnv) (state : ExecutionState)
    (nodeOffset node destination : Nat)
    (hrunning : state.exit = none)
    (hoffset : nodeOffset < 2 ^ 256)
    (hload : calldataLoad env.calldata nodeOffset = BitVec.ofNat 256 node)
    (hdestination : destination < 2 ^ 32)
    (hcode : Assembly.CodeAt whole
      (nodeRouteAssembly nodeOffset node destination) state.pc)
    (htarget : Assembly.CodeAt whole [.jumpdest] destination) :
    run 6 whole env state =
      { state with pc := destination } := by
  have hoffsetMod : nodeOffset % 2 ^ 256 = nodeOffset :=
    Nat.mod_eq_of_lt hoffset
  norm_num at hoffsetMod
  let setup : Assembly :=
    loadCalldataWord nodeOffset ++
      [ .push (.nat256 node),
        .eq,
        .push (.nat32 destination) ]
  let beforeJump : ExecutionState :=
    { state with
      pc := state.pc + setup.byteLength
      stack := (PushData.nat32 destination).value :: 1 :: state.stack }
  have hdecomp : nodeRouteAssembly nodeOffset node destination =
      setup ++ [.jumpi] := by
    simp [nodeRouteAssembly, setup, List.append_assoc]
  rw [hdecomp] at hcode
  have hsetup := hcode.left
  have hjump := hcode.right
  have hstraight : StraightRun whole env setup state beforeJump := by
    simp [StraightRun, setup, beforeJump, loadCalldataWord,
      stepInstruction, advance, hrunning,
      Nat.mod_eq_of_lt hoffsetMod, hload, boolWord]
    norm_num [Assembly.byteLength, Instruction.byteLength]
  have hrunSetup : run setup.length whole env state = beforeJump :=
    hstraight.run_eq hsetup
  have hbeforeRunning : beforeJump.exit = none := by
    simp [beforeJump, hrunning]
  have hjump' : Assembly.CodeAt whole [.jumpi] beforeJump.pc := by
    simpa [beforeJump] using hjump
  have hrunJump : run 1 whole env beforeJump =
      { state with pc := destination } := by
    simpa [beforeJump] using
      run_guardedJump destination state.stack hbeforeRunning hdestination
        (by simp [beforeJump]) hjump' htarget
  rw [show 6 = setup.length + 1 by simp [setup, loadCalldataWord],
    run_add, hrunSetup, hrunJump]

/-- Resolved caller-authentication check. -/
def callerEqAssembly (expected : AddressWord) (rejectDestination : Nat) :
    Assembly :=
  [ .caller,
    .push (.address expected),
    .eq,
    .iszero,
    .push (.nat32 rejectDestination),
    .jumpi ]

@[simp] theorem callerEqAssembly_byteLength
    (expected : AddressWord) (rejectDestination : Nat) :
    (callerEqAssembly expected rejectDestination).byteLength = 30 := by
  simp [callerEqAssembly, Assembly.byteLength, Instruction.byteLength]

theorem resolveFrom?_compileCallerEq
    (whole : LocalAssembly) (base : Nat) (expected : AddressWord)
    (reject offset : Nat)
    (hlabel : whole.labelOffset? reject = some offset) :
    whole.resolveFrom? base (compileCallerEq expected reject) =
      some (callerEqAssembly expected (base + offset)) := by
  simp [compileCallerEq, LocalAssembly.resolveFrom?,
    LocalAssembly.resolveItem?, hlabel, callerEqAssembly]

/-- The expected native sender falls through authentication without changing
the stack or effects. -/
theorem run_callerEq_accept
    (whole : Assembly) (env : ExecutionEnv) (state : ExecutionState)
    (expected : AddressWord) (destination : Nat)
    (hrunning : state.exit = none) (hcaller : env.caller = expected)
    (hcode : Assembly.CodeAt whole
      (callerEqAssembly expected destination) state.pc) :
    run 6 whole env state =
      { state with pc := state.pc + 30 } := by
  apply StraightRun.run_eq ?_ hcode
  simp [StraightRun, callerEqAssembly, stepInstruction, advance,
    hrunning, hcaller, boolWord]
  norm_num [Instruction.byteLength]

/-- Every other native sender takes the certified authentication rejection
jump. -/
theorem run_callerEq_reject
    (whole : Assembly) (env : ExecutionEnv) (state : ExecutionState)
    (expected : AddressWord) (destination : Nat)
    (hrunning : state.exit = none) (hcaller : env.caller ≠ expected)
    (hdestination : destination < 2 ^ 32)
    (hcode : Assembly.CodeAt whole
      (callerEqAssembly expected destination) state.pc)
    (htarget : Assembly.CodeAt whole [.jumpdest] destination) :
    run 6 whole env state =
      { state with pc := destination } := by
  let setup : Assembly :=
    [ .caller,
      .push (.address expected),
      .eq,
      .iszero,
      .push (.nat32 destination) ]
  let beforeJump : ExecutionState :=
    { state with
      pc := state.pc + setup.byteLength
      stack := (PushData.nat32 destination).value :: 1 :: state.stack }
  have hwordNe : BitVec.setWidth 256 env.caller ≠
      BitVec.setWidth 256 expected := by
    intro heq
    apply hcaller
    have hnarrow := congrArg (BitVec.setWidth 160) heq
    simpa using hnarrow
  have hdecomp : callerEqAssembly expected destination =
      setup ++ [.jumpi] := by
    rfl
  rw [hdecomp] at hcode
  have hsetup := hcode.left
  have hjump := hcode.right
  have hstraight : StraightRun whole env setup state beforeJump := by
    simp [StraightRun, setup, beforeJump, stepInstruction, advance,
      hrunning, hwordNe, boolWord]
    norm_num [Assembly.byteLength, Instruction.byteLength]
  have hrunSetup : run setup.length whole env state = beforeJump :=
    hstraight.run_eq hsetup
  have hbeforeRunning : beforeJump.exit = none := by
    simp [beforeJump, hrunning]
  have hjump' : Assembly.CodeAt whole [.jumpi] beforeJump.pc := by
    simpa [beforeJump] using hjump
  have hrunJump : run 1 whole env beforeJump =
      { state with pc := destination } := by
    simpa [beforeJump] using
      run_guardedJump destination state.stack hbeforeRunning hdestination
        (by simp [beforeJump]) hjump' htarget
  rw [show 6 = setup.length + 1 by simp [setup], run_add,
    hrunSetup, hrunJump]

/-- Resolved equality assertion for an arbitrary calldata word. -/
def calldataWordEqAssembly (offset : Nat) (expected : Word)
    (rejectDestination : Nat) : Assembly :=
  loadCalldataWord offset ++
    [ .push (.word expected),
      .eq,
      .iszero,
      .push (.nat32 rejectDestination),
      .jumpi ]

@[simp] theorem calldataWordEqAssembly_byteLength
    (offset : Nat) (expected : Word) (rejectDestination : Nat) :
    (calldataWordEqAssembly offset expected rejectDestination).byteLength =
      75 := by
  simp [calldataWordEqAssembly, loadCalldataWord, Assembly.byteLength,
    Instruction.byteLength]

theorem resolveFrom?_compileCalldataWordEq
    (whole : LocalAssembly) (base offset : Nat) (expected : Word)
    (reject labelOffset : Nat)
    (hlabel : whole.labelOffset? reject = some labelOffset) :
    whole.resolveFrom? base (compileCalldataWordEq offset expected reject) =
      some (calldataWordEqAssembly offset expected
        (base + labelOffset)) := by
  simp [compileCalldataWordEq, LocalAssembly.resolveFrom?_append,
    LocalAssembly.resolveFrom?, LocalAssembly.resolveItem?, hlabel,
    calldataWordEqAssembly]

/-- An equal calldata word falls through the assertion. -/
theorem run_calldataWordEq_accept
    (whole : Assembly) (env : ExecutionEnv) (state : ExecutionState)
    (offset : Nat) (expected : Word) (destination : Nat)
    (hrunning : state.exit = none) (hoffset : offset < 2 ^ 256)
    (hload : calldataLoad env.calldata offset = expected)
    (hcode : Assembly.CodeAt whole
      (calldataWordEqAssembly offset expected destination) state.pc) :
    run 7 whole env state =
      { state with pc := state.pc + 75 } := by
  have hoffsetMod : offset % 2 ^ 256 = offset :=
    Nat.mod_eq_of_lt hoffset
  norm_num at hoffsetMod
  apply StraightRun.run_eq ?_ hcode
  simp [StraightRun, calldataWordEqAssembly, loadCalldataWord,
    stepInstruction, advance, hrunning,
    Nat.mod_eq_of_lt hoffsetMod, hload, boolWord]
  norm_num [Instruction.byteLength]

/-- A different calldata word takes the certified assertion-rejection jump.
-/
theorem run_calldataWordEq_reject
    (whole : Assembly) (env : ExecutionEnv) (state : ExecutionState)
    (offset : Nat) (expected : Word) (destination : Nat)
    (hrunning : state.exit = none) (hoffset : offset < 2 ^ 256)
    (hload : calldataLoad env.calldata offset ≠ expected)
    (hdestination : destination < 2 ^ 32)
    (hcode : Assembly.CodeAt whole
      (calldataWordEqAssembly offset expected destination) state.pc)
    (htarget : Assembly.CodeAt whole [.jumpdest] destination) :
    run 7 whole env state =
      { state with pc := destination } := by
  have hoffsetMod : offset % 2 ^ 256 = offset :=
    Nat.mod_eq_of_lt hoffset
  norm_num at hoffsetMod
  let setup : Assembly :=
    loadCalldataWord offset ++
      [ .push (.word expected),
        .eq,
        .iszero,
        .push (.nat32 destination) ]
  let beforeJump : ExecutionState :=
    { state with
      pc := state.pc + setup.byteLength
      stack := (PushData.nat32 destination).value :: 1 :: state.stack }
  have hdecomp : calldataWordEqAssembly offset expected destination =
      setup ++ [.jumpi] := by
    simp [calldataWordEqAssembly, setup, List.append_assoc]
  rw [hdecomp] at hcode
  have hsetup := hcode.left
  have hjump := hcode.right
  have hstraight : StraightRun whole env setup state beforeJump := by
    simp [StraightRun, setup, beforeJump, loadCalldataWord,
      stepInstruction, advance, hrunning,
      Nat.mod_eq_of_lt hoffsetMod, hload, boolWord]
    norm_num [Assembly.byteLength, Instruction.byteLength]
  have hrunSetup : run setup.length whole env state = beforeJump :=
    hstraight.run_eq hsetup
  have hbeforeRunning : beforeJump.exit = none := by
    simp [beforeJump, hrunning]
  have hjump' : Assembly.CodeAt whole [.jumpi] beforeJump.pc := by
    simpa [beforeJump] using hjump
  have hrunJump : run 1 whole env beforeJump =
      { state with pc := destination } := by
    simpa [beforeJump] using
      run_guardedJump destination state.stack hbeforeRunning hdestination
        (by simp [beforeJump]) hjump' htarget
  rw [show 7 = setup.length + 1 by simp [setup, loadCalldataWord],
    run_add, hrunSetup, hrunJump]

/-- Resolved canonical-Boolean action validation. -/
def canonicalBoolActionAssembly (rejectDestination : Nat) : Assembly :=
  playerActionWord ++
    [ .dup ⟨0, by decide⟩,
      .push (.one (byte 0)),
      .eq,
      .dup ⟨1, by decide⟩,
      .push (.one (byte 1)),
      .eq,
      .or,
      .iszero,
      .push (.nat32 rejectDestination),
      .jumpi ]

@[simp] theorem canonicalBoolActionAssembly_byteLength
    (rejectDestination : Nat) :
    (canonicalBoolActionAssembly rejectDestination).byteLength = 50 := by
  simp [canonicalBoolActionAssembly, playerActionWord, loadCalldataWord,
    Assembly.byteLength, Instruction.byteLength]

theorem resolveFrom?_compileCanonicalBoolAction
    (whole : LocalAssembly) (base reject offset : Nat)
    (hlabel : whole.labelOffset? reject = some offset) :
    whole.resolveFrom? base (compileCanonicalBoolAction reject) =
      some (canonicalBoolActionAssembly (base + offset)) := by
  simp [compileCanonicalBoolAction, LocalAssembly.resolveFrom?_append,
    LocalAssembly.resolveFrom?, LocalAssembly.resolveItem?, hlabel,
    canonicalBoolActionAssembly]

/-- A canonical Boolean calldata word falls through validation and remains on
the stack as the action value consumed by later guard/write code. -/
theorem run_canonicalBoolAction_accept
    (whole : Assembly) (env : ExecutionEnv) (state : ExecutionState)
    (value : Bool) (destination : Nat)
    (hrunning : state.exit = none)
    (hload : calldataLoad env.calldata 68 = encodeBool value)
    (hcode : Assembly.CodeAt whole
      (canonicalBoolActionAssembly destination) state.pc) :
    run 12 whole env state =
      { state with
        pc := state.pc + 50
        stack := encodeBool value :: state.stack } := by
  apply StraightRun.run_eq ?_ hcode
  cases value <;>
    simp [StraightRun, canonicalBoolActionAssembly, playerActionWord,
      loadCalldataWord, stepInstruction, advance, hrunning, hload,
      encodeBool, boolWord] <;>
    norm_num [Instruction.byteLength]

/-- A noncanonical action word takes the certified rejection jump while
retaining the rejected word beneath the consumed jump condition. -/
theorem run_canonicalBoolAction_reject
    (whole : Assembly) (env : ExecutionEnv) (state : ExecutionState)
    (value : Word) (destination : Nat)
    (hrunning : state.exit = none)
    (hload : calldataLoad env.calldata 68 = value)
    (hzero : value ≠ 0) (hone : value ≠ 1)
    (hdestination : destination < 2 ^ 32)
    (hcode : Assembly.CodeAt whole
      (canonicalBoolActionAssembly destination) state.pc)
    (htarget : Assembly.CodeAt whole [.jumpdest] destination) :
    run 12 whole env state =
      { state with pc := destination, stack := value :: state.stack } := by
  let setup : Assembly :=
    playerActionWord ++
      [ .dup ⟨0, by decide⟩,
        .push (.one (byte 0)),
        .eq,
        .dup ⟨1, by decide⟩,
        .push (.one (byte 1)),
        .eq,
        .or,
        .iszero,
        .push (.nat32 destination) ]
  let beforeJump : ExecutionState :=
    { state with
      pc := state.pc + setup.byteLength
      stack := (PushData.nat32 destination).value :: 1 ::
        value :: state.stack }
  have hzeroWord : value ≠ (0#256) := hzero
  have honeWord : value ≠ (1#256) := hone
  have hdecomp : canonicalBoolActionAssembly destination =
      setup ++ [.jumpi] := by
    simp [canonicalBoolActionAssembly, setup, List.append_assoc]
  rw [hdecomp] at hcode
  have hsetup := hcode.left
  have hjump := hcode.right
  have hstraight : StraightRun whole env setup state beforeJump := by
    simp [StraightRun, setup, beforeJump, playerActionWord,
      loadCalldataWord, stepInstruction, advance, hrunning, hload,
      hzeroWord, honeWord, boolWord]
    norm_num [Assembly.byteLength, Instruction.byteLength]
  have hrunSetup : run setup.length whole env state = beforeJump :=
    hstraight.run_eq hsetup
  have hbeforeRunning : beforeJump.exit = none := by
    simp [beforeJump, hrunning]
  have hjump' : Assembly.CodeAt whole [.jumpi] beforeJump.pc := by
    simpa [beforeJump] using hjump
  have hrunJump : run 1 whole env beforeJump =
      { state with pc := destination, stack := value :: state.stack } := by
    simpa [beforeJump] using
      run_guardedJump destination (value :: state.stack) hbeforeRunning
        hdestination (by simp [beforeJump]) hjump' htarget
  rw [show 12 = setup.length + 1 by
      simp [setup, playerActionWord, loadCalldataWord],
    run_add, hrunSetup, hrunJump]

/-- Concrete accepted-path assembly produced for a Boolean player commit once
the retained guard has been lowered. -/
def playerCommitRealizationAssembly (expectedPlayer : Word)
    (expectedCaller : AddressWord) (rejectDestination : Nat)
    (guardCode : Assembly) : Assembly :=
  calldataWordEqAssembly 4 expectedPlayer rejectDestination ++
    callerEqAssembly expectedCaller rejectDestination ++
    canonicalBoolActionAssembly rejectDestination ++ guardCode ++
    [.iszero, .push (.nat32 rejectDestination), .jumpi]

@[simp] theorem playerCommitRealizationAssembly_byteLength
    (expectedPlayer : Word) (expectedCaller : AddressWord)
    (rejectDestination : Nat) (guardCode : Assembly) :
    (playerCommitRealizationAssembly expectedPlayer expectedCaller
      rejectDestination guardCode).byteLength =
      162 + guardCode.byteLength := by
  simp only [playerCommitRealizationAssembly, Assembly.byteLength_append,
    calldataWordEqAssembly_byteLength, callerEqAssembly_byteLength,
    canonicalBoolActionAssembly_byteLength]
  norm_num [Assembly.byteLength, Instruction.byteLength]
  omega

/-- A correctly framed and authenticated canonical action whose compiled
guard evaluates to true falls through realization with exactly that action
word on the stack. -/
theorem run_playerCommitRealization_accept
    (pre : BoolExprPrecondition)
    (expectedPlayer : Word) (expectedCaller : AddressWord)
    (rejectDestination : Nat) (guardCode : Assembly)
    (guardCorrect : BoolExprCorrect pre true guardCode)
    (whole : Assembly) (env : ExecutionEnv) (state : ExecutionState)
    (value : Bool) (rest : List Word)
    (hpre : pre env state.storage)
    (hrunning : state.exit = none)
    (hstack : state.stack = rest)
    (hplayer : calldataLoad env.calldata 4 = expectedPlayer)
    (hcaller : env.caller = expectedCaller)
    (haction : calldataLoad env.calldata 68 = encodeBool value)
    (hcode : Assembly.CodeAt whole
      (playerCommitRealizationAssembly expectedPlayer expectedCaller
        rejectDestination guardCode) state.pc) :
    run (28 + guardCode.length) whole env state =
      { state with
        pc := state.pc + 162 + guardCode.byteLength
        stack := encodeBool value :: rest } := by
  let playerCode := calldataWordEqAssembly 4 expectedPlayer rejectDestination
  let callerCode := callerEqAssembly expectedCaller rejectDestination
  let actionCode := canonicalBoolActionAssembly rejectDestination
  let guardTail : Assembly :=
    [.iszero, .push (.nat32 rejectDestination), .jumpi]
  have hdecomp :
      playerCommitRealizationAssembly expectedPlayer expectedCaller
          rejectDestination guardCode =
        playerCode ++ (callerCode ++
          (actionCode ++ (guardCode ++ guardTail))) := by
    simp [playerCommitRealizationAssembly, playerCode, callerCode, actionCode,
      guardTail, List.append_assoc]
  rw [hdecomp] at hcode
  have hplayerCode : Assembly.CodeAt whole playerCode state.pc :=
    hcode.left
  let afterPlayer : ExecutionState :=
    { state with pc := state.pc + 75 }
  have hrunPlayer : run 7 whole env state = afterPlayer := by
    have hrun := run_calldataWordEq_accept whole env state 4 expectedPlayer
      rejectDestination hrunning (by norm_num) hplayer hplayerCode
    exact hrun
  have hafterPlayerRunning : afterPlayer.exit = none := by
    simp [afterPlayer, hrunning]
  have hcallerCode : Assembly.CodeAt whole callerCode afterPlayer.pc := by
    have := hcode.right.left
    simpa [afterPlayer, playerCode] using this
  let afterCaller : ExecutionState :=
    { state with pc := state.pc + 105 }
  have hrunCaller : run 6 whole env afterPlayer = afterCaller := by
    have hrun := run_callerEq_accept whole env afterPlayer expectedCaller
      rejectDestination hafterPlayerRunning hcaller hcallerCode
    simpa [afterCaller, afterPlayer] using hrun
  have hafterCallerRunning : afterCaller.exit = none := by
    simp [afterCaller, hrunning]
  have hactionCode : Assembly.CodeAt whole actionCode afterCaller.pc := by
    have := hcode.right.right.left
    simpa [afterCaller, playerCode, callerCode] using this
  let afterAction : ExecutionState :=
    { state with
      pc := state.pc + 155
      stack := encodeBool value :: rest }
  have hrunAction : run 12 whole env afterCaller = afterAction := by
    have hrun := run_canonicalBoolAction_accept whole env afterCaller value
      rejectDestination hafterCallerRunning haction hactionCode
    simpa [afterAction, afterCaller, hstack] using hrun
  have hafterActionRunning : afterAction.exit = none := by
    simp [afterAction, hrunning]
  have hguardCode : Assembly.CodeAt whole guardCode afterAction.pc := by
    have := hcode.right.right.right.left
    simpa [afterAction, playerCode, callerCode, actionCode] using this
  let afterGuard : ExecutionState :=
    { state with
      pc := state.pc + 155 + guardCode.byteLength
      stack := encodeBool true :: encodeBool value :: rest }
  have hrunGuard : run guardCode.length whole env afterAction = afterGuard := by
    have hrun := guardCorrect whole env afterAction
      (encodeBool value :: rest) (by simpa [afterAction] using hpre)
      hafterActionRunning rfl hguardCode
    simpa [afterGuard, afterAction] using hrun
  have hafterGuardRunning : afterGuard.exit = none := by
    simp [afterGuard, hrunning]
  have htailCode : Assembly.CodeAt whole guardTail afterGuard.pc := by
    have := hcode.right.right.right.right
    simpa [afterGuard, playerCode, callerCode, actionCode] using this
  let afterTail : ExecutionState :=
    { state with
      pc := state.pc + 162 + guardCode.byteLength
      stack := encodeBool value :: rest }
  have hrunTail : run 3 whole env afterGuard = afterTail := by
    apply StraightRun.run_eq ?_ htailCode
    simp [StraightRun, guardTail, afterTail, afterGuard, stepInstruction,
      advance, hrunning, boolWord, encodeBool]
    norm_num [Instruction.byteLength]
    omega
  rw [show 28 + guardCode.length =
      7 + (6 + (12 + (guardCode.length + 3))) by omega,
    run_add, hrunPlayer, run_add, hrunCaller, run_add, hrunAction,
    run_add, hrunGuard, hrunTail]

/-- The accepted player realization contract composes with structural
readiness checks and canonical action writes into a complete successful graph
transition. -/
theorem run_playerCompletingBlock_accept
    {Player : Type} [DecidableEq Player]
    {program : Program Player simpleExpr}
    (fits : ClassicalStorageFitsWord program)
    (usesBool : UsesOnlyBoolStorage program)
    (codec : StorageCodec program) (words : WireCodec codec.Word Word)
    (canonical : CanonicalRepresentation program codec words)
    (nodes : WireCodec (Fin program.graph.nodeCount) Word)
    (cfg : EventGraph.Config program.graph)
    (pending : Option (Fin program.graph.nodeCount))
    (action : ClassicalActionIR program)
    (ready : EventGraph.Ready program.graph cfg action.node)
    (pre : BoolExprPrecondition)
    (expectedPlayer : Word) (expectedCaller : AddressWord)
    (rejectDestination : Nat) (guardCode : Assembly)
    (guardCorrect : BoolExprCorrect pre true guardCode)
    (whole : Assembly) (env : ExecutionEnv) (state : ExecutionState)
    (value : Bool)
    (hpre : pre env state.storage)
    (hrunning : state.exit = none)
    (hstorage : state.storage =
      encodeClassicalSnapshot codec words nodes
        { graph := EventGraph.StateSnapshot.ofConfig cfg, pending := pending })
    (hplayer : calldataLoad env.calldata 4 = expectedPlayer)
    (hcaller : env.caller = expectedCaller)
    (haction : calldataLoad env.calldata 68 = encodeBool value)
    (hcode : Assembly.CodeAt whole
      (classicalCompletingBlockAssembly rejectDestination action
        (playerCommitRealizationAssembly expectedPlayer expectedCaller
          rejectDestination guardCode)) state.pc) :
    run (7 * action.checks.length + (28 + guardCode.length) + 9)
        whole env state =
      { state with
        pc := state.pc +
            (classicalStorageChecksAssembly rejectDestination
              action.checks).byteLength +
            (playerCommitRealizationAssembly expectedPlayer expectedCaller
              rejectDestination guardCode).byteLength +
            (classicalActionWritesAssembly action).byteLength
        storage := encodeClassicalSnapshot codec words nodes
          { graph := EventGraph.StateSnapshot.ofConfig
              (cfg.completeNode action.node { ty := .bool, value := value })
            pending := pending }
        exit := some .stopped } := by
  let checksCode :=
    classicalStorageChecksAssembly rejectDestination action.checks
  have hcode' : Assembly.CodeAt whole
      (checksCode ++
        (playerCommitRealizationAssembly expectedPlayer expectedCaller
          rejectDestination guardCode ++
          (classicalActionWritesAssembly action ++ [.stop])))
      state.pc := by
    simpa [classicalCompletingBlockAssembly, checksCode,
      List.append_assoc] using hcode
  have hrealizeCode : Assembly.CodeAt whole
      (playerCommitRealizationAssembly expectedPlayer expectedCaller
        rejectDestination guardCode)
      (state.pc + checksCode.byteLength) := hcode'.right.left
  have hrealize :
      run (28 + guardCode.length) whole env
          { state with pc := state.pc + checksCode.byteLength } =
        { state with
          pc := state.pc + checksCode.byteLength +
            (playerCommitRealizationAssembly expectedPlayer expectedCaller
              rejectDestination guardCode).byteLength
          stack := encodeBool value :: state.stack } := by
    have hrun := run_playerCommitRealization_accept pre expectedPlayer
      expectedCaller rejectDestination guardCode guardCorrect whole env
      { state with pc := state.pc + checksCode.byteLength } value state.stack
      hpre hrunning rfl hplayer hcaller haction
      hrealizeCode
    simpa only [playerCommitRealizationAssembly_byteLength,
      Nat.add_assoc] using hrun
  exact run_classicalCompletingBlock_completeBool fits usesBool codec words
    canonical nodes cfg pending action ready whole env state rejectDestination
    (playerCommitRealizationAssembly expectedPlayer expectedCaller
      rejectDestination guardCode)
    (28 + guardCode.length) value hrunning hstorage hrealize hcode

/-- Resolved standard empty-data rejection block. -/
def rejectBlockAssembly : Assembly :=
  [ .jumpdest,
    .push (.one (byte 0)),
    .push (.one (byte 0)),
    .revert ]

@[simp] theorem rejectBlockAssembly_byteLength :
    rejectBlockAssembly.byteLength = 6 := by
  simp [rejectBlockAssembly, Assembly.byteLength, Instruction.byteLength]

@[simp] theorem resolveFrom?_classicalRejectBlock
    (whole : LocalAssembly) (base reject : Nat) :
    whole.resolveFrom? base (classicalRejectBlock reject) =
      some rejectBlockAssembly := by
  rfl

/-- Entering the standard rejection label produces an empty-data revert and
does not mutate memory, storage, or logs. -/
theorem run_rejectBlock
    (whole : Assembly) (env : ExecutionEnv) (state : ExecutionState)
    (hrunning : state.exit = none)
    (hcode : Assembly.CodeAt whole rejectBlockAssembly state.pc) :
    run 4 whole env state =
      { state with
        pc := state.pc + 5
        exit := some (.reverted []) } := by
  let setup : Assembly :=
    [ .jumpdest,
      .push (.one (byte 0)),
      .push (.one (byte 0)) ]
  let beforeRevert : ExecutionState :=
    { state with
      pc := state.pc + setup.byteLength
      stack := 0 :: 0 :: state.stack }
  have hdecomp : rejectBlockAssembly = setup ++ [.revert] := by
    rfl
  rw [hdecomp] at hcode
  have hsetup := hcode.left
  have hrevert := hcode.right
  have hstraight : StraightRun whole env setup state beforeRevert := by
    simp [StraightRun, setup, beforeRevert, stepInstruction, advance,
      hrunning]
    norm_num [Assembly.byteLength, Instruction.byteLength]
  have hrunSetup : run setup.length whole env state = beforeRevert :=
    hstraight.run_eq hsetup
  have hbeforeRunning : beforeRevert.exit = none := by
    simp [beforeRevert, hrunning]
  have hrevert' : Assembly.CodeAt whole [.revert] beforeRevert.pc := by
    simpa [beforeRevert] using hrevert
  have hrunRevert : run 1 whole env beforeRevert =
      { state with
        pc := state.pc + 5
        exit := some (.reverted []) } := by
    rw [run_succ_of_codeAt 0 hbeforeRunning hrevert']
    simp [run, stepInstruction, beforeRevert, setup, readMemory]
    norm_num [Assembly.byteLength, Instruction.byteLength]
  rw [show 4 = setup.length + 1 by simp [setup], run_add,
    hrunSetup, hrunRevert]

/-- Two consecutive canonical `PUSH value; PUSH key; SSTORE` operations. -/
def storagePairAssembly (firstValue firstKey secondValue secondKey : PushData) :
    Assembly :=
  [ .push firstValue, .push firstKey, .sstore,
    .push secondValue, .push secondKey, .sstore ]

/-- Execute a pair of structural storage writes in source order. -/
theorem run_storagePair
    (whole : Assembly) (env : ExecutionEnv) (state : ExecutionState)
    (firstValue firstKey secondValue secondKey : PushData)
    (hrunning : state.exit = none)
    (hcode : Assembly.CodeAt whole
      (storagePairAssembly firstValue firstKey secondValue secondKey)
      state.pc) :
    run 6 whole env state =
      { state with
        pc := state.pc +
          (storagePairAssembly firstValue firstKey secondValue secondKey).byteLength
        storage := Function.update
          (Function.update state.storage firstKey.value.toNat firstValue.value)
          secondKey.value.toNat secondValue.value } := by
  let first : Assembly :=
    [.push firstValue, .push firstKey, .sstore]
  let second : Assembly :=
    [.push secondValue, .push secondKey, .sstore]
  have hdecomp :
      storagePairAssembly firstValue firstKey secondValue secondKey =
        first ++ second := by
    rfl
  rw [hdecomp] at hcode
  have hfirst := hcode.left
  have hsecond := hcode.right
  let afterFirst : ExecutionState :=
    { state with
      pc := state.pc + first.byteLength
      storage := Function.update state.storage firstKey.value.toNat
        firstValue.value }
  have hrunFirst : run 3 whole env state = afterFirst := by
    have hrun := run_push_push_sstore whole env state firstValue firstKey
      hrunning hfirst
    rw [hrun]
    simp [afterFirst, first, Assembly.byteLength, Instruction.byteLength]
    omega
  have hafterRunning : afterFirst.exit = none := by
    simp [afterFirst, hrunning]
  have hsecond' : Assembly.CodeAt whole second afterFirst.pc := by
    simpa [afterFirst] using hsecond
  let afterSecond : ExecutionState :=
    { afterFirst with
      pc := afterFirst.pc + second.byteLength
      storage := Function.update afterFirst.storage secondKey.value.toNat
        secondValue.value }
  have hrunSecond : run 3 whole env afterFirst = afterSecond := by
    have hrun := run_push_push_sstore whole env afterFirst secondValue
      secondKey hafterRunning hsecond'
    rw [hrun]
    simp [afterSecond, second, Assembly.byteLength, Instruction.byteLength]
    omega
  rw [show 6 = 3 + 3 by omega, run_add, hrunFirst, hrunSecond]
  simp [afterSecond, afterFirst, hdecomp, first, second]
  simp [Assembly.byteLength]
  omega

variable {Player : Type} [DecidableEq Player]
variable {program : Program Player simpleExpr}

/-- Resolved pending-request storage writes. -/
def setPendingAssembly (program : Program Player simpleExpr) (node : Nat) :
    Assembly :=
  storagePairAssembly (.one (byte 1)) (.nat256 (pendingFlagSlot program))
    (.nat256 node) (.nat256 (pendingNodeSlot program))

@[simp] theorem setPendingAssembly_byteLength
    (program : Program Player simpleExpr) (node : Nat) :
    (setPendingAssembly program node).byteLength = 103 := by
  simp [setPendingAssembly, storagePairAssembly, Assembly.byteLength,
    Instruction.byteLength]

@[simp] theorem resolveFrom?_compileSetPending
    (whole : LocalAssembly) (base node : Nat) :
    whole.resolveFrom? base (compileSetPending (program := program) node) =
      some (setPendingAssembly program node) := by
  rfl

/-- The request prologue stores the pending flag and node at their exact
certified layout addresses. -/
theorem run_setPending
    (fits : ClassicalStorageFitsWord program)
    (whole : Assembly) (env : ExecutionEnv) (state : ExecutionState)
    (node : Nat) (hrunning : state.exit = none)
    (hcode : Assembly.CodeAt whole (setPendingAssembly program node)
      state.pc) :
    run 6 whole env state =
      { state with
        pc := state.pc + (setPendingAssembly program node).byteLength
        storage := Function.update
          (Function.update state.storage (pendingFlagSlot program) 1)
          (pendingNodeSlot program) (BitVec.ofNat 256 node) } := by
  have hrun := run_storagePair whole env state
    (.one (byte 1)) (.nat256 (pendingFlagSlot program))
    (.nat256 node) (.nat256 (pendingNodeSlot program)) hrunning hcode
  have hflag : pendingFlagSlot program < 2 ^ 256 := by
    simpa [pendingFlagSlot] using
      (classicalStorageAddress_lt_word fits
        (ClassicalStorageSlot.pendingFlag : ClassicalStorageSlot program))
  have hnode : pendingNodeSlot program < 2 ^ 256 := by
    simpa [pendingNodeSlot] using
      (classicalStorageAddress_lt_word fits
        (ClassicalStorageSlot.pendingNode : ClassicalStorageSlot program))
  norm_num at hflag hnode
  rw [hrun]
  simp [setPendingAssembly,
    Nat.mod_eq_of_lt hflag, Nat.mod_eq_of_lt hnode]

/-- Resolved pending-marker clearing writes. -/
def clearPendingAssembly (program : Program Player simpleExpr) : Assembly :=
  storagePairAssembly (.one (byte 0)) (.nat256 (pendingFlagSlot program))
    (.one (byte 0)) (.nat256 (pendingNodeSlot program))

@[simp] theorem clearPendingAssembly_byteLength
    (program : Program Player simpleExpr) :
    (clearPendingAssembly program).byteLength = 72 := by
  simp [clearPendingAssembly, storagePairAssembly, Assembly.byteLength,
    Instruction.byteLength]

@[simp] theorem resolveFrom?_compileClearPending
    (whole : LocalAssembly) (base : Nat) :
    whole.resolveFrom? base (compileClearPending program) =
      some (clearPendingAssembly program) := by
  rfl

/-- A successful callback clears both pending cells at their exact certified
layout addresses. -/
theorem run_clearPending
    (fits : ClassicalStorageFitsWord program)
    (whole : Assembly) (env : ExecutionEnv) (state : ExecutionState)
    (hrunning : state.exit = none)
    (hcode : Assembly.CodeAt whole (clearPendingAssembly program) state.pc) :
    run 6 whole env state =
      { state with
        pc := state.pc + (clearPendingAssembly program).byteLength
        storage := Function.update
          (Function.update state.storage (pendingFlagSlot program) 0)
          (pendingNodeSlot program) 0 } := by
  have hrun := run_storagePair whole env state
    (.one (byte 0)) (.nat256 (pendingFlagSlot program))
    (.one (byte 0)) (.nat256 (pendingNodeSlot program)) hrunning hcode
  have hflag : pendingFlagSlot program < 2 ^ 256 := by
    simpa [pendingFlagSlot] using
      (classicalStorageAddress_lt_word fits
        (ClassicalStorageSlot.pendingFlag : ClassicalStorageSlot program))
  have hnode : pendingNodeSlot program < 2 ^ 256 := by
    simpa [pendingNodeSlot] using
      (classicalStorageAddress_lt_word fits
        (ClassicalStorageSlot.pendingNode : ClassicalStorageSlot program))
  norm_num at hflag hnode
  rw [hrun]
  simp [clearPendingAssembly,
    Nat.mod_eq_of_lt hflag, Nat.mod_eq_of_lt hnode]

/-- Resolved anonymous log emission for one oracle request. -/
def oracleRequestLogAssembly (node : Nat) : Assembly :=
  [ .push (.nat256 node),
    .push (.one (byte 0)),
    .mstore,
    .push (.one (byte 32)),
    .push (.one (byte 0)),
    .log0 ]

@[simp] theorem oracleRequestLogAssembly_byteLength (node : Nat) :
    (oracleRequestLogAssembly node).byteLength = 41 := by
  simp [oracleRequestLogAssembly, Assembly.byteLength,
    Instruction.byteLength]

@[simp] theorem resolveFrom?_compileOracleRequestLog
    (whole : LocalAssembly) (base node : Nat) :
    whole.resolveFrom? base (compileOracleRequestLog node) =
      some (oracleRequestLogAssembly node) := by
  rfl

/-- The request log stores the full node word in scratch memory and appends
exactly those 32 bytes as one anonymous log. -/
theorem run_oracleRequestLog
    (whole : Assembly) (env : ExecutionEnv) (state : ExecutionState)
    (node : Nat) (hrunning : state.exit = none)
    (hcode : Assembly.CodeAt whole (oracleRequestLogAssembly node) state.pc) :
    run 6 whole env state =
      { state with
        pc := state.pc + 41
        memory := writeBytes state.memory 0
          (PushData.word (BitVec.ofNat 256 node)).bytes
        logs := state.logs ++
          [(PushData.word (BitVec.ofNat 256 node)).bytes] } := by
  have hread :
      readMemory
          (writeBytes state.memory 0
            (PushData.word (BitVec.ofNat 256 node)).bytes)
          0 32 =
        (PushData.word (BitVec.ofNat 256 node)).bytes := by
    simpa using readMemory_writeBytes state.memory 0
      (PushData.word (BitVec.ofNat 256 node)).bytes
  have hbyte32 : (byte 32).toNat = 32 := by decide
  apply StraightRun.run_eq ?_ hcode
  simp [StraightRun, oracleRequestLogAssembly, stepInstruction, advance,
    hrunning, hbyte32, hread]
  norm_num [Instruction.byteLength]

/-- Resolved request effect: persist the pending node, emit its anonymous log,
then stop successfully. -/
def sampleRequestEffectAssembly
    (program : Program Player simpleExpr) (node : Nat) : Assembly :=
  setPendingAssembly program node ++ oracleRequestLogAssembly node ++ [.stop]

@[simp] theorem resolveFrom?_compileSimpleSampleRequestEffect
    (whole : LocalAssembly) (base : Nat)
    (action : ClassicalActionIR program) :
    whole.resolveFrom? base (compileSimpleSampleRequestEffect action) =
      some (sampleRequestEffectAssembly program action.node) := by
  simp [compileSimpleSampleRequestEffect, sampleRequestEffectAssembly,
    LocalAssembly.resolveFrom?_append, LocalAssembly.resolveFrom?,
    LocalAssembly.resolveItem?]

/-- A ready request effect implements the waiting-state writes and exact
request log, then terminates successfully. -/
theorem run_sampleRequestEffect
    (fits : ClassicalStorageFitsWord program)
    (whole : Assembly) (env : ExecutionEnv) (state : ExecutionState)
    (node : Nat) (hrunning : state.exit = none)
    (hcode : Assembly.CodeAt whole
      (sampleRequestEffectAssembly program node) state.pc) :
    run 13 whole env state =
      { state with
        pc := state.pc + 144
        memory := writeBytes state.memory 0
          (PushData.word (BitVec.ofNat 256 node)).bytes
        storage := Function.update
          (Function.update state.storage (pendingFlagSlot program) 1)
          (pendingNodeSlot program) (BitVec.ofNat 256 node)
        logs := state.logs ++
          [(PushData.word (BitVec.ofNat 256 node)).bytes]
        exit := some .stopped } := by
  let setCode := setPendingAssembly program node
  let logCode := oracleRequestLogAssembly node
  have hdecomp : sampleRequestEffectAssembly program node =
      setCode ++ (logCode ++ [.stop]) := by
    simp [sampleRequestEffectAssembly, setCode, logCode,
      List.append_assoc]
  rw [hdecomp] at hcode
  have hsetCode : Assembly.CodeAt whole setCode state.pc :=
    hcode.left
  have htailCode : Assembly.CodeAt whole (logCode ++ [.stop])
      (state.pc + setCode.byteLength) := hcode.right
  let afterSet : ExecutionState :=
    { state with
      pc := state.pc + setCode.byteLength
      storage := Function.update
        (Function.update state.storage (pendingFlagSlot program) 1)
        (pendingNodeSlot program) (BitVec.ofNat 256 node) }
  have hrunSet : run 6 whole env state = afterSet := by
    have hrun := run_setPending fits whole env state node hrunning hsetCode
    simpa [afterSet, setCode] using hrun
  have hafterSetRunning : afterSet.exit = none := by
    simp [afterSet, hrunning]
  have hlogCode : Assembly.CodeAt whole logCode afterSet.pc := by
    have := htailCode.left
    simpa [afterSet] using this
  let afterLog : ExecutionState :=
    { afterSet with
      pc := afterSet.pc + 41
      memory := writeBytes afterSet.memory 0
        (PushData.word (BitVec.ofNat 256 node)).bytes
      logs := afterSet.logs ++
        [(PushData.word (BitVec.ofNat 256 node)).bytes] }
  have hrunLog : run 6 whole env afterSet = afterLog := by
    have hrun := run_oracleRequestLog whole env afterSet node
      hafterSetRunning hlogCode
    simpa [afterLog] using hrun
  have hafterLogRunning : afterLog.exit = none := by
    simp [afterLog, afterSet, hrunning]
  have hstopCode : Assembly.CodeAt whole [.stop] afterLog.pc := by
    have := htailCode.right
    simpa [afterLog, afterSet, logCode] using this
  have hrunStop : run 1 whole env afterLog =
      { afterLog with exit := some .stopped } := by
    rw [run_succ_of_codeAt 0 hafterLogRunning hstopCode]
    simp [run, stepInstruction]
  rw [show 13 = 6 + (6 + 1) by omega, run_add, hrunSet,
    run_add, hrunLog, hrunStop]
  simp [afterLog, afterSet, setCode]

/-- Starting from canonical idle storage, a successful request effect reaches
the canonical waiting snapshot for exactly the requested finite node. -/
theorem run_sampleRequestEffect_waiting
    (fits : ClassicalStorageFitsWord program)
    (nodesFit : NodesFitWord program)
    (codec : StorageCodec program) (words : WireCodec codec.Word Word)
    (cfg : EventGraph.Config program.graph)
    (whole : Assembly) (env : ExecutionEnv) (state : ExecutionState)
    (node : Fin program.graph.nodeCount)
    (hrunning : state.exit = none)
    (hstorage : state.storage =
      encodeClassicalSnapshot codec words (nodeWordCodec program nodesFit)
        { graph := EventGraph.StateSnapshot.ofConfig cfg, pending := none })
    (hcode : Assembly.CodeAt whole
      (sampleRequestEffectAssembly program node) state.pc) :
    run 13 whole env state =
      { state with
        pc := state.pc + 144
        memory := writeBytes state.memory 0
          (PushData.word (BitVec.ofNat 256 (node : Nat))).bytes
        storage := encodeClassicalSnapshot codec words
          (nodeWordCodec program nodesFit)
          { graph := EventGraph.StateSnapshot.ofConfig cfg, pending := some node }
        logs := state.logs ++
          [(PushData.word (BitVec.ofNat 256 (node : Nat))).bytes]
        exit := some .stopped } := by
  rw [run_sampleRequestEffect fits whole env state node hrunning hcode]
  rw [hstorage]
  congr 1
  change
    Function.update
        (Function.update
          (encodeClassicalSnapshot codec words (nodeWordCodec program nodesFit)
            { graph := EventGraph.StateSnapshot.ofConfig cfg, pending := none })
          (pendingFlagSlot program) 1)
        (pendingNodeSlot program)
          ((nodeWordCodec program nodesFit).encode node) =
      encodeClassicalSnapshot codec words (nodeWordCodec program nodesFit)
        { graph := EventGraph.StateSnapshot.ofConfig cfg, pending := some node }
  exact encodeClassicalSnapshot_setPending codec words
    (nodeWordCodec program nodesFit)
    { graph := EventGraph.StateSnapshot.ofConfig cfg, pending := none } node

/-- Resolved post-realization callback suffix: release the asynchronous lock,
commit the selected node value, and terminate successfully. -/
def sampleCallbackEffectAssembly (program : Program Player simpleExpr)
    (action : ClassicalActionIR program) : Assembly :=
  clearPendingAssembly program ++ classicalActionWritesAssembly action ++
    [.stop]

@[simp] theorem sampleCallbackEffectAssembly_byteLength
    (program : Program Player simpleExpr)
    (action : ClassicalActionIR program) :
    (sampleCallbackEffectAssembly program action).byteLength = 179 := by
  simp [sampleCallbackEffectAssembly, clearPendingAssembly,
    storagePairAssembly, classicalActionWritesAssembly,
    Assembly.byteLength, Instruction.byteLength]

/-- Given an already authenticated and realized Boolean callback result, the
emitted callback suffix reaches the exact canonical idle graph successor. -/
theorem run_sampleCallbackEffect_completeBool
    (fits : ClassicalStorageFitsWord program)
    (usesBool : UsesOnlyBoolStorage program)
    (codec : StorageCodec program) (words : WireCodec codec.Word Word)
    (canonical : CanonicalRepresentation program codec words)
    (nodes : WireCodec (Fin program.graph.nodeCount) Word)
    (cfg : EventGraph.Config program.graph)
    (whole : Assembly) (env : ExecutionEnv) (state : ExecutionState)
    (action : ClassicalActionIR program) (value : Bool) (rest : List Word)
    (hrunning : state.exit = none)
    (hstorage : state.storage =
      encodeClassicalSnapshot codec words nodes
        { graph := EventGraph.StateSnapshot.ofConfig cfg,
          pending := some action.node })
    (hstack : state.stack = encodeBool value :: rest)
    (hcode : Assembly.CodeAt whole
      (sampleCallbackEffectAssembly program action) state.pc) :
    run 15 whole env state =
      { state with
        pc := state.pc + 178
        stack := rest
        storage := encodeClassicalSnapshot codec words nodes
          { graph := EventGraph.StateSnapshot.ofConfig
              (cfg.completeNode action.node { ty := .bool, value := value })
            pending := none }
        exit := some .stopped } := by
  let clearCode := clearPendingAssembly program
  let writeCode := classicalActionWritesAssembly action
  have hdecomp : sampleCallbackEffectAssembly program action =
      clearCode ++ (writeCode ++ [.stop]) := by
    simp [sampleCallbackEffectAssembly, clearCode, writeCode,
      List.append_assoc]
  rw [hdecomp] at hcode
  have hclearCode : Assembly.CodeAt whole clearCode state.pc :=
    hcode.left
  have htailCode : Assembly.CodeAt whole (writeCode ++ [.stop])
      (state.pc + clearCode.byteLength) := hcode.right
  let afterClear : ExecutionState :=
    { state with
      pc := state.pc + clearCode.byteLength
      storage := encodeClassicalSnapshot codec words nodes
        { graph := EventGraph.StateSnapshot.ofConfig cfg, pending := none } }
  have hrunClear : run 6 whole env state = afterClear := by
    rw [run_clearPending fits whole env state hrunning hclearCode]
    rw [hstorage]
    have hclear := encodeClassicalSnapshot_clearPending codec words nodes
      { graph := EventGraph.StateSnapshot.ofConfig cfg,
        pending := some action.node }
    simp only at hclear
    have hflag : pendingFlagSlot program =
      (ClassicalStorageLayout.canonical program).address
        (ClassicalStorageSlot.pendingFlag : ClassicalStorageSlot program) := rfl
    have hnode : pendingNodeSlot program =
      (ClassicalStorageLayout.canonical program).address
        (ClassicalStorageSlot.pendingNode : ClassicalStorageSlot program) := rfl
    rw [hflag, hnode, hclear]
  have hafterClearRunning : afterClear.exit = none := by
    simp [afterClear, hrunning]
  have hwriteCode : Assembly.CodeAt whole writeCode afterClear.pc := by
    have := htailCode.left
    simpa [afterClear] using this
  let afterWrite : ExecutionState :=
    { afterClear with
      pc := afterClear.pc + writeCode.byteLength
      stack := rest
      storage := encodeClassicalSnapshot codec words nodes
        { graph := EventGraph.StateSnapshot.ofConfig
            (cfg.completeNode action.node { ty := .bool, value := value })
          pending := none } }
  have hrunWrite : run 8 whole env afterClear = afterWrite := by
    have hrun := run_classicalActionWrites_completeBool fits usesBool codec
      words canonical nodes cfg none whole env afterClear action value rest
      hafterClearRunning rfl (by simpa [afterClear] using hstack) hwriteCode
    simpa [afterWrite, writeCode] using hrun
  have hafterWriteRunning : afterWrite.exit = none := by
    simp [afterWrite, afterClear, hrunning]
  have hstopCode : Assembly.CodeAt whole [.stop] afterWrite.pc := by
    have := htailCode.right
    simpa [afterWrite, afterClear, writeCode] using this
  have hrunStop : run 1 whole env afterWrite =
      { afterWrite with exit := some .stopped } := by
    rw [run_succ_of_codeAt 0 hafterWriteRunning hstopCode]
    simp [run, stepInstruction]
  rw [show 15 = 6 + (8 + 1) by omega, run_add, hrunClear,
    run_add, hrunWrite, hrunStop]
  simp [afterWrite, afterClear, clearCode, writeCode,
    clearPendingAssembly, storagePairAssembly,
    classicalActionWritesAssembly, Assembly.byteLength,
    Instruction.byteLength]

end

end Vegas.Machine.Contract.EVM
