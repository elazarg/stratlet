/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasEVM.Contract.ClassicalEVMCodegen
import VegasEVM.Contract.EVMExecution

/-!
# Execution correctness of structural classical EVM code

These theorems connect generated instruction fragments to the gas-free EVM
semantics. They are compositional over certified byte offsets and retain the
exact ordered storage updates used by the higher-level snapshot proof.
-/

namespace Vegas.Machine.Contract.EVM

open EventGraph

noncomputable section

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} {program : Program Player L}

/-- A satisfied canonical storage check falls through without changing stack,
memory, storage, logs, or exit status. -/
theorem run_classicalStorageCheck_accept
    (whole : Assembly) (env : ExecutionEnv) (state : ExecutionState)
    (check : ClassicalStorageCheck) (rejectDestination : Nat)
    (hslot : check.slot < 2 ^ 256)
    (hrunning : state.exit = none)
    (hstorage : state.storage check.slot = encodeBool check.expected)
    (hcode : Assembly.CodeAt whole
      (classicalStorageCheckAssembly rejectDestination check) state.pc) :
    run 7 whole env state =
      { state with
        pc := state.pc +
          (classicalStorageCheckAssembly rejectDestination check).byteLength } := by
  let key := PushData.nat256 check.slot
  let expected := PushData.one (byte (if check.expected then 1 else 0))
  let destination := PushData.nat32 rejectDestination
  have hkey : key.value.toNat = check.slot := by
    exact PushData.nat256_value_toNat_of_lt hslot
  have hexpected : expected.value = encodeBool check.expected := by
    cases h : check.expected <;> simp [expected, h, encodeBool]
  let state1 := advance state (.push key) (key.value :: state.stack)
  let state2 := advance state1 .sload
    (encodeBool check.expected :: state.stack)
  let state3 := advance state2 (.push expected)
    (expected.value :: encodeBool check.expected :: state.stack)
  let state4 := advance state3 .eq (1 :: state.stack)
  let state5 := advance state4 .iszero (0 :: state.stack)
  let state6 := advance state5 (.push destination)
    (destination.value :: 0 :: state.stack)
  let state7 := advance state6 .jumpi state.stack
  have code1 := hcode.tail
  have code2 := code1.tail
  have code3 := code2.tail
  have code4 := code3.tail
  have code5 := code4.tail
  have code6 := code5.tail
  have hstate1 : stepInstruction whole env (.push key) state = state1 := by
    rfl
  have hstate1Running : state1.exit = none := by
    simp [state1, advance, hrunning]
  have hcode1 : Assembly.CodeAt whole
      [.sload, .push expected, .eq, .iszero, .push destination, .jumpi]
      state1.pc := by
    simpa [key, expected, destination, state1, advance] using code1
  have hstate2 : stepInstruction whole env .sload state1 = state2 := by
    simp [stepInstruction, state2, state1, advance, hkey, hstorage]
  have hstate2Running : state2.exit = none := by
    simp [state2, state1, advance, hrunning]
  have hcode2 : Assembly.CodeAt whole
      [.push expected, .eq, .iszero, .push destination, .jumpi]
      state2.pc := by
    simpa [key, expected, destination, state2, state1, advance] using code2
  have hstate3 :
      stepInstruction whole env (.push expected) state2 = state3 := by rfl
  have hstate3Running : state3.exit = none := by
    simp [state3, state2, state1, advance, hrunning]
  have hcode3 : Assembly.CodeAt whole
      [.eq, .iszero, .push destination, .jumpi] state3.pc := by
    simpa [key, expected, destination, state3, state2, state1, advance]
      using code3
  have hstate4 : stepInstruction whole env .eq state3 = state4 := by
    simp [stepInstruction, state4, state3, state2, state1, hexpected,
      advance, boolWord]
  have hstate4Running : state4.exit = none := by
    simp [state4, state3, state2, state1, advance, hrunning]
  have hcode4 : Assembly.CodeAt whole
      [.iszero, .push destination, .jumpi] state4.pc := by
    simpa [key, expected, destination, state4, state3, state2, state1,
      advance] using code4
  have hstate5 : stepInstruction whole env .iszero state4 = state5 := by
    simp [stepInstruction, state5, state4, state3, state2, state1,
      advance, boolWord]
  have hstate5Running : state5.exit = none := by
    simp [state5, state4, state3, state2, state1, advance, hrunning]
  have hcode5 : Assembly.CodeAt whole
      [.push destination, .jumpi] state5.pc := by
    simpa [key, expected, destination, state5, state4, state3, state2,
      state1, advance] using code5
  have hstate6 :
      stepInstruction whole env (.push destination) state5 = state6 := by rfl
  have hstate6Running : state6.exit = none := by
    simp [state6, state5, state4, state3, state2, state1, advance, hrunning]
  have hcode6 : Assembly.CodeAt whole [.jumpi] state6.pc := by
    simpa [key, expected, destination, state6, state5, state4, state3,
      state2, state1, advance] using code6
  have hstate7 : stepInstruction whole env .jumpi state6 = state7 := by
    simp [stepInstruction, state7, state6, state5, state4, state3, state2,
      state1, advance]
  rw [show 7 = 6 + 1 by omega,
    run_succ_of_codeAt 6 hrunning hcode, hstate1]
  rw [show 6 = 5 + 1 by omega,
    run_succ_of_codeAt 5 hstate1Running hcode1, hstate2]
  rw [show 5 = 4 + 1 by omega,
    run_succ_of_codeAt 4 hstate2Running hcode2, hstate3]
  rw [show 4 = 3 + 1 by omega,
    run_succ_of_codeAt 3 hstate3Running hcode3, hstate4]
  rw [show 3 = 2 + 1 by omega,
    run_succ_of_codeAt 2 hstate4Running hcode4, hstate5]
  rw [show 2 = 1 + 1 by omega,
    run_succ_of_codeAt 1 hstate5Running hcode5, hstate6]
  rw [show 1 = 0 + 1 by omega,
    run_succ_of_codeAt 0 hstate6Running hcode6, hstate7]
  simp [run, state7, state6, state5, state4, state3, state2, state1,
    key, expected, destination, advance, classicalStorageCheckAssembly,
    Assembly.byteLength, Instruction.byteLength]

/-- An ordered list of satisfied canonical checks falls through unchanged.
This is the executable EVM counterpart of readiness-check acceptance. -/
theorem run_classicalStorageChecks_accept
    (whole : Assembly) (env : ExecutionEnv) (state : ExecutionState)
    (checks : List ClassicalStorageCheck) (rejectDestination : Nat)
    (hrunning : state.exit = none)
    (hslots : ∀ check ∈ checks, check.slot < 2 ^ 256)
    (hstorage : ∀ check ∈ checks,
      state.storage check.slot = encodeBool check.expected)
    (hcode : Assembly.CodeAt whole
      (classicalStorageChecksAssembly rejectDestination checks) state.pc) :
    run (7 * checks.length) whole env state =
      { state with
        pc := state.pc +
          (classicalStorageChecksAssembly rejectDestination checks).byteLength } := by
  induction checks generalizing state with
  | nil =>
      change state = { state with pc := state.pc + 0 }
      simp
  | cons check rest ih =>
      let head := classicalStorageCheckAssembly rejectDestination check
      let tail := classicalStorageChecksAssembly rejectDestination rest
      have hdecomp :
          classicalStorageChecksAssembly rejectDestination (check :: rest) =
            head ++ tail := by rfl
      rw [hdecomp] at hcode ⊢
      have hhead : Assembly.CodeAt whole head state.pc := hcode.left
      have htail : Assembly.CodeAt whole tail
          (state.pc + head.byteLength) := hcode.right
      let after : ExecutionState :=
        { state with pc := state.pc + head.byteLength }
      have hrunHead : run 7 whole env state = after := by
        have hrun := run_classicalStorageCheck_accept whole env state check
          rejectDestination (hslots check (by simp)) hrunning
          (hstorage check (by simp))
        rw [show head = classicalStorageCheckAssembly rejectDestination check
          by rfl] at hhead
        specialize hrun hhead
        simpa [after, head] using hrun
      have hafterRunning : after.exit = none := by
        simp [after, hrunning]
      have htail' : Assembly.CodeAt whole tail after.pc := by
        simpa [after] using htail
      have hrunTail : run (7 * rest.length) whole env after =
          { after with pc := after.pc + tail.byteLength } := by
        apply ih after hafterRunning
        · intro item hmem
          exact hslots item (by simp [hmem])
        · intro item hmem
          exact hstorage item (by simp [hmem])
        · exact htail'
      rw [show 7 * (check :: rest).length = 7 + 7 * rest.length by
        simp; omega]
      rw [run_add, hrunHead, hrunTail]
      simp [after]
      omega

/-- Graph readiness is sufficient for the emitted EVM check sequence to fall
through when storage represents the same source configuration. -/
theorem run_classicalStorageChecks_of_ready
    (fits : ClassicalStorageFitsWord program)
    (codec : StorageCodec program) (words : WireCodec codec.Word Word)
    (nodes : WireCodec (Fin program.graph.nodeCount) Word)
    (cfg : Config program.graph)
    (pending : Option (Fin program.graph.nodeCount))
    (node : Fin program.graph.nodeCount)
    (ready : Ready program.graph cfg node)
    (whole : Assembly) (env : ExecutionEnv) (state : ExecutionState)
    (rejectDestination : Nat)
    (hrunning : state.exit = none)
    (hstorage : state.storage =
      encodeClassicalSnapshot codec words nodes
        { graph := StateSnapshot.ofConfig cfg, pending := pending })
    (hcode : Assembly.CodeAt whole
      (classicalStorageChecksAssembly rejectDestination
        (classicalChecks program node)) state.pc) :
    run (7 * (classicalChecks program node).length) whole env state =
      { state with
        pc := state.pc +
          (classicalStorageChecksAssembly rejectDestination
            (classicalChecks program node)).byteLength } := by
  apply run_classicalStorageChecks_accept whole env state
    (classicalChecks program node) rejectDestination hrunning
  · intro check hcheck
    exact classicalChecks_slot_lt_word fits node check hcheck
  · intro check hcheck
    rw [hstorage]
    exact classicalChecks_storage_eq_of_ready codec words nodes cfg pending
      node ready check hcheck
  · exact hcode

/-- Successful action-write code stores the existing result word, then the
presence bit, then the completion bit, and preserves the remaining stack. -/
theorem run_classicalActionWrites
    (whole : Assembly) (env : ExecutionEnv) (state : ExecutionState)
    (action : ClassicalActionIR program) (value : Word) (rest : List Word)
    (hrunning : state.exit = none)
    (hstack : state.stack = value :: rest)
    (hcode : Assembly.CodeAt whole
      (classicalActionWritesAssembly action) state.pc) :
    run 8 whole env state =
      { state with
        pc := state.pc +
          (classicalActionWritesAssembly action).byteLength
        stack := rest
        storage := Function.update
          (Function.update
            (Function.update state.storage
              (PushData.nat256 action.valueSlot).value.toNat value)
            (PushData.nat256 action.presenceSlot).value.toNat 1)
          (PushData.nat256 action.completionSlot).value.toNat 1 } := by
  let valueWrite : Assembly :=
    [.push (.nat256 action.valueSlot), .sstore]
  let presenceWrite : Assembly :=
    [.push (.one (byte 1)), .push (.nat256 action.presenceSlot), .sstore]
  let completionWrite : Assembly :=
    [.push (.one (byte 1)), .push (.nat256 action.completionSlot), .sstore]
  have hdecomp :
      classicalActionWritesAssembly action =
        valueWrite ++ presenceWrite ++ completionWrite := by
    rfl
  rw [hdecomp] at hcode ⊢
  have hcode' :
      Assembly.CodeAt whole
        (valueWrite ++ (presenceWrite ++ completionWrite)) state.pc := by
    simpa [List.append_assoc] using hcode
  have hvalueCode : Assembly.CodeAt whole valueWrite state.pc :=
    hcode'.left
  have hafterValueCode :
      Assembly.CodeAt whole (presenceWrite ++ completionWrite)
        (state.pc + valueWrite.byteLength) :=
    hcode'.right
  let afterValue : ExecutionState :=
    { state with
      pc := state.pc + valueWrite.byteLength
      stack := rest
      storage := Function.update state.storage
        (PushData.nat256 action.valueSlot).value.toNat value }
  have hrunValue : run 2 whole env state = afterValue := by
    have hrun := run_push_sstore whole env state
      (PushData.nat256 action.valueSlot) value rest hrunning hstack
    rw [show valueWrite =
      [.push (.nat256 action.valueSlot), .sstore] by rfl] at hvalueCode
    specialize hrun hvalueCode
    simpa [afterValue, valueWrite, Assembly.byteLength,
      Instruction.byteLength] using hrun
  have hpresenceCode :
      Assembly.CodeAt whole presenceWrite afterValue.pc := by
    have := hafterValueCode.left
    simpa [afterValue] using this
  have hafterPresenceCode :
      Assembly.CodeAt whole completionWrite
        (afterValue.pc + presenceWrite.byteLength) := by
    exact hafterValueCode.right
  let afterPresence : ExecutionState :=
    { afterValue with
      pc := afterValue.pc + presenceWrite.byteLength
      storage := Function.update afterValue.storage
        (PushData.nat256 action.presenceSlot).value.toNat 1 }
  have hafterValueRunning : afterValue.exit = none := by
    simp [afterValue, hrunning]
  have hrunPresence : run 3 whole env afterValue = afterPresence := by
    have hrun := run_push_push_sstore whole env afterValue
      (PushData.one (byte 1)) (PushData.nat256 action.presenceSlot)
      hafterValueRunning
    rw [show presenceWrite =
      [.push (.one (byte 1)), .push (.nat256 action.presenceSlot),
        .sstore] by rfl] at hpresenceCode
    specialize hrun hpresenceCode
    simpa [afterPresence, presenceWrite, Assembly.byteLength,
      Instruction.byteLength] using hrun
  have hcompletionCode :
      Assembly.CodeAt whole completionWrite afterPresence.pc := by
    simpa [afterPresence] using hafterPresenceCode
  let afterCompletion : ExecutionState :=
    { afterPresence with
      pc := afterPresence.pc + completionWrite.byteLength
      storage := Function.update afterPresence.storage
        (PushData.nat256 action.completionSlot).value.toNat 1 }
  have hafterPresenceRunning : afterPresence.exit = none := by
    simp [afterPresence, afterValue, hrunning]
  have hrunCompletion :
      run 3 whole env afterPresence = afterCompletion := by
    have hrun := run_push_push_sstore whole env afterPresence
      (PushData.one (byte 1)) (PushData.nat256 action.completionSlot)
      hafterPresenceRunning
    rw [show completionWrite =
      [.push (.one (byte 1)), .push (.nat256 action.completionSlot),
        .sstore] by rfl] at hcompletionCode
    specialize hrun hcompletionCode
    simpa [afterCompletion, completionWrite, Assembly.byteLength,
      Instruction.byteLength] using hrun
  rw [show 8 = 2 + (3 + 3) by omega, run_add, hrunValue,
    run_add, hrunPresence, hrunCompletion]
  simp [afterCompletion, afterPresence, afterValue, valueWrite,
    presenceWrite, completionWrite, Assembly.byteLength,
    Instruction.byteLength]

/-- With the backend's layout-capacity certificate, the same execution writes
the literal natural-number slots rather than merely their modular images. -/
theorem run_classicalActionWrites_exact
    (fits : ClassicalStorageFitsWord program)
    (whole : Assembly) (env : ExecutionEnv) (state : ExecutionState)
    (action : ClassicalActionIR program) (value : Word) (rest : List Word)
    (hrunning : state.exit = none)
    (hstack : state.stack = value :: rest)
    (hcode : Assembly.CodeAt whole
      (classicalActionWritesAssembly action) state.pc) :
    run 8 whole env state =
      { state with
        pc := state.pc +
          (classicalActionWritesAssembly action).byteLength
        stack := rest
        storage := Function.update
          (Function.update
            (Function.update state.storage action.valueSlot value)
            action.presenceSlot 1)
          action.completionSlot 1 } := by
  rw [run_classicalActionWrites whole env state action value rest
    hrunning hstack hcode]
  rw [PushData.nat256_value_toNat_of_lt
      (action.valueSlot_lt_word fits),
    PushData.nat256_value_toNat_of_lt
      (action.presenceSlot_lt_word fits),
    PushData.nat256_value_toNat_of_lt
      (action.completionSlot_lt_word fits)]

/-- On canonical Boolean storage, the three exact action writes implement the
semantic `Config.completeNode` successor rather than merely three unrelated
cell updates. -/
theorem run_classicalActionWrites_completeBool
    {program : Program Player simpleExpr}
    (fits : ClassicalStorageFitsWord program)
    (usesBool : UsesOnlyBoolStorage program)
    (codec : StorageCodec program) (words : WireCodec codec.Word Word)
    (canonical : CanonicalRepresentation program codec words)
    (nodes : WireCodec (Fin program.graph.nodeCount) Word)
    (cfg : Config program.graph)
    (pending : Option (Fin program.graph.nodeCount))
    (whole : Assembly) (env : ExecutionEnv) (state : ExecutionState)
    (action : ClassicalActionIR program) (value : Bool) (rest : List Word)
    (hrunning : state.exit = none)
    (hstorage : state.storage =
      encodeClassicalSnapshot codec words nodes
        { graph := StateSnapshot.ofConfig cfg, pending := pending })
    (hstack : state.stack = encodeBool value :: rest)
    (hcode : Assembly.CodeAt whole
      (classicalActionWritesAssembly action) state.pc) :
    run 8 whole env state =
      { state with
        pc := state.pc +
          (classicalActionWritesAssembly action).byteLength
        stack := rest
        storage := encodeClassicalSnapshot codec words nodes
          { graph := StateSnapshot.ofConfig
              (cfg.completeNode action.node { ty := .bool, value := value })
            pending := pending } } := by
  rw [run_classicalActionWrites_exact fits whole env state action
    (encodeBool value) rest hrunning hstack hcode]
  rw [hstorage, action.valueSlot_eq, action.presenceSlot_eq,
    action.completionSlot_eq]
  rw [encodeClassicalSnapshot_completeBool usesBool codec words canonical
    nodes cfg pending action.node value]

/-- Resolved success path of one completing Boolean action block. Rejection
labels live elsewhere in the handler and are deliberately not part of this
straight-line fragment. -/
def classicalCompletingBlockAssembly
    {program : Program Player simpleExpr} (rejectDestination : Nat)
    (action : ClassicalActionIR program) (realize : Assembly) : Assembly :=
  classicalStorageChecksAssembly rejectDestination action.checks ++ realize ++
    classicalActionWritesAssembly action ++ [.stop]

/-- Compositional correctness of a complete successful action block. Once a
realization fragment is proved to push the selected canonical Boolean without
changing the represented state, readiness checks, successor writes, and
successful termination are discharged here. -/
theorem run_classicalCompletingBlock_completeBool
    {program : Program Player simpleExpr}
    (fits : ClassicalStorageFitsWord program)
    (usesBool : UsesOnlyBoolStorage program)
    (codec : StorageCodec program) (words : WireCodec codec.Word Word)
    (canonical : CanonicalRepresentation program codec words)
    (nodes : WireCodec (Fin program.graph.nodeCount) Word)
    (cfg : Config program.graph)
    (pending : Option (Fin program.graph.nodeCount))
    (action : ClassicalActionIR program)
    (ready : Ready program.graph cfg action.node)
    (whole : Assembly) (env : ExecutionEnv) (state : ExecutionState)
    (rejectDestination : Nat)
    (realize : Assembly) (realizeFuel : Nat) (value : Bool)
    (hrunning : state.exit = none)
    (hstorage : state.storage =
      encodeClassicalSnapshot codec words nodes
        { graph := StateSnapshot.ofConfig cfg, pending := pending })
    (hrealize :
      run realizeFuel whole env
          { state with
            pc := state.pc +
              (classicalStorageChecksAssembly rejectDestination
                action.checks).byteLength } =
        { state with
          pc := state.pc +
              (classicalStorageChecksAssembly rejectDestination
                action.checks).byteLength + realize.byteLength
          stack := encodeBool value :: state.stack })
    (hcode : Assembly.CodeAt whole
      (classicalCompletingBlockAssembly rejectDestination action realize)
      state.pc) :
    run (7 * action.checks.length + realizeFuel + 9) whole env state =
      { state with
        pc := state.pc +
            (classicalStorageChecksAssembly rejectDestination
              action.checks).byteLength + realize.byteLength +
            (classicalActionWritesAssembly action).byteLength
        storage := encodeClassicalSnapshot codec words nodes
          { graph := StateSnapshot.ofConfig
              (cfg.completeNode action.node { ty := .bool, value := value })
            pending := pending }
        exit := some .stopped } := by
  let checksCode :=
    classicalStorageChecksAssembly rejectDestination action.checks
  let writeCode := classicalActionWritesAssembly action
  have hdecomp :
      classicalCompletingBlockAssembly rejectDestination action realize =
        checksCode ++ (realize ++ (writeCode ++ [.stop])) := by
    simp [classicalCompletingBlockAssembly, checksCode, writeCode,
      List.append_assoc]
  rw [hdecomp] at hcode
  have hchecksCode : Assembly.CodeAt whole checksCode state.pc :=
    hcode.left
  have hafterChecksCode :
      Assembly.CodeAt whole (realize ++ (writeCode ++ [.stop]))
        (state.pc + checksCode.byteLength) := hcode.right
  let afterChecks : ExecutionState :=
    { state with pc := state.pc + checksCode.byteLength }
  have hrunChecks : run (7 * action.checks.length) whole env state =
      afterChecks := by
    simp only [afterChecks, checksCode]
    change Assembly.CodeAt whole
      (classicalStorageChecksAssembly rejectDestination action.checks)
      state.pc at hchecksCode
    rw [action.checks_eq] at hchecksCode
    rw [action.checks_eq]
    exact run_classicalStorageChecks_of_ready fits codec words nodes cfg pending
      action.node ready whole env state rejectDestination hrunning hstorage
      hchecksCode
  have hrealize' : run realizeFuel whole env afterChecks =
      { state with
        pc := state.pc + checksCode.byteLength + realize.byteLength
        stack := encodeBool value :: state.stack } := by
    simpa [afterChecks, checksCode] using hrealize
  let afterRealize : ExecutionState :=
    { state with
      pc := state.pc + checksCode.byteLength + realize.byteLength
      stack := encodeBool value :: state.stack }
  have hrunRealize : run realizeFuel whole env afterChecks = afterRealize := by
    exact hrealize'
  have hafterRealizeRunning : afterRealize.exit = none := by
    simp [afterRealize, hrunning]
  have hwriteCode : Assembly.CodeAt whole writeCode afterRealize.pc := by
    have := hafterChecksCode.right.left
    simpa [afterRealize, checksCode] using this
  let afterWrite : ExecutionState :=
    { afterRealize with
      pc := afterRealize.pc + writeCode.byteLength
      stack := state.stack
      storage := encodeClassicalSnapshot codec words nodes
        { graph := StateSnapshot.ofConfig
            (cfg.completeNode action.node { ty := .bool, value := value })
          pending := pending } }
  have hrunWrite : run 8 whole env afterRealize = afterWrite := by
    have hrun := run_classicalActionWrites_completeBool fits usesBool codec
      words canonical nodes cfg pending whole env afterRealize action value
      state.stack hafterRealizeRunning
      (by simpa [afterRealize] using hstorage) rfl hwriteCode
    simpa [afterWrite, writeCode] using hrun
  have hafterWriteRunning : afterWrite.exit = none := by
    simp [afterWrite, afterRealize, hrunning]
  have hstopCode : Assembly.CodeAt whole [.stop] afterWrite.pc := by
    have := hafterChecksCode.right.right
    simpa [afterWrite, afterRealize, checksCode, writeCode] using this
  have hrunStop : run 1 whole env afterWrite =
      { afterWrite with exit := some .stopped } := by
    rw [run_succ_of_codeAt 0 hafterWriteRunning hstopCode]
    simp [run, stepInstruction]
  rw [show 7 * action.checks.length + realizeFuel + 9 =
      7 * action.checks.length + (realizeFuel + (8 + 1)) by omega,
    run_add, hrunChecks, run_add, hrunRealize, run_add, hrunWrite, hrunStop]

end

end Vegas.Machine.Contract.EVM
