/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasEVM.Contract.ClassicalEVMCodegenCorrect
import VegasEVM.Contract.SimpleEVMAction
import VegasEVM.Contract.SimpleEVMExprCorrect

/-!
# Correctness of Boolean action realization

This module discharges the state-facing part of commit and reveal realization.
The structural action-frame theorem then turns a realized Boolean into the
canonical graph successor.
-/

namespace Vegas.Machine.Contract.EVM

open EventGraph

noncomputable section

variable {Player : Type} [DecidableEq Player]
variable {program : Program Player simpleExpr}

/-- Loading a present Boolean field from a represented snapshot pushes its
canonical value word and changes only the program counter and stack. This is
the realization contract needed by generated reveal blocks. -/
theorem run_loadStorageWord_from_snapshot
    (fits : ClassicalStorageFitsWord program)
    (usesBool : UsesOnlyBoolStorage program)
    (codec : StorageCodec program) (words : WireCodec codec.Word Word)
    (canonical : CanonicalRepresentation program codec words)
    (nodes : WireCodec (Fin program.graph.nodeCount) Word)
    (snapshot : ClassicalSnapshot program)
    (field : Fin program.graph.fieldCount) (value : Bool)
    (hvalue : snapshot.graph.fieldValue? field =
      some ((usesBool.field_type field).symm ▸ value))
    (whole : Assembly) (env : ExecutionEnv) (state : ExecutionState)
    (rest : List Word)
    (hrunning : state.exit = none)
    (hstorage : state.storage =
      encodeClassicalSnapshot codec words nodes snapshot)
    (hstack : state.stack = rest)
    (hcode : Assembly.CodeAt whole (loadStorageWord field) state.pc) :
    run 2 whole env state =
      { state with
        pc := state.pc + (loadStorageWord field).byteLength
        stack := encodeBool value :: rest } := by
  let pre : BoolExprPrecondition := fun _ storage =>
    storage = encodeClassicalSnapshot codec words nodes snapshot
  have hcorrect : BoolExprCorrect pre value (loadStorageWord field) := by
    apply loadStorageWord_correct pre field (encodeBool value)
    intro _env storage hpre
    constructor
    · have hslot := classicalStorageAddress_lt_word fits
          (ClassicalStorageSlot.fieldValue field)
      simpa using hslot
    · rw [hpre]
      exact encodeClassicalSnapshot_bool_fieldValue usesBool codec words
        canonical nodes snapshot field value hvalue
  exact hcorrect whole env state rest hstorage hrunning hstack hcode

/-- The same reveal-load theorem at a raw source id accompanied by its graph
field bound. -/
theorem run_loadStorageWord_from_snapshot_raw
    (fits : ClassicalStorageFitsWord program)
    (usesBool : UsesOnlyBoolStorage program)
    (codec : StorageCodec program) (words : WireCodec codec.Word Word)
    (canonical : CanonicalRepresentation program codec words)
    (nodes : WireCodec (Fin program.graph.nodeCount) Word)
    (snapshot : ClassicalSnapshot program)
    (source : Nat) (hsource : source < program.graph.fieldCount)
    (value : Bool)
    (hvalue : snapshot.graph.fieldValue? ⟨source, hsource⟩ =
      some ((usesBool.field_type ⟨source, hsource⟩).symm ▸ value))
    (whole : Assembly) (env : ExecutionEnv) (state : ExecutionState)
    (rest : List Word)
    (hrunning : state.exit = none)
    (hstorage : state.storage =
      encodeClassicalSnapshot codec words nodes snapshot)
    (hstack : state.stack = rest)
    (hcode : Assembly.CodeAt whole (loadStorageWord source) state.pc) :
    run 2 whole env state =
      { state with
        pc := state.pc + (loadStorageWord source).byteLength
        stack := encodeBool value :: rest } := by
  exact run_loadStorageWord_from_snapshot fits usesBool codec words canonical
    nodes snapshot ⟨source, hsource⟩ value hvalue whole env state rest hrunning
    hstorage hstack hcode

end

end Vegas.Machine.Contract.EVM
