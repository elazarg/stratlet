/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasEVM.Contract.SimpleEVMExpr

/-!
# Boolean exact-table realization on EVM

The trusted oracle submits the index of one entry in the exact rational table
selected by the current public state. On chain, probabilities are irrelevant:
the callback validates that index and deterministically loads its retained
Boolean value. The oracle's fixed off-chain strategy over indices is already
proved to recover the source law.

Every retained table is checked to fit the 256-bit callback word. Conditional
distribution syntax reuses the Boolean expression compiler and local labels.
-/

namespace Vegas.Machine.Contract.EVM

open EventGraph

noncomputable section

/-- The oracle callback's table-index argument starts at byte 36. -/
def oracleChoiceWord : Assembly := loadCalldataWord 36

/-- Compare the callback index with one retained table index and branch to its
value block. -/
def compileChoiceRoute (index : Nat) (target : LocalLabel) : LocalAssembly :=
  LocalAssembly.ofAssembly oracleChoiceWord ++
    [ .op (.push (.nat256 index)),
      .op .eq,
      .jumpi target ]

/-- Emit one Boolean value block. -/
def compileBoolTableValue (label done : LocalLabel) (value : Bool) :
    LocalAssembly :=
  [ .label label,
    .op (.push (.one (byte (if value then 1 else 0)))),
    .jump done ]

/-- Compile one exact retained Boolean table. Unknown or truncated indices
reach `reject`; a successful path leaves the selected Boolean word on stack. -/
def compileBoolTable? (entries : List (Bool × ℚ≥0))
    (reject : LocalLabel) (next : Nat) : Option GeneratedLocalCode :=
  if _fits : entries.length ≤ 2 ^ 256 then
    let done := next + entries.length
    let routes := (List.range entries.length).flatMap fun index =>
      compileChoiceRoute index (next + index)
    let values := entries.zipIdx.flatMap fun entry =>
      compileBoolTableValue (next + entry.2) done entry.1.1
    some
      { code := routes ++ [.jump reject] ++ values ++ [.label done]
        nextLabel := done + 1 }
  else
    none

/-- Resolve a Boolean distribution variable from its graph field. -/
def simpleDistVariableCode (code : DistCode simpleExpr .bool)
    {name : VarId} {τ : BaseTy} (binding : HasVar code.Context name τ) :
    Assembly :=
  loadStorageWord (code.fieldOf binding)

/-- Compile Boolean distribution syntax to deterministic callback-index
realization. -/
def compileBoolDistExpr? {Γ : CtxSimple}
    (variableCode : VariableCode Γ) :
    DistExpr Γ .bool → LocalLabel → Nat → Option GeneratedLocalCode
  | .weighted law, reject, next =>
      compileBoolTable? law.entries reject next
  | .ite condition yes no, reject, next =>
      let yesLabel := next
      let doneLabel := next + 1
      match compileBoolExpr? stackLimit variableCode condition with
      | none => none
      | some conditionCode =>
          match compileBoolDistExpr? variableCode no reject
              (next + 2) with
          | none => none
          | some noCode =>
              match compileBoolDistExpr? variableCode yes reject
                  noCode.nextLabel with
              | none => none
              | some yesCode =>
                  some
                    { code := LocalAssembly.ofAssembly conditionCode ++
                        [.jumpi yesLabel] ++
                        noCode.code ++ [.jump doneLabel, .label yesLabel] ++
                        yesCode.code ++ [.label doneLabel]
                      nextLabel := yesCode.nextLabel }

/-- Compile retained Boolean graph distribution code. -/
def compileSimpleDistCode? (code : DistCode simpleExpr .bool)
    (reject : LocalLabel) (next : Nat) : Option GeneratedLocalCode :=
  compileBoolDistExpr? (simpleDistVariableCode code) code.dist reject next

end

end Vegas.Machine.Contract.EVM
