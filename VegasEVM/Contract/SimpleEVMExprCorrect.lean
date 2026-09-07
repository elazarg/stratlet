/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasEVM.Contract.SimpleEVMExpr
import VegasEVM.Contract.EVMExecution

/-!
# Execution correctness of Boolean EVM expressions

This module proves the stack semantics of the straight-line Boolean expression
instructions. The final compiler theorem is compositional in the code used for
variables, so calldata-backed guards and storage-backed distributions can
instantiate the same result.
-/

namespace Vegas.Machine.Contract.EVM

open EventGraph

noncomputable section

@[simp] theorem boolWord_encodeBool_eq (left right : Bool) :
    boolWord (encodeBool left = encodeBool right) =
      encodeBool (decide (left = right)) := by
  cases left <;> cases right <;> rfl

@[simp] theorem encodeBool_and (left right : Bool) :
    encodeBool left &&& encodeBool right = encodeBool (left && right) := by
  cases left <;> cases right <;> rfl

@[simp] theorem boolWord_encodeBool_iszero (value : Bool) :
    boolWord (encodeBool value = 0) = encodeBool (!value) := by
  cases value <;> rfl

/-- Stable facts about the dynamic EVM environment and storage on which an
expression's variable loads may rely. -/
abbrev BoolExprPrecondition := ExecutionEnv → TotalStorage → Prop

/-- Semantic contract of compiled Boolean expression code: under a stable read
precondition and over an arbitrary stack suffix, it pushes exactly one
canonical result and otherwise changes only the byte program counter. -/
def BoolExprCorrect (pre : BoolExprPrecondition)
    (value : Bool) (code : Assembly) : Prop :=
  ∀ (whole : Assembly) (env : ExecutionEnv) (state : ExecutionState)
      (rest : List Word),
    pre env state.storage →
    state.exit = none →
    state.stack = rest →
    Assembly.CodeAt whole code state.pc →
    run code.length whole env state =
      { state with
        pc := state.pc + code.byteLength
        stack := encodeBool value :: rest }

/-! ### Word arithmetic instructions

Machine words need no encoding: `encodeSimpleValue .word` is the identity, so a
word operand sits on the EVM stack as itself.

**Operand order is not uniform**, and getting it wrong is silent.
`stepInstruction` reads the top of stack as the *first* operand, so it computes
`next + top` and `next * top` — commutative, order-immaterial — but `top - next`
and `top.toNat < next.toNat`.  Emitting `sub` or `lt` in the same left-then-right
order as `add` computes the operands backwards.  The two families are therefore
stated with deliberately different stack shapes, and code generation must
respect that. -/

/-- EVM `ADD` on machine words.  Left operand pushed first. -/
theorem run_addWord (whole : Assembly) (env : ExecutionEnv)
    (state : ExecutionState) (left right : Word) (rest : List Word)
    (hrunning : state.exit = none)
    (hstack : state.stack = right :: left :: rest)
    (hcode : Assembly.CodeAt whole [.add] state.pc) :
    run 1 whole env state =
      { state with
        pc := state.pc + 1
        stack := (left + right) :: rest } := by
  rw [show 1 = 0 + 1 by omega,
    run_succ_of_codeAt 0 hrunning hcode]
  simp [run, stepInstruction, advance, hstack, Instruction.byteLength]

/-- EVM `MUL` on machine words.  Left operand pushed first. -/
theorem run_mulWord (whole : Assembly) (env : ExecutionEnv)
    (state : ExecutionState) (left right : Word) (rest : List Word)
    (hrunning : state.exit = none)
    (hstack : state.stack = right :: left :: rest)
    (hcode : Assembly.CodeAt whole [.mul] state.pc) :
    run 1 whole env state =
      { state with
        pc := state.pc + 1
        stack := (left * right) :: rest } := by
  rw [show 1 = 0 + 1 by omega,
    run_succ_of_codeAt 0 hrunning hcode]
  simp [run, stepInstruction, advance, hstack, Instruction.byteLength]

/-- EVM `SUB` on machine words.  Note the **reversed** stack shape: the left
operand is on top, so code generation must emit the right operand first. -/
theorem run_subWord (whole : Assembly) (env : ExecutionEnv)
    (state : ExecutionState) (left right : Word) (rest : List Word)
    (hrunning : state.exit = none)
    (hstack : state.stack = left :: right :: rest)
    (hcode : Assembly.CodeAt whole [.sub] state.pc) :
    run 1 whole env state =
      { state with
        pc := state.pc + 1
        stack := (left - right) :: rest } := by
  rw [show 1 = 0 + 1 by omega,
    run_succ_of_codeAt 0 hrunning hcode]
  simp [run, stepInstruction, advance, hstack, Instruction.byteLength]

/-- EVM `LT` on machine words: unsigned comparison, with the same reversed
stack shape as `SUB`. -/
theorem run_ltWord (whole : Assembly) (env : ExecutionEnv)
    (state : ExecutionState) (left right : Word) (rest : List Word)
    (hrunning : state.exit = none)
    (hstack : state.stack = left :: right :: rest)
    (hcode : Assembly.CodeAt whole [.lt] state.pc) :
    run 1 whole env state =
      { state with
        pc := state.pc + 1
        stack := boolWord (left.ult right) :: rest } := by
  rw [show 1 = 0 + 1 by omega,
    run_succ_of_codeAt 0 hrunning hcode]
  simp [run, stepInstruction, advance, hstack, Instruction.byteLength,
    BitVec.ult]

/-! ### Word expression fragments -/

/-- Semantic contract of compiled word expression code.

Machine words need no encoding — `encodeSimpleValue .word` is the identity — so
the fragment pushes its value directly.  This is *literally* `BoolExprCorrect`
composed with `encodeBool`, which `boolExprCorrect_iff_wordExprCorrect`
records. -/
def WordExprCorrect (pre : BoolExprPrecondition)
    (value : Word) (code : Assembly) : Prop :=
  ∀ (whole : Assembly) (env : ExecutionEnv) (state : ExecutionState)
      (rest : List Word),
    pre env state.storage →
    state.exit = none →
    state.stack = rest →
    Assembly.CodeAt whole code state.pc →
    run code.length whole env state =
      { state with
        pc := state.pc + code.byteLength
        stack := value :: rest }

/-- A Boolean fragment is exactly a word fragment carrying the canonical
encoding.  This is what lets word-consuming, Boolean-producing operations such
as `LT` reuse the word composition argument. -/
theorem boolExprCorrect_iff_wordExprCorrect {pre : BoolExprPrecondition}
    {value : Bool} {code : Assembly} :
    BoolExprCorrect pre value code ↔
      WordExprCorrect pre (encodeBool value) code := Iff.rfl

/-- `boolWord` and `encodeBool` are the same canonical zero/one encoding. -/
@[simp] theorem boolWord_eq_encodeBool (value : Bool) :
    boolWord value = encodeBool value := by
  cases value <;> rfl

/-- A variable-loading fragment is correct when it pushes the canonical storage
encoding of the variable's value.

One statement covers both types because `encodeSimpleValue` is `encodeBool` at
`.bool` and the identity at `.word` — the same unification that lets a Boolean
code fragment be a word fragment carrying an encoding. -/
def VariableCodeCorrect (pre : BoolExprPrecondition) {Γ : CtxSimple}
    (ρ : PlainEnv Γ) (variableCode : VariableCode Γ) : Prop :=
  ∀ {name : VarId} {τ : BaseTy} (binding : HasVar Γ name τ),
    WordExprCorrect pre (encodeSimpleValue τ (ρ.get binding))
      (variableCode binding)

/-- A compiled Boolean literal pushes its canonical word. -/
theorem run_pushBool (whole : Assembly) (env : ExecutionEnv)
    (state : ExecutionState) (value : Bool) (rest : List Word)
    (hrunning : state.exit = none) (hstack : state.stack = rest)
    (hcode : Assembly.CodeAt whole
      [.push (.one (byte (if value then 1 else 0)))] state.pc) :
    run 1 whole env state =
      { state with
        pc := state.pc + 2
        stack := encodeBool value :: rest } := by
  rw [show 1 = 0 + 1 by omega,
    run_succ_of_codeAt 0 hrunning hcode]
  cases value <;>
    simp [run, stepInstruction, advance, hstack, Instruction.byteLength,
      encodeBool]

/-- Boolean equality consumes two canonical operands and pushes its canonical
result. -/
theorem run_eqBool (whole : Assembly) (env : ExecutionEnv)
    (state : ExecutionState) (left right : Bool) (rest : List Word)
    (hrunning : state.exit = none)
    (hstack : state.stack = encodeBool right :: encodeBool left :: rest)
    (hcode : Assembly.CodeAt whole [.eq] state.pc) :
    run 1 whole env state =
      { state with
        pc := state.pc + 1
        stack := encodeBool (decide (left = right)) :: rest } := by
  rw [show 1 = 0 + 1 by omega,
    run_succ_of_codeAt 0 hrunning hcode]
  cases left <;> cases right <;>
    simp [run, stepInstruction, advance, hstack, boolWord,
      Instruction.byteLength, encodeBool]

/-- Boolean conjunction consumes two canonical operands and pushes its
canonical result. -/
theorem run_andBool (whole : Assembly) (env : ExecutionEnv)
    (state : ExecutionState) (left right : Bool) (rest : List Word)
    (hrunning : state.exit = none)
    (hstack : state.stack = encodeBool right :: encodeBool left :: rest)
    (hcode : Assembly.CodeAt whole [.and] state.pc) :
    run 1 whole env state =
      { state with
        pc := state.pc + 1
        stack := encodeBool (left && right) :: rest } := by
  rw [show 1 = 0 + 1 by omega,
    run_succ_of_codeAt 0 hrunning hcode]
  simp [run, stepInstruction, advance, hstack, Instruction.byteLength]

/-- `ISZERO` implements Boolean negation on canonical operands. -/
theorem run_notBool (whole : Assembly) (env : ExecutionEnv)
    (state : ExecutionState) (value : Bool) (rest : List Word)
    (hrunning : state.exit = none)
    (hstack : state.stack = encodeBool value :: rest)
    (hcode : Assembly.CodeAt whole [.iszero] state.pc) :
    run 1 whole env state =
      { state with
        pc := state.pc + 1
        stack := encodeBool (!value) :: rest } := by
  rw [show 1 = 0 + 1 by omega,
    run_succ_of_codeAt 0 hrunning hcode]
  cases value <;>
    simp [run, stepInstruction, advance, hstack, boolWord,
      Instruction.byteLength, encodeBool]

/-- The branchless selection circuit implements Boolean conditional choice and
removes all three input words. -/
theorem run_boolSelect (whole : Assembly) (env : ExecutionEnv)
    (state : ExecutionState) (condition yes no : Bool) (rest : List Word)
    (hrunning : state.exit = none)
    (hstack : state.stack =
      encodeBool yes :: encodeBool no :: encodeBool condition :: rest)
    (hcode : Assembly.CodeAt whole boolSelectAssembly state.pc) :
    run boolSelectAssembly.length whole env state =
      { state with
        pc := state.pc + boolSelectAssembly.byteLength
        stack := encodeBool (if condition then yes else no) :: rest } := by
  apply StraightRun.run_eq ?_ hcode
  cases condition <;> cases yes <;> cases no <;>
    simp [StraightRun, boolSelectAssembly, stepInstruction, advance, hstack,
      hrunning, Assembly.byteLength, Instruction.byteLength, encodeBool]

/-- A fixed calldata load implements one Boolean variable when the read
precondition supplies exact key representation and the expected canonical
word. -/
theorem loadCalldataWord_correct (pre : BoolExprPrecondition)
    (offset : Nat) (value : Word)
    (hread : ∀ env storage, pre env storage →
      offset < 2 ^ 256 ∧
      calldataLoad env.calldata offset = value) :
    WordExprCorrect pre value (loadCalldataWord offset) := by
  intro whole env state rest hpre hrunning hstack hcode
  rcases hread env state.storage hpre with ⟨hoffset, hload⟩
  have hkey : (PushData.nat256 offset).value.toNat = offset :=
    PushData.nat256_value_toNat_of_lt hoffset
  apply StraightRun.run_eq ?_ hcode
  simp only [loadCalldataWord, StraightRun]
  rw [hrunning]
  simp only [stepInstruction, advance]
  rw [hstack, hkey, hload]
  simp [Assembly.byteLength, Instruction.byteLength, hrunning]

/-- A fixed total-storage load implements one Boolean variable under the
corresponding canonical-cell precondition. -/
theorem loadStorageWord_correct (pre : BoolExprPrecondition)
    (slot : Nat) (value : Word)
    (hread : ∀ env storage, pre env storage →
      slot < 2 ^ 256 ∧ storage slot = value) :
    WordExprCorrect pre value (loadStorageWord slot) := by
  intro whole env state rest hpre hrunning hstack hcode
  rcases hread env state.storage hpre with ⟨hslot, hload⟩
  have hkey : (PushData.nat256 slot).value.toNat = slot :=
    PushData.nat256_value_toNat_of_lt hslot
  apply StraightRun.run_eq ?_ hcode
  simp only [loadStorageWord, StraightRun]
  rw [hrunning]
  simp only [stepInstruction, advance]
  rw [hstack, hkey, hload]
  simp [Assembly.byteLength, Instruction.byteLength, hrunning]

theorem BoolExprCorrect.literal (pre : BoolExprPrecondition) (value : Bool) :
    BoolExprCorrect pre value
      [.push (.one (byte (if value then 1 else 0)))] := by
  intro whole env state rest _hpre hrunning hstack hcode
  exact run_pushBool whole env state value rest hrunning hstack hcode

/-- **The one sequential-composition argument** shared by every binary word
operation: run the first fragment, run the second on top of its result, then
one instruction consuming both.

Factoring this out is what keeps the operand-order discipline honest.  Each
operation instantiates `first` and `second` in the order its opcode actually
reads them — left-then-right for `ADD` and `MUL`, right-then-left for `SUB` and
`LT` — and this shared proof does not care which, so the ordering is stated once
per operation instead of being retyped inside five near-identical proofs. -/
theorem WordExprCorrect.seqBinary {pre : BoolExprPrecondition}
    {first second result : Word} {firstCode secondCode : Assembly}
    {instr : Instruction}
    (hbyte : instr.byteLength = 1)
    (hfirst : WordExprCorrect pre first firstCode)
    (hsecond : WordExprCorrect pre second secondCode)
    (hinstr : ∀ (whole : Assembly) (env : ExecutionEnv)
        (state : ExecutionState) (rest : List Word),
        state.exit = none →
        state.stack = second :: first :: rest →
        Assembly.CodeAt whole [instr] state.pc →
        run 1 whole env state =
          { state with pc := state.pc + 1, stack := result :: rest }) :
    WordExprCorrect pre result (firstCode ++ secondCode ++ [instr]) := by
  intro whole env state rest hpre hrunning hstack hcode
  have hcode' : Assembly.CodeAt whole
      (firstCode ++ (secondCode ++ [instr])) state.pc := by
    simpa [List.append_assoc] using hcode
  have hfirstCode := hcode'.left
  have htailCode := hcode'.right
  let afterFirst : ExecutionState :=
    { state with
      pc := state.pc + firstCode.byteLength
      stack := first :: rest }
  have hrunFirst : run firstCode.length whole env state = afterFirst := by
    simpa [afterFirst] using
      hfirst whole env state rest hpre hrunning hstack hfirstCode
  have hafterFirstRunning : afterFirst.exit = none := by
    simp [afterFirst, hrunning]
  have hafterFirstPre : pre env afterFirst.storage := by
    simpa [afterFirst] using hpre
  have hsecondCode : Assembly.CodeAt whole secondCode afterFirst.pc := by
    have := htailCode.left
    simpa [afterFirst] using this
  let afterSecond : ExecutionState :=
    { afterFirst with
      pc := afterFirst.pc + secondCode.byteLength
      stack := second :: first :: rest }
  have hrunSecond :
      run secondCode.length whole env afterFirst = afterSecond := by
    apply hsecond whole env afterFirst (first :: rest) hafterFirstPre
    · exact hafterFirstRunning
    · simp [afterFirst]
    · exact hsecondCode
  have hafterSecondRunning : afterSecond.exit = none := by
    simp [afterSecond, afterFirst, hrunning]
  have hinstrCode : Assembly.CodeAt whole [instr] afterSecond.pc := by
    have := htailCode.right
    simpa [afterSecond, afterFirst] using this
  have hrunInstr : run 1 whole env afterSecond =
      { afterSecond with
        pc := afterSecond.pc + 1
        stack := result :: rest } := by
    apply hinstr whole env afterSecond rest hafterSecondRunning
    · simp [afterSecond]
    · exact hinstrCode
  have hlength :
      (firstCode ++ secondCode ++ [instr]).length =
      firstCode.length + (secondCode.length + 1) := by simp
  rw [hlength, run_add, hrunFirst, run_add, hrunSecond, hrunInstr]
  -- `hbyte` must fire before `Instruction.byteLength` is unfolded into a
  -- match, which would destroy the shape it matches.
  simp [afterSecond, afterFirst, Assembly.byteLength, hbyte]
  omega

/-- EVM `ADD`; operands emitted left-then-right. -/
theorem WordExprCorrect.add {pre : BoolExprPrecondition}
    {left right : Word} {leftCode rightCode : Assembly}
    (hleft : WordExprCorrect pre left leftCode)
    (hright : WordExprCorrect pre right rightCode) :
    WordExprCorrect pre (left + right) (leftCode ++ rightCode ++ [.add]) :=
  seqBinary rfl hleft hright fun whole env state rest hrun hstack hcode =>
    run_addWord whole env state left right rest hrun hstack hcode

/-- EVM `MUL`; operands emitted left-then-right. -/
theorem WordExprCorrect.mul {pre : BoolExprPrecondition}
    {left right : Word} {leftCode rightCode : Assembly}
    (hleft : WordExprCorrect pre left leftCode)
    (hright : WordExprCorrect pre right rightCode) :
    WordExprCorrect pre (left * right) (leftCode ++ rightCode ++ [.mul]) :=
  seqBinary rfl hleft hright fun whole env state rest hrun hstack hcode =>
    run_mulWord whole env state left right rest hrun hstack hcode

/-- EVM `SUB`; operands emitted **right-then-left**, because `SUB` reads its
minuend from the top of the stack. -/
theorem WordExprCorrect.sub {pre : BoolExprPrecondition}
    {left right : Word} {leftCode rightCode : Assembly}
    (hleft : WordExprCorrect pre left leftCode)
    (hright : WordExprCorrect pre right rightCode) :
    WordExprCorrect pre (left - right) (rightCode ++ leftCode ++ [.sub]) :=
  seqBinary rfl hright hleft fun whole env state rest hrun hstack hcode =>
    run_subWord whole env state left right rest hrun hstack hcode

/-- EVM `LT`, unsigned, producing a canonical Boolean word.  Operands emitted
**right-then-left**, as for `SUB`. -/
theorem BoolExprCorrect.lessWord {pre : BoolExprPrecondition}
    {left right : Word} {leftCode rightCode : Assembly}
    (hleft : WordExprCorrect pre left leftCode)
    (hright : WordExprCorrect pre right rightCode) :
    BoolExprCorrect pre (left.ult right) (rightCode ++ leftCode ++ [.lt]) := by
  rw [boolExprCorrect_iff_wordExprCorrect]
  refine WordExprCorrect.seqBinary rfl hright hleft ?_
  intro whole env state rest hrun hstack hcode
  simpa using run_ltWord whole env state left right rest hrun hstack hcode

/-- EVM `EQ` on machine words, producing a canonical Boolean word. -/
theorem BoolExprCorrect.wordEqual {pre : BoolExprPrecondition}
    {left right : Word} {leftCode rightCode : Assembly}
    (hleft : WordExprCorrect pre left leftCode)
    (hright : WordExprCorrect pre right rightCode) :
    BoolExprCorrect pre (decide (left = right))
      (leftCode ++ rightCode ++ [.eq]) := by
  rw [boolExprCorrect_iff_wordExprCorrect]
  refine WordExprCorrect.seqBinary rfl hleft hright ?_
  intro whole env state rest hrun hstack hcode
  rw [show 1 = 0 + 1 by omega, run_succ_of_codeAt 0 hrun hcode]
  simp [run, stepInstruction, advance, hstack, Instruction.byteLength]

/-- A compiled word literal pushes its full 32-byte value. -/
theorem WordExprCorrect.literal (pre : BoolExprPrecondition) (value : Word) :
    WordExprCorrect pre value [.push (.word value)] := by
  intro whole env state rest _hpre hrunning hstack hcode
  rw [show ([Instruction.push (PushData.word value)] : Assembly).length
        = 0 + 1 by simp,
    run_succ_of_codeAt 0 hrunning hcode]
  simp [run, stepInstruction, advance, hstack, Assembly.byteLength,
    Instruction.byteLength, PushData.word]

/-- **Word code generation is correct.**

Compiled word expression code pushes exactly the value the IR denotes, leaving
the rest of the stack untouched.  Compositional in the variable-loading code,
so calldata-backed and storage-backed word reads instantiate the same result —
and the operand-order discipline of `compile` is discharged here, once, by the
`add`/`mul`/`sub` composition lemmas whose stack shapes were proved against the
interpreter. -/
theorem WordExprIR.compile_correct
    {Γ : CtxSimple}
    (pre : BoolExprPrecondition)
    (variableCode : VariableCode Γ)
    (ρ : PlainEnv Γ)
    (hvariable : VariableCodeCorrect pre ρ variableCode)
    (expr : WordExprIR Γ) :
    WordExprCorrect pre (expr.eval ρ) (expr.compile variableCode) := by
  induction expr with
  | «variable» name binding => exact hvariable binding
  | literal value => exact WordExprCorrect.literal pre value
  | add left right ihleft ihright => exact ihleft.add ihright
  | mul left right ihleft ihright => exact ihleft.mul ihright
  | sub left right ihleft ihright => exact ihleft.sub ihright

/-- Sequential composition with EVM equality preserves expression
correctness. -/
theorem BoolExprCorrect.eq {pre : BoolExprPrecondition}
    {left right : Bool} {leftCode rightCode : Assembly}
    (hleft : BoolExprCorrect pre left leftCode)
    (hright : BoolExprCorrect pre right rightCode) :
    BoolExprCorrect pre (decide (left = right))
      (leftCode ++ rightCode ++ [.eq]) := by
  intro whole env state rest hpre hrunning hstack hcode
  have hcode' : Assembly.CodeAt whole
      (leftCode ++ (rightCode ++ [.eq])) state.pc := by
    simpa [List.append_assoc] using hcode
  have hleftCode := hcode'.left
  have htailCode := hcode'.right
  let afterLeft : ExecutionState :=
    { state with
      pc := state.pc + leftCode.byteLength
      stack := encodeBool left :: rest }
  have hrunLeft : run leftCode.length whole env state = afterLeft := by
    simpa [afterLeft] using
      hleft whole env state rest hpre hrunning hstack hleftCode
  have hafterLeftRunning : afterLeft.exit = none := by
    simp [afterLeft, hrunning]
  have hafterLeftPre : pre env afterLeft.storage := by
    simpa [afterLeft] using hpre
  have hrightCode : Assembly.CodeAt whole rightCode afterLeft.pc := by
    have := htailCode.left
    simpa [afterLeft] using this
  let afterRight : ExecutionState :=
    { afterLeft with
      pc := afterLeft.pc + rightCode.byteLength
      stack := encodeBool right :: encodeBool left :: rest }
  have hrunRight :
      run rightCode.length whole env afterLeft = afterRight := by
    apply hright whole env afterLeft (encodeBool left :: rest) hafterLeftPre
    · exact hafterLeftRunning
    · simp [afterLeft]
    · exact hrightCode
  have hafterRightRunning : afterRight.exit = none := by
    simp [afterRight, afterLeft, hrunning]
  have heqCode : Assembly.CodeAt whole [.eq] afterRight.pc := by
    have := htailCode.right
    simpa [afterRight, afterLeft] using this
  have hrunEq : run 1 whole env afterRight =
      { afterRight with
        pc := afterRight.pc + 1
        stack := encodeBool (decide (left = right)) :: rest } := by
    apply run_eqBool whole env afterRight left right rest
      hafterRightRunning
    · simp [afterRight]
    · exact heqCode
  have hlength :
      (leftCode ++ rightCode ++ [Instruction.eq]).length =
      leftCode.length + (rightCode.length + 1) := by simp
  rw [hlength,
    run_add, hrunLeft, run_add, hrunRight, hrunEq]
  simp [afterRight, afterLeft, Assembly.byteLength, Instruction.byteLength]
  omega

/-- Sequential composition with bitwise `AND` preserves expression
correctness for canonical Boolean words. -/
theorem BoolExprCorrect.and {pre : BoolExprPrecondition} {left right : Bool}
    {leftCode rightCode : Assembly}
    (hleft : BoolExprCorrect pre left leftCode)
    (hright : BoolExprCorrect pre right rightCode) :
    BoolExprCorrect pre (left && right)
      (leftCode ++ rightCode ++ [.and]) := by
  intro whole env state rest hpre hrunning hstack hcode
  have hcode' : Assembly.CodeAt whole
      (leftCode ++ (rightCode ++ [.and])) state.pc := by
    simpa [List.append_assoc] using hcode
  have hleftCode := hcode'.left
  have htailCode := hcode'.right
  let afterLeft : ExecutionState :=
    { state with
      pc := state.pc + leftCode.byteLength
      stack := encodeBool left :: rest }
  have hrunLeft : run leftCode.length whole env state = afterLeft := by
    simpa [afterLeft] using
      hleft whole env state rest hpre hrunning hstack hleftCode
  have hafterLeftRunning : afterLeft.exit = none := by
    simp [afterLeft, hrunning]
  have hafterLeftPre : pre env afterLeft.storage := by
    simpa [afterLeft] using hpre
  have hrightCode : Assembly.CodeAt whole rightCode afterLeft.pc := by
    have := htailCode.left
    simpa [afterLeft] using this
  let afterRight : ExecutionState :=
    { afterLeft with
      pc := afterLeft.pc + rightCode.byteLength
      stack := encodeBool right :: encodeBool left :: rest }
  have hrunRight :
      run rightCode.length whole env afterLeft = afterRight := by
    apply hright whole env afterLeft (encodeBool left :: rest) hafterLeftPre
    · exact hafterLeftRunning
    · simp [afterLeft]
    · exact hrightCode
  have hafterRightRunning : afterRight.exit = none := by
    simp [afterRight, afterLeft, hrunning]
  have handCode : Assembly.CodeAt whole [.and] afterRight.pc := by
    have := htailCode.right
    simpa [afterRight, afterLeft] using this
  have hrunAnd : run 1 whole env afterRight =
      { afterRight with
        pc := afterRight.pc + 1
        stack := encodeBool (left && right) :: rest } := by
    apply run_andBool whole env afterRight left right rest
      hafterRightRunning
    · simp [afterRight]
    · exact handCode
  have hlength :
      (leftCode ++ rightCode ++ [Instruction.and]).length =
      leftCode.length + (rightCode.length + 1) := by simp
  rw [hlength,
    run_add, hrunLeft, run_add, hrunRight, hrunAnd]
  simp [afterRight, afterLeft, Assembly.byteLength, Instruction.byteLength]
  omega

/-- Sequential composition with `ISZERO` preserves expression correctness. -/
theorem BoolExprCorrect.not {pre : BoolExprPrecondition}
    {value : Bool} {code : Assembly}
    (hcodeCorrect : BoolExprCorrect pre value code) :
    BoolExprCorrect pre (!value) (code ++ [.iszero]) := by
  intro whole env state rest hpre hrunning hstack hcode
  have hexprCode := hcode.left
  have hnotCode := hcode.right
  let after : ExecutionState :=
    { state with
      pc := state.pc + code.byteLength
      stack := encodeBool value :: rest }
  have hrunExpr : run code.length whole env state = after := by
    simpa [after] using
      hcodeCorrect whole env state rest hpre hrunning hstack hexprCode
  have hafterRunning : after.exit = none := by
    simp [after, hrunning]
  have hnotCode' : Assembly.CodeAt whole [.iszero] after.pc := by
    simpa [after] using hnotCode
  have hrunNot := run_notBool whole env after value rest hafterRunning
    (by simp [after]) hnotCode'
  have hlength : (code ++ [Instruction.iszero]).length =
      code.length + 1 := by simp
  rw [hlength, run_add, hrunExpr, hrunNot]
  simp [after, Assembly.byteLength, Instruction.byteLength]
  omega

/-- Sequential composition with the branchless selection circuit preserves
expression correctness. -/
theorem BoolExprCorrect.select {pre : BoolExprPrecondition}
    {condition yes no : Bool}
    {conditionCode noCode yesCode : Assembly}
    (hcondition : BoolExprCorrect pre condition conditionCode)
    (hno : BoolExprCorrect pre no noCode)
    (hyes : BoolExprCorrect pre yes yesCode) :
    BoolExprCorrect pre (if condition then yes else no)
      (conditionCode ++ noCode ++ yesCode ++ boolSelectAssembly) := by
  intro whole env state rest hpre hrunning hstack hcode
  have hcode' : Assembly.CodeAt whole
      (conditionCode ++ (noCode ++ (yesCode ++ boolSelectAssembly)))
      state.pc := by
    simpa [List.append_assoc] using hcode
  have hconditionCode := hcode'.left
  have htail1 := hcode'.right
  let afterCondition : ExecutionState :=
    { state with
      pc := state.pc + conditionCode.byteLength
      stack := encodeBool condition :: rest }
  have hrunCondition :
      run conditionCode.length whole env state = afterCondition := by
    simpa [afterCondition] using
      hcondition whole env state rest hpre hrunning hstack hconditionCode
  have hconditionRunning : afterCondition.exit = none := by
    simp [afterCondition, hrunning]
  have hconditionPre : pre env afterCondition.storage := by
    simpa [afterCondition] using hpre
  have hnoCode : Assembly.CodeAt whole noCode afterCondition.pc := by
    have := htail1.left
    simpa [afterCondition] using this
  let afterNo : ExecutionState :=
    { afterCondition with
      pc := afterCondition.pc + noCode.byteLength
      stack := encodeBool no :: encodeBool condition :: rest }
  have hrunNo : run noCode.length whole env afterCondition = afterNo := by
    apply hno whole env afterCondition (encodeBool condition :: rest)
      hconditionPre
    · exact hconditionRunning
    · simp [afterCondition]
    · exact hnoCode
  have hnoRunning : afterNo.exit = none := by
    simp [afterNo, afterCondition, hrunning]
  have hnoPre : pre env afterNo.storage := by
    simpa [afterNo, afterCondition] using hpre
  have htail2 := htail1.right
  have hyesCode : Assembly.CodeAt whole yesCode afterNo.pc := by
    have := htail2.left
    simpa [afterNo, afterCondition] using this
  let afterYes : ExecutionState :=
    { afterNo with
      pc := afterNo.pc + yesCode.byteLength
      stack := encodeBool yes :: encodeBool no :: encodeBool condition :: rest }
  have hrunYes : run yesCode.length whole env afterNo = afterYes := by
    apply hyes whole env afterNo
      (encodeBool no :: encodeBool condition :: rest)
      hnoPre
    · exact hnoRunning
    · simp [afterNo]
    · exact hyesCode
  have hyesRunning : afterYes.exit = none := by
    simp [afterYes, afterNo, afterCondition, hrunning]
  have hselectCode :
      Assembly.CodeAt whole boolSelectAssembly afterYes.pc := by
    have := htail2.right
    simpa [afterYes, afterNo, afterCondition] using this
  have hrunSelect := run_boolSelect whole env afterYes condition yes no rest
    hyesRunning (by simp [afterYes]) hselectCode
  have hlength :
      (conditionCode ++ noCode ++ yesCode ++ boolSelectAssembly).length =
      conditionCode.length +
        (noCode.length + (yesCode.length + boolSelectAssembly.length)) := by
    simp
  rw [hlength, run_add, hrunCondition, run_add, hrunNo, run_add, hrunYes,
    hrunSelect]
  simp [afterYes, afterNo, afterCondition, Assembly.byteLength]
  omega

/-- **End-to-end word expression compilation is correct.**

Whenever `compileWordExpr?` accepts a source expression, the assembly it emits
pushes exactly that expression's value under `evalExpr`.  This is the statement
that connects source syntax to executable EVM code: the IR is an internal step,
and nothing about it appears here. -/
theorem compileWordExpr?_correct
    {Γ : CtxSimple}
    (pre : BoolExprPrecondition)
    (maxStack : Nat)
    (variableCode : VariableCode Γ)
    (ρ : PlainEnv Γ)
    (hvariable : VariableCodeCorrect pre ρ variableCode)
    (source : Expr Γ .word) (code : Assembly)
    (hcompile : compileWordExpr? maxStack variableCode source = some code) :
    WordExprCorrect pre (evalExpr source ρ) code := by
  obtain ⟨lowered, _hfits, hcode⟩ :=
    compileWordExpr?_stackHeight_le maxStack variableCode source code hcompile
  subst hcode
  rw [← lowered.eval_eq ρ]
  exact WordExprIR.compile_correct pre variableCode ρ hvariable lowered.ir

/-- Total code generation for the accepted Boolean IR preserves its pure
meaning. -/
theorem BoolExprIR.compile_correct
    {Γ : CtxSimple}
    (pre : BoolExprPrecondition)
    (variableCode : VariableCode Γ)
    (ρ : PlainEnv Γ)
    (hvariable : VariableCodeCorrect pre ρ variableCode)
    (expr : BoolExprIR Γ) :
    BoolExprCorrect pre (expr.eval ρ) (expr.compile variableCode) := by
  induction expr with
  | «variable» name binding => exact hvariable binding
  | literal value => exact BoolExprCorrect.literal pre value
  | equal left right ihLeft ihRight =>
      exact BoolExprCorrect.eq ihLeft ihRight
  | conjunction left right ihLeft ihRight =>
      exact BoolExprCorrect.and ihLeft ihRight
  | negation expression ih => exact BoolExprCorrect.not ih
  | select condition yes no ihCondition ihYes ihNo =>
      exact BoolExprCorrect.select ihCondition ihNo ihYes
  | wordEqual left right =>
      exact BoolExprCorrect.wordEqual
        (WordExprIR.compile_correct pre variableCode ρ hvariable left)
        (WordExprIR.compile_correct pre variableCode ρ hvariable right)
  | wordLess left right =>
      exact BoolExprCorrect.lessWord
        (WordExprIR.compile_correct pre variableCode ρ hvariable left)
        (WordExprIR.compile_correct pre variableCode ρ hvariable right)

/-- Every successfully compiled Boolean expression executes to the exact source
value, assuming the caller-supplied variable fragments implement the supplied
typed environment. Unsupported source constructors cannot satisfy the compile
hypothesis. -/
theorem compileBoolExpr?_correct
    {Γ : CtxSimple}
    (pre : BoolExprPrecondition)
    (variableCode : VariableCode Γ)
    (ρ : PlainEnv Γ)
    (hvariable : VariableCodeCorrect pre ρ variableCode)
    (expr : Expr Γ .bool) (code : Assembly)
    (maxStack : Nat)
    (hcompile : compileBoolExpr? maxStack variableCode expr = some code) :
    BoolExprCorrect pre (evalExpr expr ρ) code := by
  cases hlower : lowerBoolExpr? expr with
  | none => simp [compileBoolExpr?, hlower] at hcompile
  | some lowered =>
      simp only [compileBoolExpr?, hlower] at hcompile
      split at hcompile
      · simp only [Option.some.injEq] at hcompile
        subst code
        rw [← lowered.eval_eq ρ]
        exact BoolExprIR.compile_correct pre variableCode ρ hvariable lowered.ir
      · contradiction

/-- Concrete dynamic read invariant for one retained commit guard. The head
environment binding is the proposed action calldata word; every tail binding
is its assigned graph storage cell. -/
def simpleGuardReadPrecondition (code : GuardCode simpleExpr .bool)
    (ρ : PlainEnv ((code.actionName, .bool) :: code.Context)) :
    BoolExprPrecondition :=
  fun env storage =>
    calldataLoad env.calldata 68 = encodeBool (ρ.get .here) ∧
    ∀ {name : VarId} {τ : BaseTy} (binding : HasVar code.Context name τ),
      code.fieldOf binding < 2 ^ 256 ∧
      storage (code.fieldOf binding) =
        encodeSimpleValue τ (ρ.get (.there binding))

/-- The concrete guard-variable adapter implements its corresponding typed
environment lookup under the guard read invariant. -/
theorem simpleGuardVariableCode_correct
    (code : GuardCode simpleExpr .bool)
    (ρ : PlainEnv ((code.actionName, .bool) :: code.Context)) :
    VariableCodeCorrect (simpleGuardReadPrecondition code ρ) ρ
      (simpleGuardVariableCode code) := by
  intro name τ binding
  cases binding with
  | here =>
      apply loadCalldataWord_correct _ 68
      intro env storage hpre
      exact ⟨by norm_num, hpre.1⟩
  | there stored =>
      apply loadStorageWord_correct _ (code.fieldOf stored)
      intro env storage hpre
      exact hpre.2 stored

/-- Successful retained-guard compilation pushes exactly the guard's source
Boolean value for every execution satisfying its calldata/storage read
invariant. -/
theorem compileSimpleGuardCode?_correct
    (code : GuardCode simpleExpr .bool)
    (ρ : PlainEnv ((code.actionName, .bool) :: code.Context))
    (assembly : Assembly)
    (hcompile : compileSimpleGuardCode? code = some assembly) :
    BoolExprCorrect (simpleGuardReadPrecondition code ρ)
      (evalExpr code.expr ρ) assembly := by
  exact compileBoolExpr?_correct (simpleGuardReadPrecondition code ρ)
    (simpleGuardVariableCode code) ρ
    (simpleGuardVariableCode_correct code ρ) code.expr assembly
    (stackLimit - 1) hcompile

end

end Vegas.Machine.Contract.EVM
