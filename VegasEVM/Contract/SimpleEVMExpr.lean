/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Core.ExprSimple
import VegasEVM.Contract.EVMLocalAssembly

/-!
# Boolean `simpleExpr` lowering to EVM

The first concrete expression backend compiles the exact Boolean fragment
needed by Boolean-storage games: variables, constants, Boolean equality,
conjunction, negation, and conditionals. Unsupported constructors reject
explicitly. In particular, this pass does not assign modular EVM semantics to
Vegas's unbounded integers or invent a one-word encoding for options.

Variables are lowered by a caller-supplied straight-line code fragment. The
graph guard adapter reads the proposed action from the third player argument
and stored Boolean dependencies from their certified field-value cells.

Conditionals use a canonical-Boolean selection circuit rather than dynamic
jumps. Besides simplifying executable refinement, this avoids making the
chosen pure expression branch observable through control flow.
-/

namespace Vegas.Machine.Contract.EVM

open EventGraph

noncomputable section

/-- Symbolic handler fragment plus the first unused local label. -/
structure GeneratedLocalCode where
  code : LocalAssembly
  nextLabel : Nat

/-- Load one 32-byte calldata word at a fixed byte offset. -/
def loadCalldataWord (offset : Nat) : Assembly :=
  [.push (.nat256 offset), .calldataload]

/-- Load one total-storage word at a fixed key. -/
def loadStorageWord (slot : Nat) : Assembly :=
  [.push (.nat256 slot), .sload]

/-- Select `yes` when the third stack word is one and `no` when it is zero.
Input is `yes :: no :: condition :: rest`; output is the selected canonical
Boolean word followed by `rest`. -/
def boolSelectAssembly : Assembly :=
  [ .dup ⟨1, by decide⟩,
    .xor,
    .swap ⟨1, by decide⟩,
    .swap ⟨0, by decide⟩,
    .swap ⟨1, by decide⟩,
    .and,
    .xor ]

/-- Code that loads one bound variable onto the stack as a single word.

Uniform in the variable's type on purpose: on the EVM a calldata word and a
storage slot are one 32-byte load either way, and what differs between types is
only how the loaded word is *interpreted* — which is exactly what
`encodeSimpleValue` records. -/
abbrev VariableCode (Γ : CtxSimple) : Type :=
  {name : VarId} → {τ : BaseTy} → HasVar Γ name τ → Assembly

/-- Closed word-valued expression IR accepted by the EVM backend.

Word expressions feed Boolean predicates and never the reverse — there is no
word-valued conditional here — so this needs no mutual recursion with
`BoolExprIR`.  A word-typed `ite` in the source is rejected by lowering rather
than compiled through a masking circuit. -/
inductive WordExprIR (Γ : CtxSimple) where
  | variable (name : VarId) (binding : HasVar Γ name .word)
  | literal (value : Val .word)
  | add (left right : WordExprIR Γ)
  | sub (left right : WordExprIR Γ)
  | mul (left right : WordExprIR Γ)

namespace WordExprIR

variable {Γ : CtxSimple}

/-- Pure meaning of the word backend IR: EVM arithmetic is arithmetic modulo
`2 ^ wordBits`, which is exactly `BitVec` arithmetic. -/
def eval (ρ : PlainEnv Γ) : WordExprIR Γ → Val .word
  | .variable _ binding => ρ.get binding
  | .literal value => value
  | .add left right => left.eval ρ + right.eval ρ
  | .sub left right => left.eval ρ - right.eval ρ
  | .mul left right => left.eval ρ * right.eval ρ

/-- Maximum additional EVM stack items used while evaluating.  A binary node
holds its first-emitted operand while evaluating the second, which is why `sub`
counts its operands in the opposite order from `add` and `mul`. -/
def stackHeight : WordExprIR Γ → Nat
  | .variable _ _ | .literal _ => 1
  | .add left right | .mul left right =>
      max left.stackHeight (1 + right.stackHeight)
  | .sub left right => max right.stackHeight (1 + left.stackHeight)

/-- Total straight-line code generation.

`add` and `mul` are commutative, so operand order is immaterial and they emit
left-then-right.  `sub` must emit **right-then-left**: `stepInstruction`
computes `top - next`, so the left operand has to end up on top.  See
`run_subWord`, whose stack shape is deliberately the mirror of `run_addWord`. -/
def compile (variableCode : VariableCode Γ) :
    WordExprIR Γ → Assembly
  | .variable _ binding => variableCode binding
  | .literal value => [.push (.word value)]
  | .add left right =>
      left.compile variableCode ++ right.compile variableCode ++ [.add]
  | .mul left right =>
      left.compile variableCode ++ right.compile variableCode ++ [.mul]
  | .sub left right =>
      right.compile variableCode ++ left.compile variableCode ++ [.sub]

end WordExprIR

/-- A successfully accepted source word expression carries the exact semantic
connection to its word backend IR. -/
structure LoweredWordExpr {Γ : CtxSimple} (source : Expr Γ .word) where
  ir : WordExprIR Γ
  eval_eq : ∀ ρ, ir.eval ρ = evalExpr source ρ

@[ext] theorem LoweredWordExpr.ext {Γ : CtxSimple} {source : Expr Γ .word}
    {left right : LoweredWordExpr source} (hir : left.ir = right.ir) :
    left = right := by
  cases left
  cases right
  cases hir
  rfl

/-- Validate and lower exactly the supported word source fragment.

Rejected on purpose: a word-typed `ite` would need a masking selection circuit,
and `getD` would need a one-word encoding of `option`.  Neither is invented
here, so both are refused rather than mis-compiled. -/
def lowerWordExpr? {Γ : CtxSimple} :
    (source : Expr Γ .word) → Option (LoweredWordExpr source)
  | .var name binding =>
      some { ir := .variable name binding, eval_eq := by intro; rfl }
  | .constWord value =>
      some { ir := .literal value, eval_eq := by intro; rfl }
  | .addWord left right =>
      match lowerWordExpr? left, lowerWordExpr? right with
      | some loweredLeft, some loweredRight =>
          some
            { ir := .add loweredLeft.ir loweredRight.ir
              eval_eq := by
                intro ρ
                simp only [WordExprIR.eval, evalExpr,
                  loweredLeft.eval_eq ρ, loweredRight.eval_eq ρ] }
      | _, _ => none
  | .subWord left right =>
      match lowerWordExpr? left, lowerWordExpr? right with
      | some loweredLeft, some loweredRight =>
          some
            { ir := .sub loweredLeft.ir loweredRight.ir
              eval_eq := by
                intro ρ
                simp only [WordExprIR.eval, evalExpr,
                  loweredLeft.eval_eq ρ, loweredRight.eval_eq ρ] }
      | _, _ => none
  | .mulWord left right =>
      match lowerWordExpr? left, lowerWordExpr? right with
      | some loweredLeft, some loweredRight =>
          some
            { ir := .mul loweredLeft.ir loweredRight.ir
              eval_eq := by
                intro ρ
                simp only [WordExprIR.eval, evalExpr,
                  loweredLeft.eval_eq ρ, loweredRight.eval_eq ρ] }
      | _, _ => none
  | _ => none

/-- Compile the supported word `simpleExpr` fragment to straight-line EVM
assembly only when its additional stack high-water mark fits `maxStack`. -/
def compileWordExpr?
    {Γ : CtxSimple}
    (maxStack : Nat)
    (variableCode : VariableCode Γ)
    (source : Expr Γ .word) : Option Assembly :=
  match lowerWordExpr? source with
  | none => none
  | some lowered =>
      if lowered.ir.stackHeight ≤ maxStack then
        some (lowered.ir.compile variableCode)
      else
        none

/-- Successful word lowering is statically bounded by the requested EVM stack
allowance. -/
theorem compileWordExpr?_stackHeight_le
    {Γ : CtxSimple}
    (maxStack : Nat)
    (variableCode : VariableCode Γ)
    (source : Expr Γ .word) (code : Assembly)
    (hcompile : compileWordExpr? maxStack variableCode source = some code) :
    ∃ lowered : LoweredWordExpr source,
      lowered.ir.stackHeight ≤ maxStack ∧
        code = lowered.ir.compile variableCode := by
  unfold compileWordExpr? at hcompile
  cases hlower : lowerWordExpr? source with
  | none => rw [hlower] at hcompile; exact absurd hcompile (by simp)
  | some lowered =>
      rw [hlower] at hcompile
      by_cases hfits : lowered.ir.stackHeight ≤ maxStack
      · simp only [hfits, ↓reduceIte, Option.some.injEq] at hcompile
        exact ⟨lowered, hfits, hcompile.symm⟩
      · simp only [hfits, ↓reduceIte] at hcompile
        exact absurd hcompile (by simp)


/-- Closed Boolean-only expression IR accepted by the EVM backend. Unsupported
source constructors are eliminated before code generation. -/
inductive BoolExprIR (Γ : CtxSimple) where
  | variable (name : VarId) (binding : HasVar Γ name .bool)
  | literal (value : Bool)
  | equal (left right : BoolExprIR Γ)
  | conjunction (left right : BoolExprIR Γ)
  | negation (expression : BoolExprIR Γ)
  | select (condition yes no : BoolExprIR Γ)
  /-- Equality of two word terms, via EVM `EQ`. -/
  | wordEqual (left right : WordExprIR Γ)
  /-- Unsigned comparison of two word terms, via EVM `LT`. -/
  | wordLess (left right : WordExprIR Γ)

namespace BoolExprIR

variable {Γ : CtxSimple}

/-- Pure meaning of the Boolean backend IR. -/
def eval (ρ : PlainEnv Γ) : BoolExprIR Γ → Bool
  | .variable _ binding => ρ.get binding
  | .literal value => value
  | .equal left right => decide (left.eval ρ = right.eval ρ)
  | .conjunction left right => left.eval ρ && right.eval ρ
  | .negation expression => !(expression.eval ρ)
  | .select condition yes no =>
      if condition.eval ρ then yes.eval ρ else no.eval ρ
  | .wordEqual left right => decide (left.eval ρ = right.eval ρ)
  | .wordLess left right => (left.eval ρ).ult (right.eval ρ)

/-- Maximum number of additional EVM stack items used while evaluating an
expression. Variable fragments are required to push exactly one word without
using more than that one additional item; the concrete calldata and storage
loaders below satisfy this contract. -/
def stackHeight : BoolExprIR Γ → Nat
  | .variable _ _ | .literal _ => 1
  | .equal left right | .conjunction left right =>
      max left.stackHeight (1 + right.stackHeight)
  | .negation expression => expression.stackHeight
  | .select condition yes no =>
      max condition.stackHeight
        (max (1 + no.stackHeight) (2 + yes.stackHeight))
  | .wordEqual left right =>
      max left.stackHeight (1 + right.stackHeight)
  -- `LT` reads its operands in the opposite order, so the right operand is
  -- emitted first and is the one held while the left is evaluated.
  | .wordLess left right =>
      max right.stackHeight (1 + left.stackHeight)

/-- Total straight-line code generation for the accepted Boolean IR. -/
def compile (variableCode : VariableCode Γ) :
    BoolExprIR Γ → Assembly
  | .variable _ binding => variableCode binding
  | .literal value => [.push (.one (byte (if value then 1 else 0)))]
  | .equal left right =>
      left.compile variableCode ++ right.compile variableCode ++ [.eq]
  | .conjunction left right =>
      left.compile variableCode ++ right.compile variableCode ++ [.and]
  | .negation expression => expression.compile variableCode ++ [.iszero]
  | .select condition yes no =>
      condition.compile variableCode ++ no.compile variableCode ++
        yes.compile variableCode ++ boolSelectAssembly
  | .wordEqual left right =>
      left.compile variableCode ++ right.compile variableCode ++ [.eq]
  -- Reversed, as for `SUB`: `LT` reads its first operand from the top.
  | .wordLess left right =>
      right.compile variableCode ++ left.compile variableCode ++ [.lt]

end BoolExprIR

/-- A successfully accepted source expression carries the exact semantic
connection to its Boolean-only backend IR. -/
structure LoweredBoolExpr {Γ : CtxSimple} (source : Expr Γ .bool) where
  ir : BoolExprIR Γ
  eval_eq : ∀ ρ, ir.eval ρ = evalExpr source ρ

@[ext] theorem LoweredBoolExpr.ext {Γ : CtxSimple} {source : Expr Γ .bool}
    {left right : LoweredBoolExpr source} (hir : left.ir = right.ir) :
    left = right := by
  cases left
  cases right
  cases hir
  rfl

/-- Validate and lower exactly the supported Boolean source fragment. -/
def lowerBoolExpr? {Γ : CtxSimple} :
    (source : Expr Γ .bool) → Option (LoweredBoolExpr source)
  | .var name binding =>
      some { ir := .variable name binding, eval_eq := by intro; rfl }
  | .constBool value =>
      some { ir := .literal value, eval_eq := by intro; rfl }
  | .eq (b := .bool) left right =>
      match lowerBoolExpr? left, lowerBoolExpr? right with
      | some loweredLeft, some loweredRight =>
          some
            { ir := .equal loweredLeft.ir loweredRight.ir
              eval_eq := by
                intro ρ
                simp only [BoolExprIR.eval, evalExpr,
                  loweredLeft.eval_eq ρ, loweredRight.eval_eq ρ] }
      | _, _ => none
  | .eq (b := .word) left right =>
      match lowerWordExpr? left, lowerWordExpr? right with
      | some loweredLeft, some loweredRight =>
          some
            { ir := .wordEqual loweredLeft.ir loweredRight.ir
              eval_eq := by
                intro ρ
                simp only [BoolExprIR.eval, evalExpr,
                  loweredLeft.eval_eq ρ, loweredRight.eval_eq ρ] }
      | _, _ => none
  | .ltWord left right =>
      match lowerWordExpr? left, lowerWordExpr? right with
      | some loweredLeft, some loweredRight =>
          some
            { ir := .wordLess loweredLeft.ir loweredRight.ir
              eval_eq := by
                intro ρ
                simp only [BoolExprIR.eval, evalExpr,
                  loweredLeft.eval_eq ρ, loweredRight.eval_eq ρ] }
      | _, _ => none
  | .eq (b := .int) _ _ => none
  | .eq (b := .range _ _) _ _ => none
  | .eq (b := .option _) _ _ => none
  | .andBool left right =>
      match lowerBoolExpr? left, lowerBoolExpr? right with
      | some loweredLeft, some loweredRight =>
          some
            { ir := .conjunction loweredLeft.ir loweredRight.ir
              eval_eq := by
                intro ρ
                simp only [BoolExprIR.eval, evalExpr,
                  loweredLeft.eval_eq ρ, loweredRight.eval_eq ρ] }
      | _, _ => none
  | .notBool expression =>
      match lowerBoolExpr? expression with
      | some lowered =>
          some
            { ir := .negation lowered.ir
              eval_eq := by
                intro ρ
                simp only [BoolExprIR.eval, evalExpr, lowered.eval_eq ρ] }
      | none => none
  | .ite condition yes no =>
      match lowerBoolExpr? condition, lowerBoolExpr? yes, lowerBoolExpr? no with
      | some loweredCondition, some loweredYes, some loweredNo =>
          some
            { ir := .select loweredCondition.ir loweredYes.ir loweredNo.ir
              eval_eq := by
                intro ρ
                simp only [BoolExprIR.eval, evalExpr,
                  loweredCondition.eval_eq ρ, loweredYes.eval_eq ρ,
                  loweredNo.eval_eq ρ] }
      | _, _, _ => none
  | _ => none

/-- Compile the supported Boolean `simpleExpr` fragment to straight-line EVM
assembly only when its additional stack high-water mark fits `maxStack`.
Variable fragments must obey the one-word contract of `BoolExprIR.stackHeight`.
-/
def compileBoolExpr?
    {Γ : CtxSimple}
    (maxStack : Nat)
    (variableCode : VariableCode Γ)
    (source : Expr Γ .bool) : Option Assembly :=
  match lowerBoolExpr? source with
  | none => none
  | some lowered =>
      if lowered.ir.stackHeight ≤ maxStack then
        some (lowered.ir.compile variableCode)
      else
        none

/-- Successful Boolean lowering is statically bounded by the requested EVM
stack allowance. -/
theorem compileBoolExpr?_stackHeight_le
    {Γ : CtxSimple}
    {maxStack : Nat}
    {variableCode : VariableCode Γ}
    {source : Expr Γ .bool} {assembly : Assembly}
    (hcompile :
      compileBoolExpr? maxStack variableCode source = some assembly) :
    ∃ lowered, lowerBoolExpr? source = some lowered ∧
      lowered.ir.stackHeight ≤ maxStack := by
  unfold compileBoolExpr? at hcompile
  split at hcompile
  · contradiction
  · rename_i lowered hlowered
    split at hcompile
    · rename_i hfits
      exact ⟨lowered, hlowered, hfits⟩
    · contradiction

/-- The action word is the third player-call argument, starting at byte 68. -/
def playerActionWord : Assembly := loadCalldataWord 68

/-- Resolve one Boolean guard variable to either the proposed action calldata
word or its retained graph field. -/
def simpleGuardVariableCode (code : GuardCode simpleExpr .bool)
    {name : VarId} {τ : BaseTy}
    (binding :
      HasVar ((code.actionName, .bool) :: code.Context) name τ) :
    Assembly :=
  match binding with
  | .here => playerActionWord
  | .there stored => loadStorageWord (code.fieldOf stored)

/-- Compile retained graph commit-guard code whose action word is Boolean.
The head binding is the proposed action; every tail binding is read from its
graph field-value cell. -/
def compileSimpleGuardCode? (code : GuardCode simpleExpr .bool) :
    Option Assembly :=
  compileBoolExpr?
    (stackLimit - 1)
    (simpleGuardVariableCode code)
    code.expr

/-- Player realization retains the proposed action below guard evaluation, so
successful guard compilation uses at most the remaining 1023 stack items. -/
theorem compileSimpleGuardCode?_stackHeight_le
    {code : GuardCode simpleExpr .bool} {assembly : Assembly}
    (hcompile : compileSimpleGuardCode? code = some assembly) :
    ∃ lowered, lowerBoolExpr? code.expr = some lowered ∧
      lowered.ir.stackHeight ≤ stackLimit - 1 := by
  exact compileBoolExpr?_stackHeight_le hcompile

@[simp] theorem compileBoolExpr?_constBool
    {Γ : CtxSimple}
    (maxStack : Nat) (hstack : 1 ≤ maxStack)
    (variableCode : VariableCode Γ)
    (value : Bool) :
    compileBoolExpr? maxStack variableCode (.constBool value) =
      some [.push (.one (byte (if value then 1 else 0)))] := by
  let lowered : LoweredBoolExpr (.constBool value) :=
    { ir := @BoolExprIR.literal Γ value
      eval_eq := by intro; simp [BoolExprIR.eval, evalExpr] }
  have hlower : lowerBoolExpr? (.constBool value) = some lowered := by
    unfold lowerBoolExpr?
    apply congrArg some
    apply LoweredBoolExpr.ext
    rfl
  simp [compileBoolExpr?, hlower, lowered, BoolExprIR.compile,
    BoolExprIR.stackHeight, hstack]

end

end Vegas.Machine.Contract.EVM
