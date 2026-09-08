/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.Machine
import VegasEVM.Contract.Classical

/-!
# Checked-source to deterministic classical contract

This module is the assembly point for the ordinary compiler.  A backend
configuration supplies representation and trusted deployment choices for the
machine generated from one checked source program.  `compile` returns the
complete deterministic classical contract.

The result is parameterized by its storage codec and physical identities, so a
concrete EVM backend can later refine the same artifact to bounded words,
selectors, instructions, and bytecode.  Strategic security against target-only
signals or deviations is intentionally a separate compiler layer.
-/

noncomputable section

namespace Vegas.ClassicalCompiler

open Machine
open Machine.Contract
open EventGraph

variable {Player Address : Type}
variable [DecidableEq Player] [DecidableEq Address]
variable {L : IExpr}

/-- All deployment choices required after the checked source has compiled to
its canonical machine program. -/
structure Backend (source : WFProgram Player L) (Address : Type)
    [DecidableEq Address] where
  codec : StorageCodec (Machine.compile source)
  players : PlayerRegistry Player Address
  reveals : TriggerPolicy Address
  sampleRequests : TriggerPolicy Address
  oracle : OracleRegistry Address

namespace Backend

variable {source : WFProgram Player L}
variable (backend : Backend source Address)

/-- The complete deterministic classical contract generated from checked
source and backend deployment choices. -/
def compile : ClassicalContract (Machine.compile source) Address where
  codec := backend.codec
  players := backend.players
  reveals := backend.reveals
  sampleRequests := backend.sampleRequests
  oracle := backend.oracle

/-- The compiler's executable endpoint in generic deterministic-contract
form. Messages contain no caller identity; authentication uses the blockchain
context's sender. Entropy is `Unit` because source chance has become oracle
calldata. -/
def artifact := backend.compile.toDeterministicContract

@[simp] theorem compile_codec : backend.compile.codec = backend.codec := rfl

@[simp] theorem compile_players :
    backend.compile.players = backend.players := rfl

@[simp] theorem compile_oracle : backend.compile.oracle = backend.oracle := rfl

/-- Constructor state is exactly the canonical encoding of the compiled
machine's initial state, with no pending oracle request. -/
theorem compile_initial :
    backend.compile.initial =
      OracleProtocol.idleState backend.codec (Machine.compile source).init :=
  rfl

/-- Every terminal compiler state exposes the payoff of an actual terminal
source environment. -/
theorem terminal_sourceOutcome
    (state : (Machine.compile source).State)
    (terminal : (Machine.compile source).terminal state) :
    ∃ sourceEnv :
        VEnv L (ToEventGraph.compile source.core).terminalCtx,
      backend.compile.terminalPayout?
          (backend.compile.encodeState state) =
        some (evalPayoffs
          (ToEventGraph.compile source.core).sourcePayoffs sourceEnv) := by
  unfold ClassicalContract.terminalPayout?
    ClassicalContract.encodeState OracleProtocol.idleState
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  exact Contract.terminalPayout?_compile_encodeState
    source backend.codec state terminal

/-- The compiled artifact retains the exact source payoff theorem through its
machine and deterministic contract boundary. -/
theorem terminal_sourceStar
    (state : (Machine.compile source).State)
    (terminal : (Machine.compile source).terminal state) :
    ∃ terminalEnv :
        VEnv L (ToEventGraph.compile source.core).terminalCtx,
      SmallStep.Star
        { ctx := source.core.Γ
          env := source.core.env
          cont := source.core.prog }
        { ctx := (ToEventGraph.compile source.core).terminalCtx
          env := terminalEnv
          cont := .ret
            (ToEventGraph.compile source.core).sourcePayoffs } ∧
      backend.compile.terminalPayout?
          (backend.compile.encodeState state) =
        some (evalPayoffs
          (ToEventGraph.compile source.core).sourcePayoffs terminalEnv) := by
  rcases Machine.compile_sourceStar source state terminal with
    ⟨terminalEnv, star, payoff, _agreement⟩
  refine ⟨terminalEnv, star, ?_⟩
  rw [backend.compile.terminalPayout?_encodeState_of_terminal state terminal]
  exact payoff

end Backend

end Vegas.ClassicalCompiler
