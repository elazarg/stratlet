/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasEVM.Contract.Blockchain

/-!
# Explicit entropy determinization

A blockchain contract executes deterministically once its environment and
inputs are fixed, while Vegas source semantics may prescribe a nontrivial
finite probability law. This module makes the missing refinement explicit.

An `EntropyRealization` supplies a deterministic receive function, a law for
its entropy input, and an exact pushforward theorem. It does not assert that a
real chain actually supplies that entropy law, that the seed is unpredictable,
or that adversaries cannot bias or withhold it. Those are obligations of a
concrete entropy-source pass.
-/

noncomputable section

namespace Vegas.Machine.Contract.Blockchain

open GameTheory.Math.Probability

variable {Address Msg State Action Entropy : Type}

/-- Result of one deterministic contract invocation after entropy is fixed. A
success retains the same ordered outbound-action trace as the stochastic
contract boundary. -/
inductive DeterministicResult (State Action : Type) where
  | success (result : CallSuccess State Action)
  | revert (reason : RevertReason)

namespace ReceiveResult

/-- Interpret a stochastic call result as a law over deterministic call
results. Reverts are point laws; successes transport their state-and-action
law. -/
def outcomeLaw {State Action : Type} :
    ReceiveResult State Action → FinDist (DeterministicResult State Action)
  | .success law => law.map .success
  | .revert reason => FinDist.pure (.revert reason)

@[simp] theorem outcomeLaw_success {State Action : Type}
    (law : FinDist (CallSuccess State Action)) :
    (ReceiveResult.success law).outcomeLaw = law.map .success := rfl

@[simp] theorem outcomeLaw_revert {State Action : Type}
    (reason : RevertReason) :
    (ReceiveResult.revert (State := State) (Action := Action) reason).outcomeLaw =
      FinDist.pure (.revert reason) := rfl

end ReceiveResult

/-- A deterministic contract interface with an explicit environment-provided
entropy input. -/
structure DeterministicContract
    (Address Message State Action Entropy : Type) where
  initial : State
  receive :
    ChainView → CallContext Address → State → Message → Entropy →
      DeterministicResult State Action

/-- Exact realization of a stochastic contract by deterministic execution and
an assumed finite entropy law. The law may depend on the public invocation
inputs; a concrete backend must justify that dependency and its security. -/
structure EntropyRealization
    (contract : StochasticContract Address Msg State Action) where
  Entropy : Type
  entropyLaw :
    ChainView → CallContext Address → State → Msg → FinDist Entropy
  receive :
    ChainView → CallContext Address → State → Msg → Entropy →
      DeterministicResult State Action
  law :
    ∀ chain context state message,
      (entropyLaw chain context state message).map
          (receive chain context state message) =
        (contract.receive chain context state message).outcomeLaw

namespace EntropyRealization

variable {contract : StochasticContract Address Msg State Action}
variable (realization : EntropyRealization contract)

/-- Forget the entropy-law certificate and expose the deterministic contract
implementation selected by the realization. -/
def toDeterministicContract :
    DeterministicContract Address Msg State Action realization.Entropy where
  initial := contract.initial
  receive := realization.receive

/-- A proof-facing exact realization that uses the desired deterministic
result itself as entropy. It demonstrates consistency of the interface but is
not a physical entropy implementation. -/
def semantic (contract : StochasticContract Address Msg State Action) :
    EntropyRealization contract where
  Entropy := DeterministicResult State Action
  entropyLaw := fun chain context state message =>
    (contract.receive chain context state message).outcomeLaw
  receive := fun _chain _context _state _message entropy => entropy
  law := by
    intro chain context state message
    exact FinDist.map_id _

end EntropyRealization

end Vegas.Machine.Contract.Blockchain
