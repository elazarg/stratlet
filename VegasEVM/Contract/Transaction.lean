/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasEVM.Contract.Entropy

/-!
# Atomic transaction settlement

Blockchain execution applies a successful call's state and outbound actions,
but a reverted call retains the pre-call state and emits no actions. This pass
makes that rollback convention explicit without adding a scheduler, receipts,
or a concrete gas model.

The settlement projection commutes with entropy realization: sampling entropy,
running the deterministic contract, and settling has exactly the same law as
settling the stochastic contract result directly.
-/

noncomputable section

namespace Vegas.Machine.Contract.Blockchain

open GameTheory.Math.Probability

namespace DeterministicResult

/-- Apply a deterministic call result atomically. Reversion restores the
pre-call state and suppresses every outbound action. -/
def settle {State Action : Type} (prior : State) :
    DeterministicResult State Action → CallSuccess State Action
  | .success result => result
  | .revert _ => CallSuccess.silent prior

@[simp] theorem settle_success {State Action : Type} (prior : State)
    (result : CallSuccess State Action) :
    settle prior (.success result) = result := rfl

@[simp] theorem settle_revert {State Action : Type} (prior : State)
    (reason : RevertReason) :
    settle prior (.revert reason : DeterministicResult State Action) =
      CallSuccess.silent prior := rfl

end DeterministicResult

namespace ReceiveResult

/-- Law of the atomically committed state and action trace. -/
def settledLaw {State Action : Type} (prior : State) :
    ReceiveResult State Action → FinDist (CallSuccess State Action)
  | .success law => law
  | .revert _ => FinDist.pure (CallSuccess.silent prior)

@[simp] theorem settledLaw_success {State Action : Type} (prior : State)
    (law : FinDist (CallSuccess State Action)) :
    (ReceiveResult.success law).settledLaw prior = law := rfl

@[simp] theorem settledLaw_revert {State Action : Type} (prior : State)
    (reason : RevertReason) :
    (ReceiveResult.revert (State := State) (Action := Action) reason).settledLaw
        prior =
      FinDist.pure (CallSuccess.silent prior) := rfl

/-- Settling after exposing deterministic outcomes equals settling the
stochastic call result directly. -/
theorem map_settle_outcomeLaw {State Action : Type} (prior : State)
    (result : ReceiveResult State Action) :
    result.outcomeLaw.map (DeterministicResult.settle prior) =
      result.settledLaw prior := by
  cases result with
  | success law =>
      rw [outcomeLaw, FinDist.map_comp]
      change FinDist.map id law = law
      exact FinDist.map_id law
  | revert reason =>
      simp [outcomeLaw, settledLaw, DeterministicResult.settle]

end ReceiveResult

namespace EntropyRealization

variable {Address Msg State Action : Type}
variable {contract : StochasticContract Address Msg State Action}

/-- Entropy determinization preserves the atomically settled transaction law,
including rollback and suppression of actions on revert. -/
theorem settled_law (realization : EntropyRealization contract)
    (chain : ChainView) (context : CallContext Address)
    (state : State) (message : Msg) :
    (realization.entropyLaw chain context state message).map
        (fun entropy =>
          DeterministicResult.settle state
            (realization.receive chain context state message entropy)) =
      (contract.receive chain context state message).settledLaw state := by
  change
    (realization.entropyLaw chain context state message).map
        (DeterministicResult.settle state ∘
          realization.receive chain context state message) = _
  rw [← FinDist.map_comp, realization.law,
    ReceiveResult.map_settle_outcomeLaw]

end EntropyRealization

end Vegas.Machine.Contract.Blockchain
