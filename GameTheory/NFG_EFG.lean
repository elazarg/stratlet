import Mathlib.Probability.ProbabilityMassFunction.Constructions

import GameTheory.KernelGame
import GameTheory.Probability
import GameTheory.NFG
import GameTheory.EFG

/-! ## NFG → EFG: simultaneous game as a sequential tree -/
namespace NFG

/-- Build an EFG tree from an NFG-style payoff function over action indices.
    Player 0 moves first (infoSet=0), then player 1 (infoSet=1), sequentially. -/
noncomputable def mkSimultaneousTree {ι : Type} (n₁ n₂ : Nat) (p₁ p₂ : ι)
    (payoff : Fin n₁ → Fin n₂ → GameTheory.Payoff ι) : EFG.GameTree ι :=
  .decision 0 p₁ n₁ (fun a₁ =>
    .decision 1 p₂ n₂ (fun a₂ =>
      .terminal (payoff a₁ a₂)))

/-- The EFG tree under a pure behavioral strategy produces the correct payoff. -/
theorem mkSimultaneousTree_evalDist {ι : Type} (n₁ n₂ : Nat) (p₁ p₂ : ι)
    (payoff : Fin n₁ → Fin n₂ → GameTheory.Payoff ι)
    (a₁ : Fin n₁) (a₂ : Fin n₂)
    (σ : EFG.BehavioralStrategy)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (hσ₁ : σ 0 n₁ hn₁ = PMF.pure a₁) (hσ₂ : σ 1 n₂ hn₂ = PMF.pure a₂) :
    (mkSimultaneousTree n₁ n₂ p₁ p₂ payoff).evalDist σ = PMF.pure (payoff a₁ a₂) := by
  simp [mkSimultaneousTree, EFG.GameTree.evalDist, dif_pos hn₁, dif_pos hn₂, hσ₁, hσ₂]

end NFG
