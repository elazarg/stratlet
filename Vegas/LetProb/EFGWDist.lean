import GameTheory.EFG
import Vegas.LetProb.WDist

/-!
# EFG WDist Evaluator

Bridge: behavioral strategy evaluator for `EFG.GameTree` using `WDist`.
Lives in `LetProb` because it connects the probability layer (`WDist`) to
the game-theory layer (`EFG.GameTree`), which is self-contained.
-/

namespace EFG

/-- A list-based behavioral strategy for WDist evaluation:
    maps each decision point to a list of NNReal weights. -/
abbrev ListStrategy := Nat → List NNReal

/-- Evaluate a game tree under a list-based behavioral strategy with bounded recursion depth,
    returning a `WDist` over payoff functions. -/
noncomputable def GameTree.evalWDistAux {ι : Type}
    (σ : ListStrategy) : Nat → GameTree ι → WDist NNReal (ι → ℝ)
  | _, .terminal payoff => WDist.pure payoff
  | 0, _ => WDist.zero
  | n + 1, .chance branches =>
      let pairs := branches.map (fun ⟨t, w⟩ => (GameTree.evalWDistAux σ n t, w))
      ⟨pairs.flatMap (fun (d, w) => d.weights.map (fun (v, w') => (v, w * w')))⟩
  | n + 1, .decision pid _player actions =>
      let dist := σ pid
      let actionDists := actions.map (fun t => GameTree.evalWDistAux σ n t)
      let pairs := actionDists.zip dist
      ⟨pairs.flatMap (fun (d, w) => d.weights.map (fun (v, w') => (v, w * w')))⟩

/-- Evaluate with sufficient fuel (1000 levels deep). -/
noncomputable def GameTree.evalWDist {ι : Type}
    (σ : ListStrategy) (t : GameTree ι) : WDist NNReal (ι → ℝ) :=
  GameTree.evalWDistAux σ 1000 t

@[simp] theorem evalWDist_terminal {ι : Type} (σ : ListStrategy) (payoff : ι → ℝ) :
    (GameTree.terminal payoff).evalWDist σ = WDist.pure payoff := by
  simp [GameTree.evalWDist, GameTree.evalWDistAux]

end EFG
