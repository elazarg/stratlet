import Mathlib.Data.Real.Basic

/-!
# Strategic-Form Games

A generic strategic-form (normal-form) game abstraction.
Parameterized by a player type `ι` with decidable equality,
a strategy-type family, and expected-utility function.

Solution concepts (Nash equilibrium, dominance) live here so
that concrete representations (NFG, Proto, Dag) can reuse them.
-/

namespace StrategicForm

/-- A strategic-form game.
  - `ι` is the type of players
  - `Strategy i` is the type of strategies for player `i`
  - `eu σ i` is the expected utility to player `i` under strategy profile `σ` -/
structure Game (ι : Type) [DecidableEq ι] where
  Strategy : ι → Type
  eu : (∀ i, Strategy i) → ι → ℝ

variable {ι : Type} [DecidableEq ι]

/-- A strategy profile `σ` is a Nash equilibrium if no player can
    improve their payoff by unilateral deviation. -/
def Game.IsNash (G : Game ι) (σ : ∀ i, G.Strategy i) : Prop :=
  ∀ (who : ι) (s' : G.Strategy who),
    G.eu σ who ≥ G.eu (Function.update σ who s') who

/-- Action `s` is dominant for player `who` if, regardless of others'
    actions, `s` yields at least as high a payoff as any alternative. -/
def Game.IsDominant (G : Game ι) (who : ι) (s : G.Strategy who) : Prop :=
  ∀ (σ : ∀ i, G.Strategy i) (s' : G.Strategy who),
    G.eu (Function.update σ who s) who ≥ G.eu (Function.update σ who s') who

/-- If every player has a dominant strategy, the profile of dominant
    strategies is a Nash equilibrium. -/
theorem Game.dominant_is_nash (G : Game ι) (σ : ∀ i, G.Strategy i)
    (hdom : ∀ i, G.IsDominant i (σ i)) : G.IsNash σ := by
  intro who s'
  have h := hdom who σ s'
  simp only [Function.update_eq_self, ge_iff_le] at h
  exact h

end StrategicForm
