import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Normal-Form Games (NFG)

Finite normal-form (strategic-form) games with pure strategies,
Nash equilibrium, and dominance.
-/

namespace NFG

/-- A finite normal-form game.
  - `ι` is the type of players
  - `A i` is the type of actions for player `i`
  - `payoff s i` is the payoff to player `i` under strategy profile `s` -/
structure NFGame (ι : Type) [Fintype ι] [DecidableEq ι]
    (A : ι → Type) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] where
  payoff : (∀ i, A i) → ι → ℝ

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {A : ι → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

/-- A (pure) strategy profile: each player picks an action. -/
abbrev StrategyProfile (A : ι → Type) := ∀ i, A i

/-- Deviate: replace player `i`'s action in profile `s` with `a`. -/
def deviate (s : StrategyProfile A) (i : ι) (a : A i) : StrategyProfile A :=
  Function.update s i a

omit [Fintype ι] [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] in
@[simp]
theorem deviate_same (s : StrategyProfile A) (i : ι) (a : A i) :
    deviate s i a i = a := by
  simp [deviate]

omit [Fintype ι] [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] in
@[simp]
theorem deviate_other (s : StrategyProfile A) (i j : ι) (a : A i) (h : j ≠ i) :
    deviate s i a j = s j := by
  simp [deviate, h]

/-- A pure Nash equilibrium: no player can improve by unilateral deviation. -/
def IsNashPure (G : NFGame ι A) (s : StrategyProfile A) : Prop :=
  ∀ i (a' : A i), G.payoff s i ≥ G.payoff (deviate s i a') i

/-- Action `a` is dominant for player `i`: regardless of others' actions,
    `a` yields at least as high a payoff as any alternative. -/
def IsDominant (G : NFGame ι A) (i : ι) (a : A i) : Prop :=
  ∀ (s : StrategyProfile A) (a' : A i),
    G.payoff (deviate s i a) i ≥ G.payoff (deviate s i a') i

/-- If every player has a dominant action, the profile of dominant actions
    is a pure Nash equilibrium. -/
theorem dominant_is_nash (G : NFGame ι A) (s : StrategyProfile A)
    (hdom : ∀ i, IsDominant G i (s i)) : IsNashPure G s := by
  intro i a'
  have h := hdom i s a'
  simp only [deviate, Function.update_eq_self, ge_iff_le] at h
  exact h

end NFG
