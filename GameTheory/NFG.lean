import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import GameTheory.StrategicForm
import GameTheory.OutcomeKernel
import GameTheory.EFG

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

/-- Convert an NFGame to a generic strategic-form game. -/
def NFGame.toStrategicForm (G : NFGame ι A) : StrategicForm.Game ι where
  Strategy := A
  eu := G.payoff

theorem IsNashPure_iff_strategicForm (G : NFGame ι A) (s : StrategyProfile A) :
    IsNashPure G s ↔ G.toStrategicForm.IsNash s := by
  simp [IsNashPure, StrategicForm.Game.IsNash, NFGame.toStrategicForm, deviate]

theorem IsDominant_iff_strategicForm (G : NFGame ι A) (i : ι) (a : A i) :
    IsDominant G i a ↔ G.toStrategicForm.IsDominant i a := by
  simp [IsDominant, StrategicForm.Game.IsDominant, NFGame.toStrategicForm, deviate]

/-- NFG as a deterministic kernel: pure profile → point-mass payoff distribution. -/
noncomputable def NFGame.toKernel (G : NFGame ι A) :
    GameTheory.Kernel (∀ i, A i) (GameTheory.Payoff ι) :=
  GameTheory.Kernel.ofFun (fun σ i => G.payoff σ i)

/-- NFG as a kernel-based game. Outcome type is the action profile. -/
noncomputable def NFGame.toKernelGame (G : NFGame ι A) :
    GameTheory.KernelGame ι where
  Strategy := A
  Outcome := ∀ i, A i
  payoff := G.payoff
  outcomeKernel := fun σ => PMF.pure σ

/-! ## NFG → EFG: simultaneous game as a sequential tree -/

/-- Build an EFG tree from an NFG-style payoff function over action indices.
    Player 0 moves first (pid=0), then player 1 (pid=1), sequentially. -/
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
    (hσ₁ : σ 0 n₁ = PMF.pure a₁) (hσ₂ : σ 1 n₂ = PMF.pure a₂) :
    (mkSimultaneousTree n₁ n₂ p₁ p₂ payoff).evalDist σ = PMF.pure (payoff a₁ a₂) := by
  simp [mkSimultaneousTree, EFG.GameTree.evalDist, hσ₁, hσ₂]

end NFG
