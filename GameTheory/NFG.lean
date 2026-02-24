import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import GameTheory.SolutionConcepts
import GameTheory.EFG

/-!
# Normal-Form Games (NFG)

Finite normal-form (strategic-form) games with pure strategies,
Nash equilibrium, and dominance.

Provides:
- `NFGame` — finite normal-form game structure
- `IsNashPure`, `IsDominant`, `dominant_is_nash` — pure solution concepts
- `toKernelGame` — bridge to `KernelGame`
- `IsNashPure_iff_kernelGame`, `IsDominant_iff_kernelGame` — bridge theorems
- `pmfPi` — independent product of PMFs (for mixed strategies)
- `toMixedKernelGame`, `IsNashMixed` — mixed strategy Nash
- `mkSimultaneousTree` — NFG → EFG embedding
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

/-- Deviate: replace player `i`'s action in profile `s` with `a`.
    This is `Function.update` kept for NFG readability. -/
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

/-! ## NFG → KernelGame bridge -/

/-- NFG as a deterministic kernel: pure profile → point-mass payoff distribution. -/
noncomputable def NFGame.toKernel (G : NFGame ι A) :
    GameTheory.Kernel (∀ i, A i) (GameTheory.Payoff ι) :=
  GameTheory.Kernel.ofFun G.payoff

/-- NFG as a kernel-based game. Outcome type is the action profile. -/
noncomputable def NFGame.toKernelGame (G : NFGame ι A) :
    GameTheory.KernelGame ι where
  Strategy := A
  Outcome := ∀ i, A i
  payoff := G.payoff
  outcomeKernel := fun σ => PMF.pure σ

/-- Pure Nash in NFG is equivalent to Nash in the kernel game. -/
theorem IsNashPure_iff_kernelGame (G : NFGame ι A) (s : StrategyProfile A) :
    IsNashPure G s ↔ G.toKernelGame.IsNash s := by
  simp only [IsNashPure, GameTheory.KernelGame.IsNash, GameTheory.KernelGame.eu,
      NFGame.toKernelGame, GameTheory.expect_pure, deviate]

/-- Dominance in NFG is equivalent to dominance in the kernel game. -/
theorem IsDominant_iff_kernelGame (G : NFGame ι A) (i : ι) (a : A i) :
    IsDominant G i a ↔ G.toKernelGame.IsDominant i a := by
  simp only [IsDominant, GameTheory.KernelGame.IsDominant, GameTheory.KernelGame.eu,
      NFGame.toKernelGame, GameTheory.expect_pure, deviate]

/-! ## NFG → EFG: simultaneous game as a sequential tree -/

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

/-! ## Mixed strategies -/

/-- A mixed strategy profile: each player independently randomizes over actions. -/
abbrev MixedProfile (A : ι → Type) [∀ i, Fintype (A i)] := ∀ i, PMF (A i)

/-- Independent product of PMFs over a finite index type.
    Assigns probability `∏ i, σ i (f i)` to each profile `f : ∀ i, A i`.
    The sum-to-one proof follows from the finite Fubini theorem:
    `∑ f, ∏ i, σ i (f i) = ∏ i, (∑ a, σ i a) = ∏ i, 1 = 1`. -/
noncomputable def pmfPi
    (σ : ∀ i, PMF (A i)) : PMF (∀ i, A i) :=
  PMF.ofFintype (fun f => ∏ i : ι, σ i (f i)) (by
    rw [← Fintype.prod_sum]
    have : ∀ i, ∑ j : A i, (σ i) j = 1 :=
      fun i => by
        have h := PMF.tsum_coe (σ i)
        rwa [tsum_eq_sum (s := Finset.univ)
          (fun x hx => absurd (Finset.mem_univ x) hx)] at h
    simp [this])

omit [∀ i, DecidableEq (A i)] in
@[simp] theorem pmfPi_apply (σ : ∀ i, PMF (A i)) (f : ∀ i, A i) :
    (pmfPi σ) f = ∏ i, σ i (f i) := by
  simp [pmfPi, PMF.ofFintype_apply]

/-- NFG as a kernel-based game with mixed strategies.
    The outcome kernel maps independent per-player PMFs to a joint distribution
    over pure action profiles via the product PMF construction. -/
noncomputable def NFGame.toMixedKernelGame
    (G : NFGame ι A) : GameTheory.KernelGame ι where
  Strategy := fun i => PMF (A i)
  Outcome := ∀ i, A i
  payoff := G.payoff
  outcomeKernel := fun σ => pmfPi σ

/-- A mixed Nash equilibrium: no player can improve expected payoff by
    changing their marginal distribution. -/
def IsNashMixed (G : NFGame ι A)
    (σ : MixedProfile A) : Prop :=
  G.toMixedKernelGame.IsNash σ

end NFG
