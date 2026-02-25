import GameTheory.Probability

/-!
# GameTheory.KernelGame

Kernel-based game structure: the semantic core for finite/discrete game models.

Provides:
- `KernelGame` — a game with player-indexed strategies, stochastic outcome kernel, and utility
- `eu` — expected utility for a player under a strategy profile
- `Profile`, `correlatedOutcome` — standard game-theoretic notions
- `KernelGame.ofEU` — constructs a kernel game from a direct EU function
  (absorbs the former `StrategicForm.Game`)

## Scope-outs

- **Continuous games** — the library is discrete (`PMF`) by design.
- **Correlated equilibrium** — `correlatedOutcome` is defined; CE could be added later.
-/

namespace GameTheory

/-- A payoff vector for `ι` players. -/
abbrev Payoff (ι : Type) : Type := ι → ℝ

-- ============================================================================
-- § 1. Kernel-based game (strategies + outcome kernel → EU)
-- ============================================================================

/-- A kernel-based game with explicit outcome type.
    - `Outcome` is the type of game outcomes (e.g. terminal nodes, action profiles)
    - `utility` maps outcomes to player payoffs
    - `outcomeKernel` maps strategy profiles to outcome distributions -/
structure KernelGame (ι : Type) where
  Strategy : ι → Type
  Outcome : Type
  utility : Outcome → Payoff ι
  outcomeKernel : Kernel (∀ i, Strategy i) Outcome

namespace KernelGame

variable {ι : Type} [DecidableEq ι]

abbrev Profile (G : KernelGame ι) := ∀ i, G.Strategy i

/-- Expected utility of player `who` under strategy profile `σ`. -/
noncomputable def eu (G : KernelGame ι) (σ : Profile G) (who : ι) : ℝ :=
  expect (G.outcomeKernel σ) (fun ω => G.utility ω who)

/-- Outcome distribution under a correlated profile distribution (correlation device). -/
noncomputable def correlatedOutcome (G : KernelGame ι)
    (μ : PMF (Profile G)) : PMF G.Outcome :=
  Kernel.linExt G.outcomeKernel μ

-- ============================================================================
-- § 2. Strategic-form special case (absorbs StrategicForm.Game)
-- ============================================================================

/-- Build a KernelGame from a direct expected-utility function (no stochastic kernel).
    This is the "strategic form" special case: outcome = utility vector, kernel = point mass.
    Absorbs the former `StrategicForm.Game`. -/
noncomputable def ofEU [DecidableEq ι]
    (Strategy : ι → Type) (eu : (∀ i, Strategy i) → Payoff ι) : KernelGame ι where
  Strategy := Strategy
  Outcome := Payoff ι
  utility := id
  outcomeKernel := fun σ => PMF.pure (eu σ)

/-- EU of a game built from `ofEU` is just the direct EU function. -/
@[simp] theorem eu_ofEU
    (S : ι → Type) (u : (∀ i, S i) → Payoff ι) (σ : ∀ i, S i) (i : ι) :
    (ofEU S u).eu σ i = u σ i := by
  simp [eu, ofEU, expect_pure]

end KernelGame

end GameTheory
