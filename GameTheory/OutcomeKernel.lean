import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# GameTheory.OutcomeKernel

A representation-agnostic semantic core for finite/discrete game models.

This file intentionally knows nothing about:
- EFG trees
- NFG strategic form
- any external "calculus"

It defines:
- stochastic kernels (`Kernel`) using Mathlib's `PMF`
- player-indexed expected utilities
- kernel-based game structure with Nash equilibrium

Representations (EFG/NFG/MAID/...) should *export* kernels into this interface
and then reuse generic theorems.

PMF monad laws (`PMF.pure_bind`, `PMF.bind_pure`, `PMF.bind_bind`,
`PMF.bind_comm`) are provided by Mathlib.
-/

namespace GameTheory

-- ============================================================================
-- § 1. Kernels (using Mathlib's PMF)
-- ============================================================================

/-- A stochastic kernel from `α` to `β`: maps each input to a PMF over outputs. -/
abbrev Kernel (α β : Type) : Type := α → PMF β

namespace Kernel

/-- Identity kernel. -/
noncomputable def id (α : Type) : Kernel α α := PMF.pure

/-- Kernel composition (Kleisli composition). -/
noncomputable def comp (k₁ : Kernel α β) (k₂ : Kernel β γ) : Kernel α γ :=
  fun a => (k₁ a).bind k₂

/-- Linear extension / pushforward of a kernel to input distributions. -/
noncomputable def linExt (k : Kernel α β) : PMF α → PMF β :=
  fun μ => μ.bind k

/-- Pushforward along a pure function (deterministic kernel). -/
noncomputable def ofFun (f : α → β) : Kernel α β := fun a => PMF.pure (f a)


@[simp] theorem comp_apply (k₁ : Kernel α β) (k₂ : Kernel β γ) (a : α) :
    Kernel.comp k₁ k₂ a = (k₁ a).bind k₂ := rfl

@[simp] theorem comp_assoc (k₁ : Kernel α β) (k₂ : Kernel β γ) (k₃ : Kernel γ δ) :
    Kernel.comp (Kernel.comp k₁ k₂) k₃ = Kernel.comp k₁ (Kernel.comp k₂ k₃) := by
  funext a
  simp_all only [comp_apply, PMF.bind_bind]
  rfl

@[simp] theorem comp_id_left (k : Kernel α β) :
    Kernel.comp (Kernel.id α) k = k := by
  funext a
  simp [Kernel.comp, Kernel.id]

@[simp] theorem comp_id_right (k : Kernel α β) :
    Kernel.comp k (Kernel.id β) = k := by
  funext a
  simp [Kernel.comp, Kernel.id]

/-- Linear extension is just `bind` at the PMF level. -/
@[simp] theorem linExt_apply (k : Kernel α β) (μ : PMF α) :
    Kernel.linExt k μ = μ.bind k := rfl

/-- `linExt` along a deterministic kernel is exactly `mapPMF`. -/
@[simp] theorem linExt_ofFun (f : α → β) (μ : PMF α) :
    Kernel.linExt (Kernel.ofFun f) μ = μ.bind (fun a => PMF.pure (f a)) := by
  rfl

/-- Linear extension respects Kleisli composition. -/
@[simp] theorem linExt_comp (k₁ : Kernel α β) (k₂ : Kernel β γ) (μ : PMF α) :
    Kernel.linExt (Kernel.comp k₁ k₂) μ = Kernel.linExt k₂ (Kernel.linExt k₁ μ) := by
  -- μ.bind (fun a => (k₁ a).bind k₂) = (μ.bind k₁).bind k₂
  simp_all only [linExt_apply, PMF.bind_bind]
  rfl

end Kernel

-- ============================================================================
-- § 2. Player-indexed payoffs and expected utilities
-- ============================================================================

/-- A payoff vector for `ι` players. -/
abbrev Payoff (ι : Type) : Type := ι → ℝ

/-- Expected value of a real-valued function under a PMF. -/
noncomputable def expect {Ω : Type} (d : PMF Ω) (f : Ω → ℝ) : ℝ :=
  ∑' ω, (d ω).toReal * f ω

/--
For finite `Ω`, your `expect` is literally a finite sum.
This is a *huge* simplification for many game models (EFG/NFG/MAID with finite outcomes).
-/
theorem expect_eq_sum {Ω : Type} [Fintype Ω] (d : PMF Ω) (f : Ω → ℝ) :
    expect d f = (∑ ω : Ω, (d ω).toReal * f ω) := by
  simp [expect]

-- ============================================================================
-- § 3. Kernel-based game (strategies + outcome kernel → EU + Nash)
-- ============================================================================

/-- A kernel-based game with explicit outcome type.
    - `Outcome` is the type of game outcomes (e.g. terminal nodes, action profiles)
    - `payoff` maps outcomes to player payoffs
    - `outcomeKernel` maps strategy profiles to outcome distributions -/
structure KernelGame (ι : Type) [DecidableEq ι] where
  Strategy : ι → Type
  Outcome : Type
  payoff : Outcome → Payoff ι
  outcomeKernel : Kernel (∀ i, Strategy i) Outcome

namespace KernelGame

variable {ι : Type} [DecidableEq ι]

abbrev Profile (G : KernelGame ι) := ∀ i, G.Strategy i

/-- Expected utility of player `who` under strategy profile `σ`. -/
noncomputable def eu (G : KernelGame ι) (σ : Profile G) (who : ι) : ℝ :=
  expect (G.outcomeKernel σ) (fun ω => G.payoff ω who)

def IsNash (G : KernelGame ι) (σ : Profile G) : Prop :=
  ∀ (who : ι) (s' : G.Strategy who),
    G.eu σ who ≥ G.eu (Function.update σ who s') who

/-- Outcome distribution under a correlated profile distribution (correlation device). -/
noncomputable def correlatedOutcome (G : KernelGame ι)
    (μ : PMF (Profile G)) : PMF G.Outcome :=
  Kernel.linExt G.outcomeKernel μ

end KernelGame

end GameTheory
