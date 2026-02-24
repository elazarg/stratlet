import GameTheory.NFG
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Product PMF Lemmas

Factorization and marginalization lemmas for `NFG.pmfPi` (the independent
product of PMFs over a finite index type). These are needed for Kuhn's theorem
in `EFG2Kuhn.lean`.

## Main results

- `pmfPi_bind_factor` — factor out one coordinate: if `g(s_j, s)` doesn't
  depend on `s_j` through `s`, then the product bind factors into
  `(σ j).bind` composed with the full product bind.
- `pmfPi_bind_const_pure` — binding a product with a constant function gives
  the constant.

## Proof strategy

Both lemmas follow from manipulating `Finset.sum` and `Finset.prod`:
- `pmfPi σ` assigns weight `∏ i, σ i (s i)` to each `s : ∀ i, A i`.
- `(pmfPi σ).bind g` at outcome `ω` is `∑ s, (∏ i, σ i (s i)) * (g s ω)`.
- For factorization, group by `s j = a` and use `Finset.prod_insert`
  plus `∑ s, ∏ i, σ i (s i) = 1`.
-/

namespace NFG

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {A : ι → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

-- ============================================================================
-- Lemma 1: Binding a product PMF with a constant function
-- ============================================================================

/-- Binding any PMF with a constant function `fun _ => PMF.pure c`
    yields `PMF.pure c`. This is a consequence of `∑ s, μ s = 1`. -/
theorem PMF.bind_const_pure {α β : Type} (μ : PMF α) (c : β) :
    μ.bind (fun _ => PMF.pure c) = PMF.pure c := by
  sorry

-- ============================================================================
-- Lemma 2: Product PMF factorization at one coordinate
-- ============================================================================

/-- **Product PMF factorization**: if `g(a, s)` does not depend on the `j`-th
    coordinate of `s`, then binding the product PMF with `g(s_j, s)` factors as
    `(σ j).bind (fun a => (pmfPi σ).bind (fun s => g a s))`.

    Concretely, this says:
    ```
    ∑_s (∏_i σ_i(s_i)) · g(s_j, s)
    = ∑_a σ_j(a) · ∑_s (∏_i σ_i(s_i)) · g(a, s)
    ```
    The key step is grouping the LHS by `s_j = a`, factoring out `σ_j(a)`,
    and observing that the remaining sum over `s_{-j}` combined with `∑_{a'} σ_j(a')`
    gives back the full product (since `∑_{a'} σ_j(a') = 1`).

    The hypothesis `hg` says `g(a, s)` only depends on `s` through coordinates `≠ j`. -/
theorem pmfPi_bind_factor
    (σ : ∀ i, PMF (A i)) (j : ι) {β : Type}
    (g : A j → (∀ i, A i) → PMF β)
    (hg : ∀ a (s₁ s₂ : ∀ i, A i), (∀ i, i ≠ j → s₁ i = s₂ i) → g a s₁ = g a s₂) :
    (pmfPi σ).bind (fun s => g (s j) s) =
    (σ j).bind (fun a => (pmfPi σ).bind (fun s => g a s)) := by
  sorry

-- ============================================================================
-- Corollary: pointwise version (at each outcome)
-- ============================================================================

/-- Pointwise version of `pmfPi_bind_factor`:
    `∑_s (∏_i σ_i(s_i)) · g(s_j, s)(ω) = ∑_a σ_j(a) · ∑_s (∏_i σ_i(s_i)) · g(a, s)(ω)` -/
theorem pmfPi_bind_factor_apply
    (σ : ∀ i, PMF (A i)) (j : ι) {β : Type}
    (g : A j → (∀ i, A i) → PMF β)
    (hg : ∀ a (s₁ s₂ : ∀ i, A i), (∀ i, i ≠ j → s₁ i = s₂ i) → g a s₁ = g a s₂)
    (ω : β) :
    ((pmfPi σ).bind (fun s => g (s j) s)) ω =
    ((σ j).bind (fun a => (pmfPi σ).bind (fun s => g a s))) ω := by
  rw [pmfPi_bind_factor σ j g hg]

end NFG
