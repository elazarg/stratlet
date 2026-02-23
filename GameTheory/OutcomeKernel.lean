import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.List.Basic

/-!
# GameTheory.OutcomeKernel

A representation-agnostic semantic core for finite/discrete game models.

This file intentionally knows nothing about:
- EFG trees
- NFG strategic form
- any external "calculus"

It defines:
- finitely-supported distributions (`FDist`)
- Markov kernels (`Kernel`)
- linear extension / pushforward of a kernel to distributions (`linExt`)
- expectation and player-indexed expected utilities

Representations (EFG/NFG/MAID/...) should *export* kernels into this interface
and then reuse generic theorems.
-/

namespace GameTheory

-- ============================================================================
-- § 1. Finite-support distributions (list-based)
-- ============================================================================

/-- Finitely-supported distribution as a weighted list.

Intended invariants (not baked into the type):
- weights are nonnegative
- optionally: weights sum to 1

We keep this minimal; each representation can impose its own well-formedness.
-/
structure FDist (α : Type) where
  weights : List (α × NNReal)
deriving Inhabited

namespace FDist

abbrev Kernel (α β : Type) : Type := α → FDist β

/-- Point mass. -/
def pure (a : α) : FDist α := ⟨[(a, 1)]⟩

/-- Empty support (zero mass). -/
def zero : FDist α := ⟨[]⟩

/-- Map values, keep weights. -/
def map (f : α → β) (d : FDist α) : FDist β :=
  ⟨d.weights.map (fun (a,w) => (f a, w))⟩

/-- Scale all weights by `c`. -/
def scale (c : NNReal) (d : FDist α) : FDist α :=
  ⟨d.weights.map (fun (a,w) => (a, c * w))⟩

/-- Append supports (mixture without normalization and without merging equal atoms). -/
def append (d₁ d₂ : FDist α) : FDist α := ⟨d₁.weights ++ d₂.weights⟩

/-- Monadic bind: linear extension of a kernel `α → FDist β`. -/
def bind (d : FDist α) (k : α → FDist β) : FDist β :=
  ⟨d.weights.flatMap (fun (a, w) =>
    (k a).weights.map (fun (b, w') => (b, w * w')))⟩

/-- Total mass (sum of weights). -/
noncomputable def mass (d : FDist α) : NNReal :=
  (d.weights.map Prod.snd).sum

/-- Expectation of a real-valued function (no normalization assumed). -/
noncomputable def expect (f : α → ℝ) (d : FDist α) : ℝ :=
  (d.weights.map (fun (a,w) => (w : ℝ) * f a)).sum

end FDist

-- ============================================================================
-- § 2. Kernels and linear extension
-- ============================================================================

/-- A (finite-support) stochastic kernel from `α` to `β`. -/
abbrev Kernel (α β : Type) : Type := α → FDist β

namespace Kernel

/-- Identity kernel. -/
def id (α : Type) : Kernel α α := fun a => FDist.pure a

/-- Kernel composition (Kleisli composition). -/
def comp (k₁ : Kernel α β) (k₂ : Kernel β γ) : Kernel α γ :=
  fun a => (k₁ a).bind k₂

/-- Linear extension / pushforward of a kernel to input distributions.

This is the canonical `FDist α → FDist β` induced by a kernel `α → FDist β`.
-/
def linExt (k : Kernel α β) : FDist α → FDist β :=
  fun μ => μ.bind k

/-- Pushforward along a pure function as a special case (deterministic kernel). -/
def ofFun (f : α → β) : Kernel α β := fun a => FDist.pure (f a)

end Kernel

-- ============================================================================
-- § 3. Player-indexed payoffs and expected utilities
-- ============================================================================

/-- A payoff vector for `ι` players. -/
abbrev Payoff (ι : Type) : Type := ι → ℝ

/-- Expected utility of player `who` under an outcome distribution on payoff vectors. -/
noncomputable def EU {ι : Type} (who : ι) (d : FDist (Payoff ι)) : ℝ :=
  d.expect (fun u => u who)

-- ============================================================================
-- § 4. Generic kernel laws (extensional, representation-agnostic)
-- ============================================================================

namespace Laws

/-- `linExt` is exactly `bind`. (Useful for rewriting.) -/
@[simp] theorem linExt_def (k : Kernel α β) (μ : FDist α) :
    Kernel.linExt k μ = μ.bind k := rfl

/-- `map` is `bind` with a deterministic kernel. -/
theorem map_eq_bind_ofFun (f : α → β) (μ : FDist α) :
    μ.map f = μ.bind (Kernel.ofFun f) := by
  cases μ with | mk ws =>
  simp only [FDist.map, FDist.bind, Kernel.ofFun, FDist.pure]
  congr 1
  induction ws with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨a, w⟩ := hd
    simp only [List.map_cons, List.flatMap_cons, List.map_cons, List.map_nil, mul_one] at ih ⊢
    exact congrArg ((f a, w) :: ·) ih

/-- Left identity: `pure` then `bind` is kernel application. -/
@[simp] theorem bind_pure (a : α) (k : Kernel α β) :
    (FDist.pure a).bind k = k a := by
  change FDist.mk _ = k a
  simp only [FDist.pure, List.flatMap_cons, List.flatMap_nil, List.append_nil, one_mul]
  congr 1
  exact List.map_id' (k a).weights

/-- Right identity: `bind` with `id` is identity. -/
theorem bind_id (μ : FDist α) :
    μ.bind (Kernel.id α) = μ := by
  cases μ with | mk ws =>
  simp only [FDist.bind, Kernel.id, FDist.pure]
  congr 1
  induction ws with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨a, w⟩ := hd
    simp only [List.flatMap_cons, List.map_cons, List.map_nil, mul_one] at ih ⊢
    exact congrArg ((a, w) :: ·) ih

/-- Associativity of `bind`. -/
theorem bind_assoc (μ : FDist α) (k₁ : Kernel α β) (k₂ : Kernel β γ) :
    (μ.bind k₁).bind k₂ = μ.bind (Kernel.comp k₁ k₂) := by
  cases μ with | mk ws =>
  simp only [FDist.bind, Kernel.comp]
  congr 1
  induction ws with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨a, w⟩ := hd
    simp only [List.flatMap_cons, List.flatMap_append]
    rw [ih]; congr 1
    -- inner: (k₁ a).weights.map(scale w) |>.flatMap(bind k₂)
    --      = (k₁ a).weights.flatMap(bind k₂) |>.map(scale w)
    induction (k₁ a).weights with
    | nil => simp
    | cons hd' tl' ih' =>
      obtain ⟨b, w'⟩ := hd'
      simp only [List.map_cons, List.flatMap_cons, List.map_append, List.map_map]
      rw [ih']; congr 1
      congr 1; funext x
      obtain ⟨c, w''⟩ := x
      exact Prod.ext rfl (mul_assoc w w' w'')

end Laws

end GameTheory
