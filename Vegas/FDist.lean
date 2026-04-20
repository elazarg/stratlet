import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNRat.Order
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Math.Probability

/-!
# Finite-support weighted distributions

This file provides `FDist α`, the finite-support, sub-probability,
nonnegative-rational-weighted distribution layer used throughout the Vegas
protocol semantics.

## Design

`FDist α` is `α →₀ ℚ≥0` — a `Finsupp` with nonnegative rational weights.
Three choices distinguish it from Mathlib's `PMF`:

* **Sub-probability.** `totalWeight d` may take any value in `[0, ∞)`, not
  just `1`. Normalization is tracked as a separately-discharged invariant
  (see `totalWeight_bind_of_normalized`), so intermediate distributions in a
  `bind`-tree can be built without per-step normalization proofs.
* **Rational weights.** Equality is decidable and concrete distributions
  are computationally meaningful — the MAID compiler relies on this when
  emitting chance-node CPDs.
* **Decidable carrier.** `[DecidableEq α]` is what makes `Finsupp`
  arithmetic and the `support` Finset usable.

## Layout

* The monadic operations `pure`, `zero`, `bind`, `map`, plus `totalWeight`
  and the data-constructor `ofList`.
* Pointwise formulae (`pure_apply`, `bind_apply`, `map_apply`) and the
  `Supported` predicate used to express "every value with positive weight
  satisfies `P`".
* The monad and functor laws, including commutativity (`bind_comm`), which
  underpins program-level commutation theorems in the Vegas semantics.
* A monad homomorphism `toPMF : {d : FDist α // d.totalWeight = 1} → PMF α`
  bridging into Mathlib's measure-theoretic `PMF`. The bridge is one-way
  and is the only exit point from `FDist`.

The operations are `noncomputable` because `Finsupp.single` and `Finsupp.sum`
are noncomputable in Mathlib; reasoning about `FDist` is fully constructive
but `#eval` is not available.
-/

namespace Vegas

/-- Finite-support, sub-probability, rational-weighted distributions over a
type with decidable equality. See the file docstring for design rationale. -/
abbrev FDist (α : Type) [DecidableEq α] := α →₀ ℚ≥0

namespace FDist

variable {α : Type} {β : Type} [DecidableEq α] [DecidableEq β]

/-! ## Operations -/

/-- The Dirac mass at `x`: weight `1` on `x`, weight `0` elsewhere. -/
noncomputable def pure (x : α) : FDist α := Finsupp.single x 1

/-- The empty distribution; total weight `0`. Acts as the identity for
addition of distributions and as the absorbing element for `bind` on the
left (`bind_zero_left`). -/
noncomputable def zero : FDist α := 0

/-- Monadic continuation: each support point `a` of `d`, weighted by `w`,
contributes the distribution `f a` rescaled by `w`. -/
noncomputable def bind (d : FDist α) (f : α → FDist β) : FDist β :=
  d.sum fun a w => (f a).mapRange (w * ·) (mul_zero w)

/-- Pushforward of `d` along `g`. If `g` is not injective, the weights of
collided keys add. -/
noncomputable def map (g : α → β) (d : FDist α) : FDist β :=
  d.sum (fun a w => Finsupp.single (g a) w)

/-- Total mass of `d` — the sum of weights over the support. Equals `1`
exactly for normalized (probability) distributions. -/
noncomputable def totalWeight (d : FDist α) : ℚ≥0 := d.sum (fun _ w => w)

/-! ## Constructors from data -/

/-- Sum of all weights for key `a` in an association list. Defined
recursively so that `ofList` can be built without classical choice on the
list structure. -/
def ofListWeight (a : α) : List (α × ℚ≥0) → ℚ≥0
  | [] => 0
  | entry :: rest => (if entry.1 = a then entry.2 else 0) + ofListWeight a rest

/-- Build an `FDist` from an explicit list of `(value, weight)` entries.
Duplicate keys add; entries with weight `0` (or whose weights cancel to `0`
through duplication) are filtered from the support. This is the only data
constructor of `FDist`; every other distribution arises from `pure`,
`bind`, `map`, or a user-supplied kernel. -/
def ofList (entries : List (α × ℚ≥0)) : FDist α where
  support := (entries.map Prod.fst).toFinset.filter (fun a => ofListWeight a entries ≠ 0)
  toFun a := ofListWeight a entries
  mem_support_toFun a := by
    rw [Finset.mem_filter]
    constructor
    · intro h
      exact h.2
    · intro hne
      constructor
      · simp only [List.mem_toFinset, List.mem_map]
        induction entries with
        | nil => simp [ofListWeight] at hne
        | cons hd tl ih =>
            simp only [ofListWeight] at hne
            by_cases h : hd.1 = a
            · exact ⟨hd, by simp, h⟩
            · have htail : ofListWeight a tl ≠ 0 := by
                intro hzero
                apply hne
                simp [h, hzero]
              rcases ih htail with ⟨entry, hmem, heq⟩
              exact ⟨entry, List.mem_cons_of_mem hd hmem, heq⟩
      · exact hne

/-! ## Pointwise formulae and support -/

@[simp] theorem pure_apply (x y : α) : FDist.pure x y = if x = y then 1 else 0 := by
  simp [FDist.pure, Finsupp.single_apply]

/-- Pointwise unfolding of `bind` to a finite sum over the support of `d`.
Not a `simp` lemma: applied eagerly it would expand bind-heavy terms. Use
explicitly when a pointwise formula is needed, for example in adequacy or
support-correctness proofs. -/
theorem bind_apply (d : FDist α) (f : α → FDist β) (b : β) :
    (d.bind f) b = d.support.sum (fun a => d a * (f a) b) := by
  simp only [bind, Finsupp.sum, Finsupp.finset_sum_apply, Finsupp.mapRange_apply]

/-- Pointwise unfolding of `map` to a finite sum over the support of `d`.
The conditional handles the case where `g` collides keys; `map_apply_injective`
and `map_apply_of_forall_ne` are the two clean specializations that avoid it. -/
theorem map_apply (g : α → β) (d : FDist α) (b : β) :
    (d.map g) b = d.support.sum (fun a => if g a = b then d a else 0) := by
  simp only [map, Finsupp.sum, Finsupp.finset_sum_apply, Finsupp.single_apply]

/-- "`P` holds at every value with positive weight". The standard idiom for
expressing semantic side conditions on a distribution — for example, the
fair-play requirement that every committed action satisfies its guard. -/
def Supported (d : FDist α) (P : α → Prop) : Prop := ∀ a ∈ d.support, P a

@[simp] theorem totalWeight_pure (x : α) : (FDist.pure x).totalWeight = 1 := by
  simp [totalWeight, FDist.pure, Finsupp.sum_single_index]

@[simp] theorem support_pure (x : α) : (FDist.pure x).support = {x} :=
  Finsupp.support_single_ne_zero _ one_ne_zero

@[simp] theorem support_zero : (FDist.zero : FDist α).support = ∅ :=
  Finsupp.support_zero

@[simp] theorem Supported_pure {P : α → Prop} (x : α) :
    (FDist.pure x).Supported P ↔ P x := by
  simp [Supported]

theorem Supported_zero (P : α → Prop) : (FDist.zero : FDist α).Supported P := by
  simp [Supported, FDist.zero]

theorem pure_bind (x : α) (f : α → FDist β) : (FDist.pure x).bind f = f x := by
  simp only [FDist.pure, bind]
  rw [Finsupp.sum_single_index]
  · ext a
    simp [Finsupp.mapRange_apply]
  · ext a
    simp [Finsupp.mapRange_apply]

theorem bind_pure (d : FDist α) : d.bind FDist.pure = d := by
  simp only [bind, FDist.pure]
  simp_rw [Finsupp.mapRange_single, mul_one]
  exact d.sum_single

theorem bind_zero_left (f : α → FDist β) :
    (FDist.zero : FDist α).bind f = FDist.zero := by
  simp [bind, FDist.zero, Finsupp.sum_zero_index]

@[simp] theorem ofList_nil : (FDist.ofList (α := α) []) = FDist.zero := by
  ext a
  simp [ofList, ofListWeight, FDist.zero]

theorem ofList_cons (a : α) (w : ℚ≥0) (rest : List (α × ℚ≥0)) :
    FDist.ofList ((a, w) :: rest) = Finsupp.single a w + FDist.ofList rest := by
  ext x
  simp [ofList, ofListWeight, Finsupp.single_apply]

/-- Support characterization of `bind`: `b` is reachable through `d.bind f`
iff some `a` in `d`'s support carries `b` in `f a`'s support. The basis for
"reachable iff in support" theorems at the program level. -/
theorem mem_support_bind {d : FDist α} {f : α → FDist β} {b : β} :
    b ∈ (d.bind f).support ↔ ∃ a ∈ d.support, b ∈ (f a).support := by
  rw [Finsupp.mem_support_iff, bind_apply]
  constructor
  · intro h
    by_contra hall
    push Not at hall
    apply h
    apply Finset.sum_eq_zero
    intro a ha
    have hfab : (f a) b = 0 := by
      by_contra hne
      exact hall a ha (Finsupp.mem_support_iff.mpr hne)
    rw [hfab, mul_zero]
  · rintro ⟨a, ha, hb⟩
    intro heq
    have hsplit := Finset.add_sum_erase d.support (fun a => d a * (f a) b) ha
    rw [heq] at hsplit
    have hle : d a * (f a) b ≤ 0 := hsplit ▸ le_self_add
    have hge : 0 ≤ d a * (f a) b := zero_add (d a * (f a) b) ▸ le_self_add
    exact mul_ne_zero (Finsupp.mem_support_iff.mp ha)
      (Finsupp.mem_support_iff.mp hb) (le_antisymm hle hge)

@[simp] theorem mem_support_pure {a b : α} :
    b ∈ (FDist.pure a).support ↔ b = a := by
  rw [support_pure, Finset.mem_singleton]

/-! ## Algebraic laws and total-weight propagation -/

/-- Total mass of a `bind` is the weighted sum of the branches' total
masses. The general identity from which the normalized version
(`totalWeight_bind_of_normalized`) is derived. -/
theorem totalWeight_bind (d : FDist α) (f : α → FDist β) :
    (d.bind f).totalWeight = d.support.sum (fun a => d a * (f a).totalWeight) := by
  unfold totalWeight bind
  rw [Finsupp.sum_sum_index (fun _ => rfl) (fun _ _ _ => rfl)]
  have hmr : ∀ (a : α) (w : ℚ≥0),
      (Finsupp.mapRange (w * ·) (mul_zero w) (f a)).sum (fun _ x => x) =
        (f a).sum (fun _ b => w * b) := fun _ _ =>
      Finsupp.sum_mapRange_index (fun _ => rfl)
  simp_rw [hmr]
  simp only [Finsupp.sum, Finset.mul_sum]

/-- Normalization propagates through `bind`: a normalized head and uniformly
normalized branches give a normalized result. The single load-bearing lemma
behind every `outcomeDist_totalWeight_eq_one`-style induction in the Vegas
semantics. -/
theorem totalWeight_bind_of_normalized {d : FDist α} {f : α → FDist β}
    (hd : d.totalWeight = 1) (hf : ∀ a ∈ d.support, (f a).totalWeight = 1) :
    (d.bind f).totalWeight = 1 := by
  rw [totalWeight_bind]
  have hs : d.support.sum (fun a => d a * (f a).totalWeight) = d.support.sum (fun a => d a) := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [hf a ha, mul_one]
  rw [hs]
  exact hd

/-- Pushforward through an injective `g` is read pointwise: no collisions, so
`(d.map g) (g a) = d a`. Avoids the conditional in `map_apply`. -/
theorem map_apply_injective (g : α → β) (d : FDist α) (a : α)
    (hinj : Function.Injective g) :
    (d.map g) (g a) = d a := by
  rw [map_apply]
  simp only [hinj.eq_iff]
  rw [Finset.sum_ite_eq' d.support a (fun x => d x)]
  split
  · rfl
  · next h => simp [Finsupp.mem_support_iff] at h; exact h.symm

/-- A point `b` outside the image of `g` on the support of `d` carries weight
`0` in the pushforward. The companion to `map_apply_injective` for the
"`b` is unreachable" case. -/
theorem map_apply_of_forall_ne (g : α → β) (d : FDist α) (b : β)
    (h : ∀ a ∈ d.support, g a ≠ b) :
    (d.map g) b = 0 := by
  rw [map_apply]
  apply Finset.sum_eq_zero
  intro a ha
  simp [h a ha]

theorem map_pure (g : α → β) (a : α) :
    (FDist.pure a).map g = FDist.pure (g a) := by
  simp only [FDist.pure, map]
  rw [Finsupp.sum_single_index (Finsupp.single_zero _)]

theorem map_map {γ : Type} [DecidableEq γ] (f : α → β) (g : β → γ) (d : FDist α) :
    (d.map f).map g = d.map (g ∘ f) := by
  simp only [map]
  rw [Finsupp.sum_sum_index (fun _ => Finsupp.single_zero _)
    (fun _ _ _ => Finsupp.single_add _ _ _)]
  have hz : ∀ b : β, (fun x : ℚ≥0 => Finsupp.single (g b) x) 0 = 0 := fun b =>
    Finsupp.single_zero _
  simp_rw [show ∀ b w, (Finsupp.single (f b) w).sum (fun x => Finsupp.single (g x)) =
    Finsupp.single (g (f b)) w from fun b w => Finsupp.sum_single_index (hz (f b))]
  rfl

theorem bind_map (d : FDist α) (f : α → FDist β) {γ : Type} [DecidableEq γ]
    (g : β → γ) :
    (d.bind f).map g = d.bind (fun a => (f a).map g) := by
  simp only [bind, map]
  rw [Finsupp.sum_sum_index (fun _ => Finsupp.single_zero _)
    (fun _ _ _ => Finsupp.single_add _ _ _)]
  congr 1
  ext a w
  rw [Finsupp.sum_mapRange_index (fun _ => Finsupp.single_zero _)]
  simp only [Finsupp.sum, Finsupp.mapRange_apply, Finsupp.finset_sum_apply,
    Finsupp.single_apply]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  split <;> simp [mul_zero]

theorem bind_assoc {γ : Type} [DecidableEq γ]
    (d : FDist α) (f : α → FDist β) (g : β → FDist γ) :
    (d.bind f).bind g = d.bind (fun a => (f a).bind g) := by
  simp only [bind]
  rw [Finsupp.sum_sum_index
    (fun b => by ext x; simp [Finsupp.mapRange_apply, zero_mul])
    (fun b m₁ m₂ => by ext x; simp [Finsupp.mapRange_apply, add_mul])]
  congr 1
  funext a
  funext w
  rw [Finsupp.sum_mapRange_index
    (fun b => by ext x; simp [Finsupp.mapRange_apply, zero_mul])]
  ext c
  simp only [Finsupp.sum, Finsupp.mapRange_apply, Finsupp.finset_sum_apply]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  exact mul_assoc w ((f a) b) ((g b) c)

/-- Independent `bind`s commute: the order in which two independent random
choices are made does not affect the joint distribution. The algebraic
substrate for program-level commutation results — for example, two adjacent
commits with independent strategies produce the same outcome distribution
regardless of order. -/
theorem bind_comm {γ : Type} [DecidableEq γ]
    (d₁ : FDist α) (d₂ : FDist β) (f : α → β → FDist γ) :
    d₁.bind (fun a => d₂.bind (fun b => f a b)) =
      d₂.bind (fun b => d₁.bind (fun a => f a b)) := by
  ext c
  simp only [bind_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  exact mul_left_comm (d₁ a) (d₂ b) ((f a b) c)

theorem bind_pure_comp (d : FDist α) (g : α → β) :
    FDist.bind d (fun a => FDist.pure (g a)) = FDist.map g d := by
  simp only [FDist.bind, FDist.pure, FDist.map]
  congr 1
  funext a
  funext w
  rw [Finsupp.mapRange_single, mul_one]

theorem totalWeight_map (d : FDist α) (g : α → β) :
    FDist.totalWeight (FDist.map g d) = FDist.totalWeight d := by
  simp only [FDist.map, FDist.totalWeight]
  rw [Finsupp.sum_sum_index (fun _ => rfl) (fun _ _ _ => rfl)]
  apply Finset.sum_congr rfl
  intro a _
  simp [Finsupp.sum_single_index]

end FDist

/-! ## Cast `ℚ≥0 → ℝ≥0`

The bridge to `PMF` produces `ENNReal` weights. Mathlib does not ship a
direct ring map `ℚ≥0 → ENNReal`, so we go via `NNReal`. The lemmas below
are the targeted rewrite rules used inside the bridge — none are `@[simp]`. -/

/-- Canonical embedding `ℚ≥0 → ℝ≥0`. -/
noncomputable def NNRat.toNNReal (q : ℚ≥0) : NNReal :=
  ⟨((q : ℚ) : ℝ), by exact_mod_cast q.coe_nonneg⟩

theorem NNRat.toNNReal_one : NNRat.toNNReal 1 = 1 := by
  unfold NNRat.toNNReal
  ext
  push_cast
  ring

theorem NNRat.toNNReal_zero : NNRat.toNNReal 0 = 0 := by
  unfold NNRat.toNNReal
  ext
  push_cast
  ring

theorem NNRat.toNNReal_add (a b : ℚ≥0) :
    NNRat.toNNReal (a + b) = NNRat.toNNReal a + NNRat.toNNReal b := by
  unfold NNRat.toNNReal
  ext
  push_cast
  ring

theorem NNRat.toNNReal_mul (a b : ℚ≥0) :
    NNRat.toNNReal (a * b) = NNRat.toNNReal a * NNRat.toNNReal b := by
  unfold NNRat.toNNReal
  ext
  push_cast
  ring

theorem NNRat.toNNReal_coe_real (q : ℚ≥0) :
    ((NNRat.toNNReal q : NNReal) : ℝ) = (q : ℝ) := by
  rfl

theorem NNRat.toNNReal_finset_sum {γ : Type} (s : Finset γ) (f : γ → ℚ≥0) :
    NNRat.toNNReal (s.sum f) = s.sum (fun a => NNRat.toNNReal (f a)) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [NNRat.toNNReal_zero]
  · intro a s ha hs
    simp [Finset.sum_insert, ha, NNRat.toNNReal_add, hs]

namespace FDist

/-! ## Bridge to `PMF`

`toPMF` casts a normalized `FDist` into a Mathlib `PMF`. The bridge is a
monad homomorphism (`toPMF_pure`, `toPMF_bind`, `toPMF_map`), and
`expect_toPMF_eq_sum` reduces `PMF`-expectations to finite rational sums
— the basis for computable expected utility in the strategic semantics.
The bridge is one-way: `PMF → FDist` does not exist in general (a `PMF`
may carry irrational or infinite-support weights). -/

/-- Convert a normalized finite-support weighted distribution into a `PMF`. -/
noncomputable def toPMF {γ : Type} [DecidableEq γ]
    (d : FDist γ) (h : d.totalWeight = 1) : PMF γ :=
  PMF.ofFinset
    (fun a => (NNRat.toNNReal (d a) : ENNReal))
    d.support
    (by
      have hsum : d.support.sum (fun a => d a) = 1 := by
        simpa [FDist.totalWeight, Finsupp.sum] using h
      calc
        d.support.sum (fun a => ((NNRat.toNNReal (d a) : NNReal) : ENNReal))
            = ((d.support.sum fun a => NNRat.toNNReal (d a) : NNReal) : ENNReal) := by
                rw [← ENNReal.coe_finset_sum]
        _ = (NNRat.toNNReal (d.support.sum fun a => d a) : ENNReal) := by
              rw [NNRat.toNNReal_finset_sum]
        _ = 1 := by simp [hsum, NNRat.toNNReal_one])
    (by
      intro a ha
      have hz : d a = 0 := by
        simpa [Finsupp.mem_support_iff] using ha
      simp [hz, NNRat.toNNReal_zero])

/-- `toPMF` applied at a point equals the cast of the original weight. -/
theorem toPMF_apply {γ : Type} [DecidableEq γ]
    (d : FDist γ) (h : d.totalWeight = 1) (a : γ) :
    (d.toPMF h) a = (NNRat.toNNReal (d a) : ENNReal) := by
  simp [FDist.toPMF, PMF.ofFinset_apply]

/-- `toPMF` converts `FDist.pure` to `PMF.pure`. -/
theorem toPMF_pure [DecidableEq α] (a : α) :
    (FDist.pure a).toPMF (FDist.totalWeight_pure a) = PMF.pure a := by
  ext b
  rw [toPMF_apply]
  simp only [FDist.pure, PMF.pure_apply]
  rw [Finsupp.single_apply]
  split
  · next h => subst h; simp [NNRat.toNNReal_one]
  · next h => simp [NNRat.toNNReal_zero, Ne.symm h]

/-- `toPMF` converts `FDist.map` to `PMF.map`. -/
theorem toPMF_map [DecidableEq α] [DecidableEq β]
    (d : FDist α) (g : α → β) (h : d.totalWeight = 1)
    (hmap : (d.map g).totalWeight = 1) :
    (d.map g).toPMF hmap = (d.toPMF h).map g := by
  ext b
  rw [toPMF_apply]
  simp only [PMF.map_apply, toPMF_apply]
  rw [FDist.map_apply]
  rw [tsum_eq_sum (s := d.support) (fun a ha => by
    have hz : d a = 0 := by simpa [Finsupp.mem_support_iff] using ha
    simp [hz, NNRat.toNNReal_zero])]
  have hlhs :
      ((NNRat.toNNReal (∑ a ∈ d.support, if g a = b then d a else 0) : NNReal) : ENNReal) =
        ∑ a ∈ d.support, ((NNRat.toNNReal (if g a = b then d a else 0) : NNReal) : ENNReal) := by
    rw [NNRat.toNNReal_finset_sum, ENNReal.coe_finset_sum]
  rw [hlhs]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hgab : g a = b
  · simp [hgab]
  · simp [hgab, Ne.symm hgab, NNRat.toNNReal_zero]

/-- Pointwise `toPMF` of `FDist.bind`. -/
theorem toPMF_bind_apply [DecidableEq α] [DecidableEq β]
    (d : FDist α) (f : α → FDist β)
    (hbind : (d.bind f).totalWeight = 1) (b : β) :
    ((d.bind f).toPMF hbind) b =
      d.support.sum (fun a =>
        (NNRat.toNNReal (d a) : ENNReal) * (NNRat.toNNReal ((f a) b) : ENNReal)) := by
  rw [toPMF_apply, bind_apply]
  rw [show ((NNRat.toNNReal (d.support.sum fun a => d a * (f a) b) : NNReal) : ENNReal) =
      d.support.sum (fun a => ((NNRat.toNNReal (d a * (f a) b) : NNReal) : ENNReal)) from by
    rw [NNRat.toNNReal_finset_sum, ENNReal.coe_finset_sum]]
  apply Finset.sum_congr rfl
  intro a _
  rw [NNRat.toNNReal_mul, ENNReal.coe_mul]

/-- `toPMF` commutes with `bind` when the branches are normalized. -/
theorem toPMF_bind [DecidableEq α] [DecidableEq β]
    (d : FDist α) (f : α → FDist β)
    (hd : d.totalWeight = 1)
    (hf : ∀ a, FDist.totalWeight (f a) = 1)
    (hbind : (FDist.bind d f).totalWeight = 1) :
    (FDist.bind d f).toPMF hbind =
      (d.toPMF hd).bind (fun a => (f a).toPMF (hf a)) := by
  ext b
  rw [toPMF_bind_apply]
  simp only [PMF.bind_apply, toPMF_apply]
  rw [tsum_eq_sum (s := d.support) (fun a ha => by
    have hz : d a = 0 := by simpa [Finsupp.mem_support_iff] using ha
    simp [hz, NNRat.toNNReal_zero])]

/-- Expectation under `FDist.toPMF` reduces to a finite sum over support. -/
theorem expect_toPMF_eq_sum {γ : Type} [DecidableEq γ]
    (d : FDist γ) (h : d.totalWeight = 1) (f : γ → ℝ) :
    Math.Probability.expect (d.toPMF h) f =
      d.support.sum (fun a => ((NNRat.toNNReal (d a) : NNReal) : ℝ) * f a) := by
  unfold Math.Probability.expect
  rw [tsum_eq_sum (s := d.support)]
  · refine Finset.sum_congr rfl ?_
    intro a ha
    simp [FDist.toPMF]
  · intro a ha
    have hz : d a = 0 := by
      simpa [Finsupp.mem_support_iff] using ha
    simp [FDist.toPMF, hz, NNRat.toNNReal_zero]

end FDist

end Vegas
