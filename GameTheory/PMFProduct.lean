import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators
universe uι uA uβ
set_option autoImplicit false

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
variable {A : ι → Type uA}

open scoped BigOperators

noncomputable def pmfPi [∀ i, Fintype (A i)] (σ : ∀ i, PMF (A i)) : PMF (∀ i, A i) :=
  PMF.ofFintype (fun s => ∏ i, σ i (s i)) (by
    rw [← Fintype.prod_sum]
    have : ∀ i, ∑ j : A i, (σ i) j = 1 :=
      fun i => by
        have h := PMF.tsum_coe (σ i)
        rwa [tsum_eq_sum (s := Finset.univ)
          (fun x hx => absurd (Finset.mem_univ x) hx)] at h
    simp [this])

@[simp] lemma pmfPi_apply [∀ i, Fintype (A i)] (σ : ∀ i, PMF (A i)) (s : ∀ i, A i) :
    pmfPi (A := A) σ s = ∏ i, σ i (s i) := by
  simp [pmfPi, PMF.ofFintype_apply]

/-- Factor the product weight into the `j`-coordinate and the rest. -/
lemma prod_factor_erase (σ : ∀ i, PMF (A i)) (j : ι) (s : ∀ i, A i) :
    (∏ i : ι, σ i (s i))
      =
    (σ j) (s j) * (∏ i ∈ (Finset.univ.erase j), σ i (s i)) := by
  classical
  simpa [Finset.mem_univ] using
    (Finset.mul_prod_erase (s := (Finset.univ : Finset ι))
      (f := fun i => σ i (s i)) (a := j) (by simp)).symm

/-!
## 1) “Rest product is invariant under update at j”
This is your `h2` packaged.
-/

/-- Updating a profile at coordinate `j` does not change the product over `univ.erase j`. -/
lemma prod_erase_update_eq (σ : ∀ i, PMF (A i)) (j : ι) (s : ∀ i, A i) (a : A j) :
    (∏ i ∈ Finset.univ.erase j, σ i ((Function.update s j a) i))
      =
    (∏ i ∈ Finset.univ.erase j, σ i (s i)) := by
  classical
  apply Finset.prod_congr rfl
  intro i hi
  have hij : i ≠ j := Finset.ne_of_mem_erase hi
  simp [Function.update, hij]

/-!
## 2) The “swap” involution on pairs (a, s)
This is your `e_fun` and `e_inv` packaged.
-/

/-- Swap outer `a` with the `j`-coordinate of `s`, and update `s` at `j` to `a`. -/
def swapJA (j : ι) : (A j × (∀ i, A i)) → (A j × (∀ i, A i)) :=
  fun p => (p.2 j, Function.update p.2 j p.1)

omit [Fintype ι] in
/-- `swapJA` is an involution. -/
lemma swapJA_involutive (j : ι) : Function.Involutive (swapJA (A := A) j) := by
  intro p
  rcases p with ⟨a, s⟩
  apply Prod.ext
  · -- first component
    simp [swapJA]
  · -- second component
    funext i
    by_cases h : i = j
    · subst h
      simp [swapJA]
    · simp [swapJA]

omit [Fintype ι] in
/-- `swapJA` is bijective (as a corollary of involutive). -/
lemma swapJA_bijective (j : ι) : Function.Bijective (swapJA (A := A) j) :=
  (swapJA_involutive (A := A) j).bijective

/-!
## 3) “hg implies update at j doesn’t change g”
This is your `h3` packaged.
-/

omit [Fintype ι] in
/-- If `g a s` ignores the `j`-coordinate of `s`, then updating `s` at `j` does not change `g`. -/
lemma hg_update_eq {j : ι}
    {β : Type uβ} (g : A j → (∀ i, A i) → PMF β)
    (hg : ∀ a (s₁ s₂ : ∀ i, A i), (∀ i, i ≠ j → s₁ i = s₂ i) → g a s₁ = g a s₂)
    (a0 : A j) (s : ∀ i, A i) (a : A j) :
    g a0 (Function.update s j a) = g a0 s := by
  apply hg a0 (Function.update s j a) s
  intro i hi
  simp [Function.update, hi]

/-!
## 4) A reusable “sum over univ is invariant under an involution”
This replaces the ad-hoc `Finset.sum_bij` tail.
-/

lemma sum_univ_eq_sum_univ_of_involutive
    {α : Type _} [Fintype α]
    {δ : Type _} [AddCommMonoid δ]
    (e : α → α) (he : Function.Involutive e) (f : α → δ) :
    (∑ x : α, f (e x)) = ∑ x : α, f x := by
  -- Use `Finset.sum_bij` on `Finset.univ` with the involution as the bijection.
  -- Map is `e`; inverse is itself.
  simpa using
    (Finset.sum_bij
      (s := (Finset.univ : Finset α))
      (t := (Finset.univ : Finset α))
      (fun x _ => e x)
      (by intro x hx; simp))
      (by
        intro x₁ hx₁ x₂ hx₂ hxe
        -- injective: apply e to both sides and use involutive
        have := congrArg e hxe
        simpa [he x₁, he x₂] using this)
      (by
        intro y hy
        refine ⟨e y, ?_, ?_⟩
        · simp
        · simp [he y])
      (by
        intro x hx
        rfl)

/-- Specialization: `swapJA` preserves sums over `A j × (∀ i, A i)`. -/
lemma sum_univ_swapJA [∀ i, Fintype (A i)] (σ : ∀ i, PMF (A i)) (j : ι) {β : Type uβ}
    (g : A j → (∀ i, A i) → PMF β) (b : β) :
    (∑ p : A j × (∀ i, A i),
        (σ j) p.1 * ((σ j) (p.2 j) * (∏ i ∈ Finset.univ.erase j, σ i (p.2 i)) * g p.1 p.2 b))
      =
    (∑ p : A j × (∀ i, A i),
        (σ j) (swapJA (A := A) j p).1 *
          ((σ j) ((swapJA (A := A) j p).2 j) *
            (∏ i ∈ Finset.univ.erase j, σ i ((swapJA (A := A) j p).2 i)) *
              g (swapJA (A := A) j p).1 (swapJA (A := A) j p).2 b)) := by
  symm
  have he : Function.Involutive (swapJA (A := A) j) := swapJA_involutive (A := A) j
  simpa using
    (sum_univ_eq_sum_univ_of_involutive
      (e := swapJA (A := A) j)
      (he := he)
      (f := fun p =>
        (σ j) p.1 * ((σ j) (p.2 j) * (∏ i ∈ Finset.univ.erase j, σ i (p.2 i)) * g p.1 p.2 b)))

/-- **Product PMF factorization** at coordinate `j`. -/
theorem pmfPi_bind_factor [∀ i, Fintype (A i)]
    (σ : ∀ i, PMF (A i)) (j : ι) {β : Type uβ}
    (g : A j → (∀ i, A i) → PMF β)
    (hg : ∀ a (s₁ s₂ : ∀ i, A i), (∀ i, i ≠ j → s₁ i = s₂ i) → g a s₁ = g a s₂) :
    (pmfPi (A := A) σ).bind (fun s => g (s j) s) =
    (σ j).bind (fun a => (pmfPi (A := A) σ).bind (fun s => g a s)) := by
  ext b
  simp only [PMF.bind_apply, pmfPi_apply, tsum_fintype]
  -- `∑ a, σ j a = 1`
  have h_one : (∑ a : A j, σ j a) = 1 := by
    simpa [tsum_fintype] using (PMF.tsum_coe (σ j))
  let W : (A j × (∀ i, A i)) → ENNReal :=
    fun p =>
      σ j p.1 *
        ((σ j (p.2 j) * ∏ i ∈ Finset.univ.erase j, σ i (p.2 i)) * g p.1 p.2 b)
  let e : (A j × (∀ i, A i)) → (A j × (∀ i, A i)) := swapJA (A := A) (j := j)
  have he : Function.Involutive e := swapJA_involutive (j := j)
  have H_W_eq :
      ∀ (a : A j) (s : ∀ i, A i),
        σ j a * ((∏ i : ι, σ i (s i)) * g (s j) s b)
          =
        W (e (a, s)) := by
    intro a s
    have h_update_g : g (s j) (Function.update s j a) b = g (s j) s b := by
      have := congrArg (fun pmf => pmf b) (hg_update_eq (g := g) hg (a0 := s j) (s := s) (a := a))
      simpa using this
    dsimp [W, e, swapJA]
    simp_rw [prod_factor_erase σ j s]
    have h2 :
        (∏ i ∈ Finset.univ.erase j, σ i ((Function.update s j a) i))
          =
        (∏ i ∈ Finset.univ.erase j, σ i (s i)) :=
      prod_erase_update_eq (A := A) (σ := σ) (j := j) (s := s) (a := a)
    simp [h2, h_update_g, mul_left_comm, mul_comm]
  calc
    (∑ s : (∀ i, A i), (∏ i : ι, σ i (s i)) * g (s j) s b)
        =
      (∑ s : (∀ i, A i), (∏ i : ι, σ i (s i)) * g (s j) s b) * 1 := by
        simp
    _ =
      (∑ s : (∀ i, A i), (∏ i : ι, σ i (s i)) * g (s j) s b) * (∑ a : A j, σ j a) := by
        simp [h_one]
    _ =
      ∑ a : A j, ∑ s : (∀ i, A i), σ j a * ((∏ i : ι, σ i (s i)) * g (s j) s b) := by
        simp only [mul_comm, Finset.mul_sum, mul_assoc]
        exact Finset.sum_comm
    _ =
      ∑ a : A j, ∑ s : (∀ i, A i), W (e (a, s)) := by
        simp [H_W_eq]
    _ =
      ∑ p : A j × (∀ i, A i), W (e p) := Eq.symm (Fintype.sum_prod_type fun x ↦ W (e x))
    _ =
      ∑ p : A j × (∀ i, A i), W p := Eq.symm (sum_univ_swapJA σ j g b)
    _ =
      ∑ a : A j, σ j a * ∑ s : (∀ i, A i), (∏ i : ι, σ i (s i)) * g a s b := by
        simp [W, Fintype.sum_prod_type, Finset.mul_sum,
          prod_factor_erase σ j, mul_left_comm, mul_comm]
