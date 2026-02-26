import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions

open scoped BigOperators

universe uι uA uα uβ uγ

set_option autoImplicit false

namespace GameTheory

namespace PMFProduct

-- ============================================================================
-- § Aux. Helpers (private, used by later proofs)
-- ============================================================================

private lemma pmf_sum_eq_one {α : Type*} [Fintype α] (μ : PMF α) :
    ∑ a : α, μ a = 1 := by
  have h := PMF.tsum_coe μ
  rwa [tsum_eq_sum (s := Finset.univ)
    (fun x hx => absurd (Finset.mem_univ x) hx)] at h

section Aux

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
variable {A : ι → Type uA}

/-- Factor the product weight into the `j`-coordinate and the rest. -/
lemma prod_factor_erase (σ : ∀ i, PMF (A i)) (j : ι) (s : ∀ i, A i) :
    (∏ i : ι, σ i (s i))
      = (σ j) (s j) * (∏ i ∈ (Finset.univ.erase j), σ i (s i)) := by
  classical
  simpa [Finset.mem_univ] using
    (Finset.mul_prod_erase (s := (Finset.univ : Finset ι))
      (f := fun i => σ i (s i)) (a := j) (by simp)).symm

/-- Updating at coordinate `j` does not change the product over `univ.erase j`. -/
lemma prod_erase_update_eq (σ : ∀ i, PMF (A i)) (j : ι) (s : ∀ i, A i) (a : A j) :
    (∏ i ∈ Finset.univ.erase j, σ i ((Function.update s j a) i))
      = (∏ i ∈ Finset.univ.erase j, σ i (s i)) := by
  apply Finset.prod_congr rfl
  intro i hi
  simp [Function.update, Finset.ne_of_mem_erase hi]

/-- Swap outer `a` with the `j`-coordinate of `s`, and update `s` at `j` to `a`. -/
def swapJA (j : ι) : (A j × (∀ i, A i)) → (A j × (∀ i, A i)) :=
  fun p => (p.2 j, Function.update p.2 j p.1)

omit [Fintype ι] in
lemma swapJA_involutive (j : ι) : Function.Involutive (swapJA (A := A) j) := by
  intro ⟨a, s⟩
  apply Prod.ext
  · simp [swapJA]
  · funext i; by_cases h : i = j
    · subst h; simp [swapJA]
    · simp [swapJA, Function.update]

lemma sum_univ_eq_sum_univ_of_involutive
    {α : Type _} [Fintype α] {δ : Type _} [AddCommMonoid δ]
    (e : α → α) (he : Function.Involutive e) (f : α → δ) :
    (∑ x : α, f (e x)) = ∑ x : α, f x := by
  simpa using
    (Finset.sum_bij (s := Finset.univ) (t := Finset.univ)
      (fun x _ => e x) (by intro x _; simp))
      (by intro x₁ _ x₂ _ hxe; have := congrArg e hxe; simpa [he x₁, he x₂] using this)
      (by intro y _; exact ⟨e y, Finset.mem_univ _, he y⟩)
      (by intro _ _; rfl)

end Aux

-- ============================================================================
-- § Core
-- ============================================================================

section Core

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
variable {A : ι → Type uA}

/-- Product PMF over a finite index type: independently sample each coordinate. -/
noncomputable def pmfPi [∀ i, Fintype (A i)] (σ : ∀ i, PMF (A i)) : PMF (∀ i, A i) :=
  PMF.ofFintype (fun s => ∏ i, σ i (s i)) (by
    rw [← Fintype.prod_sum]
    have : ∀ i, ∑ j : A i, (σ i) j = 1 := fun i => pmf_sum_eq_one (σ i)
    simp [this])

@[simp] lemma pmfPi_apply [∀ i, Fintype (A i)]
    (σ : ∀ i, PMF (A i)) (s : ∀ i, A i) :
    pmfPi (A := A) σ s = ∏ i, σ i (s i) := by
  simp [pmfPi, PMF.ofFintype_apply]

/-- Coordinate projection. -/
@[simp] def coord (j : ι) (s : (∀ i, A i)) : A j := s j

/-- Update the `j`-coordinate of an assignment. -/
@[simp] def update (s : (∀ i, A i)) (j : ι) (a : A j) : (∀ i, A i) :=
  Function.update s j a

omit [Fintype ι] in
@[simp] lemma update_self (s : (∀ i, A i)) (j : ι) (a : A j) :
    update (A := A) s j a j = a := by
  simp [update]

omit [Fintype ι] in
@[simp] lemma update_ne (s : (∀ i, A i)) {i j : ι} (a : A j) (h : i ≠ j) :
    update (A := A) s j a i = s i := by
  simp [update, h]

/-- "`F` ignores coordinate `j`": updating `j` does not change `F`. -/
def Ignores {α : Type uα} (j : ι) (F : (∀ i, A i) → α) : Prop :=
  ∀ s a, F (update (A := A) s j a) = F s

/-- "`G a0 s` ignores coordinate `j` in `s`", uniformly in the external parameter `a0`. -/
def Ignores₂ {α : Type uα} (j : ι) (G : A j → (∀ i, A i) → α) : Prop :=
  ∀ a0 s a, G a0 (update (A := A) s j a) = G a0 s

omit [Fintype ι] in
/-- A pointwise (extensional) criterion implying `Ignores`. -/
lemma Ignores_of_pointwise {α : Type uα} (j : ι) (F : (∀ i, A i) → α)
    (h : ∀ s₁ s₂, (∀ i, i ≠ j → s₁ i = s₂ i) → F s₁ = F s₂) :
    Ignores (A := A) j F := by
  intro s a
  apply h (update (A := A) s j a) s
  intro i hi
  simp [update, hi]

omit [Fintype ι] in
/-- A pointwise (extensional) criterion implying `Ignores₂`. -/
lemma Ignores₂_of_pointwise {α : Type uα} (j : ι) (G : A j → (∀ i, A i) → α)
    (h : ∀ a0 s₁ s₂, (∀ i, i ≠ j → s₁ i = s₂ i) → G a0 s₁ = G a0 s₂) :
    Ignores₂ (A := A) j G := by
  intro a0 s a
  apply h a0 (update (A := A) s j a) s
  intro i hi
  simp [update, hi]

end Core

section BindFactor

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
variable {A : ι → Type uA} [∀ i, Fintype (A i)]
variable {β : Type uβ}

/-- ENNReal-sum version: "Fubini" for product weights with an `Ignores₂` condition. -/
theorem sum_pmfPi_factor
    (σ : ∀ i, PMF (A i)) (j : ι)
    (F : A j → (∀ i, A i) → ENNReal)
    (hF : Ignores₂ (A := A) j F) :
    (∑ s : (∀ i, A i), (∏ i, σ i (s i)) * F (s j) s)
      =
    ∑ a : A j, (σ j a) * (∑ s : (∀ i, A i), (∏ i, σ i (s i)) * F a s) := by
  have h_one : (∑ a : A j, σ j a) = 1 := pmf_sum_eq_one (σ j)
  let W : (A j × (∀ i, A i)) → ENNReal := fun p =>
    σ j p.1 * ((σ j (p.2 j) * ∏ i ∈ Finset.univ.erase j, σ i (p.2 i)) * F p.1 p.2)
  let e := swapJA (A := A) j
  have he : Function.Involutive e := swapJA_involutive j
  -- Key: each summand under the swap equals the original summand
  have H_W_eq : ∀ (a : A j) (s : ∀ i, A i),
      σ j a * ((∏ i : ι, σ i (s i)) * F (s j) s) = W (e (a, s)) := by
    intro a s
    -- F (s j) (Function.update s j a) = F (s j) s by Ignores₂
    have hF_upd : F (s j) (Function.update s j a) = F (s j) s :=
      hF (s j) s a
    dsimp [W, e, swapJA]
    rw [prod_erase_update_eq σ j s a, hF_upd]
    simp_rw [prod_factor_erase σ j s]
    simp [mul_left_comm, mul_comm]
  calc (∑ s, (∏ i, σ i (s i)) * F (s j) s)
      = (∑ s, (∏ i, σ i (s i)) * F (s j) s) * 1 := by simp
    _ = (∑ s, (∏ i, σ i (s i)) * F (s j) s) * (∑ a, σ j a) := by
        simp [h_one]
    _ = ∑ a, ∑ s, σ j a * ((∏ i, σ i (s i)) * F (s j) s) := by
        simp only [mul_comm, Finset.mul_sum, mul_assoc]
        exact Finset.sum_comm
    _ = ∑ a, ∑ s, W (e (a, s)) := by
        simp only [H_W_eq]
    _ = ∑ p : A j × (∀ i, A i), W (e p) :=
        (Fintype.sum_prod_type fun x ↦ W (e x)).symm
    _ = ∑ p : A j × (∀ i, A i), W p :=
        sum_univ_eq_sum_univ_of_involutive e he W
    _ = ∑ a, σ j a * ∑ s, (∏ i, σ i (s i)) * F a s := by
        simp [W, Fintype.sum_prod_type, Finset.mul_sum,
          prod_factor_erase σ j, mul_left_comm, mul_comm]

/-- Bind factorization over a coordinate when the continuation ignores that coordinate. -/
theorem pmfPi_bind_factor
    (σ : ∀ i, PMF (A i)) (j : ι)
    (g : A j → (∀ i, A i) → PMF β)
    (hg : Ignores₂ (A := A) j g) :
    (pmfPi (A := A) σ).bind (fun s => g (s j) s)
      =
    (σ j).bind (fun a => (pmfPi (A := A) σ).bind (fun s => g a s)) := by
  ext b
  simp only [PMF.bind_apply, pmfPi_apply, tsum_fintype]
  exact sum_pmfPi_factor σ j (fun a s => g a s b) (fun a0 s a => by
    -- Need: (g a0 (update s j a)) b = (g a0 s) b
    -- hg gives: g a0 (update s j a) = g a0 s  (as PMFs)
    exact congrFun (congrArg DFunLike.coe (hg a0 s a)) b)

end BindFactor

section Pushforward

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
variable {A : ι → Type uA} [∀ i, Fintype (A i)]
variable {α : Type uα} {β : Type uβ}

/-- Pushforward of a PMF along a function. -/
noncomputable def pushforward (μ : PMF α) (f : α → β) : PMF β :=
  μ.bind (fun a => PMF.pure (f a))

open Classical in
/-- Pointwise marginal (sum-form) for a coordinate event. -/
theorem pmfPi_coord_mass
    (σ : ∀ i, PMF (A i)) (j : ι) (a : A j) :
    (∑ s : (∀ i, A i), if s j = a then (pmfPi (A := A) σ) s else 0) = σ j a := by
  simp only [pmfPi_apply]
  -- Use the Dirac trick: substitute coordinate j with PMF.pure a
  have h_sum := pmf_sum_eq_one (pmfPi (A := A) (Function.update σ j (PMF.pure a)))
  simp only [pmfPi_apply] at h_sum
  -- Expand the updated product into indicator * rest
  have h_expand : ∀ s : (∀ i, A i),
      (∏ i : ι, (Function.update σ j (PMF.pure a)) i (s i))
        = (if s j = a then 1 else 0) *
            ∏ i ∈ Finset.univ.erase j, σ i (s i) := by
    intro s
    rw [prod_factor_erase (Function.update σ j (PMF.pure a)) j s]
    congr 1
    · simp [Function.update, PMF.pure_apply, eq_comm]
    · apply Finset.prod_congr rfl; intro i hi
      simp [Function.update, Finset.ne_of_mem_erase hi]
  simp_rw [h_expand] at h_sum
  -- h_sum : ∑ s, (if s j = a then 1 else 0) * ∏ i ∈ erase j, σ i (s i) = 1
  -- Factor out σ j a from our goal and use h_sum
  have h_factor : ∀ s : (∀ i, A i),
      (if s j = a then ∏ i, σ i (s i) else 0)
        = σ j a * ((if s j = a then 1 else 0) *
            ∏ i ∈ Finset.univ.erase j, σ i (s i)) := by
    intro s; by_cases h : s j = a
    · simp [h, prod_factor_erase σ j s]
    · simp [h]
  simp_rw [h_factor, ← Finset.mul_sum, h_sum, mul_one]

open Classical in
/-- The pushforward of a product distribution along a coordinate
    is the factor at that coordinate. -/
theorem pmfPi_push_coord
    (σ : ∀ i, PMF (A i)) (j : ι) :
    pushforward (pmfPi (A := A) σ) (fun s => s j) = σ j := by
  ext a
  simp only [pushforward, PMF.bind_apply, PMF.pure_apply,
    tsum_fintype, mul_ite, mul_one, mul_zero]
  simp_rw [@eq_comm _ a]
  exact pmfPi_coord_mass σ j a

end Pushforward

section Conditioning

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
variable {A : ι → Type uA} [∀ i, Fintype (A i)]
variable {α : Type uα}

/-- Mask a PMF by a decidable event (as an ENNReal-valued function). -/
noncomputable def pmfMask (μ : PMF α) (E : α → Prop) [DecidablePred E] : α → ENNReal :=
  fun a => if E a then μ a else 0

/-- Total mass of a masked PMF. -/
noncomputable def pmfMass (μ : PMF α) (E : α → Prop) [Fintype α] [DecidablePred E] : ENNReal :=
  ∑ a : α, pmfMask (μ := μ) E a

/-- Condition a PMF on an event with nonzero mass. -/
noncomputable def pmfCond (μ : PMF α) (E : α → Prop) [Fintype α] [DecidablePred E]
    (h : pmfMass (μ := μ) E ≠ 0) : PMF α :=
  PMF.ofFintype
    (fun a => pmfMask (μ := μ) E a / pmfMass (μ := μ) E)
    (by
      simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
      have h_ne_top : pmfMass (μ := μ) E ≠ ⊤ := by
        apply ne_of_lt
        calc pmfMass (μ := μ) E = ∑ a, pmfMask (μ := μ) E a := rfl
          _ ≤ ∑ a : α, μ a := by
              apply Finset.sum_le_sum; intro a _; simp [pmfMask]; split_ifs <;> simp
          _ = 1 := pmf_sum_eq_one μ
          _ < ⊤ := ENNReal.one_lt_top
      exact ENNReal.mul_inv_cancel h h_ne_top)

@[simp] lemma pmfCond_apply (μ : PMF α) (E : α → Prop) [Fintype α] [DecidablePred E]
    (h : pmfMass (μ := μ) E ≠ 0) (a : α) :
    pmfCond (μ := μ) E h a = pmfMask (μ := μ) E a / pmfMass (μ := μ) E := by
  simp [pmfCond, PMF.ofFintype_apply]

open Classical in
/-- The mass of the coordinate-lifted event under a product is the mass under the factor. -/
theorem pmfMass_pmfPi_coord
    (σ : ∀ i, PMF (A i)) (j : ι)
    (E : A j → Prop) [DecidablePred E] :
    pmfMass (μ := pmfPi (A := A) σ) (fun s => E (s j))
      =
    pmfMass (μ := σ j) E := by
  simp only [pmfMass, pmfMask, pmfPi_apply]
  -- Partition the sum over s by s j values, introducing a double sum
  have hdecomp : ∀ s : (∀ i, A i),
      (if E (s j) then ∏ i, σ i (s i) else 0 : ENNReal)
      = Finset.sum Finset.univ (fun a : A j =>
          if s j = a ∧ E a then ∏ i, σ i (s i) else 0) := by
    intro s
    symm
    rw [Finset.sum_eq_single (s j)]
    · simp
    · intro b _ hb; exact if_neg (fun ⟨heq, _⟩ => hb heq.symm)
    · intro h; exact absurd (Finset.mem_univ _) h
  simp_rw [hdecomp]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  by_cases hE : E a
  · simp only [hE, and_true, ↓reduceIte]
    have := pmfPi_coord_mass σ j a
    simpa [pmfPi_apply] using this
  · simp [hE]

/-- Conditioning a product PMF on a coordinate event updates only that coordinate's factor. -/
theorem pmfPi_cond_coord
    (σ : ∀ i, PMF (A i)) (j : ι)
    (E : A j → Prop) [DecidablePred E]
    (hE : pmfMass (μ := σ j) E ≠ 0) :
    pmfCond (μ := pmfPi (A := A) σ) (fun s => E (s j))
      (by
        simpa [pmfMass_pmfPi_coord (A := A) (σ := σ) (j := j) (E := E)] using hE)
      =
    pmfPi (A := A) (Function.update σ j (pmfCond (μ := σ j) E hE)) := by
  ext s
  simp only [pmfCond_apply, pmfPi_apply, pmfMask, pmfMass_pmfPi_coord]
  -- Factor the RHS product at j
  rw [prod_factor_erase (Function.update σ j (pmfCond (μ := σ j) E hE)) j s]
  -- The j-th factor
  have hj : (Function.update σ j (pmfCond (μ := σ j) E hE)) j (s j)
      = (if E (s j) then σ j (s j) else 0) / pmfMass (μ := σ j) E := by
    simp [Function.update, pmfCond_apply, pmfMask]
  rw [hj]
  -- The rest factors are unchanged
  have h_rest : (∏ i ∈ Finset.univ.erase j,
      (Function.update σ j (pmfCond (μ := σ j) E hE)) i (s i))
      = ∏ i ∈ Finset.univ.erase j, σ i (s i) := by
    apply Finset.prod_congr rfl; intro i hi
    simp [Function.update, Finset.ne_of_mem_erase hi]
  rw [h_rest, prod_factor_erase σ j s]
  -- Now algebra: LHS = (if E then σj*rest else 0) / mass
  --              RHS = ((if E then σj else 0) / mass) * rest
  by_cases hE_s : E (s j)
  · simp only [hE_s, ↓reduceIte]
    -- σ j (s j) * rest / mass = (σ j (s j) / mass) * rest
    simp only [div_eq_mul_inv, mul_comm, mul_left_comm]
  · simp [hE_s]

/-- Corollary: conditioning on coordinate `j` does not change other coordinate marginals. -/
theorem pmfPi_cond_coord_push_other
    (σ : ∀ i, PMF (A i)) {j q : ι} (hq : q ≠ j)
    (E : A j → Prop) [DecidablePred E]
    (hE : pmfMass (μ := σ j) E ≠ 0) :
    pushforward
      (pmfCond (μ := pmfPi (A := A) σ) (fun s => E (s j))
        (by simpa [pmfMass_pmfPi_coord (A := A) (σ := σ) (j := j) (E := E)] using hE))
      (fun s => s q)
      =
    σ q := by
  rw [pmfPi_cond_coord σ j E hE,
      pmfPi_push_coord (Function.update σ j (pmfCond (μ := σ j) E hE)) q]
  simp [Function.update, hq]

end Conditioning


section UpdateLemmas

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
variable {A : ι → Type uA} [∀ i, Fintype (A i)]
variable {β : Type uβ}

/-- Pointwise: updating the *factor family* at `j` only changes that coordinate's factor. -/
@[simp] lemma pmfPi_apply_update_family (σ : ∀ i, PMF (A i)) (j : ι) (τ : PMF (A j))
    (s : ∀ i, A i) :
    pmfPi (A := A) (Function.update σ j τ) s
      =
    (τ (s j)) * (∏ i ∈ Finset.univ.erase j, σ i (s i)) := by
  classical
  simp only [pmfPi_apply]
  rw [prod_factor_erase (Function.update σ j τ) j s]
  congr 1
  · simp [Function.update]
  · apply Finset.prod_congr rfl; intro i hi
    simp [Function.update, Finset.ne_of_mem_erase hi]

/-- A robust, division-free form: cross-multiplication of the updated and original products. -/
lemma pmfPi_update_family_mul (σ : ∀ i, PMF (A i)) (j : ι) (τ : PMF (A j))
    (s : ∀ i, A i) :
    pmfPi (A := A) (Function.update σ j τ) s * σ j (s j)
      =
    pmfPi (A := A) σ s * τ (s j) := by
  rw [pmfPi_apply_update_family, pmfPi_apply, prod_factor_erase σ j s]
  -- LHS: (τ (s j) * rest) * σ j (s j)
  -- RHS: (σ j (s j) * rest) * τ (s j)
  simp [mul_comm, mul_left_comm]

omit [Fintype ι] [∀ i, Fintype (A i)] in
/-- "Update then read": trivial simp lemma, but you want it globally available. -/
@[simp] lemma update_family_same (σ : ∀ i, PMF (A i)) (j : ι) (τ : PMF (A j)) :
    (Function.update σ j τ) j = τ := by
  simp [Function.update]

omit [Fintype ι] [∀ i, Fintype (A i)] in
@[simp] lemma update_family_other (σ : ∀ i, PMF (A i)) {i j : ι}
    (τ : PMF (A j)) (h : i ≠ j) :
    (Function.update σ j τ) i = σ i := by
  simp [Function.update, h]

end UpdateLemmas

section ConditioningCoord

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
variable {A : ι → Type uA} [∀ i, Fintype (A i)]

-- assume you already have:
-- pushforward, pmfMask, pmfMass, pmfCond, pmfCond_apply
-- pmfMass_pmfPi_coord : pmfMass (pmfPi σ) (fun s => E (s j)) = pmfMass (σ j) E

/-- The *definition* you want to use everywhere: update family at `j`. -/
noncomputable def updateAt (σ : ∀ i, PMF (A i)) (j : ι) (τ : PMF (A j)) : ∀ i, PMF (A i) :=
  Function.update σ j τ

/-- Conditioning a product on a coordinate event = product of updated family.
    This is the lemma Gemini is pointing to; note how clean the RHS becomes. -/
theorem pmfPi_cond_coord_updateAt
    (σ : ∀ i, PMF (A i)) (j : ι)
    (E : A j → Prop) [DecidablePred E]
    (hE : pmfMass (μ := σ j) E ≠ 0) :
    pmfCond (μ := pmfPi (A := A) σ) (fun s => E (s j))
      (by
        -- discharge "mass ≠ 0" for the lifted event using pmfMass_pmfPi_coord
        simpa [pmfMass_pmfPi_coord (A := A) (σ := σ) (j := j) (E := E)] using hE)
      =
    pmfPi (A := A) (updateAt (A := A) σ j (pmfCond (μ := σ j) E hE)) := by
  -- updateAt unfolds to Function.update, so this is exactly pmfPi_cond_coord.
  exact pmfPi_cond_coord σ j E hE

/-- Corollary in the "no pain" style: other marginals are unchanged. -/
theorem pmfPi_cond_coord_other_marginal
    (σ : ∀ i, PMF (A i)) {j q : ι} (hq : q ≠ j)
    (E : A j → Prop) [DecidablePred E]
    (hE : pmfMass (μ := σ j) E ≠ 0) :
    pushforward
      (pmfCond (μ := pmfPi (A := A) σ) (fun s => E (s j))
        (by simpa [pmfMass_pmfPi_coord (A := A) (σ := σ) (j := j) (E := E)] using hE))
      (fun s => s q)
      =
    σ q := by
  exact pmfPi_cond_coord_push_other σ hq E hE

/-- The ratio of an event's mass is invariant under updating coordinate `j`,
    provided the event ignores coordinate `j`. -/
theorem pmfPi_event_ratio_invariant_of_ignores
    (σ : ∀ i, PMF (A i)) (j : ι) (τ : PMF (A j))
    (Num Denom : (∀ i, A i) → Prop) [DecidablePred Num] [DecidablePred Denom]
    (hNum_ign : Ignores (A := A) j Num)
    (hDenom_ign : Ignores (A := A) j Denom) :
    (∑ s, if Num s then pmfPi (A := A) (Function.update σ j τ) s else 0)
      * (∑ s, if Denom s then pmfPi (A := A) σ s else 0)
      =
    (∑ s, if Num s then pmfPi (A := A) σ s else 0)
      * (∑ s, if Denom s then pmfPi (A := A) (Function.update σ j τ) s else 0) := by
  let W : (∀ i, A i) × (∀ i, A i) → ENNReal := fun p =>
    (if Num p.1 then pmfPi (A := A) (Function.update σ j τ) p.1 else 0) *
    (if Denom p.2 then pmfPi (A := A) σ p.2 else 0)
  let W_CD : (∀ i, A i) × (∀ i, A i) → ENNReal := fun p =>
    (if Num p.1 then pmfPi (A := A) σ p.1 else 0) *
    (if Denom p.2 then pmfPi (A := A) (Function.update σ j τ) p.2 else 0)
  -- The swap bijection
  let e : (∀ i, A i) × (∀ i, A i) → (∀ i, A i) × (∀ i, A i) :=
    fun p => (update (A := A) p.1 j (p.2 j), update (A := A) p.2 j (p.1 j))
  have he : Function.Involutive e := by
    intro ⟨s1, s2⟩
    dsimp [e]
    congr 1
    · ext i; by_cases hi : i = j
      · subst hi; simp
      · simp [hi]
    · ext i; by_cases hi : i = j
      · subst hi; simp
      · simp [hi]
  have hW : ∀ p, W (e p) = W_CD p := by
    intro ⟨s1, s2⟩
    dsimp only [W, W_CD, e]
    -- The events ignore j, so the conditions match.
    simp_rw [hNum_ign s1 (s2 j), hDenom_ign s2 (s1 j)]
    -- (The rest of your proof remains exactly the same)
    have h1 : pmfPi (A := A) (Function.update σ j τ) (update (A := A) s1 j (s2 j))
              = τ (s2 j) * ∏ i ∈ Finset.univ.erase j, σ i (s1 i) := by
      rw [pmfPi_apply_update_family]
      congr 1
      · simp
      · apply Finset.prod_congr rfl; intro i hi
        simp [Finset.ne_of_mem_erase hi]
    have h2 : pmfPi (A := A) σ (update (A := A) s2 j (s1 j)) = σ j (s1 j)
              * ∏ i ∈ Finset.univ.erase j, σ i (s2 i) := by
      rw [pmfPi_apply, prod_factor_erase σ j (update (A := A) s2 j (s1 j))]
      congr 1
      · simp
      · apply Finset.prod_congr rfl; intro i hi
        simp [Finset.ne_of_mem_erase hi]
    have h3 : pmfPi (A := A) σ s1 = σ j (s1 j) * ∏ i ∈ Finset.univ.erase j, σ i (s1 i) := by
      rw [pmfPi_apply, prod_factor_erase σ j s1]
    have h4 : pmfPi (A := A) (Function.update σ j τ) s2 = τ (s2 j)
              * ∏ i ∈ Finset.univ.erase j, σ i (s2 i) := by
      rw [pmfPi_apply_update_family]
    -- Substitute all evaluations back into the equality
    rw [h1, h2, h3, h4]
    -- Push the if-statements and sort the commutative factors
    by_cases hN : Num s1 <;> by_cases hD : Denom s2
    · simp only [hN, hD, ↓reduceIte]
      simp only [mul_comm, mul_left_comm]
    · simp [hN, hD]
    · simp [hN, hD]
    · simp [hN, hD]
  -- Finally, thread the double sum through the bijection
  calc (∑ s, if Num s then pmfPi (A := A) (Function.update σ j τ) s else 0)
     * (∑ s, if Denom s then pmfPi (A := A) σ s else 0)
    _ = ∑ s1, ∑ s2, (if Num s1 then pmfPi (A := A) (Function.update σ j τ) s1 else 0)
      * (if Denom s2 then pmfPi (A := A) σ s2 else 0) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro s1 _
        rw [Finset.mul_sum]
    _ = ∑ p : (∀ i, A i) × (∀ i, A i), W p := (Fintype.sum_prod_type W).symm
    _ = ∑ p : (∀ i, A i) × (∀ i, A i), W (e p) := (sum_univ_eq_sum_univ_of_involutive e he W).symm
    _ = ∑ p : (∀ i, A i) × (∀ i, A i), W_CD p := by
        apply Finset.sum_congr rfl; intro p _
        exact hW p
    _ = ∑ s1, ∑ s2, W_CD (s1, s2) := Fintype.sum_prod_type W_CD
    _ = (∑ s, if Num s then pmfPi (A := A) σ s else 0)
      * (∑ s, if Denom s then pmfPi (A := A) (Function.update σ j τ) s else 0) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro s1 _
        rw [Finset.mul_sum]

end ConditioningCoord

end PMFProduct

end GameTheory
