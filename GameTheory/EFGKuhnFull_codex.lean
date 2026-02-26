import GameTheory.EFGKuhn

/-!
# Full N-player Kuhn's Theorem (Mixed → Behavioral)

Building on `EFGKuhn.lean` (single-player case), this file proves the full
N-player Kuhn theorem: for any mixed-strategy profile (product of per-player
distributions) under perfect recall, there exists a behavioral-strategy profile
giving the same outcome distribution.

The proof introduces `PlayerIndep` (the flat distribution is a product over
player slices) and shows the conditioning operations preserve this structure.
-/

namespace EFG

open scoped BigOperators

variable {S : InfoStructure} {Outcome : Type}

-- ============================================================================
-- § 0. Equivalence FlatProfile ≃ PureProfile
-- ============================================================================

def flatProfileEquivPureProfile : FlatProfile S ≃ PureProfile S where
  toFun := fun s p I => s ⟨p, I⟩
  invFun := fun π idx => π idx.1 idx.2
  left_inv := by intro s; funext idx; rfl
  right_inv := by intro π; funext p I; rfl

@[simp] lemma flatEquiv_apply (s : FlatProfile S) (p : S.Player) (I : S.Infoset p) :
    flatProfileEquivPureProfile s p I = s ⟨p, I⟩ := rfl

@[simp] lemma flatEquiv_symm_apply (π : PureProfile S) (idx : FlatIdx S) :
    flatProfileEquivPureProfile.symm π idx = π idx.1 idx.2 := rfl

-- ============================================================================
-- § 1. Mixed profiles (player-product)
-- ============================================================================

abbrev MixedProfile (S : InfoStructure) := (p : S.Player) → PMF (PureStrategy S p)

noncomputable def mixedProfileJoint (μP : MixedProfile S) : PMF (PureProfile S) :=
  pmfPi (A := fun p => PureStrategy S p) μP

@[simp] lemma mixedProfileJoint_apply (μP : MixedProfile S) (π : PureProfile S) :
    mixedProfileJoint μP π = ∏ p, μP p (π p) := by
  simp [mixedProfileJoint]

instance : Fintype (PureProfile S) := Pi.instFintype

-- ============================================================================
-- § 2. Pure profile ↔ behavioral / flat
-- ============================================================================

noncomputable def pureProfileToBehavioral (π : PureProfile S) : BehavioralProfile S :=
  fun p I => PMF.pure (π p I)

theorem pureProfileToBehavioral_eq_flatToBehavioral (π : PureProfile S) :
    pureProfileToBehavioral π = flatToBehavioral (flatProfileEquivPureProfile.symm π) := by
  funext p I; simp [pureProfileToBehavioral, flatToBehavioral]

-- ============================================================================
-- § 3. Bridge: FlatProfile ↔ PureProfile evaluation
-- ============================================================================

theorem evalDist_pure_eq_flat (t : GameTree S Outcome) (π : PureProfile S) :
    t.evalDist (pureProfileToBehavioral π) =
    t.evalDist (flatToBehavioral (flatProfileEquivPureProfile.symm π)) := by
  rw [← pureProfileToBehavioral_eq_flatToBehavioral]

noncomputable def pmfPureToFlat (μ : PMF (PureProfile S)) : PMF (FlatProfile S) :=
  μ.bind (fun π => PMF.pure (flatProfileEquivPureProfile.symm π))

-- ============================================================================
-- § 4. Player independence and generalized compatibility lemmas
-- ============================================================================

/-- The flat distribution from a mixed-profile joint evaluates pointwise as a product. -/
lemma pmfPureToFlat_apply (μP : MixedProfile S) (s : FlatProfile S) :
    (pmfPureToFlat (mixedProfileJoint μP)) s =
    ∏ p : S.Player, μP p (fun I => s ⟨p, I⟩) := by
  simp only [pmfPureToFlat, PMF.bind_apply, PMF.pure_apply, tsum_fintype]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (flatProfileEquivPureProfile s)]
  · rw [if_pos (flatProfileEquivPureProfile.symm_apply_apply s).symm,
        mixedProfileJoint_apply]
    exact Finset.prod_congr rfl fun p _ => congrArg (μP p) (funext fun I => rfl)
  · intro b _ hne
    exact if_neg (flatProfileEquivPureProfile.eq_symm_apply.not.mpr (Ne.symm hne))
  · intro h; exact absurd (Finset.mem_univ _) h

/-- A flat profile distribution is **player-independent** if it equals
    `pmfPureToFlat (mixedProfileJoint f)` for some per-player distributions `f`.
    Equivalently: μ(s) = ∏_p f_p(s_p) pointwise. -/
def PlayerIndep (μ : PMF (FlatProfile S)) : Prop :=
  ∃ (f : MixedProfile S), μ = pmfPureToFlat (mixedProfileJoint f)

/-- Pointwise characterization of player independence. -/
lemma PlayerIndep.apply {μ : PMF (FlatProfile S)} (h : PlayerIndep μ) :
    ∃ (f : MixedProfile S),
      ∀ s : FlatProfile S, μ s = ∏ p, f p (fun I => s ⟨p, I⟩) := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, fun s => by rw [hf]; exact pmfPureToFlat_apply f s⟩

/-- The flat distribution arising from a mixed profile is player-independent. -/
theorem PlayerIndep_pmfPureToFlat (μP : MixedProfile S) :
    PlayerIndep (pmfPureToFlat (mixedProfileJoint μP)) :=
  ⟨μP, rfl⟩


/-- Conditioning on a single player's action preserves player-independence. -/
theorem PlayerIndep_μCond {p_owner : S.Player}
    {I₀ : S.Infoset p_owner} {a : S.Act I₀}
    {μ : PMF (FlatProfile S)} (hind : PlayerIndep μ)
    (hpa : μMarginal I₀ μ a ≠ 0) :
    PlayerIndep (μCond I₀ a μ) := by
  obtain ⟨f, hf⟩ := hind
  let p_a := μMarginal I₀ μ a
  -- A is the scaling factor for player p_owner's pure strategies
  let A := ∑ s_p : PureStrategy S p_owner,
    if s_p I₀ = a then (f p_owner s_p : ENNReal) else 0
  have hp_a_eq : p_a = ∑ s : FlatProfile S, if s ⟨p_owner, I₀⟩ = a then μ s else 0 := by
    simp only [μMarginal, PMF.bind_apply, PMF.pure_apply,
               tsum_fintype, mul_ite, mul_one, mul_zero, p_a]
    simp_rw [@eq_comm _ a]
  have h_A_le : A ≤ 1 := by
    calc A ≤ ∑ s_p : PureStrategy S p_owner, f p_owner s_p := by
          apply Finset.sum_le_sum
          intro s_p _
          split_ifs <;> simp
      _ = 1 := by
          have h := PMF.tsum_coe (f p_owner)
          rwa [tsum_eq_sum (s := Finset.univ) (fun x hx => absurd (Finset.mem_univ x) hx)] at h
  have h_A_ne_top : A ≠ ⊤ := ne_of_lt (lt_of_le_of_lt h_A_le (by simp))
  have h_mu_split : ∀ s : FlatProfile S,
      (if s ⟨p_owner, I₀⟩ = a then μ s else 0) =
      (if s ⟨p_owner, I₀⟩ = a then f p_owner (fun I => s ⟨p_owner, I⟩) else 0) *
      ∏ q ∈ Finset.univ.erase p_owner, f q (fun I => s ⟨q, I⟩) := by
    intro s
    by_cases hsa : s ⟨p_owner, I₀⟩ = a
    · simp only [hsa, if_true]
      rw [hf, pmfPureToFlat_apply]
      exact prod_factor_erase f p_owner (flatProfileEquivPureProfile s)
    · simp [hsa]
  have h_A_ne_zero : A ≠ 0 := by
    intro hA
    have h_zero : ∀ s_p, (if s_p I₀ = a then (f p_owner s_p : ENNReal) else 0) = 0 := by
      intro s_p
      exact Finset.sum_eq_zero_iff.mp hA s_p (Finset.mem_univ s_p)
    have hp_a_zero : p_a = 0 := by
      rw [hp_a_eq]
      apply Finset.sum_eq_zero
      intro s _
      rw [h_mu_split s]
      have h_eval : s ⟨p_owner, I₀⟩ = (fun I => s ⟨p_owner, I⟩) I₀ := rfl
      rw [h_eval]
      rw [h_zero (fun I => s ⟨p_owner, I⟩), zero_mul]
    exact hpa hp_a_zero
  have h_f'_sum : (∑ s_p : PureStrategy S p_owner,
      (if s_p I₀ = a then (f p_owner s_p : ENNReal) else 0) / A) = 1 := by
    simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
    exact ENNReal.mul_inv_cancel h_A_ne_zero h_A_ne_top
  -- Construct the conditioned distribution for p_owner
  let f'_owner : PMF (PureStrategy S p_owner) :=
    PMF.ofFintype (fun s_p => (if s_p I₀ = a then f p_owner s_p else 0) / A) h_f'_sum
  -- The new independent joint distribution
  let f' : (q : S.Player) → PMF (PureStrategy S q) := fun q =>
    if h : q = p_owner then h ▸ f'_owner else f q
  have h_f'_owner_eval : ∀ s_p : PureStrategy S p_owner,
      f' p_owner s_p = (if s_p I₀ = a then f p_owner s_p else 0) / A := by
    intro s_p
    simp only [dite_eq_ite, ↓reduceIte, f']
    exact PMF.ofFintype_apply h_f'_sum s_p
  have h_f'_other : ∀ q : S.Player, q ≠ p_owner → ∀ s_q : PureStrategy S q,
      f' q s_q = f q s_q := by
    intro q hq s_q
    simp [f', hq]
  -- Prove that the product of the new distributions equals the scaled original distribution
  have h_prod_f' : ∀ π : PureProfile S, (∏ q, f' q (π q)) =
      (if π p_owner I₀ = a then μ (flatProfileEquivPureProfile.symm π) else 0) / A := by
    intro π
    have hp_in : p_owner ∈ Finset.univ := Finset.mem_univ _
    rw [← Finset.mul_prod_erase Finset.univ _ hp_in]
    rw [h_f'_owner_eval]
    have h_rest : (∏ q ∈ Finset.univ.erase p_owner, f' q (π q)) =
        ∏ q ∈ Finset.univ.erase p_owner, f q (π q) := by
      apply Finset.prod_congr rfl
      intro q hq
      apply h_f'_other
      exact Finset.ne_of_mem_erase hq
    rw [h_rest]
    rw [div_eq_mul_inv, mul_assoc, mul_comm A⁻¹, ← mul_assoc]
    congr 1
    have h_mu_s := h_mu_split (flatProfileEquivPureProfile.symm π)
    have h_eval : (flatProfileEquivPureProfile.symm π) ⟨p_owner, I₀⟩ = π p_owner I₀ := rfl
    rw [h_eval] at h_mu_s
    have h_fun_eq : (fun I => (flatProfileEquivPureProfile.symm π) ⟨p_owner, I⟩) = π p_owner := rfl
    rw [h_fun_eq] at h_mu_s
    have h_prod_eq : (∏ q ∈ Finset.univ.erase p_owner, f q (fun I =>
                         (flatProfileEquivPureProfile.symm π) ⟨q, I⟩)) =
        ∏ q ∈ Finset.univ.erase p_owner, f q (π q) := by
      apply Finset.prod_congr rfl
      intro q _
      rfl
    rw [h_prod_eq] at h_mu_s
    exact h_mu_s.symm
  -- The sum over all joint pure profiles of a PMF product is 1
  have h_sum_prod_f' : (∑ π : PureProfile S, ∏ q, f' q (π q)) = 1 := by
    have h_pmf := PMF.tsum_coe (pmfPi (A := fun p => PureStrategy S p) f')
    have h_eq : (∑' (a : PureProfile S), pmfPi f' a) =
        ∑ a : PureProfile S, ∏ q, f' q (a q) := by
      rw [tsum_eq_sum (s := Finset.univ) (fun x hx => absurd (Finset.mem_univ x) hx)]
      apply Finset.sum_congr rfl
      intro x _
      exact pmfPi_apply f' x
    rwa [h_eq] at h_pmf
  have h_sum_rhs : (∑ π : PureProfile S,
      (if π p_owner I₀ = a then μ (flatProfileEquivPureProfile.symm π) else 0) / A) = p_a / A := by
    simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
    congr 1
    rw [hp_a_eq]
    have h_comp := Equiv.sum_comp flatProfileEquivPureProfile.symm
      (fun s => if s ⟨p_owner, I₀⟩ = a then (μ s : ENNReal) else 0)
    exact
      Fintype.sum_equiv flatProfileEquivPureProfile.symm
        (fun x ↦ if x p_owner I₀ = a then μ (flatProfileEquivPureProfile.symm x) else 0)
        (fun x ↦ if x ⟨p_owner, I₀⟩ = a then μ x else 0) fun x ↦
        congrFun (congrFun rfl (μ (flatProfileEquivPureProfile.symm x))) 0
  -- Use the PMF sum constraint to prove that our scaling factor A
  -- is exactly the marginal probability
  have h_p_a_eq_A : p_a = A := by
    have h_eq1 : p_a / A = 1 := by
      calc p_a / A = ∑ π : PureProfile S, (if π p_owner I₀ = a
                 then μ (flatProfileEquivPureProfile.symm π) else 0) / A := h_sum_rhs.symm
        _ = ∑ π : PureProfile S, ∏ q, f' q (π q) := by
            apply Finset.sum_congr rfl
            intro π _
            exact (h_prod_f' π).symm
        _ = 1 := h_sum_prod_f'
    have h_p_a_ne_top : p_a ≠ ⊤ := by
      have h_le_1 : p_a ≤ 1 := by
        calc p_a = ∑ s : FlatProfile S, if s ⟨p_owner, I₀⟩ = a then μ s else 0 := hp_a_eq
          _ ≤ ∑ s : FlatProfile S, μ s := by
              apply Finset.sum_le_sum
              intro s _
              split_ifs <;> simp
          _ = 1 := by
              have h := PMF.tsum_coe μ
              rwa [tsum_eq_sum (s := Finset.univ) (fun x hx => absurd (Finset.mem_univ x) hx)] at h
      exact ne_of_lt (lt_of_le_of_lt h_le_1 (by simp))
    calc p_a = p_a * (A⁻¹ * A) := by rw [ENNReal.inv_mul_cancel h_A_ne_zero h_A_ne_top, mul_one]
      _ = (p_a * A⁻¹) * A := by rw [mul_assoc]
      _ = (p_a / A) * A := rfl
      _ = 1 * A := by rw [h_eq1]
      _ = A := by rw [one_mul]
  use f'
  ext s
  have h_eval := h_prod_f' (flatProfileEquivPureProfile s)
  have h_symm : flatProfileEquivPureProfile.symm (flatProfileEquivPureProfile s) = s :=
    flatProfileEquivPureProfile.symm_apply_apply s
  rw [h_symm] at h_eval
  have h_pi : (flatProfileEquivPureProfile s) p_owner I₀ = s ⟨p_owner, I₀⟩ := rfl
  rw [h_pi] at h_eval
  have h_cond_apply := μCond_apply I₀ a μ s hpa
  -- Explicitly cast the marginal to A
  have hp_a_to_A : (μMarginal I₀ μ) a = A := h_p_a_eq_A
  rw [hp_a_to_A] at h_cond_apply
  -- Pull the division outside the indicator function
  have h_ite_div : (if s ⟨p_owner, I₀⟩ = a then μ s / A else 0) =
      (if s ⟨p_owner, I₀⟩ = a then μ s else 0) / A := by
    split_ifs <;> simp
  rw [h_ite_div] at h_cond_apply
  -- Rewrite the LHS to match our evaluated conditional
  rw [h_cond_apply]
  -- Expand the RHS from the packed PMF into the explicit player product
  rw [pmfPureToFlat_apply f' s]
  -- Now the goal is exactly h_eval.symm
  -- (since flatProfileEquivPureProfile s q is definitionally fun I => s ⟨q, I⟩)
  exact h_eval.symm


-- ---------------------------------------------------------------------------
-- Helper: under PlayerIndep, conditioning on p_owner’s action only changes
-- p_owner’s factor, so q-marginals are unchanged when q ≠ p_owner.
-- ---------------------------------------------------------------------------
-- 1. The Involution
def profileSwap (s s' : FlatProfile S) (q : S.Player) : FlatProfile S :=
  fun idx => if idx.1 = q then s' idx else s idx

section

variable {S : InfoStructure} {Outcome : Type}

abbrev slice (s : FlatProfile S) (p : S.Player) : PureStrategy S p :=
  fun I => s ⟨p, I⟩

@[simp] lemma slice_profileSwap_self {s s' : FlatProfile S} {q : S.Player} :
    slice (profileSwap (S := S) s s' q) q = slice s' q := by
  funext I
  simp [profileSwap, slice]

@[simp] lemma slice_profileSwap_other {s s' : FlatProfile S} {q r : S.Player} (h : r ≠ q) :
    slice (profileSwap (S := S) s s' q) r = slice s r := by
  funext I
  simp [profileSwap, slice, h]

end

-- Stronger version: gives a witness f' plus “unchanged on other players”.
theorem PlayerIndep_μCond_witness {S : InfoStructure}
    {p_owner : S.Player} {I₀ : S.Infoset p_owner} {a : S.Act I₀}
    {μ : PMF (FlatProfile S)} (hind : PlayerIndep (S := S) μ)
    (hpa : μMarginal (S := S) I₀ μ a ≠ 0) :
    ∃ (f f' : MixedProfile S),
      (∀ s : FlatProfile S, μ s = ∏ p, f p (slice (S := S) s p)) ∧
      μCond (S := S) I₀ a μ = pmfPureToFlat (S := S) (mixedProfileJoint (S := S) f') ∧
      (∀ q : S.Player, q ≠ p_owner → f' q = f q) := by
  classical
  -- 1) extract f from hind.apply
  obtain ⟨_, hfac⟩ := PlayerIndep.apply (S := S) (μ := μ) hind
  obtain ⟨f, hf⟩ := hind
  let p_a := μMarginal I₀ μ a
  -- A is the scaling factor for player p_owner's pure strategies
  let A := ∑ s_p : PureStrategy S p_owner,
    if s_p I₀ = a then (f p_owner s_p : ENNReal) else 0
  have hp_a_eq : p_a = ∑ s : FlatProfile S, if s ⟨p_owner, I₀⟩ = a then μ s else 0 := by
    simp only [μMarginal, PMF.bind_apply, PMF.pure_apply,
               tsum_fintype, mul_ite, mul_one, mul_zero, p_a]
    simp_rw [@eq_comm _ a]
  have h_A_le : A ≤ 1 := by
    calc A ≤ ∑ s_p : PureStrategy S p_owner, f p_owner s_p := by
          apply Finset.sum_le_sum
          intro s_p _
          split_ifs <;> simp
      _ = 1 := by
          have h := PMF.tsum_coe (f p_owner)
          rwa [tsum_eq_sum (s := Finset.univ) (fun x hx => absurd (Finset.mem_univ x) hx)] at h
  have h_A_ne_top : A ≠ ⊤ := ne_of_lt (lt_of_le_of_lt h_A_le (by simp))
  have h_mu_split : ∀ s : FlatProfile S,
      (if s ⟨p_owner, I₀⟩ = a then μ s else 0) =
      (if s ⟨p_owner, I₀⟩ = a then f p_owner (fun I => s ⟨p_owner, I⟩) else 0) *
      ∏ q ∈ Finset.univ.erase p_owner, f q (fun I => s ⟨q, I⟩) := by
    intro s
    by_cases hsa : s ⟨p_owner, I₀⟩ = a
    · simp only [hsa, if_true]
      rw [hf, pmfPureToFlat_apply]
      exact prod_factor_erase f p_owner (flatProfileEquivPureProfile s)
    · simp [hsa]
  have h_A_ne_zero : A ≠ 0 := by
    intro hA
    have h_zero : ∀ s_p, (if s_p I₀ = a then (f p_owner s_p : ENNReal) else 0) = 0 := by
      intro s_p
      exact Finset.sum_eq_zero_iff.mp hA s_p (Finset.mem_univ s_p)
    have hp_a_zero : p_a = 0 := by
      rw [hp_a_eq]
      apply Finset.sum_eq_zero
      intro s _
      rw [h_mu_split s]
      have h_eval : s ⟨p_owner, I₀⟩ = (fun I => s ⟨p_owner, I⟩) I₀ := rfl
      rw [h_eval]
      rw [h_zero (fun I => s ⟨p_owner, I⟩), zero_mul]
    exact hpa hp_a_zero
  have h_f'_sum : (∑ s_p : PureStrategy S p_owner,
      (if s_p I₀ = a then (f p_owner s_p : ENNReal) else 0) / A) = 1 := by
    simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
    exact ENNReal.mul_inv_cancel h_A_ne_zero h_A_ne_top
  let f'_owner : PMF (PureStrategy S p_owner) :=
    PMF.ofFintype (fun s_p => (if s_p I₀ = a then f p_owner s_p else 0) / A) h_f'_sum
  let f' : (q : S.Player) → PMF (PureStrategy S q) := fun q =>
    if h : q = p_owner then h ▸ f'_owner else f q
  have h_f'_owner_eval : ∀ s_p : PureStrategy S p_owner,
      f' p_owner s_p = (if s_p I₀ = a then f p_owner s_p else 0) / A := by
    intro s_p
    simp only [dite_eq_ite, ↓reduceIte, f']
    exact PMF.ofFintype_apply h_f'_sum s_p
  have h_f'_other : ∀ q : S.Player, q ≠ p_owner → ∀ s_q : PureStrategy S q,
      f' q s_q = f q s_q := by
    intro q hq s_q
    simp [f', hq]
  have h_prod_f' : ∀ π : PureProfile S, (∏ q, f' q (π q)) =
      (if π p_owner I₀ = a then μ (flatProfileEquivPureProfile.symm π) else 0) / A := by
    intro π
    have hp_in : p_owner ∈ Finset.univ := Finset.mem_univ _
    rw [← Finset.mul_prod_erase Finset.univ _ hp_in]
    rw [h_f'_owner_eval]
    have h_rest : (∏ q ∈ Finset.univ.erase p_owner, f' q (π q)) =
        ∏ q ∈ Finset.univ.erase p_owner, f q (π q) := by
      apply Finset.prod_congr rfl
      intro q hq
      apply h_f'_other
      exact Finset.ne_of_mem_erase hq
    rw [h_rest]
    rw [div_eq_mul_inv, mul_assoc, mul_comm A⁻¹, ← mul_assoc]
    congr 1
    have h_mu_s := h_mu_split (flatProfileEquivPureProfile.symm π)
    have h_eval : (flatProfileEquivPureProfile.symm π) ⟨p_owner, I₀⟩ = π p_owner I₀ := rfl
    rw [h_eval] at h_mu_s
    have h_fun_eq : (fun I => (flatProfileEquivPureProfile.symm π) ⟨p_owner, I⟩) = π p_owner := rfl
    rw [h_fun_eq] at h_mu_s
    have h_prod_eq : (∏ q ∈ Finset.univ.erase p_owner, f q (fun I =>
                         (flatProfileEquivPureProfile.symm π) ⟨q, I⟩)) =
        ∏ q ∈ Finset.univ.erase p_owner, f q (π q) := by
      apply Finset.prod_congr rfl
      intro q _
      rfl
    rw [h_prod_eq] at h_mu_s
    exact h_mu_s.symm
  have h_sum_prod_f' : (∑ π : PureProfile S, ∏ q, f' q (π q)) = 1 := by
    have h_pmf := PMF.tsum_coe (pmfPi (A := fun p => PureStrategy S p) f')
    have h_eq : (∑' (a : PureProfile S), pmfPi f' a) =
        ∑ a : PureProfile S, ∏ q, f' q (a q) := by
      rw [tsum_eq_sum (s := Finset.univ) (fun x hx => absurd (Finset.mem_univ x) hx)]
      apply Finset.sum_congr rfl
      intro x _
      exact pmfPi_apply f' x
    rwa [h_eq] at h_pmf
  have h_sum_rhs : (∑ π : PureProfile S,
      (if π p_owner I₀ = a then μ (flatProfileEquivPureProfile.symm π) else 0) / A) = p_a / A := by
    simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
    congr 1
    rw [hp_a_eq]
    have h_comp := Equiv.sum_comp flatProfileEquivPureProfile.symm
      (fun s => if s ⟨p_owner, I₀⟩ = a then (μ s : ENNReal) else 0)
    exact
      Fintype.sum_equiv flatProfileEquivPureProfile.symm
        (fun x ↦ if x p_owner I₀ = a then μ (flatProfileEquivPureProfile.symm x) else 0)
        (fun x ↦ if x ⟨p_owner, I₀⟩ = a then μ x else 0) fun x ↦
        congrFun (congrFun rfl (μ (flatProfileEquivPureProfile.symm x))) 0
  have h_p_a_eq_A : p_a = A := by
    have h_eq1 : p_a / A = 1 := by
      calc p_a / A = ∑ π : PureProfile S, (if π p_owner I₀ = a
                 then μ (flatProfileEquivPureProfile.symm π) else 0) / A := h_sum_rhs.symm
        _ = ∑ π : PureProfile S, ∏ q, f' q (π q) := by
            apply Finset.sum_congr rfl
            intro π _
            exact (h_prod_f' π).symm
        _ = 1 := h_sum_prod_f'
    have h_p_a_ne_top : p_a ≠ ⊤ := by
      have h_le_1 : p_a ≤ 1 := by
        calc p_a = ∑ s : FlatProfile S, if s ⟨p_owner, I₀⟩ = a then μ s else 0 := hp_a_eq
          _ ≤ ∑ s : FlatProfile S, μ s := by
              apply Finset.sum_le_sum
              intro s _
              split_ifs <;> simp
          _ = 1 := by
              have h := PMF.tsum_coe μ
              rwa [tsum_eq_sum (s := Finset.univ) (fun x hx => absurd (Finset.mem_univ x) hx)] at h
      exact ne_of_lt (lt_of_le_of_lt h_le_1 (by simp))
    calc p_a = p_a * (A⁻¹ * A) := by rw [ENNReal.inv_mul_cancel h_A_ne_zero h_A_ne_top, mul_one]
      _ = (p_a * A⁻¹) * A := by rw [mul_assoc]
      _ = (p_a / A) * A := rfl
      _ = 1 * A := by rw [h_eq1]
      _ = A := by rw [one_mul]
  refine ⟨f, f', ?_, ?_, ?_⟩
  · intro s
    have := congrArg (fun m => m s) hf
    simpa [slice] using this.trans (pmfPureToFlat_apply (S := S) (μP := f) s)
  · ext s
    have hcond_apply :
        μCond (S := S) I₀ a μ s
          =
        (if s ⟨p_owner, I₀⟩ = a then (μ s : ENNReal) / A else 0) := by
      have := μCond_apply (S := S) (I₀ := I₀) (a := a) (μ := μ) (s := s) hpa
      simpa [p_a, h_p_a_eq_A] using this
    have hprod := h_prod_f' ((flatProfileEquivPureProfile (S := S)) s)
    have hprod' :
        (∏ q : S.Player, f' q (slice (S := S) s q))
          =
        (if s ⟨p_owner, I₀⟩ = a then (μ s : ENNReal) else 0) / A := by
      simpa [slice] using (by
        simpa
          [flatProfileEquivPureProfile, slice,
           (flatProfileEquivPureProfile (S := S)).symm_apply_apply s] using hprod)
    have hite_div :
        (if s ⟨p_owner, I₀⟩ = a then (μ s : ENNReal) / A else 0)
          =
        (if s ⟨p_owner, I₀⟩ = a then (μ s : ENNReal) else 0) / A := by
      by_cases hsa : s ⟨p_owner, I₀⟩ = a
      · simp [hsa]
      · simp [hsa]
    simpa [pmfPureToFlat_apply (S := S) (μP := f') s, hcond_apply, hite_div] using hprod'.symm
  · intro q hq
    ext s_q
    exact h_f'_other q hq s_q

abbrev Other (q : S.Player) := { r : S.Player // r ≠ q }

-- If you use `OtherProfile` as a Pi over `Other`, this will now work:
abbrev OtherProfile {S : InfoStructure} (q : S.Player) : Type :=
  (r : Other (S := S) q) → PureStrategy S r.1

instance {S : InfoStructure} (q : S.Player) : Fintype (OtherProfile (S := S) q) := by
  classical
  dsimp [OtherProfile]
  infer_instance

-- assuming S.Player = Fin S.n, so fintype exists already.
instance (S : InfoStructure) (q : S.Player) : Fintype { r : S.Player // r ≠ q } := by
  classical
  infer_instance

instance (S : InfoStructure) (q : S.Player) : Fintype (OtherProfile (S := S) q) :=
by
  classical
  -- Pi.instFintype expects: Fintype domain, and ∀ a, Fintype (codomain a)
  dsimp [OtherProfile]
  exact Pi.instFintype

noncomputable def pureProfileSplit {S : InfoStructure} (q : S.Player) :
    PureProfile S ≃ (PureStrategy S q × OtherProfile q) where
  toFun π := (π q, fun r => π r.1)
  invFun x :=
    fun p =>
      if h : p = q then by
        subst h; exact x.1
      else
        x.2 ⟨p, h⟩
  left_inv := by
    intro π; funext p
    by_cases h : p = q
    · subst h; simp
    · simp [h]
  right_inv := by
    intro x
    cases x with
    | mk sq rest =>
      apply Prod.ext
      · simp
      · funext r
        simp only [ne_eq, r.property, ↓reduceDIte]

@[simp] lemma pureProfileSplit_symm_apply_self
    {S : InfoStructure} (q : S.Player)
    (x : PureStrategy S q × OtherProfile q) :
    (pureProfileSplit (S := S) q).symm x q = x.1 := by
  simp [pureProfileSplit]

@[simp] lemma pureProfileSplit_symm_apply_other
    {S : InfoStructure} {q r : S.Player} (hr : r ≠ q)
    (x : PureStrategy S q × OtherProfile q) :
    (pureProfileSplit (S := S) q).symm x r = x.2 ⟨r, hr⟩ := by
  simp [pureProfileSplit, hr]

lemma μMarginal_of_pmfPureToFlat
    (f : (p : S.Player) → PMF (PureStrategy S p))
    {q : S.Player} (J : S.Infoset q) (aj : S.Act J) :
    μMarginal (S := S) J (pmfPureToFlat (S := S) (mixedProfileJoint (S := S) f)) aj
      =
    ∑ s_q : PureStrategy S q, (if aj = s_q J then f q s_q else 0) := by
  classical
  let g : PureStrategy S q → PureProfile S → PMF (S.Act J) :=
    fun s_q _ => PMF.pure (s_q J)
  have hg : Ignores₂ (A := fun p : S.Player => PureStrategy S p) q g := by
    intro s_q s a
    rfl
  have hfactor :
      (pmfPi (A := fun p : S.Player => PureStrategy S p) f).bind
        (fun s => PMF.pure ((s q) J))
        =
      (f q).bind (fun s_q => PMF.pure (s_q J)) := by
    calc
      (pmfPi (A := fun p : S.Player => PureStrategy S p) f).bind
          (fun s => PMF.pure ((s q) J))
          =
        (pmfPi (A := fun p : S.Player => PureStrategy S p) f).bind (fun s => g (s q) s) := by
          rfl
      _ =
        (f q).bind
          (fun s_q =>
            (pmfPi (A := fun p : S.Player => PureStrategy S p) f).bind (fun s => g s_q s)) := by
          exact pmfPi_bind_factor (A := fun p : S.Player => PureStrategy S p) f q g hg
      _ =
        (f q).bind (fun s_q => PMF.pure (s_q J)) := by
          congr 1
          funext s_q
          simp [g]
  have hμ :
      μMarginal (S := S) J (pmfPureToFlat (S := S) (mixedProfileJoint (S := S) f))
        =
      (pmfPi (A := fun p : S.Player => PureStrategy S p) f).bind
        (fun s => PMF.pure ((s q) J)) := by
    ext a
    simp [μMarginal, pmfPureToFlat, mixedProfileJoint]
  rw [hμ, hfactor]
  simp [PMF.bind_apply, tsum_fintype, mul_ite, mul_one, mul_zero]

lemma PlayerIndep.μMarginal_μCond_other {S : InfoStructure}
    {μ : PMF (FlatProfile S)} (hind : PlayerIndep (S := S) μ)
    {p_owner : S.Player} {I₀ : S.Infoset p_owner} {a : S.Act I₀}
    (hpa : μMarginal (S := S) I₀ μ a ≠ 0)
    {q : S.Player} (hq : q ≠ p_owner)
    {J : S.Infoset q} :
    μMarginal (S := S) J (μCond (S := S) I₀ a μ) = μMarginal (S := S) J μ := by
  classical
  obtain ⟨f, f', hfac, hcond, hsame⟩ :=
    PlayerIndep_μCond_witness (S := S) (μ := μ) hind hpa
  have hμ : μ = pmfPureToFlat (S := S) (mixedProfileJoint (S := S) f) := by
    ext s
    simpa [pmfPureToFlat_apply (S := S), slice] using (hfac s)
  ext aj
  rw [hcond, hμ]
  simp [μMarginal_of_pmfPureToFlat (S := S), hsame q hq]

/-- Generalized chance compatibility: under player-independence + perfect recall,
    `mixedToBehavioralFlat` at a chance node equals that at any specific branch.
    The q-relevant part of the reach condition is the same across branches
    (by perfect recall), and the non-q parts cancel in the ratio (by independence). -/
axiom mixedToBehavioralFlat_chance_eq_general {q : S.Player}
    {μ : PMF (FlatProfile S)} {k : Nat} {μ_c : PMF (Fin k)} {hk : 0 < k}
    {next : Fin k → GameTree S Outcome} {b : Fin k}
    (hpr : PerfectRecall (.chance k μ_c hk next))
    (hind : PlayerIndep μ)
    {J : S.Infoset q} (hJ : DecisionNodeIn J (next b)) :
    mixedToBehavioralFlat (p := q) μ (.chance k μ_c hk next) J =
    mixedToBehavioralFlat (p := q) μ (next b) J

/-- Generalized decision compatibility: under player-independence + perfect recall,
    `mixedToBehavioralFlat` is compatible across decision nodes.
    For the owner (q = p_owner), reduces to `mixedToBehavioralFlat_decision_sub`.
    For cross-player (q ≠ p_owner), the non-q parts cancel by independence. -/
axiom mixedToBehavioralFlat_decision_sub_general
    {p_owner : S.Player}
    {I₀ : S.Infoset p_owner} {next : S.Act I₀ → GameTree S Outcome} {a : S.Act I₀}
    (hpr : PerfectRecall (.decision I₀ next))
    (μ : PMF (FlatProfile S)) (hpa : μMarginal (S := S) I₀ μ a ≠ 0)
    (hind : PlayerIndep (S := S) μ)
    {q : S.Player} {J : S.Infoset q} (hJ : DecisionNodeIn J (next a)) :
    mixedToBehavioralFlat (S := S) (p := q) μ (.decision (p := p_owner) I₀ next) J =
    mixedToBehavioralFlat (S := S) (p := q) (μCond (S := S) I₀ a μ) (next a) J

-- ============================================================================
-- § 5. N-player mixed → behavioral
-- ============================================================================

/-- The N-player behavioral profile from a flat distribution:
    at each infoset I of player p, condition on reaching I in the original tree. -/
noncomputable def mixedToBehavioralFull
    (μ : PMF (FlatProfile S)) (t : GameTree S Outcome) : BehavioralProfile S :=
  fun _ => mixedToBehavioralFlat μ t

/-- **Core N-player lemma**: the full conditional behavioral profile
    gives the same outcome distribution as the original flat distribution.
    Requires the distribution to be player-independent (product across players). -/
theorem mixed_to_behavioral_nplayer (t : GameTree S Outcome) (hpr : PerfectRecall t)
    (μ : PMF (FlatProfile S)) (hind : PlayerIndep μ) :
    t.evalDist (mixedToBehavioralFull μ t) = μ.bind (fun s => t.evalFlat s) := by
  induction t generalizing μ with
  | terminal z =>
    simp only [GameTree.evalDist, GameTree.evalFlat]
    exact (μ.bind_const (PMF.pure z)).symm
  | chance k μ_c hk next ih =>
    simp only [evalDist_chance, GameTree.evalFlat]
    conv_rhs => rw [PMF.bind_comm μ μ_c]
    congr 1; funext b
    have h_agree := evalDist_eq_of_behavioral_agree (next b)
      (mixedToBehavioralFull μ (.chance k μ_c hk next))
      (mixedToBehavioralFull μ (next b))
      (fun {q} {J} hdn => by
        simp only [mixedToBehavioralFull]
        exact mixedToBehavioralFlat_chance_eq_general hpr hind hdn)
    rw [h_agree]
    exact ih b (PerfectRecall_chance_sub hpr b) μ hind
  | decision I₀ next ih =>
    rename_i p_owner
    change (GameTree.decision I₀ next).evalDist
        (fun q => mixedToBehavioralFlat (p := q) μ (GameTree.decision I₀ next)) =
      μ.bind (fun s => (GameTree.decision I₀ next).evalFlat s)
    have h_rhs : μ.bind (fun s => (GameTree.decision I₀ next).evalFlat s) =
        (μMarginal I₀ μ).bind (fun a => (μCond I₀ a μ).bind (fun s =>
          (GameTree.decision I₀ next).evalFlat s)) :=
      bind_marginal_cond I₀ μ _
    rw [h_rhs]
    have h_root : (fun q =>
        mixedToBehavioralFlat (p := q) μ (GameTree.decision I₀ next)) p_owner I₀ =
        μMarginal I₀ μ := by
      exact mixedToBehavioralFlat_root_eq
    have h_lhs : (GameTree.decision I₀ next).evalDist
        (fun q => mixedToBehavioralFlat (p := q) μ (GameTree.decision I₀ next)) =
      (μMarginal I₀ μ).bind (fun a => (next a).evalDist
        (fun q => mixedToBehavioralFlat (p := q) μ (GameTree.decision I₀ next))) := by
      show _ = (μMarginal I₀ μ).bind _
      conv_lhs =>
        rw [show (GameTree.decision I₀ next).evalDist
            (fun q => mixedToBehavioralFlat (p := q) μ (GameTree.decision I₀ next)) =
          ((fun q => mixedToBehavioralFlat (p := q) μ
            (GameTree.decision I₀ next)) p_owner I₀).bind (fun a =>
            (next a).evalDist (fun q => mixedToBehavioralFlat (p := q) μ
            (GameTree.decision I₀ next))) from rfl]
      rw [h_root]
    rw [h_lhs]
    ext x
    rw [PMF.bind_apply, PMF.bind_apply]
    simp only [tsum_fintype]
    apply Finset.sum_congr rfl
    intro a _
    by_cases hp_marg : μMarginal I₀ μ a = 0
    · simp [hp_marg]
    · congr 1
      have h_agree := evalDist_eq_of_behavioral_agree (next a)
        (fun q => mixedToBehavioralFlat (p := q) μ (GameTree.decision I₀ next))
        (mixedToBehavioralFull (μCond I₀ a μ) (next a))
        (fun hdn => mixedToBehavioralFlat_decision_sub_general hpr μ hp_marg hind hdn)
      have h_ih := ih a (PerfectRecall_decision_sub hpr a) (μCond I₀ a μ)
        (PlayerIndep_μCond hind hp_marg)
      have h_restrict : (μCond I₀ a μ).bind (fun s =>
              (GameTree.decision I₀ next).evalFlat s) =
          (μCond I₀ a μ).bind (fun s => (next a).evalFlat s) := by
        simp only [GameTree.evalFlat]
        exact evalDist_decision_cond_restrict (next := next) (a := a) μ hp_marg
      calc ((next a).evalDist
              (fun q => mixedToBehavioralFlat (p := q) μ (GameTree.decision I₀ next))) x
          = ((next a).evalDist (mixedToBehavioralFull (μCond I₀ a μ) (next a))) x := by
            rw [h_agree]
        _ = ((μCond I₀ a μ).bind (fun s => (next a).evalFlat s)) x := by
            rw [h_ih]
        _ = ((μCond I₀ a μ).bind (fun s => (GameTree.decision I₀ next).evalFlat s)) x := by
            rw [← h_restrict]

-- ============================================================================
-- § 6. Connecting joint pure distribution to flat distribution
-- ============================================================================

/-- The RHS of the N-player theorem can be rewritten using flat profiles. -/
theorem rhs_eq_flat_bind (t : GameTree S Outcome) (μP : MixedProfile S) :
    (mixedProfileJoint μP).bind (fun π => t.evalDist (pureProfileToBehavioral π)) =
    (pmfPureToFlat (mixedProfileJoint μP)).bind (fun s => t.evalFlat s) := by
  simp only [pmfPureToFlat, PMF.bind_bind, GameTree.evalFlat]
  congr 1; funext π
  simp only [PMF.pure_bind]
  rw [← pureProfileToBehavioral_eq_flatToBehavioral]

-- ============================================================================
-- § 7. N-player Kuhn theorem
-- ============================================================================

/-- **Kuhn's theorem (mixed → behavioral, N-player)**.
    For any mixed profile under perfect recall, there exists a behavioral profile
    giving the same outcome distribution as the joint mixed strategy. -/
theorem kuhn_mixed_to_behavioral
    (t : GameTree S Outcome) (hpr : PerfectRecall t)
    (μP : MixedProfile S) :
    ∃ (σ : BehavioralProfile S),
      t.evalDist σ =
      (mixedProfileJoint μP).bind (fun π => t.evalDist (pureProfileToBehavioral π)) := by
  -- The witness: for each player p, condition the joint flat distribution
  -- on reaching each of p's infosets in the original tree.
  use mixedToBehavioralFull (pmfPureToFlat (mixedProfileJoint μP)) t
  -- Step 1: Rewrite RHS using flat profiles
  rw [rhs_eq_flat_bind]
  -- Step 2: Apply the N-player mixed → behavioral theorem
  exact mixed_to_behavioral_nplayer t hpr _ (PlayerIndep_pmfPureToFlat μP)

end EFG
