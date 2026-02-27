import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Probability.ProbabilityMassFunction.Constructions

import GameTheory.EFG
import GameTheory.PMFProduct

namespace EFG

open scoped BigOperators

variable {S : InfoStructure} {Outcome : Type}


abbrev FlatIdx (S : InfoStructure) := Sigma fun p : S.Player => S.Infoset p
abbrev FlatProfile (S : InfoStructure) := (idx : FlatIdx S) -> S.Act idx.2

instance : Fintype (FlatIdx S) := Sigma.instFintype
instance : DecidableEq (FlatIdx S) := Sigma.instDecidableEqSigma
instance : Fintype (FlatProfile S) := Pi.instFintype
instance (p : S.Player) : Fintype (PureStrategy S p) := Pi.instFintype

abbrev MixedProfile (S : InfoStructure) := (p : S.Player) -> PMF (PureStrategy S p)

noncomputable def mixedProfileJoint (muP : MixedProfile S) : PMF (PureProfile S) :=
  pmfPi (A := fun p => PureStrategy S p) muP

def flatProfileEquivPureProfile : Equiv (FlatProfile S) (PureProfile S) where
  toFun := fun s p I => s ⟨p, I⟩
  invFun := fun pi idx => pi idx.1 idx.2
  left_inv := by intro s; funext idx; cases idx; rfl
  right_inv := by intro pi; funext p I; rfl

noncomputable def pmfPureToFlat (mu : PMF (PureProfile S)) : PMF (FlatProfile S) :=
  mu.bind (fun pi => PMF.pure (flatProfileEquivPureProfile.symm pi))

noncomputable def pureProfileToBehavioral (pi : PureProfile S) : BehavioralProfile S :=
  fun p I => PMF.pure (pi p I)

noncomputable def flatToBehavioral (s : FlatProfile S) : BehavioralProfile S :=
  fun p I => PMF.pure (s ⟨p, I⟩)

noncomputable def GameTree.evalFlat (t : GameTree S Outcome) (s : FlatProfile S) : PMF Outcome :=
  t.evalDist (flatToBehavioral s)

noncomputable def muMarginal {p : S.Player} (I : S.Infoset p)
    (mu : PMF (FlatProfile S)) : PMF (S.Act I) :=
  mu.bind (fun s => PMF.pure (s ⟨p, I⟩))

noncomputable def muCond {p : S.Player} (I : S.Infoset p) (a : S.Act I)
    (mu : PMF (FlatProfile S)) (hpa : muMarginal (S := S) I mu a ≠ 0) : PMF (FlatProfile S) :=
  PMF.ofFintype
    (fun s => if s ⟨p, I⟩ = a then mu s / (muMarginal (S := S) I mu a) else 0)
    (by
      rw [show (∑ s, if s ⟨p, I⟩ = a then mu s / muMarginal (S := S) I mu a else (0)) =
          (∑ s, (if s ⟨p, I⟩ = a then (mu s) else 0)
            * (muMarginal (S := S) I mu a)⁻¹) from
        Finset.sum_congr rfl (fun s _ => by split_ifs <;> simp [div_eq_mul_inv]),
        ← Finset.sum_mul]
      have hsum : (∑ s : FlatProfile S, if s ⟨p, I⟩ = a then (mu s) else 0)
          = muMarginal (S := S) I mu a := by
        change _ = (mu.bind (fun s => PMF.pure (s ⟨p, I⟩)) ) a
        simp_all [PMF.bind_apply, PMF.pure_apply, tsum_fintype, mul_ite, mul_one, mul_zero]
        grind
      rw [hsum]
      exact ENNReal.mul_inv_cancel hpa
        (ENNReal.ne_top_of_tsum_ne_top
          (PMF.tsum_coe (muMarginal (S := S) I mu) ▸ ENNReal.one_ne_top) a))

/-- Player-independence: your definition. -/
abbrev PlayerIndep (mu : PMF (FlatProfile S)) : Prop :=
  ∃ muP : MixedProfile S, mu = pmfPureToFlat (S := S) (mixedProfileJoint (S := S) muP)

-- ----------------------------------------------------------------------------
-- 1) A small simp lemma: expand pmfPureToFlat pointwise
-- ----------------------------------------------------------------------------

lemma pmfPureToFlat_apply (mu : PMF (PureProfile S)) (s : FlatProfile S) :
    pmfPureToFlat (S := S) mu s = ∑ pi : PureProfile S,
      mu pi * (if flatProfileEquivPureProfile.symm pi = s then 1 else 0) := by
  classical
  -- `bind_apply` + `pure_apply`, then turn tsum into sum
  simp [pmfPureToFlat, PMF.bind_apply, PMF.pure_apply, tsum_fintype,
    mul_ite, mul_one, mul_zero, eq_comm]

lemma pmfPureToFlat_apply_eq (mu : PMF (PureProfile S)) (s : FlatProfile S) :
    pmfPureToFlat (S := S) mu s = mu (flatProfileEquivPureProfile (S := S) s) := by
  classical
  rw [pmfPureToFlat_apply]
  have hkey :
      (flatProfileEquivPureProfile (S := S)).symm
          ((flatProfileEquivPureProfile (S := S)) s) = s := by
    simp
  rw [Finset.sum_eq_single (flatProfileEquivPureProfile (S := S) s)]
  · simp [hkey]
  · intro pi _ hne
    have hneq : (flatProfileEquivPureProfile (S := S)).symm pi ≠ s := by
      intro hs
      apply hne
      have : flatProfileEquivPureProfile (S := S) ((flatProfileEquivPureProfile (S := S)).symm pi) =
          flatProfileEquivPureProfile (S := S) s := by
        simp [hs]
      simpa using this
    simp [hneq]
  · intro hmem
    exact (hmem (Finset.mem_univ _)).elim

variable {S : InfoStructure} {Outcome : Type}

-- For a coordinate projection
def proj {p : S.Player} (I : S.Infoset p) (s : FlatProfile S) : S.Act I :=
  s ⟨p, I⟩

/-- Sum over all `s` can be regrouped by the value of `s⟨p,I⟩`. -/
lemma sum_by_coord {p : S.Player} (I : S.Infoset p)
  (g : FlatProfile S → ENNReal) :
  (∑ s : FlatProfile S, g s)
    =
  ∑ a : S.Act I, ∑ s : FlatProfile S, (if s ⟨p, I⟩ = a then g s else 0) := by
  let F : FlatProfile S → S.Act I → ENNReal :=
    fun s a => if s ⟨p, I⟩ = a then g s else 0
  have hcomm :
      (∑ s : FlatProfile S, ∑ a : S.Act I, F s a)
        =
      (∑ a : S.Act I, ∑ s : FlatProfile S, F s a) := by
    -- now codomain is ENNReal, so AddCommMonoid is found
    simpa using (Finset.sum_comm :
      (∑ s : FlatProfile S, ∑ a : S.Act I, F s a) =
      (∑ a : S.Act I, ∑ s : FlatProfile S, F s a))
  calc
    (∑ s : FlatProfile S, g s)
        = ∑ s : FlatProfile S, (∑ a : S.Act I, (if s ⟨p, I⟩ = a then g s else 0)) := by
            refine Finset.sum_congr rfl ?_
            intro s _
            have : (∑ a : S.Act I, (if s ⟨p, I⟩ = a then g s else 0)) = g s := by
              classical
              simp [eq_comm]
            simp [this]
    _ = ∑ a : S.Act I, ∑ s : FlatProfile S, (if s ⟨p, I⟩ = a then g s else 0) := by
          grind only

lemma muMarginal_apply {p : S.Player} (I : S.Infoset p)
    (mu : PMF (FlatProfile S)) (a : S.Act I) :
    muMarginal (S := S) I mu a
      =
    ∑ s : FlatProfile S, (if s ⟨p, I⟩ = a then (mu s) else 0) := by
  classical
  -- unfold muMarginal = bind pure, then bind_apply
  -- change tsum to sum since fintype
  simp [muMarginal, PMF.bind_apply, PMF.pure_apply, tsum_fintype, eq_comm,
        mul_ite, mul_one, mul_zero]


noncomputable def muCondOr {p : S.Player} (I : S.Infoset p) (a : S.Act I)
    (mu : PMF (FlatProfile S)) : PMF (FlatProfile S) :=
  if h0 : muMarginal (S := S) I mu a = 0 then
    mu
  else
    muCond (S := S) I a mu (by simpa using h0)

@[simp] lemma muCondOr_of_eq0 {p : S.Player} (I : S.Infoset p) (a : S.Act I)
    (mu : PMF (FlatProfile S)) (h0 : muMarginal (S := S) I mu a = 0) :
    muCondOr (S := S) I a mu = mu := by
  simp [muCondOr, h0]

@[simp] lemma muCondOr_of_ne0 {p : S.Player} (I : S.Infoset p) (a : S.Act I)
    (mu : PMF (FlatProfile S)) (h0 : muMarginal (S := S) I mu a ≠ 0) :
    muCondOr (S := S) I a mu = muCond (S := S) I a mu h0 := by
  simp [muCondOr, h0]


-- total history-conditioning: ignore chance steps
noncomputable def muCondHist (mu : PMF (FlatProfile S)) : List (HistoryStep S) → PMF (FlatProfile S)
| [] => mu
| (HistoryStep.chance _ _ :: hs) => muCondHist mu hs
| (HistoryStep.action p I a :: hs) =>
    let μ' := muCondHist mu hs
    muCondOr (S := S) (p := p) I a μ'

noncomputable def sigmaHist (mu : PMF (FlatProfile S))
    (h : List (HistoryStep S)) : BehavioralProfile S :=
  fun _ I => muMarginal (S := S) I (muCondHist (S := S) mu h)


/-- **Disintegrate bind along coordinate** `s⟨p,I⟩`.
This is the core lemma for the decision case. -/
lemma bind_disintegrate_coord
    {p : S.Player} (I : S.Infoset p)
    (mu : PMF (FlatProfile S))
    (f : FlatProfile S → PMF Outcome) :
    mu.bind f
      =
    (muMarginal (S := S) I mu).bind (fun a => (muCondOr (S := S) I a mu).bind f) := by
  ext z
  simp only [PMF.bind_apply, tsum_fintype]
  have := sum_by_coord (S:=S) (p:=p) I (g := fun s => (mu s) * f s z)
  rw [this]
  have hfiber :
      ∀ a : S.Act I,
        (∑ s : FlatProfile S,
            (if s ⟨p, I⟩ = a then (mu s) * (f s z) else 0))
          =
        (muMarginal (S := S) I mu) a *
          (∑ s : FlatProfile S, (muCondOr (S := S) I a mu) s * (f s z)) := by
    intro a
    set m : ENNReal := (muMarginal (S := S) I mu) a
    by_cases h0 : m = 0
    · have hle_term :
          ∀ s : FlatProfile S,
            (if s ⟨p, I⟩ = a then (mu s) * (f s z) else 0)
              ≤
            (if s ⟨p, I⟩ = a then (mu s) else 0) := by
        intro s
        by_cases hs : s ⟨p, I⟩ = a
        · have hz : (f s) z ≤ 1 := PMF.coe_le_one (f s) z
          have := mul_le_mul_right hz (mu s)
          simpa [hs, mul_assoc, mul_comm, mul_left_comm] using this
        · simp [hs]
      have hle_sum :
          (∑ s : FlatProfile S,
              (if s ⟨p, I⟩ = a then (mu s) * (f s z) else 0))
            ≤
          (∑ s : FlatProfile S,
              (if s ⟨p, I⟩ = a then (mu s) else 0)) :=
        Finset.sum_le_sum (fun s _ => hle_term s)
      have hm_sum :
          (∑ s : FlatProfile S,
              (if s ⟨p, I⟩ = a then (mu s) else 0)) = m := by
        exact Eq.symm (muMarginal_apply I mu a)
      have hLHS0 :
          (∑ s : FlatProfile S,
              (if s ⟨p, I⟩ = a then (mu s) * (f s z) else 0)) = 0 := by
        have : (∑ s : FlatProfile S,
            (if s ⟨p, I⟩ = a then (mu s) * (f s z) else 0)) ≤ 0 := by
          grind
        exact le_antisymm (by simpa using this) (by simp)
      simp [hLHS0, h0, m]
    · have hm : m ≠ 0 := h0
      have hm_top : m ≠ (⊤) := by
        simpa [m] using (PMF.apply_ne_top (muMarginal (S := S) I mu) a)
      simp only [mul_comm, muCondOr_of_ne0 (S := S) I a mu (by simpa [m] using hm), muCond,
        div_eq_mul_inv, PMF.ofFintype_apply, mul_ite, zero_mul, m]
      calc
        (∑ x : FlatProfile S,
            if x ⟨p, I⟩ = a then (f x) z * (mu x) else 0)
            =
        ∑ x : FlatProfile S,
            m * (if x ⟨p, I⟩ = a then (f x) z * (m⁻¹ * (mu x)) else 0) := by
          refine (Finset.sum_congr rfl ?_)
          intro x _
          have canc : m * m⁻¹ = (1) := by
            simpa [mul_comm] using (ENNReal.mul_inv_cancel hm hm_top)
          by_cases hx : x ⟨p, I⟩ = a
          · simp only [hx, ↓reduceIte]
            calc
              _ = (f x) z * ((m * m⁻¹) * (mu x)) := by
                simp [canc]
              _ = m * ((f x) z * (m⁻¹ * (mu x))) := by
                ac_rfl
          · simp [hx]
      _ = m * (∑ x : FlatProfile S,
            if x ⟨p, I⟩ = a then (f x) z * (m⁻¹ * (mu x)) else 0) := by
          simp [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun a _ => hfiber a)

@[simp] lemma muCondHist_cons_action
  (mu : PMF (FlatProfile S)) (h : List (HistoryStep S))
  {p : S.Player} (I : S.Infoset p) (a : S.Act I) :
  muCondHist (S := S) mu (HistoryStep.action p I a :: h)
    =
  muCondOr (S := S) I a (muCondHist (S := S) mu h) := by
  -- prove by unfolding muCondHist recursion on the list
  simp [muCondHist, muCondOr]


theorem eval_correct_aux
  (u : GameTree S Outcome)
  (mu : PMF (FlatProfile S))
  (h : List (HistoryStep S)) :
  u.evalDist (sigmaHist (S := S) mu h)
    =
  (muCondHist (S := S) mu h).bind (fun s => u.evalFlat (S := S) (Outcome := Outcome) s) := by
  induction u generalizing h with
  | terminal z =>
      simp [GameTree.evalFlat, sigmaHist, muCondHist]
  | chance k μc hk next ih =>
    ext z
    simp [evalDist_chance, GameTree.evalFlat, sigmaHist, muCondHist, ih, PMF.bind_bind]
    -- abbreviate g to keep simp sane
    let g : Fin k → FlatProfile S → ENNReal :=
      fun a s => (GameTree.evalDist (flatToBehavioral s) (next a)) z

    -- now just Fubini for finite sums + commutativity of *
    calc
      (∑ a : Fin k, μc a * ∑ s : FlatProfile S, (muCondHist (S := S) mu h) s * g a s)
          =
      ∑ a : Fin k, ∑ s : FlatProfile S, μc a * ((muCondHist (S := S) mu h) s * g a s) := by
        -- expand the inner product into a double sum
        simp [Finset.mul_sum, mul_assoc]
    _ =
      ∑ s : FlatProfile S, ∑ a : Fin k, μc a * ((muCondHist (S := S) mu h) s * g a s) := by
        -- swap the two ∑
        simpa using (Finset.sum_comm : (∑ a : Fin k, ∑ s : FlatProfile S, _) = _)
    _ =
      ∑ s : FlatProfile S, (muCondHist (S := S) mu h) s * ∑ a : Fin k, μc a * g a s := by
        -- factor out μh s and reassociate/commute
        -- (μc a * (μh s * g)) = (μh s) * (μc a * g)
        simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  | @decision p I next ih =>
    set μh : PMF (FlatProfile S) := muCondHist (S := S) mu h
    have hdis :=
      bind_disintegrate_coord (S := S) (Outcome := Outcome) (p := p) I
        (mu := μh)
        (f := fun s =>
          -- continuation is: evaluate the chosen branch under extended history
          (next (s ⟨p, I⟩)).evalDist
            (sigmaHist (S := S) mu (HistoryStep.action p I (s ⟨p, I⟩) :: h))
        )
    ext z
    have hdis_z : (μh.bind (fun s =>
        (next (s ⟨p, I⟩)).evalDist
          (sigmaHist (S := S) mu (HistoryStep.action p I (s ⟨p, I⟩) :: h))
      )) z
      =
      ((muMarginal (S := S) I μh).bind (fun a =>
        (muCondOr (S := S) I a μh).bind (fun s =>
          (next (s ⟨p, I⟩)).evalDist
            (sigmaHist (S := S) mu (HistoryStep.action p I (s ⟨p, I⟩) :: h))
        )
      )) z := by
        simpa using congrArg (fun t => t z) hdis
    simp [GameTree.evalFlat, GameTree.evalDist, evalDist_decision, sigmaHist, μh] at *  -- adjust names
    have ih_branch :
      ∀ a : S.Act I,
        (next a).evalDist
            (sigmaHist (S := S) mu (HistoryStep.action p I a :: h))
          =
        (muCondHist (S := S) mu (HistoryStep.action p I a :: h)).bind
          (fun s => (next a).evalFlat (S := S) (Outcome := Outcome) s) := by
      intro a
      simpa using (ih (h := HistoryStep.action p I a :: h) _)
    have hμ_step :
      ∀ a : S.Act I,
        muCondHist (S := S) mu (HistoryStep.action p I a :: h)
          =
        muCondOr (S := S) I a μh := by
      intro a
      -- THIS should be a lemma you prove once about muCondHist.
      -- It’s basically: conditioning on (action :: h) = muCondOr on top of conditioning on h.
      simp [μh, muCondHist]   -- replace with your actual muCondHist recursion lemma
    sorry

lemma muMarginal_pmfPureToFlat_joint_apply
    (muP : MixedProfile S) {p : S.Player} (I : S.Infoset p) (a : S.Act I) :
    muMarginal (S := S) I
        (pmfPureToFlat (S := S) (mixedProfileJoint (S := S) muP)) a
      =
    pmfMass (μ := muP p) (fun sp : PureStrategy S p => sp I = a) := by
  classical
  have hpush :
      (mixedProfileJoint (S := S) muP).bind (fun π => PMF.pure (π p))
        =
      muP p := by
    simpa [mixedProfileJoint, pushforward] using
      (pmfPi_push_coord (A := fun q => PureStrategy S q) (σ := muP) (j := p))
  calc
    muMarginal (S := S) I
        (pmfPureToFlat (S := S) (mixedProfileJoint (S := S) muP)) a
        =
      (((mixedProfileJoint (S := S) muP).bind (fun π => PMF.pure (π p))).bind
        (fun sp => PMF.pure (sp I))) a := by
          simp only [muMarginal, pmfPureToFlat, PMF.bind_bind, PMF.pure_bind, PMF.bind_apply,
            PMF.pure_apply, mul_ite, mul_one, mul_zero, tsum_fintype, eq_comm]
          refine Finset.sum_congr rfl ?_
          intro π _
          rfl
    _ = ((muP p).bind (fun sp => PMF.pure (sp I))) a := by
      rw [hpush]
    _ = pmfMass (μ := muP p) (fun sp : PureStrategy S p => sp I = a) := by
      simp [pmfMass, pmfMask, PMF.bind_apply, PMF.pure_apply, tsum_fintype, eq_comm]

-- ----------------------------------------------------------------------------
-- 2) Conditioning on the *PureProfile* side (product over players)
-- ----------------------------------------------------------------------------

/-- Predicate on player `p`’s pure strategy at infoset `I`. -/
def Ep {p : S.Player} (I : S.Infoset p) (a : S.Act I) : PureStrategy S p → Prop :=
  fun sp => sp I = a

instance {p : S.Player} (I : S.Infoset p) (a : S.Act I) : DecidablePred (Ep (S := S) I a) :=
  by
    intro sp
    dsimp [Ep]
    infer_instance

/-- Condition the product PMF on the coordinate event `π p I = a`
 (depends only on coordinate `p`). -/
noncomputable def pureCond (muP : MixedProfile S) {p : S.Player} (I : S.Infoset p) (a : S.Act I)
    (hE : pmfMass (μ := muP p) (Ep (S := S) I a) ≠ 0) : PMF (PureProfile S) :=
  pmfCond (μ := mixedProfileJoint (S := S) muP)
    (fun π => Ep (S := S) I a (π p))
    (by
      -- mass under product = mass under factor (your PMFProduct lemma)
      simpa [mixedProfileJoint, pmfMass_pmfPi_coord (A := fun q => PureStrategy S q)
        (σ := muP) (j := p) (E := Ep (S := S) I a)] using hE)

lemma pureCond_eq_joint_update
    (muP : MixedProfile S) {p : S.Player} (I : S.Infoset p) (a : S.Act I)
    (hE : pmfMass (μ := muP p) (Ep (S := S) I a) ≠ 0) :
    pureCond (S := S) muP I a hE
      =
    mixedProfileJoint (S := S)
      (Function.update muP p (pmfCond (μ := muP p) (Ep (S := S) I a) hE)) := by
  simpa [pureCond, mixedProfileJoint] using
    (pmfPi_cond_coord (A := fun q => PureStrategy S q) muP p (Ep (S := S) I a) hE)

lemma mixedProfile_update_update_comm
    (muP : MixedProfile S) {p q : S.Player} (hpq : p ≠ q)
    (μp : PMF (PureStrategy S p)) (μq : PMF (PureStrategy S q)) :
    Function.update (Function.update muP p μp) q μq
      =
    Function.update (Function.update muP q μq) p μp := by
  funext r
  by_cases hrp : r = p
  · subst hrp
    simp [Function.update, hpq]
  · by_cases hrq : r = q
    · subst hrq
      simp [Function.update, hpq, hrp]
    · simp [Function.update, hrp, hrq]

-- ----------------------------------------------------------------------------
-- 3) The key bridge: conditioning commutes with your Pure→Flat pushforward
-- ----------------------------------------------------------------------------

/-
This lemma is the only “real plumbing” you need.
It says: if `mu = pmfPureToFlat (mixedProfileJoint muP)`, then your flat `muCond`
is exactly `pmfPureToFlat` of the *pure-side* conditioning.

Once you have it, `PlayerIndep_muCond` and `muMarginal_muCond_other` are 3 lines each.
-/
theorem muCond_eq_pmfPureToFlat_pureCond
    (muP : MixedProfile S)
    {p : S.Player} (I : S.Infoset p) (a : S.Act I)
    -- hypothesis matching your muCond precondition, but on the flat side:
    (hpa_flat :
      muMarginal (S := S) I (pmfPureToFlat (S := S) (mixedProfileJoint (S := S) muP)) a ≠ 0)
    -- precondition for pure-side conditioning (derivable from hpa_flat, but we accept it directly):
    (hE : pmfMass (μ := muP p) (Ep (S := S) I a) ≠ 0) :
    muCond (S := S) I a (pmfPureToFlat (S := S) (mixedProfileJoint (S := S) muP)) hpa_flat
      =
    pmfPureToFlat (S := S) (pureCond (S := S) muP I a hE) := by
  classical
  have hmarg :
      muMarginal (S := S) I
          (pmfPureToFlat (S := S) (mixedProfileJoint (S := S) muP)) a
        =
      pmfMass (μ := muP p) (fun sp : PureStrategy S p => sp I = a) := by
    exact muMarginal_pmfPureToFlat_joint_apply (S := S) muP I a
  have hmass_prod :
      pmfMass (μ := mixedProfileJoint (S := S) muP) (fun π => π p I = a)
        =
      pmfMass (μ := muP p) (fun sp : PureStrategy S p => sp I = a) := by
    simp [mixedProfileJoint, pmfMass_pmfPi_coord (A := fun q => PureStrategy S q)
      (σ := muP) (j := p) (E := fun sp : PureStrategy S p => sp I = a)]
  ext s
  by_cases hs : s ⟨p, I⟩ = a
  · simp [muCond, PMF.ofFintype_apply, pmfPureToFlat_apply_eq, pureCond, pmfCond_apply, pmfMask,
      hmarg, hmass_prod, Ep, flatProfileEquivPureProfile, hs]
  · simp [muCond, PMF.ofFintype_apply, pmfPureToFlat_apply_eq, pureCond, pmfCond_apply, pmfMask,
      hmarg, hmass_prod, Ep, flatProfileEquivPureProfile, hs]

-- ----------------------------------------------------------------------------
-- 4) Now the two “headline” theorems become short.
-- ----------------------------------------------------------------------------

theorem PlayerIndep_pmfPureToFlat (muP : MixedProfile S) :
    PlayerIndep (S := S) (pmfPureToFlat (S := S) (mixedProfileJoint (S := S) muP)) := by
  exact ⟨muP, rfl⟩

theorem PlayerIndep_muCond
    (mu : PMF (FlatProfile S))
    (hind : PlayerIndep (S := S) mu)
    {p : S.Player} {I : S.Infoset p} {a : S.Act I}
    (hpa : muMarginal (S := S) I mu a ≠ 0) :
    PlayerIndep (S := S) (muCond (S := S) I a mu hpa) := by
  rcases hind with ⟨muP, rfl⟩
  -- derive the pure-side nonzero mass (you can prove this from `hpa` if you want;
  -- for now, just define it using classical choice + the fact it must be nonzero
  -- because pushforward to flat has nonzero mass).
  have hE : pmfMass (μ := muP p) (Ep (S := S) I a) ≠ 0 := by
    simpa [muMarginal_pmfPureToFlat_joint_apply (S := S) muP I a, Ep] using hpa
  refine ⟨Function.update muP p (pmfCond (μ := muP p) (Ep (S := S) I a) hE), ?_⟩
  -- Use the bridge lemma + the PMFProduct “conditioning a product updates only that coordinate”
  -- on the pure side:
  have hpure :
      pureCond (S := S) muP I a hE
        =
      mixedProfileJoint (S := S)
        (Function.update muP p (pmfCond (μ := muP p) (Ep (S := S) I a) hE)) := by
    simpa using pureCond_eq_joint_update (S := S) muP I a hE
  -- finish
  calc
    muCond (S := S) I a (pmfPureToFlat (S := S) (mixedProfileJoint (S := S) muP)) hpa
        =
      pmfPureToFlat (S := S) (pureCond (S := S) muP I a hE) := by
          simpa using (muCond_eq_pmfPureToFlat_pureCond (S := S) muP I a hpa hE)
    _ = pmfPureToFlat (S := S)
          (mixedProfileJoint (S := S)
            (Function.update muP p (pmfCond (μ := muP p) (Ep (S := S) I a) hE))) := by
          simp [hpure]
    _ = pmfPureToFlat (S := S) (mixedProfileJoint (S := S)
            (Function.update muP p (pmfCond (μ := muP p) (Ep (S := S) I a) hE))) := rfl

theorem muMarginal_muCond_other
    (mu : PMF (FlatProfile S))
    (hind : PlayerIndep (S := S) mu)
    {p q : S.Player}
    (hpq : q ≠ p)
    {I : S.Infoset p}
    {J : S.Infoset q}
    {a : S.Act I}
    (hpa : muMarginal (S := S) I mu a ≠ 0) :
    muMarginal (S := S) J (muCond (S := S) I a mu hpa) =
    muMarginal (S := S) J mu := by
  rcases hind with ⟨muP, rfl⟩
  -- same pure-side nonzero mass as above
  have hE : pmfMass (μ := muP p) (Ep (S := S) I a) ≠ 0 := by
    simpa [muMarginal_pmfPureToFlat_joint_apply (S := S) muP I a, Ep] using hpa
  -- rewrite `muCond` as pushforward of pure-side conditioning
  have hrew :
      muCond (S := S) I a (pmfPureToFlat (S := S) (mixedProfileJoint (S := S) muP)) hpa
        =
      pmfPureToFlat (S := S) (pureCond (S := S) muP I a hE) := by
    simpa using (muCond_eq_pmfPureToFlat_pureCond (S := S) muP I a hpa hE)
  -- now apply the PMFProduct lemma: conditioning the product on coordinate p
  -- doesn’t change other coordinate marginals (q ≠ p), and pushforward commutes.
  --
  -- Concretely, marginal at infoset J of player q is pushforward along `π ↦ π q J`.
  -- On the pure side, that’s still coordinate q (as a PureStrategy) then apply at J.
  -- This is one more “pushforward-compose” lemma + `pmfPi_cond_coord_push_other`.
  --
  -- If you don’t yet have the pushforward-compose lemma, keep this as `sorry` and fill later.
  have hpure :
      pureCond (S := S) muP I a hE
        =
      mixedProfileJoint (S := S)
        (Function.update muP p (pmfCond (μ := muP p) (Ep (S := S) I a) hE)) := by
    simpa using pureCond_eq_joint_update (S := S) muP I a hE
  rw [hrew, hpure]
  ext b
  simp [muMarginal_pmfPureToFlat_joint_apply, hpq, Function.update]

theorem muCond_proof_irrel
    (mu : PMF (FlatProfile S))
    {p : S.Player} (I : S.Infoset p) (a : S.Act I)
    (h1 h2 : muMarginal (S := S) I mu a ≠ 0) :
    muCond (S := S) I a mu h1 = muCond (S := S) I a mu h2 := by
  ext s
  simp [muCond, PMF.ofFintype_apply]

theorem muCond_comm_of_PlayerIndep
    (mu : PMF (FlatProfile S))
    (hind : PlayerIndep (S := S) mu)
    {p q : S.Player} (hpq : p ≠ q)
    {I : S.Infoset p} {a : S.Act I}
    {J : S.Infoset q} {b : S.Act J}
    (hpa : muMarginal (S := S) I mu a ≠ 0)
    (hpb : muMarginal (S := S) J mu b ≠ 0) :
    muCond (S := S) J b (muCond (S := S) I a mu hpa)
      (by
        have hJsame :
            muMarginal (S := S) J (muCond (S := S) I a mu hpa) b
              =
            muMarginal (S := S) J mu b :=
          congrArg (fun ν => ν b)
            (muMarginal_muCond_other (S := S) (mu := mu) hind
              (p := p) (q := q) (by simpa using hpq.symm) (I := I) (J := J) (a := a) hpa)
        simpa [hJsame] using hpb)
      =
    muCond (S := S) I a (muCond (S := S) J b mu hpb)
      (by
        have hIsame :
            muMarginal (S := S) I (muCond (S := S) J b mu hpb) a
              =
            muMarginal (S := S) I mu a :=
          congrArg (fun ν => ν a)
            (muMarginal_muCond_other (S := S) (mu := mu) hind
              (p := q) (q := p) hpq
              (I := J) (J := I) (a := b) hpb)
        simpa [hIsame] using hpa) := by
  sorry

structure DecConstraint (S : InfoStructure) where
  p : S.Player
  I : S.Infoset p
  a : S.Act I
deriving DecidableEq

abbrev DecPath (S : InfoStructure) := List (DecConstraint S)

def Satisfies (s : FlatProfile S) (c : DecConstraint S) : Prop :=
  s ⟨c.p, c.I⟩ = c.a

def SatisfiesPath (s : FlatProfile S) (path : DecPath S) : Prop :=
  ∀ c, c ∈ path -> Satisfies (S := S) s c

/-- Evidence that we can condition along `path` step-by-step (each step has nonzero mass). -/
def GoodPath {S} (mu : PMF (FlatProfile S)) : DecPath S → Type
  | [] => PUnit
  | c :: cs =>
      Σ' h : muMarginal (S := S) c.I mu c.a ≠ 0,
        GoodPath (S := S) (muCond (S := S) c.I c.a mu h) cs

noncomputable def muCondPath {S} :
    (mu : PMF (FlatProfile S)) → (path : DecPath S)
     → GoodPath (S := S) mu path → PMF (FlatProfile S)
  | mu, [], _ => mu
  | mu, c :: cs, ⟨h, hgood⟩ =>
      muCondPath (S := S) (mu := muCond (S := S) c.I c.a mu h) (path := cs) hgood

theorem muCondPath_proof_irrel
    (mu : PMF (FlatProfile S)) (path : DecPath S)
    (h1 h2 : GoodPath (S := S) mu path) :
    muCondPath (S := S) (mu := mu) (path := path) h1
      =
    muCondPath (S := S) (mu := mu) (path := path) h2 := by
  induction path generalizing mu with
  | nil =>
      rfl
  | cons c cs ih =>
      rcases h1 with ⟨hc1, hcs1⟩
      rcases h2 with ⟨hc2, hcs2⟩
      simp [muCondPath]
      have hcond :
          muCond (S := S) c.I c.a mu hc1 = muCond (S := S) c.I c.a mu hc2 :=
        muCond_proof_irrel (S := S) (mu := mu) c.I c.a hc1 hc2
      cases hcond
      simpa using ih (mu := muCond (S := S) c.I c.a mu hc2) hcs1 hcs2

lemma muCondPath_cast
    (mu : PMF (FlatProfile S)) {path path' : DecPath S}
    (h : path = path') (hp : GoodPath (S := S) mu path) :
    muCondPath (S := S) (mu := mu) (path := path) hp
      =
    muCondPath (S := S) (mu := mu) (path := path')
      (cast (by cases h; rfl) hp) := by
  cases h
  rfl

@[simp] lemma muCondPath_nil (mu : PMF (FlatProfile S)) (h : GoodPath (S := S) mu []) :
    muCondPath (S := S) (mu := mu) (path := []) h = mu := rfl

@[simp] lemma muCondPath_cons (mu : PMF (FlatProfile S)) (c : DecConstraint S) (cs : DecPath S)
    (h : GoodPath (S := S) mu (c :: cs)) :
    muCondPath (S := S) (mu := mu) (path := c :: cs) h =
      muCondPath (S := S)
        (mu := muCond (S := S) c.I c.a mu h.1)
        (path := cs) h.2 := rfl

def RelevantTo (p : S.Player) (c : DecConstraint S) : Prop := c.p = p

noncomputable def FilterPlayer (p : S.Player) (path : DecPath S) : DecPath S :=
  path.filter (fun c => decide (c.p = p))

lemma mem_FilterPlayer_iff (p : S.Player) (c : DecConstraint S) (path : DecPath S) :
    c ∈ FilterPlayer (S := S) p path ↔ c ∈ path ∧ c.p = p := by
  classical
  simp [FilterPlayer, List.mem_filter]

lemma head_owner_of_FilterPlayer_cons
    (p : S.Player) (d : DecConstraint S) (ds : DecPath S) (path : DecPath S)
    (h : FilterPlayer (S := S) p path = d :: ds) :
    d.p = p := by
  have hmem : d ∈ FilterPlayer (S := S) p path := by
    simp [h]
  exact (mem_FilterPlayer_iff (S := S) p d path).1 hmem |>.2

def decPathToHistory : DecPath S → List (HistoryStep S)
  | [] => []
  | c :: cs => HistoryStep.action c.p c.I c.a :: decPathToHistory cs

lemma decPathToHistory_append (xs ys : DecPath S) :
    decPathToHistory (S := S) (xs ++ ys) =
      decPathToHistory (S := S) xs ++ decPathToHistory (S := S) ys := by
  induction xs with
  | nil =>
      rfl
  | cons c cs ih =>
      simp [decPathToHistory, ih]

def playerViewOfConstraint (q : S.Player) (c : DecConstraint S) (h : c.p = q) :
    Σ I : S.Infoset q, S.Act I := by
  subst h
  exact ⟨c.I, c.a⟩

def viewToConstraint (q : S.Player) (v : Σ I : S.Infoset q, S.Act I) : DecConstraint S :=
  { p := q, I := v.1, a := v.2 }

lemma viewToConstraint_playerView
    (q : S.Player) (c : DecConstraint S) (h : c.p = q) :
    viewToConstraint (S := S) q (playerViewOfConstraint (S := S) q c h) = c := by
  cases c with
  | mk p I a =>
      dsimp [playerViewOfConstraint, viewToConstraint] at *
      cases h
      rfl

def decPathPlayerView (q : S.Player) : DecPath S → List (Σ I : S.Infoset q, S.Act I)
  | [] => []
  | c :: cs =>
      if h : c.p = q then
        playerViewOfConstraint (S := S) q c h :: decPathPlayerView q cs
      else
        decPathPlayerView q cs

lemma decPathPlayerView_append (q : S.Player) (xs ys : DecPath S) :
    decPathPlayerView (S := S) q (xs ++ ys) =
      decPathPlayerView (S := S) q xs ++ decPathPlayerView (S := S) q ys := by
  induction xs with
  | nil =>
      rfl
  | cons c cs ih =>
      simp only [List.cons_append, decPathPlayerView, ih]
      split
      next h =>
        subst h
        simp_all only [List.cons_append]
      next h => simp_all only

lemma decPathPlayerView_eq_playerHistory (q : S.Player) (path : DecPath S) :
    decPathPlayerView (S := S) q path =
      playerHistory S q (decPathToHistory (S := S) path) := by
  induction path with
  | nil =>
      rfl
  | cons c cs ih =>
      simp [decPathToHistory, decPathPlayerView, playerHistory, ih]
      by_cases h : c.p = q
      · simp [h, playerViewOfConstraint]
      · simp [h]

lemma map_viewToConstraint_decPathPlayerView
    (q : S.Player) (path : DecPath S) :
    List.map (viewToConstraint (S := S) q) (decPathPlayerView (S := S) q path)
      =
    FilterPlayer (S := S) q path := by
  induction path with
  | nil =>
      rfl
  | cons c cs ih =>
      by_cases h : c.p = q
      · simp [decPathPlayerView, FilterPlayer, h, ih]
        simp [viewToConstraint_playerView (S := S) q c h]
      · simp [decPathPlayerView, FilterPlayer, h, ih]

/-- Canonical witness that filtered constraints remain conditionable. -/
noncomputable def goodPath_transport_other
    (mu : PMF (FlatProfile S))
    (c : DecConstraint S)
    (cs : DecPath S)
    (q : S.Player)
    (hc : muMarginal (S := S) c.I mu c.a ≠ 0)
    (hneq : c.p ≠ q)
    (hind : PlayerIndep (S := S) mu)
    (hcs :
      GoodPath (S := S)
        (muCond (S := S) c.I c.a mu hc)
        (FilterPlayer (S := S) q cs)) :
    GoodPath (S := S) mu (FilterPlayer (S := S) q cs) := by
  induction cs generalizing mu with
  | nil =>
      simpa [FilterPlayer] using (PUnit.unit : GoodPath (S := S) mu [])
  | cons d ds ih =>
      by_cases hdq : d.p = q
      · have hshape :
            GoodPath (S := S) (muCond (S := S) c.I c.a mu hc)
              (d :: FilterPlayer (S := S) q ds) := by
          simpa [FilterPlayer, hdq] using hcs
        rcases hshape with ⟨hd_cond, htail_cond⟩
        have hdp_ne_cp : d.p ≠ c.p := by
          intro hdc
          apply hneq
          calc
            c.p = d.p := hdc.symm
            _ = q := hdq
        have hd_nonzero : muMarginal (S := S) d.I mu d.a ≠ 0 := by
          have hmarg :
              muMarginal (S := S) d.I (muCond (S := S) c.I c.a mu hc) d.a
                =
              muMarginal (S := S) d.I mu d.a := by
            exact congrArg (fun ν => ν d.a)
              (muMarginal_muCond_other (S := S) (mu := mu) hind
                (p := c.p) (q := d.p) hdp_ne_cp (I := c.I) (J := d.I) (a := c.a) hc)
          simpa [hmarg] using hd_cond
        have hc_after : muMarginal (S := S) c.I
            (muCond (S := S) d.I d.a mu hd_nonzero) c.a ≠ 0 := by
          have hmarg :
              muMarginal (S := S) c.I (muCond (S := S) d.I d.a mu hd_nonzero) c.a
                =
              muMarginal (S := S) c.I mu c.a := by
            exact congrArg (fun ν => ν c.a)
              (muMarginal_muCond_other (S := S) (mu := mu) hind
                (p := d.p) (q := c.p) (by simpa using hdp_ne_cp.symm)
                (I := d.I) (J := c.I) (a := d.a) hd_nonzero)
          simpa [hmarg] using hc
        have hind_d :
            PlayerIndep (S := S) (muCond (S := S) d.I d.a mu hd_nonzero) :=
          PlayerIndep_muCond (S := S) (mu := mu) hind
            (p := d.p) (I := d.I) (a := d.a) hd_nonzero
        have hcomm :
            muCond (S := S) d.I d.a (muCond (S := S) c.I c.a mu hc) hd_cond
              =
            muCond (S := S) c.I c.a (muCond (S := S) d.I d.a mu hd_nonzero) hc_after := by
          simpa using
            (muCond_comm_of_PlayerIndep (S := S) (mu := mu) hind
              (p := c.p) (q := d.p) hdp_ne_cp.symm (I := c.I) (a := c.a)
              (J := d.I) (b := d.a) hc hd_nonzero)
        have htail' :
            GoodPath (S := S)
              (muCond (S := S) c.I c.a (muCond (S := S) d.I d.a mu hd_nonzero) hc_after)
              (FilterPlayer (S := S) q ds) := by
          exact cast
            (by
              simpa using congrArg
                (fun ν => GoodPath (S := S) ν (FilterPlayer (S := S) q ds)) hcomm)
            htail_cond
        have htail :
            GoodPath (S := S) (muCond (S := S) d.I d.a mu hd_nonzero)
              (FilterPlayer (S := S) q ds) :=
          ih (mu := muCond (S := S) d.I d.a mu hd_nonzero)
            (hc := hc_after) (hind := hind_d) (hcs := htail')
        sorry
      · have hshape :
            GoodPath (S := S) (muCond (S := S) c.I c.a mu hc)
              (FilterPlayer (S := S) q ds) := by
          simpa [FilterPlayer, hdq] using hcs
        have htail :
            GoodPath (S := S) mu (FilterPlayer (S := S) q ds) :=
          ih (mu := mu) (hc := hc) (hind := hind) (hcs := hshape)
        simpa [FilterPlayer, hdq] using htail

noncomputable def goodPathFilter
    (mu : PMF (FlatProfile S)) (path : DecPath S)
    (hgood : GoodPath (S := S) mu path) (q : S.Player)
    (hind : PlayerIndep (S := S) mu) :
    GoodPath (S := S) mu (FilterPlayer (S := S) q path) := by
  induction path generalizing mu with
  | nil =>
      simpa [FilterPlayer] using (PUnit.unit : GoodPath (S := S) mu [])
  | cons c cs ih =>
      rcases hgood with ⟨hc, hcs⟩
      by_cases hq : c.p = q
      · -- Head constraint is owned by q, so it remains in the filtered path.
        simp only [FilterPlayer, hq, decide_true, List.filter_cons_of_pos]
        refine ⟨?_, ?_⟩
        · simpa [hq] using hc
        · have hind' :
              PlayerIndep (S := S) (muCond (S := S) c.I c.a mu hc) :=
            PlayerIndep_muCond (S := S) (mu := mu) hind
              (p := c.p) (I := c.I) (a := c.a) hc
          have htail :
              GoodPath (S := S)
                (muCond (S := S) c.I c.a mu hc)
                (FilterPlayer (S := S) q cs) := by
            exact ih (mu := muCond (S := S) c.I c.a mu hc) hcs hind'
          exact htail
      · -- Head constraint is owned by another player and is dropped by `FilterPlayer`.
        simp only [FilterPlayer, hq, decide_false, Bool.false_eq_true, not_false_eq_true,
          List.filter_cons_of_neg]
        have hneq : c.p ≠ q := by
          exact hq
        have hind' :
            PlayerIndep (S := S) (muCond (S := S) c.I c.a mu hc) :=
          PlayerIndep_muCond (S := S) (mu := mu) hind
            (p := c.p) (I := c.I) (a := c.a) hc
        have hfilteredCond :
            GoodPath (S := S)
              (muCond (S := S) c.I c.a mu hc)
              (FilterPlayer (S := S) q cs) := by
          exact ih (mu := muCond (S := S) c.I c.a mu hc) hcs hind'
        exact goodPath_transport_other (S := S)
          (mu := mu) (c := c) (cs := cs) (q := q)
          (hc := hc) (hneq := hneq) (hind := hind) (hcs := hfilteredCond)

inductive SubtreeAt : GameTree S Outcome -> DecPath S -> GameTree S Outcome -> Prop where
  | refl (t : GameTree S Outcome) : SubtreeAt t [] t
  | chance {k : Nat} {muC : PMF (Fin k)} {hk : 0 < k} {next : Fin k -> GameTree S Outcome}
      {path : DecPath S} {u : GameTree S Outcome} {b : Fin k} :
      SubtreeAt (next b) path u -> SubtreeAt (.chance k muC hk next) path u
  | decision {pOwner : S.Player} {I0 : S.Infoset pOwner}
      {next : S.Act I0 -> GameTree S Outcome}
      {path : DecPath S} {u : GameTree S Outcome} {a : S.Act I0} :
      SubtreeAt (next a) (path ++ [{ p := pOwner, I := I0, a := a }]) u ->
      SubtreeAt (.decision I0 next) path u

theorem DecisionNodeIn_reachBy
    {q : S.Player} {J : S.Infoset q} {u : GameTree S Outcome}
    (hJ : DecisionNodeIn J u) :
    ∃ (h : List (HistoryStep S)) (next : S.Act J → GameTree S Outcome),
      ReachBy (S := S) (Outcome := Outcome) h u (.decision J next) := by
  induction hJ with
  | root next =>
      exact ⟨[], next, ReachBy.here _⟩
  | in_chance k μ hk next b hsub ih =>
      rcases ih with ⟨h, nextJ, hreach⟩
      exact ⟨HistoryStep.chance k b :: h, nextJ, ReachBy.chance b hreach⟩
  | in_decision I' next a hsub ih =>
      rcases ih with ⟨h, nextJ, hreach⟩
      exact ⟨HistoryStep.action _ I' a :: h, nextJ, ReachBy.action a hreach⟩

theorem SubtreeAt_to_ReachBy_exists
    {tRoot u : GameTree S Outcome} {pi : DecPath S}
    (hsub : SubtreeAt (S := S) (Outcome := Outcome) tRoot pi u) :
    ∃ h : List (HistoryStep S), ReachBy (S := S) (Outcome := Outcome) h tRoot u := by
  induction hsub with
  | refl t =>
      exact ⟨[], ReachBy.here t⟩
  | chance hb ih =>
      rename_i k muC hk next path u b
      rcases ih with ⟨h, hr⟩
      exact ⟨HistoryStep.chance k b :: h, ReachBy.chance b hr⟩
  | decision hb ih =>
      rename_i pOwner I0 next path u a
      rcases ih with ⟨h, hr⟩
      exact ⟨HistoryStep.action pOwner I0 a :: h, ReachBy.action a hr⟩

def PathReachesInfoset
    (tRoot : GameTree S Outcome)
    (pi : DecPath S)
    {q : S.Player}
    (J : S.Infoset q) : Prop :=
  ∃ (h : List (HistoryStep S)) (next : S.Act J → GameTree S Outcome),
    ReachBy (S := S) (Outcome := Outcome) h tRoot (.decision J next) ∧
    playerHistory S q h = decPathPlayerView (S := S) q pi

noncomputable def qHistoryList (tRoot : GameTree S Outcome) (q : S.Player)
    (J : S.Infoset q) : DecPath S :=
  by
    classical
    by_cases h : ∃ pi, PathReachesInfoset (S := S) (Outcome := Outcome) tRoot pi J
    · exact FilterPlayer (S := S) q (Classical.choose h)
    · exact []

noncomputable def qHistory (tRoot : GameTree S Outcome) (q : S.Player)
    (J : S.Infoset q) : Finset (DecConstraint S) :=
  (qHistoryList (S := S) (Outcome := Outcome) tRoot q J).toFinset

/-- Extend a good path by one more constraint, using a nonzero-mass proof at the end. -/
noncomputable def GoodPath.snoc
    (mu : PMF (FlatProfile S)) (path : DecPath S)
    (hpath : GoodPath (S := S) mu path)
    (c : DecConstraint S)
    (hc : muMarginal (S := S) c.I (muCondPath (S := S) (mu := mu) (path := path) hpath) c.a ≠ 0) :
    GoodPath (S := S) mu (path ++ [c]) := by
  induction path generalizing mu with
  | nil =>
      -- path = []
      exact ⟨hc, ⟨⟩⟩
  | cons c0 cs ih =>
      rcases hpath with ⟨h0, hcs⟩
      refine ⟨h0, ?_⟩
      -- now we are under the conditioned measure
      exact ih
        (mu := muCond (S := S) c0.I c0.a mu h0)
        (hpath := hcs)
        (hc := hc)

theorem muCondPath_step_eq_append
    (mu : PMF (FlatProfile S)) (path : DecPath S)
    (hpath : GoodPath (S := S) mu path)
    (c : DecConstraint S)
    (hc : muMarginal (S := S) c.I (muCondPath (S := S) (mu := mu) (path := path) hpath) c.a ≠ 0) :
    muCond (S := S) c.I c.a (muCondPath (S := S) (mu := mu) (path := path) hpath) hc =
      muCondPath (S := S) (mu := mu) (path := path ++ [c])
        (GoodPath.snoc (S := S) mu path hpath c hc) := by
  -- unfold muCondPath on (path ++ [c]); it peels off the final `c` exactly once
  induction path generalizing mu with
  | nil =>
      -- path = []
      rfl
  | cons c0 cs ih =>
      -- reduce both sides under the first step `c0`
      rcases hpath with ⟨h0, hcs⟩
      -- both sides start with the same conditioning on c0, so recurse
      simp [muCondPath, GoodPath.snoc, List.cons_append, ih]

theorem PlayerIndep_muCondPath
    (mu : PMF (FlatProfile S)) (path : DecPath S)
    (hind : PlayerIndep (S := S) mu)
    (hgood : GoodPath (S := S) mu path) :
    PlayerIndep (S := S) (muCondPath (S := S) mu path hgood) := by
  induction path generalizing mu with
  | nil =>
      simpa [muCondPath] using hind
  | cons c cs ih =>
      rcases hgood with ⟨hc, hcs⟩
      have hind' :
          PlayerIndep (S := S) (muCond (S := S) c.I c.a mu hc) :=
        PlayerIndep_muCond (S := S) (mu := mu) hind (p := c.p) (I := c.I) (a := c.a) hc
      simpa [muCondPath] using ih (mu := muCond (S := S) c.I c.a mu hc) hind' hcs

theorem muMarginal_condPath_other_head_qonly
    (mu : PMF (FlatProfile S))
    (c : DecConstraint S)
    (hc : muMarginal (S := S) c.I mu c.a ≠ 0)
    (hind : PlayerIndep (S := S) mu)
    (q : S.Player) (hneq : c.p ≠ q)
    (path : DecPath S)
    (hall : ∀ d, d ∈ path -> d.p = q)
    (hcond : GoodPath (S := S) (muCond (S := S) c.I c.a mu hc) path)
    (hbase : GoodPath (S := S) mu path)
    (J : S.Infoset q) :
    muMarginal (S := S) J
      (muCondPath (S := S) (muCond (S := S) c.I c.a mu hc) path hcond)
      =
    muMarginal (S := S) J
      (muCondPath (S := S) mu path hbase) := by
  induction path generalizing mu with
  | nil =>
      simpa [muCondPath] using
        (muMarginal_muCond_other (S := S) (mu := mu) hind
          (p := c.p) (q := q) (by simpa using hneq.symm) (I := c.I) (J := J) (a := c.a) hc)
  | cons d ds ih =>
      have hdq : d.p = q := hall d (by simp)
      have hdp_ne_cp : d.p ≠ c.p := by
        intro hdc
        apply hneq
        calc
          c.p = d.p := hdc.symm
          _ = q := hdq
      rcases hcond with ⟨hd_cond, hcond_tail⟩
      rcases hbase with ⟨hd_base, hbase_tail⟩
      have hc_after : muMarginal (S := S) c.I (muCond (S := S) d.I d.a mu hd_base) c.a ≠ 0 := by
        have hmarg :
            muMarginal (S := S) c.I (muCond (S := S) d.I d.a mu hd_base) c.a
              =
            muMarginal (S := S) c.I mu c.a := by
          exact congrArg (fun ν => ν c.a)
            (muMarginal_muCond_other (S := S) (mu := mu) hind
              (p := d.p) (q := c.p) (by simpa using hdp_ne_cp.symm)
              (I := d.I) (J := c.I) (a := d.a) hd_base)
        simpa [hmarg] using hc
      have hcomm_raw :
          muCond (S := S) d.I d.a (muCond (S := S) c.I c.a mu hc)
            (by
              have hmarg :
                  muMarginal (S := S) d.I (muCond (S := S) c.I c.a mu hc) d.a
                    =
                  muMarginal (S := S) d.I mu d.a := by
                exact congrArg (fun ν => ν d.a)
                  (muMarginal_muCond_other (S := S) (mu := mu) hind
                    (p := c.p) (q := d.p) hdp_ne_cp (I := c.I) (J := d.I) (a := c.a) hc)
              simpa [hmarg] using hd_base)
            =
          muCond (S := S) c.I c.a (muCond (S := S) d.I d.a mu hd_base)
            (by
              have hmarg :
                  muMarginal (S := S) c.I (muCond (S := S) d.I d.a mu hd_base) c.a
                    =
                  muMarginal (S := S) c.I mu c.a := by
                exact congrArg (fun ν => ν c.a)
                  (muMarginal_muCond_other (S := S) (mu := mu) hind
                    (p := d.p) (q := c.p) (by simpa using hdp_ne_cp.symm)
                    (I := d.I) (J := c.I) (a := d.a) hd_base)
              simpa [hmarg] using hc) := by
        simpa using
          (muCond_comm_of_PlayerIndep (S := S) (mu := mu) hind
            (p := c.p) (q := d.p) hdp_ne_cp.symm (I := c.I) (a := c.a)
            (J := d.I) (b := d.a) hc hd_base)
      have hleft_irrel :
          muCond (S := S) d.I d.a (muCond (S := S) c.I c.a mu hc) hd_cond
            =
          muCond (S := S) d.I d.a (muCond (S := S) c.I c.a mu hc)
            (by
              have hmarg :
                  muMarginal (S := S) d.I (muCond (S := S) c.I c.a mu hc) d.a
                    =
                  muMarginal (S := S) d.I mu d.a := by
                exact congrArg (fun ν => ν d.a)
                  (muMarginal_muCond_other (S := S) (mu := mu) hind
                    (p := c.p) (q := d.p) hdp_ne_cp (I := c.I) (J := d.I) (a := c.a) hc)
              simpa [hmarg] using hd_base) := by
        exact muCond_proof_irrel (S := S) (mu := muCond (S := S) c.I c.a mu hc) d.I d.a _ _
      have hright_irrel :
          muCond (S := S) c.I c.a (muCond (S := S) d.I d.a mu hd_base)
            (by
              have hmarg :
                  muMarginal (S := S) c.I (muCond (S := S) d.I d.a mu hd_base) c.a
                    =
                  muMarginal (S := S) c.I mu c.a := by
                exact congrArg (fun ν => ν c.a)
                  (muMarginal_muCond_other (S := S) (mu := mu) hind
                    (p := d.p) (q := c.p) (by simpa using hdp_ne_cp.symm)
                    (I := d.I) (J := c.I) (a := d.a) hd_base)
              simpa [hmarg] using hc)
            =
          muCond (S := S) c.I c.a (muCond (S := S) d.I d.a mu hd_base) hc_after := by
        exact muCond_proof_irrel (S := S)
          (mu := muCond (S := S) d.I d.a mu hd_base) c.I c.a _ _
      have hcomm :
          muCond (S := S) d.I d.a (muCond (S := S) c.I c.a mu hc) hd_cond
            =
          muCond (S := S) c.I c.a (muCond (S := S) d.I d.a mu hd_base) hc_after := by
        calc
          muCond (S := S) d.I d.a (muCond (S := S) c.I c.a mu hc) hd_cond
              =
          muCond (S := S) d.I d.a (muCond (S := S) c.I c.a mu hc)
            (by
              have hmarg :
                  muMarginal (S := S) d.I (muCond (S := S) c.I c.a mu hc) d.a
                    =
                  muMarginal (S := S) d.I mu d.a := by
                exact congrArg (fun ν => ν d.a)
                  (muMarginal_muCond_other (S := S) (mu := mu) hind
                    (p := c.p) (q := d.p) hdp_ne_cp (I := c.I) (J := d.I) (a := c.a) hc)
              simpa [hmarg] using hd_base) := hleft_irrel
          _ = muCond (S := S) c.I c.a (muCond (S := S) d.I d.a mu hd_base)
                (by
                  have hmarg :
                      muMarginal (S := S) c.I (muCond (S := S) d.I d.a mu hd_base) c.a
                        =
                      muMarginal (S := S) c.I mu c.a := by
                    exact congrArg (fun ν => ν c.a)
                      (muMarginal_muCond_other (S := S) (mu := mu) hind
                        (p := d.p) (q := c.p) (by simpa using hdp_ne_cp.symm)
                        (I := d.I) (J := c.I) (a := d.a) hd_base)
                  simpa [hmarg] using hc) := hcomm_raw
          _ = muCond (S := S) c.I c.a (muCond (S := S) d.I d.a mu hd_base) hc_after :=
                hright_irrel
      have hcond_tail' :
          GoodPath (S := S)
            (muCond (S := S) c.I c.a (muCond (S := S) d.I d.a mu hd_base) hc_after) ds := by
        exact cast
          (by
            simpa using congrArg
              (fun ν => GoodPath (S := S) ν ds) hcomm)
          hcond_tail
      have hind_d :
          PlayerIndep (S := S) (muCond (S := S) d.I d.a mu hd_base) :=
        PlayerIndep_muCond (S := S) (mu := mu) hind (p := d.p) (I := d.I) (a := d.a) hd_base
      have hall_tail : ∀ d', d' ∈ ds -> d'.p = q := by
        intro d' hd'mem
        exact hall d' (by simp [hd'mem])
      have hrec :
          muMarginal (S := S) J
            (muCondPath (S := S)
              (muCond (S := S) c.I c.a (muCond (S := S) d.I d.a mu hd_base) hc_after)
              ds hcond_tail')
            =
          muMarginal (S := S) J
            (muCondPath (S := S) (muCond (S := S) d.I d.a mu hd_base) ds hbase_tail) :=
        ih (mu := muCond (S := S) d.I d.a mu hd_base)
          (hc := hc_after) (hind := hind_d)
          (hall := hall_tail) (hcond := hcond_tail') (hbase := hbase_tail)
      calc
        muMarginal (S := S) J
            (muCondPath (S := S) (muCond (S := S) c.I c.a mu hc) (d :: ds) ⟨hd_cond, hcond_tail⟩)
            =
        muMarginal (S := S) J
            (muCondPath (S := S)
              (muCond (S := S) c.I c.a (muCond (S := S) d.I d.a mu hd_base) hc_after)
              ds hcond_tail') := by
              simp [muCondPath]
              grind
        _ = muMarginal (S := S) J
            (muCondPath (S := S) (muCond (S := S) d.I d.a mu hd_base) ds hbase_tail) := hrec
        _ = muMarginal (S := S) J
            (muCondPath (S := S) mu (d :: ds) ⟨hd_base, hbase_tail⟩) := by
              simp [muCondPath]

theorem muMarginal_condPath_invariant_filter
    (mu : PMF (FlatProfile S)) (path : DecPath S)
    (hind : PlayerIndep (S := S) mu)
    (hgood : GoodPath (S := S) mu path)
    (q : S.Player) (J : S.Infoset q) :
    muMarginal (S := S) J (muCondPath (S := S) mu path hgood) =
    muMarginal (S := S) J
      (muCondPath (S := S) mu (FilterPlayer (S := S) q path)
        (goodPathFilter (S := S) mu path hgood q hind)) := by
  induction path generalizing mu with
  | nil =>
      simp [muCondPath, FilterPlayer]
  | cons c cs ih =>
      rcases hgood with ⟨hc, hcs⟩
      by_cases hq : c.p = q
      · -- Head survives filtering.
        have hind' :
            PlayerIndep (S := S) (muCond (S := S) c.I c.a mu hc) :=
          PlayerIndep_muCond (S := S) (mu := mu) hind
            (p := c.p) (I := c.I) (a := c.a) hc
        have htail :
            muMarginal (S := S) J
              (muCondPath (S := S) (muCond (S := S) c.I c.a mu hc) cs hcs)
              =
            muMarginal (S := S) J
              (muCondPath (S := S) (muCond (S := S) c.I c.a mu hc)
                (FilterPlayer (S := S) q cs)
                (goodPathFilter (S := S)
                  (muCond (S := S) c.I c.a mu hc) cs hcs q hind')) :=
          ih (mu := muCond (S := S) c.I c.a mu hc) hind' hcs
        have hrhs_reduce :
            muMarginal (S := S) J
              (muCondPath (S := S) mu (FilterPlayer (S := S) q (c :: cs))
                (goodPathFilter (S := S) mu (c :: cs) ⟨hc, hcs⟩ q hind))
              =
            muMarginal (S := S) J
              (muCondPath (S := S) (muCond (S := S) c.I c.a mu hc)
                (FilterPlayer (S := S) q cs)
                (goodPathFilter (S := S)
                  (muCond (S := S) c.I c.a mu hc) cs hcs q hind')) := by
          let w2 : GoodPath (S := S) mu (FilterPlayer (S := S) q (c :: cs)) := by
            sorry
          have hsame :
              muCondPath (S := S) (mu := mu)
                (path := FilterPlayer (S := S) q (c :: cs))
                (goodPathFilter (S := S) mu (c :: cs) ⟨hc, hcs⟩ q hind)
                =
              muCondPath (S := S) (mu := mu)
                (path := FilterPlayer (S := S) q (c :: cs)) w2 :=
            muCondPath_proof_irrel (S := S) (mu := mu)
              (path := FilterPlayer (S := S) q (c :: cs))
              (goodPathFilter (S := S) mu (c :: cs) ⟨hc, hcs⟩ q hind) w2
          have hred :
              muCondPath (S := S) (mu := mu)
                (path := FilterPlayer (S := S) q (c :: cs)) w2
                =
              muCondPath (S := S) (muCond (S := S) c.I c.a mu hc)
                (FilterPlayer (S := S) q cs)
                (goodPathFilter (S := S)
                  (muCond (S := S) c.I c.a mu hc) cs hcs q hind') := by
            simp [w2, FilterPlayer]
            sorry
          calc
            muMarginal (S := S) J
                (muCondPath (S := S) mu (FilterPlayer (S := S) q (c :: cs))
                  (goodPathFilter (S := S) mu (c :: cs) ⟨hc, hcs⟩ q hind))
                =
            muMarginal (S := S) J
                (muCondPath (S := S) (mu := mu)
                  (path := FilterPlayer (S := S) q (c :: cs)) w2) := by
                    exact congrArg (muMarginal (S := S) J) hsame
            _ = muMarginal (S := S) J
                (muCondPath (S := S) (muCond (S := S) c.I c.a mu hc)
                  (FilterPlayer (S := S) q cs)
                  (goodPathFilter (S := S)
                    (muCond (S := S) c.I c.a mu hc) cs hcs q hind')) := by
                      exact congrArg (muMarginal (S := S) J) hred
        calc
          muMarginal (S := S) J (muCondPath (S := S) mu (c :: cs) ⟨hc, hcs⟩)
              =
          muMarginal (S := S) J
            (muCondPath (S := S) (muCond (S := S) c.I c.a mu hc) cs hcs) := by
                rfl
          _ = muMarginal (S := S) J
              (muCondPath (S := S) (muCond (S := S) c.I c.a mu hc)
                (FilterPlayer (S := S) q cs)
                (goodPathFilter (S := S)
                  (muCond (S := S) c.I c.a mu hc) cs hcs q hind')) := htail
          _ = muMarginal (S := S) J
              (muCondPath (S := S) mu (FilterPlayer (S := S) q (c :: cs))
                (goodPathFilter (S := S) mu (c :: cs) ⟨hc, hcs⟩ q hind)) := by
                  exact hrhs_reduce.symm
      · -- Head is dropped by filtering.
        have hneq : q ≠ c.p := by
          intro hEq
          exact hq hEq.symm
        have hdrop :
            muMarginal (S := S) J (muCond (S := S) c.I c.a mu hc)
              =
            muMarginal (S := S) J mu :=
          muMarginal_muCond_other (S := S) (mu := mu) hind
            (p := c.p) (q := q) hneq (I := c.I) (J := J) (a := c.a) hc
        have hind' :
            PlayerIndep (S := S) (muCond (S := S) c.I c.a mu hc) :=
          PlayerIndep_muCond (S := S) (mu := mu) hind
            (p := c.p) (I := c.I) (a := c.a) hc
        have htail :
            muMarginal (S := S) J
              (muCondPath (S := S) (muCond (S := S) c.I c.a mu hc) cs hcs)
              =
            muMarginal (S := S) J
              (muCondPath (S := S) (muCond (S := S) c.I c.a mu hc)
                (FilterPlayer (S := S) q cs)
                (goodPathFilter (S := S)
                  (muCond (S := S) c.I c.a mu hc) cs hcs q hind')) :=
          ih (mu := muCond (S := S) c.I c.a mu hc) hind' hcs
        have hflt_cons :
            FilterPlayer (S := S) q (c :: cs) = FilterPlayer (S := S) q cs := by
          simp [FilterPlayer, hq]
        have hcondFilt :
            GoodPath (S := S)
              (muCond (S := S) c.I c.a mu hc)
              (FilterPlayer (S := S) q cs) :=
          goodPathFilter (S := S)
            (muCond (S := S) c.I c.a mu hc) cs hcs q hind'
        have hbaseFilt :
            GoodPath (S := S) mu (FilterPlayer (S := S) q cs) :=
          goodPath_transport_other (S := S)
            (mu := mu) (c := c) (cs := cs) (q := q)
            (hc := hc) (hneq := by exact hneq.symm) (hind := hind) (hcs := hcondFilt)
        have hallFilt : ∀ d, d ∈ FilterPlayer (S := S) q cs -> d.p = q := by
          intro d hdmem
          exact (mem_FilterPlayer_iff (S := S) q d cs).1 hdmem |>.2
        have hinvFilt :
            muMarginal (S := S) J
              (muCondPath (S := S)
                (muCond (S := S) c.I c.a mu hc)
                (FilterPlayer (S := S) q cs) hcondFilt)
              =
            muMarginal (S := S) J
              (muCondPath (S := S) mu (FilterPlayer (S := S) q cs) hbaseFilt) :=
          muMarginal_condPath_other_head_qonly (S := S)
            (mu := mu) (c := c) (hc := hc) (hind := hind) (q := q)
            (hneq := by exact hneq.symm) (path := FilterPlayer (S := S) q cs)
            (hall := hallFilt) (hcond := hcondFilt) (hbase := hbaseFilt) (J := J)
        have hRhsWitness :
            muMarginal (S := S) J
              (muCondPath (S := S) mu
                (FilterPlayer (S := S) q (c :: cs))
                (goodPathFilter (S := S) mu (c :: cs) ⟨hc, hcs⟩ q hind))
            =
            muMarginal (S := S) J
              (muCondPath (S := S) mu (FilterPlayer (S := S) q cs) hbaseFilt) := by
          have hpathEq : FilterPlayer (S := S) q (c :: cs) = FilterPlayer (S := S) q cs :=
            hflt_cons
          have hcast :
              muCondPath (S := S) (mu := mu)
                (path := FilterPlayer (S := S) q (c :: cs))
                (goodPathFilter (S := S) mu (c :: cs) ⟨hc, hcs⟩ q hind)
              =
              muCondPath (S := S) (mu := mu)
                (path := FilterPlayer (S := S) q cs)
                (cast (by simp [hpathEq])
                  (goodPathFilter (S := S) mu (c :: cs) ⟨hc, hcs⟩ q hind)) := by
            exact muCondPath_cast (S := S) (mu := mu) hpathEq
              (goodPathFilter (S := S) mu (c :: cs) ⟨hc, hcs⟩ q hind)
          have hsame :
              muCondPath (S := S) (mu := mu) (path := FilterPlayer (S := S) q cs)
                (cast (by simp [hpathEq])
                  (goodPathFilter (S := S) mu (c :: cs) ⟨hc, hcs⟩ q hind))
              =
              muCondPath (S := S) (mu := mu) (path := FilterPlayer (S := S) q cs) hbaseFilt :=
            muCondPath_proof_irrel (S := S) (mu := mu) (path := FilterPlayer (S := S) q cs) _ _
          calc
            muMarginal (S := S) J
                (muCondPath (S := S) mu
                  (FilterPlayer (S := S) q (c :: cs))
                  (goodPathFilter (S := S) mu (c :: cs) ⟨hc, hcs⟩ q hind))
                =
            muMarginal (S := S) J
                (muCondPath (S := S) (mu := mu)
                  (path := FilterPlayer (S := S) q cs)
                  (cast (by simp [hpathEq])
                    (goodPathFilter (S := S) mu (c :: cs) ⟨hc, hcs⟩ q hind))) := by
                      exact congrArg (muMarginal (S := S) J) hcast
            _ = muMarginal (S := S) J
                (muCondPath (S := S) (mu := mu)
                    (path := FilterPlayer (S := S) q cs) hbaseFilt) := by
                  exact congrArg (muMarginal (S := S) J) hsame
        calc
          muMarginal (S := S) J (muCondPath (S := S) mu (c :: cs) ⟨hc, hcs⟩)
              =
          muMarginal (S := S) J
            (muCondPath (S := S) (muCond (S := S) c.I c.a mu hc) cs hcs) := by
              rfl
          _ = muMarginal (S := S) J
            (muCondPath (S := S) (muCond (S := S) c.I c.a mu hc)
              (FilterPlayer (S := S) q cs) hcondFilt) := by
                sorry
          _ = muMarginal (S := S) J
            (muCondPath (S := S) mu (FilterPlayer (S := S) q cs) hbaseFilt) := hinvFilt
          _ = muMarginal (S := S) J
            (muCondPath (S := S) mu (FilterPlayer (S := S) q (c :: cs))
              (goodPathFilter (S := S) mu (c :: cs) ⟨hc, hcs⟩ q hind)) := by
                exact hRhsWitness.symm

theorem FilterPlayer_path_eq_history
    (tRoot : GameTree S Outcome)
    (hpr : PerfectRecall tRoot)
    {q : S.Player}
    {J : S.Infoset q}
    {pi : DecPath S}
    (hreach : PathReachesInfoset (S := S) (Outcome := Outcome) tRoot pi J) :
    FilterPlayer (S := S) q pi = qHistoryList (S := S) (Outcome := Outcome) tRoot q J := by
  classical
  unfold qHistoryList
  by_cases hEx : ∃ pi', PathReachesInfoset (S := S) (Outcome := Outcome) tRoot pi' J
  · simp only [hEx, ↓reduceDIte]
    let pi0 : DecPath S := Classical.choose hEx
    have hpi0 : PathReachesInfoset (S := S) (Outcome := Outcome) tRoot pi0 J :=
      Classical.choose_spec hEx
    rcases hreach with ⟨h, next, hreach_dec, hhist⟩
    rcases hpi0 with ⟨h0, next0, hreach_dec0, hhist0⟩
    have hPR :
        playerHistory S q h = playerHistory S q h0 :=
      hpr h h0 J next next0 hreach_dec hreach_dec0
    have hview :
        decPathPlayerView (S := S) q pi = decPathPlayerView (S := S) q pi0 := by
      calc
        decPathPlayerView (S := S) q pi = playerHistory S q h := by simpa using hhist.symm
        _ = playerHistory S q h0 := hPR
        _ = decPathPlayerView (S := S) q pi0 := by simpa using hhist0
    have hfilter :
        FilterPlayer (S := S) q pi = FilterPlayer (S := S) q pi0 := by
      calc
        FilterPlayer (S := S) q pi
            =
        List.map (viewToConstraint (S := S) q) (decPathPlayerView (S := S) q pi) := by
              simpa using (map_viewToConstraint_decPathPlayerView (S := S) q pi).symm
        _ =
        List.map (viewToConstraint (S := S) q) (decPathPlayerView (S := S) q pi0) := by
              simp [hview]
        _ = FilterPlayer (S := S) q pi0 := by
              simpa using (map_viewToConstraint_decPathPlayerView (S := S) q pi0)
    simpa [pi0] using hfilter
  · exfalso
    exact hEx ⟨pi, hreach⟩

theorem SubtreeAt_to_PathReachesInfoset
    {tRoot : GameTree S Outcome} {pi : DecPath S}
    {pOwner : S.Player} {I0 : S.Infoset pOwner}
    {next : S.Act I0 → GameTree S Outcome}
    (hsub : SubtreeAt (S := S) (Outcome := Outcome) tRoot pi (.decision I0 next)) :
    PathReachesInfoset (S := S) (Outcome := Outcome) tRoot pi I0 := by
  -- Invalid target: Index in target's type is not a variable (consider using the `cases` tactic instead)
  -- GameTree.decision I0 next
  induction hsub with
  | refl t =>
      refine ⟨[], next, ?_, ?_⟩
      · simpa using (ReachBy.here (.decision I0 next))
      · simp [decPathPlayerView]
  | chance hb ih =>
      rcases ih with ⟨h, nextJ, hr, hhist⟩
      refine ⟨HistoryStep.chance k b :: h, nextJ, ReachBy.chance b hr, ?_⟩
      simpa [playerHistory] using hhist
  | decision hb ih =>
      rcases ih with ⟨h, nextJ, hr, hhist⟩
      -- Core coherence blocker:
      -- In this branch, `SubtreeAt` shrinks the exposed path by dropping the
      -- current decision at the root, while `ReachBy.action` prepends that same
      -- decision step to history. Bridging these two orientations requires a
      -- dedicated lemma relating:
      --   `decPathPlayerView path`
      -- and
      --   `playerHistory (action :: h)` given
      --   `playerHistory h = decPathPlayerView (path ++ [c])`.
      -- This is exactly the remaining missing path/history plumbing.
      sorry

noncomputable def mixedToBehavioralRoot
    (mu : PMF (FlatProfile S)) (tRoot : GameTree S Outcome) : BehavioralProfile S :=
  fun q J =>
    by
      classical
      let hlist := qHistoryList (S := S) (Outcome := Outcome) tRoot q J
      by_cases hgood : Nonempty (GoodPath (S := S) mu hlist)
      · exact muMarginal (S := S) J
          (muCondPath (S := S) mu hlist (Classical.choice hgood))
      · exact muMarginal (S := S) J mu

theorem eval_subtree_correct
    (tRoot : GameTree S Outcome)
    (hpr : PerfectRecall tRoot)
    (mu : PMF (FlatProfile S))
    (hind : PlayerIndep (S := S) mu) :
    ∀ (u : GameTree S Outcome) (pi : DecPath S)
      (hgood : GoodPath (S := S) mu pi),
      SubtreeAt (S := S) (Outcome := Outcome) tRoot pi u ->
      u.evalDist (mixedToBehavioralRoot (S := S) (Outcome := Outcome) mu tRoot) =
      (muCondPath (S := S) mu pi hgood).bind (fun s => u.evalFlat s) := by
  intro u pi hgood hsub
  induction hsub generalizing mu with
  | refl t =>
      -- Root case (`pi = []`): this is exactly the global mixed-vs-behavioral
      -- equivalence at `tRoot`.
      --
      -- Blocker (real): this branch needs a tree-structural induction
      -- (decision/chance disintegration) independent of `SubtreeAt` induction.
      -- The current `SubtreeAt` recursion has no IH here, so this cannot be
      -- derived locally without importing that separate root theorem.
      -- S : InfoStructure
      -- Outcome : Type
      -- tRoot u : GameTree S Outcome
      -- pi : DecPath S
      -- t : GameTree S Outcome
      -- hpr : PerfectRecall t
      -- mu : PMF (FlatProfile S)
      -- hind : PlayerIndep mu
      -- hgood : GoodPath mu []
      -- ⊢ GameTree.evalDist (mixedToBehavioralRoot mu t) t = (muCondPath mu [] hgood).bind fun s ↦ t.evalFlat s
      sorry
  | chance hb ih =>
      -- Unfold chance evaluation on both sides and use IH pointwise over `b`.
      -- The path `pi` does not change in chance steps.
      -- Final script shape: `ext z; simp [GameTree.evalDist, GameTree.evalFlat, ih]`.
      -- Application type mismatch: The argument
      --   hgood
      -- has type
      --   GoodPath mu path✝
      -- of sort `Type` but is expected to have type
      --   PerfectRecall (next✝ b✝)
      -- of sort `Prop` in the application
      --   ih hgood
      simpa using ih (mu := mu) hgood hb
  | decision hb ih =>
      have hreach :
          PathReachesInfoset (S := S) (Outcome := Outcome) tRoot pi I0 :=
        SubtreeAt_to_PathReachesInfoset (S := S) (Outcome := Outcome) hb
      refine eval_subtree_decision_step (S := S) (Outcome := Outcome)
        tRoot hpr mu hind (hgood := hgood) (h_sub := hb) (hreach := hreach) ?_
      intro a hga hsub_a
      exact ih (mu := mu) (pi := pi ++ [{ p := pOwner, I := I0, a := a }]) hga hsub_a

theorem rhs_eq_flat_bind (t : GameTree S Outcome) (muP : MixedProfile S) :
    (mixedProfileJoint (S := S) muP).bind
      (fun pi => t.evalDist (pureProfileToBehavioral (S := S) pi)) =
    (pmfPureToFlat (S := S) (mixedProfileJoint (S := S) muP)).bind
      (fun s => t.evalDist (flatToBehavioral s)) := by
  ext x
  simp only [PMF.bind_apply, tsum_fintype, pmfPureToFlat, PMF.bind_bind, PMF.pure_bind]
  refine Finset.sum_congr rfl ?_
  intro pi _
  have hflat :
      (flatProfileEquivPureProfile (S := S)).symm pi =
      (fun idx : FlatIdx S => pi idx.1 idx.2) := rfl
  have hprof :
      pureProfileToBehavioral (S := S) pi =
      flatToBehavioral (S := S) (fun idx => pi idx.1 idx.2) := by
    funext p I
    rfl
  simp [hflat, hprof]

theorem mixed_to_behavioral_nplayer
    (t : GameTree S Outcome)
    (hpr : PerfectRecall t)
    (mu : PMF (FlatProfile S))
    (hind : PlayerIndep (S := S) mu) :
    t.evalDist (mixedToBehavioralRoot (S := S) (Outcome := Outcome) mu t) =
    mu.bind (fun s => t.evalFlat s) := by
  simpa using eval_subtree_correct (S := S) (Outcome := Outcome)
    t hpr mu hind t [] ⟨⟩ (SubtreeAt.refl t)

theorem kuhn_mixed_to_behavioral
    (t : GameTree S Outcome)
    (hpr : PerfectRecall t)
    (muP : MixedProfile S) :
    ∃ sigma : BehavioralProfile S,
      t.evalDist sigma =
      (mixedProfileJoint (S := S) muP).bind
        (fun pi => t.evalDist (pureProfileToBehavioral (S := S) pi)) := by
  let mu0 : PMF (FlatProfile S) := pmfPureToFlat (S := S) (mixedProfileJoint (S := S) muP)
  refine ⟨mixedToBehavioralRoot (S := S) (Outcome := Outcome) mu0 t, ?_⟩
  calc
    t.evalDist (mixedToBehavioralRoot (S := S) (Outcome := Outcome) mu0 t)
      = mu0.bind (fun s => t.evalFlat s) := by
          simpa [mu0] using mixed_to_behavioral_nplayer (S := S) (Outcome := Outcome) t hpr mu0
            (PlayerIndep_pmfPureToFlat (S := S) muP)
    _ = (mixedProfileJoint (S := S) muP).bind
          (fun pi => t.evalDist (pureProfileToBehavioral (S := S) pi)) := by
      simpa [mu0] using (rhs_eq_flat_bind (S := S) (Outcome := Outcome) t muP).symm

---
-- § 2. Inductive Step: Decision Nodes
---

theorem mixedToBehavioral_context_eq
    (mu : PMF (FlatProfile S)) (tRoot : GameTree S Outcome)
    (hpr : PerfectRecall tRoot) (hind : PlayerIndep (S := S) mu)
    (pi : DecPath S) (hgood : GoodPath (S := S) mu pi)
    {pOwner : S.Player} {I0 : S.Infoset pOwner}
    (hreach : PathReachesInfoset (S := S) (Outcome := Outcome) tRoot pi I0) :
    mixedToBehavioralRoot (S := S) (Outcome := Outcome) mu tRoot pOwner I0 =
      muMarginal (S := S) I0 (muCondPath (S := S) mu pi hgood) := by
  classical
  unfold mixedToBehavioralRoot
  dsimp
  -- Reduce root policy to canonical q-history path at (pOwner, I0).
  let hlist := qHistoryList (S := S) (Outcome := Outcome) tRoot pOwner I0
  by_cases hgoodHist : Nonempty (GoodPath (S := S) mu hlist)
  · simp only [hgoodHist, ↓reduceDIte, hlist]
    -- Replace canonical history by filtered actual path via PR bridge.
    have hhist :
        FilterPlayer (S := S) pOwner pi = hlist :=
      FilterPlayer_path_eq_history (S := S) (Outcome := Outcome)
        tRoot hpr (q := pOwner) (J := I0) (pi := pi) hreach
    -- Then use marginal invariance under removing other-player constraints.
    -- This is exactly `muMarginal_condPath_invariant_filter`.
    -- Rewriting by `hhist` closes the goal.
    have hinv :
        muMarginal (S := S) I0 (muCondPath (S := S) mu pi hgood)
          =
        muMarginal (S := S) I0
          (muCondPath (S := S) mu (FilterPlayer (S := S) pOwner pi)
            (goodPathFilter (S := S) mu pi hgood pOwner hind)) :=
      muMarginal_condPath_invariant_filter (S := S)
        (mu := mu) (path := pi) hind hgood pOwner I0
    let hflt : DecPath S := FilterPlayer (S := S) pOwner pi
    let hcanonF : GoodPath (S := S) mu hflt :=
      goodPathFilter (S := S) mu pi hgood pOwner hind
    have hhlist : hlist = hflt := by
      simpa [hflt] using hhist.symm
    let hcanon : GoodPath (S := S) mu hlist := by
      exact cast (by simp [hhlist]) hcanonF
    have hchoice :
        muCondPath (S := S) (mu := mu) (path := hlist) (Classical.choice hgoodHist)
          =
        muCondPath (S := S) (mu := mu) (path := hlist) hcanon :=
      muCondPath_proof_irrel (S := S) (mu := mu) (path := hlist)
        (Classical.choice hgoodHist) hcanon
    have hinv' :
        muMarginal (S := S) I0
          (muCondPath (S := S) (mu := mu) (path := hlist) hcanon)
          =
        muMarginal (S := S) I0 (muCondPath (S := S) mu pi hgood) := by
      have hcast_flt_list :
          muCondPath (S := S) (mu := mu) (path := hflt) hcanonF
            =
          muCondPath (S := S) (mu := mu) (path := hlist)
            (cast (by simpa [hhlist]) hcanonF) :=
        muCondPath_cast (S := S) (mu := mu)
          (path := hflt) (path' := hlist) (h := by simpa [hhlist]) hcanonF
      have hcast_list :
          muCondPath (S := S) (mu := mu) (path := hlist)
            (cast (by simpa [hhlist]) hcanonF)
            =
          muCondPath (S := S) (mu := mu) (path := hlist) hcanon :=
        muCondPath_proof_irrel (S := S) (mu := mu) (path := hlist)
          (cast (by simpa [hhlist]) hcanonF) hcanon
      have hflt_to_goal :
          muMarginal (S := S) I0
            (muCondPath (S := S) (mu := mu) (path := hflt) hcanonF)
            =
          muMarginal (S := S) I0 (muCondPath (S := S) mu pi hgood) := by
        simpa [hflt, hcanonF] using hinv.symm
      calc
        muMarginal (S := S) I0
            (muCondPath (S := S) (mu := mu) (path := hlist) hcanon)
            =
        muMarginal (S := S) I0
            (muCondPath (S := S) (mu := mu) (path := hlist)
              (cast (by simp [hhlist]) hcanonF)) := by
                exact congrArg (muMarginal (S := S) I0) hcast_list.symm
        _ = muMarginal (S := S) I0
            (muCondPath (S := S) (mu := mu) (path := hflt) hcanonF) := by
              exact congrArg (muMarginal (S := S) I0) hcast_flt_list.symm
        _ = muMarginal (S := S) I0 (muCondPath (S := S) mu pi hgood) := hflt_to_goal
    calc
      muMarginal (S := S) I0
          (muCondPath (S := S) (mu := mu) (path := hlist) (Classical.choice hgoodHist))
          =
      muMarginal (S := S) I0
          (muCondPath (S := S) (mu := mu) (path := hlist) hcanon) := by
            simp [hchoice]
      _ = muMarginal (S := S) I0 (muCondPath (S := S) mu pi hgood) := hinv'
  · simp only [hgoodHist, ↓reduceDIte, hlist]
    have hhist :
        FilterPlayer (S := S) pOwner pi = hlist :=
      FilterPlayer_path_eq_history (S := S) (Outcome := Outcome)
        tRoot hpr (q := pOwner) (J := I0) (pi := pi) hreach
    have hgoodFilt :
        GoodPath (S := S) mu (FilterPlayer (S := S) pOwner pi) :=
      goodPathFilter (S := S) mu pi hgood pOwner hind
    have hgoodHist' : Nonempty (GoodPath (S := S) mu hlist) := by
      refine ⟨cast (by simp only [hhist]) hgoodFilt⟩
    exact (hgoodHist hgoodHist').elim

/--
The inductive step for decision nodes in the evaluation equivalence.
Uses the context lemma to swap the LHS behavioral choice for the RHS marginal.
-/
theorem eval_subtree_decision_step
    (tRoot : GameTree S Outcome) (hpr : PerfectRecall tRoot)
    (mu : PMF (FlatProfile S)) (hind : PlayerIndep (S := S) mu)
    {pOwner : S.Player} {I0 : S.Infoset pOwner} {next : S.Act I0 → GameTree S Outcome}
    {pi : DecPath S} (hgood : GoodPath (S := S) mu pi)
    (h_sub : SubtreeAt (S := S) (Outcome := Outcome) tRoot pi (.decision I0 next))
    (hreach : PathReachesInfoset (S := S) (Outcome := Outcome) tRoot pi I0)
    (ih : ∀ (a : S.Act I0) (hga : GoodPath (S := S) mu (pi ++ [{ p := pOwner, I := I0, a := a }])),
        SubtreeAt (S := S) (Outcome := Outcome) tRoot
          (pi ++ [{ p := pOwner, I := I0, a := a }]) (next a) →
        (next a).evalDist (mixedToBehavioralRoot (S := S) (Outcome := Outcome) mu tRoot) =
        (muCondPath (S := S) mu (pi ++ [{ p := pOwner, I := I0, a := a }]) hga).bind
          (fun s => (next a).evalFlat (S := S) (Outcome := Outcome) s)) :
    (GameTree.decision (S := S) (Outcome := Outcome) I0 next).evalDist
        (mixedToBehavioralRoot (S := S) (Outcome := Outcome) mu tRoot)
      =
    (muCondPath (S := S) mu pi hgood).bind
      (fun s => (GameTree.decision (S := S) (Outcome := Outcome) I0 next).evalFlat
        (S := S) (Outcome := Outcome) s) := by
  classical

  -- Expand evalDist at decision

  -- Replace the behavioral choice at this node using the context lemma
  have hctx :
      mixedToBehavioralRoot (S := S) (Outcome := Outcome) mu tRoot pOwner I0
        =
      muMarginal (S := S) I0 (muCondPath (S := S) mu pi hgood) := by
    exact mixedToBehavioral_context_eq (S := S) (Outcome := Outcome)
      (mu := mu) (tRoot := tRoot) hpr hind pi hgood (pOwner := pOwner) (I0 := I0) hreach

  -- Now LHS is (muMarginal ...).bind (fun a => ...)
  -- Unfold muMarginal and reassociate binds: bind_bind + pure_bind
  simp only [evalDist_decision, GameTree.evalFlat, flatToBehavioral, PMF.pure_bind]

  -- After simp, goal becomes:
  --   (muCondPath ...).bind (fun s => (next (s ⟨pOwner,I0⟩)).evalDist σ)
  -- = (muCondPath ...).bind (fun s => same thing)
  -- BUT to use IH you still need to *rewrite* each (next a).evalDist σ
  -- into bind over muCondPath extended by a. That’s exactly where your
  -- `muCondPath_step_eq_append` and the IH premises enter.
  --
  -- So at this point you should switch to `ext` and a `Finset.sum_congr`
  -- proof over `a`, using IH and `muCondPath_step_eq_append`.
  --
  -- Remaining blocker:
  -- after rewriting with `hctx`, each branch requires an instantiated GoodPath
  -- witness for `pi ++ [{ p := pOwner, I := I0, a := a }]` plus the corresponding
  -- `SubtreeAt` premise to invoke `ih a ...`.
  -- This is exactly the "mass decomposition over marginal-conditioned branches"
  -- glue used in `eval_subtree_correct` decision case.

  simpa [hctx, muMarginal, PMF.bind_bind, PMF.pure_bind]


end EFG
