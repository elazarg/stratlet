import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Probability.ProbabilityMassFunction.Constructions

import GameTheory.EFG
import GameTheory.PMFProduct

namespace EFG

open scoped BigOperators
open Classical

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
      rw [show (∑ s, if s ⟨p, I⟩ = a then mu s / muMarginal (S := S) I mu a else (0 : ENNReal)) =
          (∑ s, (if s ⟨p, I⟩ = a then (mu s : ENNReal) else 0) * (muMarginal (S := S) I mu a)⁻¹) from
        Finset.sum_congr rfl (fun s _ => by split_ifs <;> simp [div_eq_mul_inv]),
        ← Finset.sum_mul]
      have hsum : (∑ s : FlatProfile S, if s ⟨p, I⟩ = a then (mu s : ENNReal) else 0)
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
  simp [pmfPureToFlat, PMF.bind_apply, PMF.pure_apply, tsum_fintype,
    mul_ite, mul_one, mul_zero, eq_comm]

/-- `pmfPureToFlat mu` at flat profile `s` equals `mu` at the corresponding pure profile. -/
lemma pmfPureToFlat_eq (mu : PMF (PureProfile S)) (s : FlatProfile S) :
    pmfPureToFlat (S := S) mu s =
    mu (flatProfileEquivPureProfile (S := S) s) := by
  rw [pmfPureToFlat_apply]
  have : ∀ pi : PureProfile S,
      mu pi * (if flatProfileEquivPureProfile.symm pi = s then 1 else 0) =
      if pi = flatProfileEquivPureProfile (S := S) s then mu pi else 0 := by
    intro pi
    simp only [Equiv.symm_apply_eq]
    split_ifs with h <;> simp [h]
  simp_rw [this]
  simp [Finset.sum_ite_eq']

-- ----------------------------------------------------------------------------
-- 2) Conditioning on the *PureProfile* side (product over players)
-- ----------------------------------------------------------------------------

/-- Predicate on player `p`’s pure strategy at infoset `I`. -/
def Ep {p : S.Player} (I : S.Infoset p) (a : S.Act I) : PureStrategy S p → Prop :=
  fun sp => sp I = a

/-- The flat marginal at infoset I equals the pure-side pushforward. -/
lemma muMarginal_pmfPureToFlat_eq (mu : PMF (PureProfile S))
    {p : S.Player} (I : S.Infoset p) (a : S.Act I) :
    muMarginal (S := S) I (pmfPureToFlat (S := S) mu) a =
    pmfMass (μ := mu) (fun π => Ep (S := S) I a (π p)) := by
  simp only [muMarginal, PMF.bind_apply, PMF.pure_apply, tsum_fintype,
    pmfPureToFlat_eq, mul_ite, mul_one, mul_zero]
  simp only [pmfMass, pmfMask, Ep]
  -- Reindex: FlatProfile → PureProfile via the equivalence
  exact Fintype.sum_equiv (flatProfileEquivPureProfile (S := S)) _ _
    (fun s => by simp [flatProfileEquivPureProfile, eq_comm])

/-- Condition the product PMF on the coordinate event `π p I = a` (depends only on coordinate `p`). -/
noncomputable def pureCond (muP : MixedProfile S) {p : S.Player} (I : S.Infoset p) (a : S.Act I)
    (hE : pmfMass (μ := muP p) (Ep (S := S) I a) ≠ 0) : PMF (PureProfile S) :=
  pmfCond (μ := mixedProfileJoint (S := S) muP)
    (fun π => Ep (S := S) I a (π p))
    (by
      change pmfMass (μ := pmfPi (A := fun q => PureStrategy S q) muP)
        (fun π => Ep (S := S) I a (π p)) ≠ 0
      rwa [pmfMass_pmfPi_coord (A := fun q => PureStrategy S q)
        (σ := muP) (j := p) (E := Ep (S := S) I a)])

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
    (hpa_flat :
      muMarginal (S := S) I
        (pmfPureToFlat (S := S) (mixedProfileJoint (S := S) muP)) a ≠ 0)
    (hE : pmfMass (μ := muP p) (Ep (S := S) I a) ≠ 0) :
    muCond (S := S) I a
      (pmfPureToFlat (S := S) (mixedProfileJoint (S := S) muP)) hpa_flat
      =
    pmfPureToFlat (S := S) (pureCond (S := S) muP I a hE) := by
  let e := flatProfileEquivPureProfile (S := S)
  let mu := mixedProfileJoint (S := S) muP
  -- The two denominators are equal
  have hd_eq : muMarginal (S := S) I (pmfPureToFlat (S := S) mu) a =
      pmfMass (μ := mu) (fun π => Ep (S := S) I a (π p)) :=
    muMarginal_pmfPureToFlat_eq mu I a
  ext s
  -- Expand LHS: muCond at flat profile s
  simp only [muCond, PMF.ofFintype_apply, pmfPureToFlat_eq]
  -- Expand RHS: pmfPureToFlat of pureCond at s = pureCond at e s
  rw [pmfPureToFlat_eq]
  -- Unfold pureCond
  unfold pureCond
  rw [pmfCond_apply]
  simp only [pmfMask]
  -- Key: Ep I a ((e s) p) ↔ s ⟨p, I⟩ = a
  have hep : Ep (S := S) I a ((e s) p) ↔ s ⟨p, I⟩ = a := by
    simp [Ep, e, flatProfileEquivPureProfile]
  by_cases hs : s ⟨p, I⟩ = a
  · simp only [hs, ↓reduceIte, hep.mpr hs, hd_eq]
  · simp only [hs, ↓reduceIte, show ¬ Ep (S := S) I a ((e s) p)
      from (not_congr hep).mpr hs, zero_div]

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
    -- clean way: use `pmfMass_pmfPi_coord` on the product and the fact
    -- `muMarginal` is exactly pushforward along `π ↦ π p I` after `pmfPureToFlat`.
    -- If you don’t want to do that now, you can keep this as `sorry`.
    sorry
  refine ⟨Function.update muP p (pmfCond (μ := muP p) (Ep (S := S) I a) hE), ?_⟩
  -- Use the bridge lemma + the PMFProduct “conditioning a product updates only that coordinate”
  -- on the pure side:
  have hpure :
      pureCond (S := S) muP I a hE
        =
      mixedProfileJoint (S := S)
        (Function.update muP p (pmfCond (μ := muP p) (Ep (S := S) I a) hE)) := by
    -- This is exactly `pmfPi_cond_coord` specialized to index = players, event on coordinate p.
    -- (your PMFProduct lemma)
    ext π
    -- unfold pureCond/mixedProfileJoint and apply the lemma
    -- (this simp is usually enough once the lemma is in scope)
    -- If it doesn’t close, expand `pmfCond_apply` + `pmfPi_apply`.
    sorry
  -- finish
  calc
    muCond (S := S) I a (pmfPureToFlat (S := S) (mixedProfileJoint (S := S) muP)) hpa
        =
      pmfPureToFlat (S := S) (pureCond (S := S) muP I a hE) := by
          simpa using (muCond_eq_pmfPureToFlat_pureCond (S := S) muP I a hpa hE)
    _ = pmfPureToFlat (S := S)
          (mixedProfileJoint (S := S)
            (Function.update muP p (pmfCond (μ := muP p) (Ep (S := S) I a) hE))) := by
          simpa [hpure]
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
    sorry
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
  simp [muMarginal, hrew]
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
    (mu : PMF (FlatProfile S)) → (path : DecPath S) → GoodPath (S := S) mu path → PMF (FlatProfile S)
  | mu, [], _ => mu
  | mu, c :: cs, ⟨h, hgood⟩ =>
      muCondPath (S := S) (mu := muCond (S := S) c.I c.a mu h) (path := cs) hgood

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

def PathReachesInfoset
    (tRoot : GameTree S Outcome)
    (pi : DecPath S)
    {q : S.Player}
    (J : S.Infoset q) : Prop :=
  ∃ u, SubtreeAt (S := S) (Outcome := Outcome) tRoot pi u ∧ DecisionNodeIn J u

noncomputable def qHistoryList (tRoot : GameTree S Outcome) (q : S.Player)
    (J : S.Infoset q) : DecPath S :=
  if h : ∃ pi, PathReachesInfoset (S := S) (Outcome := Outcome) tRoot pi J then
    FilterPlayer (S := S) q (Classical.choose h)
  else
    []

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
  sorry

theorem muMarginal_condPath_invariant_filter
    (mu : PMF (FlatProfile S)) (path : DecPath S)
    (hind : PlayerIndep (S := S) mu)
    (hgood : GoodPath (S := S) mu path)
    (q : S.Player) (J : S.Infoset q)
    (hgoodF : GoodPath (S := S) mu (FilterPlayer (S := S) q path)) :
    muMarginal (S := S) J (muCondPath (S := S) mu path hgood) =
    muMarginal (S := S) J
      (muCondPath (S := S) mu (FilterPlayer (S := S) q path) hgoodF) := by
  sorry

theorem FilterPlayer_path_eq_history
    (tRoot : GameTree S Outcome)
    (hpr : PerfectRecall tRoot)
    {q : S.Player}
    {J : S.Infoset q}
    {pi : DecPath S}
    (hreach : PathReachesInfoset (S := S) (Outcome := Outcome) tRoot pi J) :
    FilterPlayer (S := S) q pi = qHistoryList (S := S) (Outcome := Outcome) tRoot q J := by
  sorry

noncomputable def mixedToBehavioralRoot
    (mu : PMF (FlatProfile S)) (tRoot : GameTree S Outcome)
    (hgoodHist : ∀ (q : S.Player) (J : S.Infoset q),
      GoodPath (S := S) mu
        (qHistoryList (S := S) (Outcome := Outcome) tRoot q J)) :
    BehavioralProfile S :=
  fun q J =>
    muMarginal (S := S) J
      (muCondPath (S := S) mu
        (qHistoryList (S := S) (Outcome := Outcome) tRoot q J)
        (hgoodHist q J))

theorem eval_subtree_correct
    (tRoot : GameTree S Outcome)
    (hpr : PerfectRecall tRoot)
    (mu : PMF (FlatProfile S))
    (hind : PlayerIndep (S := S) mu)
    (hgoodHist : ∀ (q : S.Player) (J : S.Infoset q),
      GoodPath (S := S) mu
        (qHistoryList (S := S) (Outcome := Outcome) tRoot q J)) :
    ∀ (u : GameTree S Outcome) (pi : DecPath S)
      (hgood : GoodPath (S := S) mu pi),
      SubtreeAt (S := S) (Outcome := Outcome) tRoot pi u ->
      u.evalDist (mixedToBehavioralRoot (S := S) (Outcome := Outcome)
        mu tRoot hgoodHist) =
      (muCondPath (S := S) mu pi hgood).bind
        (fun s => u.evalFlat s) := by
  sorry

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
    (hind : PlayerIndep (S := S) mu)
    (hgoodHist : ∀ (q : S.Player) (J : S.Infoset q),
      GoodPath (S := S) mu
        (qHistoryList (S := S) (Outcome := Outcome) t q J)) :
    t.evalDist (mixedToBehavioralRoot (S := S) (Outcome := Outcome)
      mu t hgoodHist) =
    mu.bind (fun s => t.evalFlat s) := by
  simpa using eval_subtree_correct (S := S) (Outcome := Outcome)
    t hpr mu hind hgoodHist t [] ⟨⟩ (SubtreeAt.refl t)

theorem kuhn_mixed_to_behavioral
    (t : GameTree S Outcome)
    (hpr : PerfectRecall t)
    (muP : MixedProfile S) :
    ∃ sigma : BehavioralProfile S,
      t.evalDist sigma =
      (mixedProfileJoint (S := S) muP).bind
        (fun pi => t.evalDist
          (pureProfileToBehavioral (S := S) pi)) := by
  let mu0 : PMF (FlatProfile S) :=
    pmfPureToFlat (S := S) (mixedProfileJoint (S := S) muP)
  -- We need a GoodPath witness for all histories
  -- (this is provable from PlayerIndep + nonzero mass, but
  -- for now we sorry it and thread it through)
  have hgoodHist : ∀ (q : S.Player) (J : S.Infoset q),
      GoodPath (S := S) mu0
        (qHistoryList (S := S) (Outcome := Outcome) t q J) := by
    sorry
  refine ⟨mixedToBehavioralRoot (S := S) (Outcome := Outcome)
    mu0 t hgoodHist, ?_⟩
  calc
    t.evalDist (mixedToBehavioralRoot (S := S) (Outcome := Outcome)
      mu0 t hgoodHist)
      = mu0.bind (fun s => t.evalFlat s) := by
          exact mixed_to_behavioral_nplayer (S := S)
            (Outcome := Outcome) t hpr mu0
            (PlayerIndep_pmfPureToFlat (S := S) muP) hgoodHist
    _ = (mixedProfileJoint (S := S) muP).bind
          (fun pi => t.evalDist
            (pureProfileToBehavioral (S := S) pi)) := by
        exact (rhs_eq_flat_bind (S := S)
          (Outcome := Outcome) t muP).symm

---
-- § 2. Inductive Step: Decision Nodes
---

theorem mixedToBehavioral_context_eq
    (mu : PMF (FlatProfile S)) (tRoot : GameTree S Outcome)
    (hpr : PerfectRecall tRoot) (hind : PlayerIndep (S := S) mu)
    (hgoodHist : ∀ (q : S.Player) (J : S.Infoset q),
      GoodPath (S := S) mu
        (qHistoryList (S := S) (Outcome := Outcome) tRoot q J))
    (pi : DecPath S) (hgood : GoodPath (S := S) mu pi)
    {pOwner : S.Player} {I0 : S.Infoset pOwner}
    (hreach : PathReachesInfoset (S := S) (Outcome := Outcome)
      tRoot pi I0) :
    mixedToBehavioralRoot (S := S) (Outcome := Outcome)
      mu tRoot hgoodHist pOwner I0 =
      muMarginal (S := S) I0
        (muCondPath (S := S) mu pi hgood) := by
  classical
  -- unfold the definition of σroot at (pOwner,I0)
  unfold mixedToBehavioralRoot
  -- PR: the “chosen reaching path” history equals FilterPlayer pOwner pi
  have h_hist :
      FilterPlayer (S := S) pOwner pi =
      qHistoryList (S := S) (Outcome := Outcome) tRoot pOwner I0 := by
    -- this is exactly your PR lemma
    simpa using
      (FilterPlayer_path_eq_history (S := S) (Outcome := Outcome)
        (tRoot := tRoot) hpr (q := pOwner) (J := I0) (pi := pi) hreach)

  -- rewrite qHistoryList into FilterPlayer pOwner pi
  -- and then use “conditioning on others doesn't affect pOwner marginal”
  -- (i.e. marginal depends only on filtered path)
  -- Goal now is: muMarginal I0 (muCondPath mu (qHistoryList ...) ...) =
  --              muMarginal I0 (muCondPath mu pi hgood)
  --
  -- We do it by comparing both to conditioning on FilterPlayer pOwner pi:
  --   muCondPath mu pi      ≈ muCondPath mu (FilterPlayer pOwner pi)
  --   muCondPath mu history ≈ muCondPath mu (FilterPlayer pOwner history)=same
  --
  -- First rewrite left:
  rw [← h_hist]
  -- Now LHS is muMarginal I0 (muCondPath mu (FilterPlayer pOwner pi) _)
  -- RHS is muMarginal I0 (muCondPath mu pi hgood)
  -- Apply invariant lemma (with q = pOwner):
  sorry

/--
The inductive step for decision nodes in the evaluation equivalence.
Uses the context lemma to swap the LHS behavioral choice for the RHS marginal.
-/
theorem eval_subtree_decision_step
    (tRoot : GameTree S Outcome) (hpr : PerfectRecall tRoot)
    (mu : PMF (FlatProfile S)) (hind : PlayerIndep (S := S) mu)
    (hgoodHist : ∀ (q : S.Player) (J : S.Infoset q),
      GoodPath (S := S) mu
        (qHistoryList (S := S) (Outcome := Outcome) tRoot q J))
    {pOwner : S.Player} {I0 : S.Infoset pOwner}
    {next : S.Act I0 → GameTree S Outcome}
    {pi : DecPath S} (hgood : GoodPath (S := S) mu pi)
    (h_sub : SubtreeAt (S := S) (Outcome := Outcome)
      tRoot pi (.decision I0 next))
    (hreach : PathReachesInfoset (S := S) (Outcome := Outcome)
      tRoot pi I0)
    (ih : ∀ (a : S.Act I0)
        (hga : GoodPath (S := S) mu
          (pi ++ [{ p := pOwner, I := I0, a := a }])),
        SubtreeAt (S := S) (Outcome := Outcome)
          tRoot (pi ++ [{ p := pOwner, I := I0, a := a }])
          (next a) →
        (next a).evalDist (mixedToBehavioralRoot (S := S)
          (Outcome := Outcome) mu tRoot hgoodHist) =
        (muCondPath (S := S) mu
          (pi ++ [{ p := pOwner, I := I0, a := a }]) hga).bind
          (fun s => (next a).evalFlat (S := S)
            (Outcome := Outcome) s)) :
    (GameTree.decision (S := S) (Outcome := Outcome)
      I0 next).evalDist
        (mixedToBehavioralRoot (S := S) (Outcome := Outcome)
          mu tRoot hgoodHist)
      =
    (muCondPath (S := S) mu pi hgood).bind
      (fun s => (GameTree.decision (S := S) (Outcome := Outcome)
        I0 next).evalFlat (S := S) (Outcome := Outcome) s) := by
  sorry


end EFG
