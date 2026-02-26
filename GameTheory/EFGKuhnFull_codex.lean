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
      rw [show (∑ s, if s ⟨p, I⟩ = a then mu s / muMarginal (S := S) I mu a else (0 : ENNReal)) =
          (∑ s, (if s ⟨p, I⟩ = a then (mu s : ENNReal) else 0)
            * (muMarginal (S := S) I mu a)⁻¹) from
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
    simpa [pureCond, mixedProfileJoint] using
      (pmfPi_cond_coord (A := fun q => PureStrategy S q) muP p (Ep (S := S) I a) hE)
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
    simpa [pureCond, mixedProfileJoint] using
      (pmfPi_cond_coord (A := fun r => PureStrategy S r) muP p (Ep (S := S) I a) hE)
  rw [hrew, hpure]
  ext b
  simp [muMarginal_pmfPureToFlat_joint_apply, hpq, Function.update]

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

theorem muCond_proof_irrel
    (mu : PMF (FlatProfile S))
    {p : S.Player} (I : S.Infoset p) (a : S.Act I)
    (h1 h2 : muMarginal (S := S) I mu a ≠ 0) :
    muCond (S := S) I a mu h1 = muCond (S := S) I a mu h2 := by
  ext s
  simp [muCond, PMF.ofFintype_apply]

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

def playerViewOfConstraint (q : S.Player) (c : DecConstraint S) (h : c.p = q) :
    Σ I : S.Infoset q, S.Act I := by
  subst h
  exact ⟨c.I, c.a⟩

def decPathPlayerView (q : S.Player) : DecPath S → List (Σ I : S.Infoset q, S.Act I)
  | [] => []
  | c :: cs =>
      if h : c.p = q then
        playerViewOfConstraint (S := S) q c h :: decPathPlayerView q cs
      else
        decPathPlayerView q cs

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
  induction hflt : FilterPlayer (S := S) q cs generalizing mu with
  | nil =>
      simpa [hflt] using (PUnit.unit : GoodPath (S := S) mu [])
  | cons d ds ih =>
      have hshape :
          GoodPath (S := S) (muCond (S := S) c.I c.a mu hc) (d :: ds) := by
        simpa [hflt] using hcs
      rcases hshape with ⟨hd_cond, hds_cond⟩
      have hindCond :
          PlayerIndep (S := S) (muCond (S := S) c.I c.a mu hc) :=
        PlayerIndep_muCond (S := S) (mu := mu) hind
          (p := c.p) (I := c.I) (a := c.a) hc
      have hdq : d.p = q :=
        head_owner_of_FilterPlayer_cons (S := S) q d ds cs hflt
      -- Remaining hard part:
      -- transport `hd_cond` back to `mu` using `muMarginal_muCond_other`,
      -- then recurse on `hds_cond` with updated measure.
      -- This is exactly the nonzero-witness transport layer.
      sorry

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

def PathReachesInfoset
    (tRoot : GameTree S Outcome)
    (pi : DecPath S)
    {q : S.Player}
    (J : S.Infoset q) : Prop :=
  ∃ u, SubtreeAt (S := S) (Outcome := Outcome) tRoot pi u ∧ DecisionNodeIn J u

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
        -- TODO(blocker): transport RHS witness from
        -- `goodPathFilter (muCond ...) cs ...` to
        -- `goodPathFilter mu (c::cs) ...` after unfolding the `hq` branch.
        -- This is a dependent witness-alignment step for `muCondPath`.
        sorry
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
        -- Remaining blocker: align witnesses/rewrites between
        -- `goodPathFilter mu (c::cs) ...` and the tail witness above, then compose
        -- `hdrop` with `htail`.
        -- TODO(blocker): two-step rewrite
        -- 1) use `hdrop` to replace the head-conditioned marginal by the base marginal,
        -- 2) use `hflt_cons` and `muCondPath_proof_irrel` to identify RHS witnesses.
        sorry

theorem FilterPlayer_path_eq_history
    (tRoot : GameTree S Outcome)
    (hpr : PerfectRecall tRoot)
    {q : S.Player}
    {J : S.Infoset q}
    {pi : DecPath S}
    (hreach : PathReachesInfoset (S := S) (Outcome := Outcome) tRoot pi J) :
    FilterPlayer (S := S) q pi = qHistoryList (S := S) (Outcome := Outcome) tRoot q J := by
  classical
  -- Expand the canonical choice in `qHistoryList`.
  unfold qHistoryList
  by_cases hEx : ∃ pi', PathReachesInfoset (S := S) (Outcome := Outcome) tRoot pi' J
  · simp only [hEx, ↓reduceDIte]
    -- Let `pi0` be the chosen witness path to J.
    let pi0 : DecPath S := Classical.choose hEx
    have hpi0 : PathReachesInfoset (S := S) (Outcome := Outcome) tRoot pi0 J :=
      Classical.choose_spec hEx
    -- Blocker: bridge `PathReachesInfoset/SubtreeAt/DecPath` to the
    -- `PerfectRecall` statement in `EFG.lean` (`ReachBy` + `playerHistory`).
    -- Once available, PR yields equality of q-player histories between `pi` and `pi0`.
    -- Converting those histories back to filtered constraints gives the goal.
    --
    -- Needed interface lemmas:
    --   1) SubtreeAt_to_ReachBy : SubtreeAt tRoot pi u -> ReachBy (decPathToHistory pi) tRoot u
    --   2) DecisionNodeIn_to_decisionShape : DecisionNodeIn J u -> ∃ next, u = .decision J next
    --   3) decPathPlayerView_eq_playerHistory (already proved above)
    --   4) FilterPlayer_eq_decPathPlayerView_asConstraints
    --
    -- With these, conclude by `hpr`.
    sorry
  · exfalso
    exact hEx ⟨pi, hreach⟩

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
      -- Goal:
      --   t.evalDist (mixedToBehavioralRoot mu tRoot) =
      --   mu.bind (fun s => t.evalFlat s)
      -- This is the root case of the invariant and is discharged after the
      -- decision/chance induction infrastructure is in place.
      sorry
  | chance hb ih =>
      -- Unfold chance evaluation on both sides and use IH pointwise over `b`.
      -- The path `pi` does not change in chance steps.
      -- Final script shape: `ext z; simp [GameTree.evalDist, GameTree.evalFlat, ih]`.
      sorry
  | decision hb ih =>
      -- Use context equality to rewrite `mixedToBehavioralRoot ... pOwner I0`
      -- as `muMarginal I0 (muCondPath mu pi hgood)`, then branch on action `a`
      -- and apply IH at path `pi ++ [{p := pOwner, I := I0, a := a}]`.
      --
      -- Required glue:
      --   1) `mixedToBehavioral_context_eq`
      --   2) `muCondPath_step_eq_append`
      --   3) GoodPath witnesses for appended constraints.
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
      -- TODO(blocker): normalize the casted witness `hcanon` back to `hcanonF`
      -- along `hhlist`, then apply `hinv.symm`.
      sorry
    calc
      muMarginal (S := S) I0
          (muCondPath (S := S) (mu := mu) (path := hlist) (Classical.choice hgoodHist))
          =
      muMarginal (S := S) I0
          (muCondPath (S := S) (mu := mu) (path := hlist) hcanon) := by
            simp [hchoice]
      _ = muMarginal (S := S) I0 (muCondPath (S := S) mu pi hgood) := hinv'
  · simp [hlist, hgoodHist]
    -- This branch means no GoodPath witness for canonical history. To conclude
    -- equality with the conditioned marginal, we need contradiction from reach:
    -- reaching I0 provides positive-probability support under the model assumptions.
    -- That positivity bridge is currently missing from the local development.
    sorry

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
  sorry

---
-- § 3. Proof of Kuhn (The Theorem)
---

end EFG
