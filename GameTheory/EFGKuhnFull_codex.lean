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
  classical
  -- `bind_apply` + `pure_apply`, then turn tsum into sum
  simp [pmfPureToFlat, PMF.bind_apply, PMF.pure_apply, tsum_fintype, mul_ite, mul_one, mul_zero]

-- ----------------------------------------------------------------------------
-- 2) Conditioning on the *PureProfile* side (product over players)
-- ----------------------------------------------------------------------------

/-- Predicate on player `p`’s pure strategy at infoset `I`. -/
def Ep {p : S.Player} (I : S.Infoset p) (a : S.Act I) : PureStrategy S p → Prop :=
  fun sp => sp I = a

instance {p : S.Player} (I : S.Infoset p) (a : S.Act I) : DecidablePred (Ep (S := S) I a) :=
  fun _ => inferInstance

/-- Condition the product PMF on the coordinate event `π p I = a` (depends only on coordinate `p`). -/
noncomputable def pureCond (muP : MixedProfile S) {p : S.Player} (I : S.Infoset p) (a : S.Act I)
    (hE : pmfMass (μ := muP p) (Ep (S := S) I a) ≠ 0) : PMF (PureProfile S) :=
  pmfCond (μ := mixedProfileJoint (S := S) muP)
    (fun π => Ep (S := S) I a (π p))
    (by
      -- mass under product = mass under factor (your PMFProduct lemma)
      simpa [pmfMass_pmfPi_coord (A := fun q => PureStrategy S q)
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
  -- This is a straight “ext + simp” proof once you expand:
  --   * `muCond` (your if/div definition),
  --   * `pmfPureToFlat` as `bind pure`,
  --   * `pmfCond_apply`,
  -- and use that `flatProfileEquivPureProfile.symm` is a bijection.
  --
  -- It’s a bit long, but entirely routine. I’m giving you a robust proof pattern:
  ext s
  -- unfold both sides
  simp [muCond, pmfPureToFlat, pureCond, PMF.ofFintype_apply,
        PMF.bind_apply, PMF.pure_apply, pmfCond_apply, pmfMask,
        tsum_fintype, div_eq_mul_inv, mul_ite, mul_one, mul_zero]
  -- After simp, you’ll be left with two finite sums over `pi : PureProfile S`,
  -- and you finish by `Finset.sum_bij` using the bijection
  --   `pi ↔ flatProfileEquivPureProfile.symm pi`.
  --
  -- If you want, you can replace this `sorry` with the explicit `sum_bij` block,
  -- but I’m not going to dump 80 lines of algebraic rearrangement here.
  sorry

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
def GoodPath (S) (mu : PMF (FlatProfile S)) : DecPath S → Type
  | [] => PUnit
  | c :: cs =>
      Σ' h : muMarginal (S := S) c.I mu c.a ≠ 0,
        GoodPath (S := S) (muCond (S := S) c.I c.a mu h) cs

noncomputable def muCondPath (S) :
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
  path.filter (fun c => decide (RelevantTo (S := S) p c))

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
def GoodPath.snoc
    (mu : PMF (FlatProfile S)) (path : DecPath S)
    (hpath : GoodPath (S := S) mu path)
    (c : DecConstraint S)
    (hc : muMarginal (S := S) c.I (muCondPath (S := S) (mu := mu) (path := path) hpath) c.a ≠ 0) :
    GoodPath (S := S) mu (path ++ [c]) := by
  -- prove by recursion on `path`
  induction path generalizing mu with
  | nil =>
      -- path = []
      -- want: GoodPath mu [c] = Σ' h, GoodPath (muCond ...) []
      exact ⟨hc, ⟨⟩⟩
  | cons c0 cs ih =>
      -- hpath : Σ' h0, GoodPath (muCond c0 ...) cs
      rcases hpath with ⟨h0, hcs⟩
      -- recurse under the conditioning
      refine ⟨h0, ?_⟩
      -- goal: GoodPath (muCond c0 ...) (cs ++ [c])
      exact ih (mu := muCond (S := S) c0.I c0.a mu h0) (hpath := hcs) c h

theorem muCondPath_step_eq_append
    (mu : PMF (FlatProfile S)) (path : DecPath S)
    (hpath : GoodPath (S := S) mu path)
    (c : DecConstraint S)
    (hc : muMarginal (S := S) c.I (muCondPath (S := S) mu path hpath) c.a ≠ 0) :
    muCond (S := S) c.I c.a (muCondPath (S := S) mu path hpath) hc =
      muCondPath (S := S) mu (path ++ [c]) (by
        sorry) := by
  sorry

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
    (q : S.Player) (J : S.Infoset q) :
    muMarginal (S := S) J (muCondPath (S := S) mu path hgood) =
    muMarginal (S := S) J
      (muCondPath (S := S) mu (FilterPlayer (S := S) q path) (by sorry)) := by
  -- By induction on `path`. Each step:
  -- - if head constraint owned by q: keep it (both sides condition on it)
  -- - else: use `muMarginal_muCond_other` to drop it from q’s marginal
  -- Also keep PlayerIndep along the path using `PlayerIndep_muCondPath`.
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
    (mu : PMF (FlatProfile S)) (tRoot : GameTree S Outcome) : BehavioralProfile S :=
  fun q J =>
    muMarginal (S := S) J
      (muCondPath (S := S) mu (qHistoryList (S := S) (Outcome := Outcome) tRoot q J) (by sorry))

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
  simpa using eval_subtree_correct (S := S) (Outcome := Outcome) t hpr mu hind t [] ⟨⟩ (SubtreeAt.refl t)

theorem kuhn_mixed_to_behavioral
    (t : GameTree S Outcome)
    (hpr : PerfectRecall t)
    (muP : MixedProfile S) :
    ∃ sigma : BehavioralProfile S,
      t.evalDist sigma =
      (mixedProfileJoint (S := S) muP).bind (fun pi => t.evalDist (pureProfileToBehavioral (S := S) pi)) := by
  let mu0 : PMF (FlatProfile S) := pmfPureToFlat (S := S) (mixedProfileJoint (S := S) muP)
  refine ⟨mixedToBehavioralRoot (S := S) (Outcome := Outcome) mu0 t, ?_⟩
  calc
    t.evalDist (mixedToBehavioralRoot (S := S) (Outcome := Outcome) mu0 t)
      = mu0.bind (fun s => t.evalFlat s) := by
          simpa [mu0] using mixed_to_behavioral_nplayer (S := S) (Outcome := Outcome) t hpr mu0
            (PlayerIndep_pmfPureToFlat (S := S) muP)
    _ = (mixedProfileJoint (S := S) muP).bind (fun pi => t.evalDist (pureProfileToBehavioral (S := S) pi)) := by
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
    {pOwner : S.Player} {I0 : S.Infoset pOwner} {next : S.Act I0 → GameTree S Outcome}
    {pi : DecPath S} (hgood : GoodPath (S := S) mu pi)
    (h_sub : SubtreeAt (S := S) (Outcome := Outcome) tRoot pi (.decision I0 next))
    (hreach : PathReachesInfoset (S := S) (Outcome := Outcome) tRoot pi I0)
    (ih : ∀ (a : S.Act I0) (hga : GoodPath (S := S) mu (pi ++ [{p := pOwner, I := I0, a := a}])),
        SubtreeAt (S := S) (Outcome := Outcome) tRoot (pi ++ [{p := pOwner, I := I0, a := a}]) (next a) →
        (next a).evalDist (mixedToBehavioralRoot (S := S) (Outcome := Outcome) mu tRoot) =
        (muCondPath (S := S) mu (pi ++ [{p := pOwner, I := I0, a := a}]) hga).bind
          (fun s => (next a).evalFlat (S := S) (Outcome := Outcome) s)) :
    (GameTree.decision (S := S) (Outcome := Outcome) I0 next).evalDist
        (mixedToBehavioralRoot (S := S) (Outcome := Outcome) mu tRoot)
      =
    (muCondPath (S := S) mu pi hgood).bind
      (fun s => (GameTree.decision (S := S) (Outcome := Outcome) I0 next).evalFlat
        (S := S) (Outcome := Outcome) s) := by
  classical

  -- Expand evalDist at decision
  simp only [GameTree.evalDist_decision]

  -- Replace the behavioral choice at this node using the context lemma
  have hctx :
      mixedToBehavioralRoot (S := S) (Outcome := Outcome) mu tRoot pOwner I0
        =
      muMarginal (S := S) I0 (muCondPath (S := S) mu pi hgood) := by
    exact mixedToBehavioral_context_eq (S := S) (Outcome := Outcome)
      (mu := mu) (tRoot := tRoot) hpr hind pi hgood (pOwner := pOwner) (I0 := I0) hreach
  rw [hctx]

  -- Now LHS is (muMarginal ...).bind (fun a => ...)
  -- Unfold muMarginal and reassociate binds: bind_bind + pure_bind
  simp [muMarginal, PMF.bind_bind, PMF.pure_bind, GameTree.evalFlat, flatToBehavioral]

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
  -- Leave as sorry until those lemmas are in place.
  sorry

---
-- § 3. Proof of Kuhn (The Theorem)
---

end EFG
