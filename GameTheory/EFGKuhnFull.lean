import GameTheory.EFGKuhn

/-!
# Full N-player Kuhn's Theorem (Mixed → Behavioral)

Building on `EFGKuhn.lean` (single-player case), this file lifts to the
full N-player theorem via tree restriction.
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
-- § 3. Tree restriction (compile away other players' decisions)
-- ============================================================================

/-- Restrict a tree to player `p`: resolve other players' decisions via `π`,
    keep `p`'s decisions and all chance nodes. -/
noncomputable def restrictToPlayer (p : S.Player) (π : PureProfile S) :
    GameTree S Outcome → GameTree S Outcome
  | .terminal z => .terminal z
  | .chance k μ hk next => .chance k μ hk (fun b => restrictToPlayer p π (next b))
  | .decision (p := q) I next =>
      if q = p then
        .decision I (fun a => restrictToPlayer p π (next a))
      else
        restrictToPlayer p π (next (π q I))

-- ============================================================================
-- § 4. All decision nodes in restricted tree belong to p
-- ============================================================================

theorem restrictToPlayer_hsp (p : S.Player) (π : PureProfile S)
    (t : GameTree S Outcome) :
    ∀ {q : S.Player} {J : S.Infoset q},
      DecisionNodeIn J (restrictToPlayer p π t) → q = p := by
  induction t with
  | terminal _ => intro q J h; cases h
  | chance _k _μ _hk next ih =>
    intro q J h
    simp only [restrictToPlayer] at h
    obtain ⟨b, hb⟩ := DecisionNodeIn_chance_inv h
    exact ih b hb
  | decision I next ih =>
    rename_i q'
    intro q J h
    simp only [restrictToPlayer] at h
    split at h
    · next heq =>
      rcases DecisionNodeIn_decision_inv h with ⟨hp, _⟩ | ⟨a, ha⟩
      · exact hp ▸ heq
      · exact ih a ha
    · exact ih _ h

-- ============================================================================
-- § 5. evalDist commutes with restriction under pure profile
-- ============================================================================

theorem evalDist_restrictToPlayer (p : S.Player) (π : PureProfile S)
    (t : GameTree S Outcome) :
    t.evalDist (pureProfileToBehavioral π) =
    (restrictToPlayer p π t).evalDist (pureProfileToBehavioral π) := by
  induction t with
  | terminal _ => simp [restrictToPlayer]
  | chance _k _μ _hk next ih =>
    simp only [GameTree.evalDist, restrictToPlayer]
    congr 1; funext b; exact ih b
  | decision I next ih =>
    rename_i q
    -- Unfold restrictToPlayer only (not evalDist yet)
    change (GameTree.decision I next).evalDist (pureProfileToBehavioral π) =
      (if q = p then .decision I (fun a => restrictToPlayer p π (next a))
       else restrictToPlayer p π (next (π q I))).evalDist (pureProfileToBehavioral π)
    by_cases hqp : q = p
    · -- q = p: decision node kept
      rw [if_pos hqp]
      simp only [GameTree.evalDist, pureProfileToBehavioral, PMF.pure_bind]
      exact ih (π q I)
    · -- q ≠ p: decision resolved
      rw [if_neg hqp]
      simp only [GameTree.evalDist, pureProfileToBehavioral, PMF.pure_bind]
      exact ih (π q I)

-- ============================================================================
-- § 6. ReachBy target → DecisionNodeIn
-- ============================================================================

/-- If a ReachBy path reaches a decision node, that node is "in" the root tree. -/
theorem DecisionNodeIn_of_ReachBy
    {hist : List (HistoryStep S)} {root : GameTree S Outcome}
    {q : S.Player} {I : S.Infoset q} {next : S.Act I → GameTree S Outcome}
    (hr : ReachBy hist root (.decision I next)) : DecisionNodeIn I root := by
  -- Induction on the ReachBy proof
  cases hr with
  | here => exact .root _
  | chance b hr' =>
    exact .in_chance _ _ _ _ b (DecisionNodeIn_of_ReachBy hr')
  | action a hr' =>
    exact .in_decision _ _ a (DecisionNodeIn_of_ReachBy hr')

-- ============================================================================
-- § 7. Unrestriction lemma: lift paths from restricted tree to original
-- ============================================================================

/-- A ReachBy path in the restricted tree lifts to a path in the original tree
    with the same player-`p` history. -/
theorem ReachBy_unrestrict (p : S.Player) (π : PureProfile S) :
    ∀ (t : GameTree S Outcome) {hist : List (HistoryStep S)}
      {q : S.Player} {J : S.Infoset q} {next_r : S.Act J → GameTree S Outcome},
    ReachBy hist (restrictToPlayer p π t) (.decision J next_r) →
    ∃ (hist' : List (HistoryStep S)) (next_o : S.Act J → GameTree S Outcome),
      ReachBy hist' t (.decision J next_o) ∧
      playerHistory S p hist = playerHistory S p hist' := by
  intro t
  induction t with
  | terminal _ =>
    intro hist q J next_r hr
    simp only [restrictToPlayer] at hr; nomatch hr
  | chance _k _μ _hk next ih =>
    intro hist q J next_r hr
    simp only [restrictToPlayer] at hr
    obtain ⟨b, rest, rfl, hr'⟩ := ReachBy_chance_inv' hr
    obtain ⟨hist', next_o, hro, hph⟩ := ih b hr'
    exact ⟨.chance _ b :: hist', next_o, .chance b hro, by simp [playerHistory, hph]⟩
  | decision I next ih =>
    rename_i q'
    intro hist q J next_r hr
    simp only [restrictToPlayer] at hr
    split at hr
    · next heq =>
      -- q' = p, decision kept in restricted tree
      rcases ReachBy_decision_inv hr with ⟨rfl, hpq, hIJ, _⟩ | ⟨a, rest, rfl, hr'⟩
      · -- ReachBy.here: target IS this node
        -- hpq : q' = q, hIJ : HEq I J
        subst hpq
        have hI := eq_of_heq hIJ; subst hI
        exact ⟨[], next, .here _, rfl⟩
      · -- ReachBy.action a rest
        obtain ⟨hist', next_o, hro, hph⟩ := ih a hr'
        refine ⟨.action q' I a :: hist', next_o, .action a hro, ?_⟩
        simp only [playerHistory]; split <;> simp [hph]
    · next hne =>
      -- q' ≠ p, decision was resolved to next (π q' I)
      obtain ⟨hist', next_o, hro, hph⟩ := ih (π q' I) hr
      refine ⟨.action q' I (π q' I) :: hist', next_o, .action _ hro, ?_⟩
      simp only [playerHistory]
      -- playerHistory S p (.action q' I (π q' I) :: hist')
      -- = if q' = p then ... else playerHistory S p hist'
      -- Since q' ≠ p (hne), this simplifies to playerHistory S p hist' = hph
      have : ¬(q' = p) := hne
      simp only [this, ↓reduceDIte, hph]

-- ============================================================================
-- § 8. Perfect recall preserved under restriction
-- ============================================================================

theorem PerfectRecall_restrictToPlayer (p : S.Player) (π : PureProfile S)
    (t : GameTree S Outcome) (hpr : PerfectRecall t) :
    PerfectRecall (restrictToPlayer p π t) := by
  intro h₁ h₂ r I next₁ next₂ hr₁ hr₂
  -- All decision nodes in restricted tree belong to p, so r = p
  have hrp : r = p := restrictToPlayer_hsp p π t (DecisionNodeIn_of_ReachBy hr₁)
  subst r
  -- Lift both paths to the original tree
  obtain ⟨h₁', next₁', hr₁', hph₁⟩ := ReachBy_unrestrict p π t hr₁
  obtain ⟨h₂', next₂', hr₂', hph₂⟩ := ReachBy_unrestrict p π t hr₂
  -- Perfect recall in original tree gives playerHistory S p h₁' = S p h₂'
  rw [hph₁, hph₂]
  exact hpr h₁' h₂' I next₁' next₂' hr₁' hr₂'

-- ============================================================================
-- § 9. Bridge: FlatProfile ↔ PureProfile evaluation
-- ============================================================================

theorem evalDist_pure_eq_flat (t : GameTree S Outcome) (π : PureProfile S) :
    t.evalDist (pureProfileToBehavioral π) =
    t.evalDist (flatToBehavioral (flatProfileEquivPureProfile.symm π)) := by
  rw [← pureProfileToBehavioral_eq_flatToBehavioral]

noncomputable def pmfPureToFlat (μ : PMF (PureProfile S)) : PMF (FlatProfile S) :=
  μ.bind (fun π => PMF.pure (flatProfileEquivPureProfile.symm π))

-- ============================================================================
-- § 10. Applying the single-player theorem to restricted trees
-- ============================================================================

/-- On a restricted tree (single-player for `p`), the single-player mixed→behavioral
    theorem applies. -/
theorem mixed_behavioral_on_restricted
    (p : S.Player) (π : PureProfile S)
    (t : GameTree S Outcome) (hpr : PerfectRecall t)
    (μ : PMF (FlatProfile S)) :
    let t_p := restrictToPlayer p π t
    t_p.evalDist (fun q => if h : q = p then h ▸ mixedToBehavioralFlat μ t_p
                           else fun I => PMF.pure ⟨0, S.arity_pos q I⟩) =
    μ.bind (fun s => t_p.evalDist (flatToBehavioral s)) :=
  mixed_to_behavioral_flat _ (PerfectRecall_restrictToPlayer p π t hpr) p μ
    (restrictToPlayer_hsp p π t)

-- ============================================================================
-- § 11. Player independence and generalized compatibility lemmas
-- ============================================================================

/-- A flat profile distribution is **player-independent** if there exist per-player
    distributions whose product recovers μ: μ(s) = ∏_p f_p(s_p).
    This is satisfied by `pmfPureToFlat (mixedProfileJoint μP)` with witness `μP`. -/
def PlayerIndep (μ : PMF (FlatProfile S)) : Prop :=
  ∃ (f : (p : S.Player) → PMF (PureStrategy S p)),
    ∀ s : FlatProfile S, μ s = ∏ p, f p (fun I => s ⟨p, I⟩)

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

/-- The flat distribution arising from a mixed profile is player-independent. -/
theorem PlayerIndep_pmfPureToFlat (μP : MixedProfile S) :
    PlayerIndep (pmfPureToFlat (mixedProfileJoint μP)) :=
  ⟨μP, pmfPureToFlat_apply μP⟩

/-- Conditioning on a single player's action preserves player-independence. -/
theorem PlayerIndep_μCond {p_owner : S.Player}
    {I₀ : S.Infoset p_owner} {a : S.Act I₀}
    {μ : PMF (FlatProfile S)} (hind : PlayerIndep μ)
    (hpa : μMarginal I₀ μ a ≠ 0) :
    PlayerIndep (μCond I₀ a μ) := by
  sorry

/-- Generalized chance compatibility: under player-independence + perfect recall,
    `mixedToBehavioralFlat` at a chance node equals that at any specific branch.
    The q-relevant part of the reach condition is the same across branches
    (by perfect recall), and the non-q parts cancel in the ratio (by independence). -/
theorem mixedToBehavioralFlat_chance_eq_general {q : S.Player}
    {μ : PMF (FlatProfile S)} {k : Nat} {μ_c : PMF (Fin k)} {hk : 0 < k}
    {next : Fin k → GameTree S Outcome} {b : Fin k}
    (hpr : PerfectRecall (.chance k μ_c hk next))
    (hind : PlayerIndep μ)
    {J : S.Infoset q} (hJ : DecisionNodeIn J (next b)) :
    mixedToBehavioralFlat (p := q) μ (.chance k μ_c hk next) J =
    mixedToBehavioralFlat (p := q) μ (next b) J := by
  sorry

/-- Generalized decision compatibility: under player-independence + perfect recall,
    `mixedToBehavioralFlat` is compatible across decision nodes.
    For the owner (q = p_owner), reduces to `mixedToBehavioralFlat_decision_sub`.
    For cross-player (q ≠ p_owner), the non-q parts cancel by independence. -/
theorem mixedToBehavioralFlat_decision_sub_general
    {p_owner : S.Player}
    {I₀ : S.Infoset p_owner} {next : S.Act I₀ → GameTree S Outcome} {a : S.Act I₀}
    (hpr : PerfectRecall (.decision I₀ next))
    (μ : PMF (FlatProfile S)) (hpa : μMarginal I₀ μ a ≠ 0)
    (hind : PlayerIndep μ)
    {q : S.Player} {J : S.Infoset q} (hJ : DecisionNodeIn J (next a)) :
    mixedToBehavioralFlat (p := q) μ (.decision (p := p_owner) I₀ next) J =
    mixedToBehavioralFlat (p := q) (μCond I₀ a μ) (next a) J := by
  by_cases hqp : q = p_owner
  · subst hqp
    exact mixedToBehavioralFlat_decision_sub hpr μ hpa hJ
  · sorry -- cross-player case: uses PlayerIndep

-- ============================================================================
-- § 12. N-player mixed → behavioral
-- ============================================================================

/-- The N-player behavioral profile from a flat distribution:
    at each infoset I of player p, condition on reaching I in the original tree. -/
noncomputable def mixedToBehavioralFull
    (μ : PMF (FlatProfile S)) (t : GameTree S Outcome) : BehavioralProfile S :=
  fun p => mixedToBehavioralFlat μ t

/-- **Core N-player lemma**: the full conditional behavioral profile
    gives the same outcome distribution as the original flat distribution.
    Requires the distribution to be player-independent (product across players). -/
theorem mixed_to_behavioral_nplayer (t : GameTree S Outcome) (hpr : PerfectRecall t)
    (μ : PMF (FlatProfile S)) (hind : PlayerIndep μ) :
    t.evalDist (mixedToBehavioralFull μ t) = μ.bind (fun s => t.evalFlat s) := by
  induction t generalizing μ with
  | terminal z =>
    simp only [GameTree.evalDist, GameTree.evalFlat]
    exact (PMF.bind_const_pure μ z).symm
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
-- § 12. Connecting joint pure distribution to flat distribution
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
-- § 13. N-player Kuhn theorem
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
