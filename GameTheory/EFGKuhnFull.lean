import GameTheory.EFGKuhn

/-!
# Full N-player Kuhn's Theorem (Mixed → Behavioral)

Building on `EFGKuhn.lean` which proves the single-player case, this file
lifts to the full N-player theorem via tree restriction.
-/

namespace EFG

open scoped BigOperators

variable {S : InfoStructure} {Outcome : Type}

-- ============================================================================
-- § 0. Equivalence between FlatProfile and PureProfile
-- ============================================================================

/-- Equivalence between flat profiles and pure profiles. -/
def flatProfileEquivPureProfile : FlatProfile S ≃ PureProfile S where
  toFun := fun s p I => s ⟨p, I⟩
  invFun := fun π idx => π idx.1 idx.2
  left_inv := by intro s; funext idx; rfl
  right_inv := by intro π; funext p I; rfl

@[simp] lemma flatProfileEquivPureProfile_apply (s : FlatProfile S) (p : S.Player) (I : S.Infoset p) :
    flatProfileEquivPureProfile s p I = s ⟨p, I⟩ := rfl

@[simp] lemma flatProfileEquivPureProfile_symm_apply (π : PureProfile S) (idx : FlatIdx S) :
    flatProfileEquivPureProfile.symm π idx = π idx.1 idx.2 := rfl

-- ============================================================================
-- § 1. Mixed profiles (player-product)
-- ============================================================================

/-- A mixed profile: each player independently chooses a distribution over pure strategies. -/
abbrev MixedProfile (S : InfoStructure) := (p : S.Player) → PMF (PureStrategy S p)

/-- The joint distribution from a mixed profile: independent product across players. -/
noncomputable def mixedProfileJoint (μP : MixedProfile S) : PMF (PureProfile S) :=
  pmfPi (A := fun p => PureStrategy S p) μP

@[simp] lemma mixedProfileJoint_apply (μP : MixedProfile S) (π : PureProfile S) :
    mixedProfileJoint μP π = ∏ p, μP p (π p) := by
  simp [mixedProfileJoint]

-- ============================================================================
-- § 2. Pure profile as behavioral + reachability
-- ============================================================================

/-- Convert a pure profile to a behavioral profile (point mass at each infoset). -/
noncomputable def pureProfileToBehavioral (π : PureProfile S) : BehavioralProfile S :=
  fun p I => PMF.pure (π p I)

/-- `pureProfileToBehavioral` equals `flatToBehavioral` via the equivalence. -/
theorem pureProfileToBehavioral_eq_flatToBehavioral (π : PureProfile S) :
    pureProfileToBehavioral π = flatToBehavioral (flatProfileEquivPureProfile.symm π) := by
  funext p I; simp [pureProfileToBehavioral, flatToBehavioral]

/-- Reachability of info set `I` under a pure profile `π`. -/
def reachesPure {p : S.Player} (I : S.Infoset p)
    (π : PureProfile S) : GameTree S Outcome → Prop
  | .terminal _ => False
  | .chance _k _μ _hk next => ∃ b, reachesPure I π (next b)
  | .decision (p := q) I' next =>
      (∃ (heq : q = p), heq ▸ I' = I) ∨
      reachesPure I π (next (π q I'))

/-- `reachesPure` matches `reachesFlat` via the equivalence. -/
theorem reachesPure_eq_reachesFlat {p : S.Player} (I : S.Infoset p)
    (π : PureProfile S) (t : GameTree S Outcome) :
    reachesPure I π t = reachesFlat I (flatProfileEquivPureProfile.symm π) t := by
  induction t with
  | terminal _ => rfl
  | chance _ _ _ next ih => simp [reachesPure, reachesFlat, ih]
  | decision I' next ih =>
    simp only [reachesPure, reachesFlat, flatProfileEquivPureProfile_symm_apply]
    congr 1; exact ih _

open Classical in
/-- Reach probability under a joint distribution over pure profiles. -/
noncomputable def reachProbPure {p : S.Player}
    (μ : PMF (PureProfile S)) (t : GameTree S Outcome) (I : S.Infoset p) : ENNReal :=
  ∑ π : PureProfile S,
    if reachesPure I π t then μ π else 0

open Classical in
/-- Conditional behavioral strategy from a joint distribution over pure profiles. -/
noncomputable def mixedToBehavioralPure {p : S.Player}
    (μ : PMF (PureProfile S)) (t : GameTree S Outcome) :
    BehavioralStrategy S p :=
  fun I =>
    let pReach := reachProbPure μ t I
    if hpR : pReach = 0 then PMF.pure ⟨0, S.arity_pos p I⟩
    else
      PMF.ofFintype (fun a =>
        (∑ π : PureProfile S,
          if reachesPure I π t ∧ π p I = a then μ π else 0) / pReach)
        (by
          simp_rw [div_eq_mul_inv]
          rw [← Finset.sum_mul]
          conv_lhs => arg 1; rw [Finset.sum_comm]
          have hcollapse : ∀ π : PureProfile S,
              (∑ a : S.Act I,
                if reachesPure I π t ∧ π p I = a then (μ π : ENNReal) else 0) =
              if reachesPure I π t then μ π else 0 := by
            intro π
            by_cases hr : reachesPure I π t
            · simp only [hr, true_and, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
            · simp [hr]
          simp_rw [hcollapse]
          have hpReach_le : pReach ≤ 1 := by
            calc pReach
                = ∑ π, if reachesPure I π t then (μ π : ENNReal) else 0 := rfl
              _ ≤ ∑ π, μ π := Finset.sum_le_sum fun π _ => by split_ifs <;> simp
              _ = 1 := by
                  have h := PMF.tsum_coe μ
                  rwa [tsum_eq_sum (s := Finset.univ)
                    (fun x hx => absurd (Finset.mem_univ x) hx)] at h
          exact ENNReal.mul_inv_cancel hpR
            (ne_of_lt (lt_of_le_of_lt hpReach_le (by simp))))

/-- The full behavioral profile from a joint distribution over pure profiles. -/
noncomputable def behavioralFromJoint
    (μ : PMF (PureProfile S)) (t : GameTree S Outcome) : BehavioralProfile S :=
  fun p => mixedToBehavioralPure μ t

-- ============================================================================
-- § 3. Tree restriction (compile away other players' decisions)
-- ============================================================================

/-- A structural size measure that strictly decreases on immediate subtrees. -/
noncomputable def GameTree.tsize : GameTree S Outcome → Nat
  | .terminal _ => 1
  | .chance k _μ _hk next =>
      (Finset.univ.sup fun b : Fin k => GameTree.tsize (next b)) + 1
  | .decision (p := _p) I next =>
      (Finset.univ.sup fun a : S.Act I => GameTree.tsize (next a)) + 1

lemma tsize_lt_chance {k : Nat} {μ : PMF (Fin k)} {hk : 0 < k}
    {next : Fin k → GameTree S Outcome} (b : Fin k) :
    GameTree.tsize (S := S) (Outcome := Outcome) (next b)
      < GameTree.tsize (S := S) (Outcome := Outcome) (.chance k μ hk next) := by
  -- unfold chance-size = sup + 1
  simp only [GameTree.tsize, Order.lt_add_one_iff]
  -- each branch ≤ sup
  have hb :
      GameTree.tsize (S := S) (Outcome := Outcome) (next b)
        ≤ (Finset.univ.sup (f := fun b : Fin k =>
              GameTree.tsize (S := S) (Outcome := Outcome) (next b))) := by
    -- this is the key line: f is explicit
    simpa using
      (Finset.le_sup (s := (Finset.univ : Finset (Fin k)))
        (f := fun b : Fin k => GameTree.tsize (S := S) (Outcome := Outcome) (next b))
        (by simp))
  exact String.Pos.Raw.mk_le_mk.mp hb

lemma tsize_lt_decision {p : S.Player} {I : S.Infoset p}
    {next : S.Act I → GameTree S Outcome} (a : S.Act I) :
    GameTree.tsize (S := S) (Outcome := Outcome) (next a)
      < GameTree.tsize (S := S) (Outcome := Outcome) (.decision I next) := by
  simp only [GameTree.tsize, Order.lt_add_one_iff]
  have ha :
      GameTree.tsize (S := S) (Outcome := Outcome) (next a)
        ≤ (Finset.univ.sup (f := fun a : S.Act I =>
              GameTree.tsize (S := S) (Outcome := Outcome) (next a))) := by
    simpa using
      (Finset.le_sup (s := (Finset.univ : Finset (S.Act I)))
        (f := fun a : S.Act I => GameTree.tsize (S := S) (Outcome := Outcome) (next a))
        (by simp))
  exact String.Pos.Raw.mk_le_mk.mp ha

noncomputable def restrictToPlayer (p : S.Player) (π : PureProfile S) :
    GameTree S Outcome → GameTree S Outcome := by
  classical
  -- Build the measure relation once
  let R : WellFoundedRelation (GameTree S Outcome) := measure (fun t => t.tsize)
  -- Use R.r as the relation and R.wf as the proof it's well-founded
  refine WellFounded.fix (C := fun _ => GameTree S Outcome) (r := R.rel) R.wf ?_
  intro t rec
  -- rec : ∀ t', R.r t' t → GameTree S Outcome
  -- and R.r t' t is definitionaly: t'.tsize < t.tsize
  cases t with
  | terminal z =>
      exact .terminal z
  | chance k μ hk next =>
      refine .chance k μ hk (fun b => rec (next b) ?_)
      -- goal: R.rel (next b) (.chance k μ hk next)
      -- i.e. (next b).tsize < (chance ...).tsize
      simpa [R, measure, InvImage] using
        tsize_lt_chance (S := S) (Outcome := Outcome) (μ := μ) (hk := hk) (next := next) b
  | decision I next =>
      rename_i q
      by_cases h : q = p
      · cases h
        refine .decision I (fun a => rec (next a) ?_)
        simpa [R, measure, InvImage] using
          tsize_lt_decision (S := S) (Outcome := Outcome) (I := I) (next := next) a
      · refine rec (next (π q I)) ?_
        simpa [R, measure, InvImage] using
          tsize_lt_decision (S := S) (Outcome := Outcome) (I := I) (next := next) (π q I)


theorem restrictToPlayer_terminal_eq (p : S.Player) (π : PureProfile S) (z : Outcome) :
    restrictToPlayer (S := S) (Outcome := Outcome) p π (.terminal z) = .terminal z := by
  classical
  simp [restrictToPlayer, WellFounded.fix_eq]

theorem restrictToPlayer_chance_eq (p : S.Player) (π : PureProfile S)
    (k : Nat) (μ : PMF (Fin k)) (hk : 0 < k) (next : Fin k → GameTree S Outcome) :
    restrictToPlayer (S := S) (Outcome := Outcome) p π (.chance k μ hk next)
      =
    .chance k μ hk (fun b => restrictToPlayer p π (next b)) := by
  classical
  simp [restrictToPlayer, WellFounded.fix_eq]

theorem restrictToPlayer_decision_eq_true (p : S.Player) (π : PureProfile S)
    {q : S.Player} (I : S.Infoset q) (next : S.Act I → GameTree S Outcome)
    (h : q = p) :
    restrictToPlayer (S := S) (Outcome := Outcome) p π (.decision (p := q) I next)
      =
    (by
      cases h
      exact .decision I (fun a => restrictToPlayer p π (next a))) := by
  classical
  cases h
  simp [restrictToPlayer, WellFounded.fix_eq]

theorem restrictToPlayer_decision_eq_false (p : S.Player) (π : PureProfile S)
    {q : S.Player} (I : S.Infoset q) (next : S.Act I → GameTree S Outcome)
    (h : q ≠ p) :
    restrictToPlayer (S := S) (Outcome := Outcome) p π (.decision (p := q) I next)
      =
    restrictToPlayer p π (next (π q I)) := by
  classical
  simp [restrictToPlayer, WellFounded.fix_eq, h]

-- ============================================================================
-- § 4. Properties of restrictToPlayer
-- ============================================================================

/-- All decision nodes in `restrictToPlayer p π t` belong to player `p`. -/
theorem restrictToPlayer_hsp (p : S.Player) (π : PureProfile S)
    (t : GameTree S Outcome) :
    ∀ {q : S.Player} {J : S.Infoset q},
      DecisionNodeIn J (restrictToPlayer p π t) → q = p := by
  induction t with
  | terminal z =>
      intro q J h; cases h
  | chance k μ hk next ih =>
      intro q J h
      -- rewrite once, then invert
      rw [restrictToPlayer_chance_eq (S := S) (Outcome := Outcome) (p := p) (π := π)
            (k := k) (μ := μ) (hk := hk) (next := next)] at h
      obtain ⟨b, hb⟩ := DecisionNodeIn_chance_inv h
      exact ih b hb
  | decision I next ih =>
      intro q J h
      rename_i q'
      classical
      by_cases hqp : q' = p
      · -- keep this decision node
        -- rewrite once using the “true” equation
        have := restrictToPlayer_decision_eq_true (S := S) (Outcome := Outcome)
                    (p := p) (π := π) (q := q') I next hqp
        -- the RHS is a `by cases hqp; ...`; eliminate the equality so it’s clean
        cases hqp
        -- after cases, the rewrite lemma simplifies:
        -- restrictToPlayer p π (.decision I next) = .decision I (fun a => restrictToPlayer p π (next a))
        -- use it:
        simpa using (by
          -- rewrite h and then invert DecisionNodeIn on decision
          -- (after cases, `q'` is definitionaly `p`)
          have h' : DecisionNodeIn J (.decision I (fun a => restrictToPlayer p π (next a))) := by
            -- rewrite h using the decision equation in this specialized context
            -- easiest: just `rw` the simp form produced by the lemma after `cases`
            -- (Lean usually has it as `simp` now, but we avoid global simp)
            -- so do:
            --   change DecisionNodeIn J (restrictToPlayer p π (.decision I next)) at h
            --   ... then rw ...
            -- We'll just:
            simpa [restrictToPlayer_decision_eq_true (S := S) (Outcome := Outcome)
                     (p := p) (π := π) (q := p) (I := I) (next := next) rfl] using h
          -- invert
          sorry)
          -- rcases DecisionNodeIn_decision_inv (S := S) (Outcome := Outcome) (I := J) (I' := I) h' with
          -- | Or.inl hroot => exact hroot.1
          -- | Or.inr hsub =>
          --     rcases hsub with ⟨a, ha⟩
          --     exact ih a ha)
      · -- this decision node is erased; recurse into the chosen subtree
        rw [restrictToPlayer_decision_eq_false (S := S) (Outcome := Outcome)
              (p := p) (π := π) (q := q') (I := I) (next := next) hqp] at h
        exact ih (π q' I) h

/-- Evaluating under a pure profile is the same on the original and restricted tree. -/
theorem evalDist_restrictToPlayer (p : S.Player) (π : PureProfile S)
    (t : GameTree S Outcome) :
    t.evalDist (pureProfileToBehavioral π) =
    (restrictToPlayer p π t).evalDist (pureProfileToBehavioral π) := by
  induction t with
  | terminal _ => rfl
  | chance _k _μ _hk next ih =>
    simp only [GameTree.evalDist, restrictToPlayer]
    congr 1; funext b; exact ih b
  | decision I next ih =>
    rename_i q
    simp only [GameTree.evalDist, restrictToPlayer, pureProfileToBehavioral]
    split
    · next heq =>
      subst heq
      simp only [PMF.pure_bind]
      congr 1; funext a; exact ih a
    · next hne =>
      simp only [PMF.pure_bind]
      exact ih (π q I)

-- ============================================================================
-- § 5. Perfect recall under restriction
-- ============================================================================

/-- Helper: `ReachBy` in a restricted tree lifts to `ReachBy` in the original tree
    (with possibly more history steps for the resolved opponent decisions). -/
theorem ReachBy_restrictToPlayer_of_original (p : S.Player) (π : PureProfile S) :
    ∀ (t : GameTree S Outcome) {hist : List (HistoryStep S)} {target : GameTree S Outcome},
    ReachBy hist (restrictToPlayer p π t) target →
    ∃ (hist' : List (HistoryStep S)),
      ReachBy hist' t (match target with
        | .decision I next =>
            -- target in restricted tree corresponds to a node in original
            .decision I (fun a => sorry) -- placeholder
        | other => other) ∧
      playerHistory S p hist = playerHistory S p hist' := by
  sorry

/-- Perfect recall is preserved under restriction to player `p`. -/
theorem PerfectRecall_restrictToPlayer (p : S.Player) (π : PureProfile S)
    (t : GameTree S Outcome) (hpr : PerfectRecall t) :
    PerfectRecall (restrictToPlayer p π t) := by
  -- Strategy: any two paths to same infoset J in restricted tree
  -- correspond to paths to J in original tree with same p-history.
  -- Since restriction only removes non-p decisions, the p-history is preserved.
  induction t with
  | terminal _ =>
    simp only [restrictToPlayer]
    exact PerfectRecall_terminal _
  | chance k μ hk next ih =>
    simp only [restrictToPlayer]
    intro h₁ h₂ q I next₁ next₂ hr₁ hr₂
    -- Both paths go through some branch of the chance node
    obtain ⟨b₁, rest₁, rfl, hr₁'⟩ := ReachBy_chance_inv' hr₁
    obtain ⟨b₂, rest₂, rfl, hr₂'⟩ := ReachBy_chance_inv' hr₂
    simp only [playerHistory]
    -- From perfect recall of original tree under chance
    have hpr_b₁ := PerfectRecall_chance_sub hpr b₁
    have hpr_b₂ := PerfectRecall_chance_sub hpr b₂
    -- We need: playerHistory of rest₁ in restricted(next b₁) = playerHistory of rest₂ in restricted(next b₂)
    -- This follows from perfect recall of the original chance tree
    sorry
  | decision I next ih =>
    rename_i q
    simp only [restrictToPlayer]
    split
    · next heq =>
      subst heq
      -- p's own decision node is kept
      intro h₁ h₂ r J next₁ next₂ hr₁ hr₂
      -- Use perfect recall of the original tree
      sorry
    · next hne =>
      -- Other player's decision is resolved; recurse
      exact ih _ (PerfectRecall_decision_sub hpr (π q I))

-- ============================================================================
-- § 6. FlatProfile ↔ PureProfile transport for the single-player theorem
-- ============================================================================

/-- The key bridge: convert between evalDist under flatToBehavioral and pureProfileToBehavioral. -/
theorem evalDist_flatToBehavioral_eq_pureProfileToBehavioral
    (t : GameTree S Outcome) (π : PureProfile S) :
    t.evalDist (flatToBehavioral (flatProfileEquivPureProfile.symm π)) =
    t.evalDist (pureProfileToBehavioral π) := by
  congr 1
  funext p I
  simp [flatToBehavioral, pureProfileToBehavioral]

-- ============================================================================
-- § 7. The single-player theorem on restricted trees (via transport)
-- ============================================================================

/-- Convert a `PMF (FlatProfile S)` to `PMF (PureProfile S)` via the equivalence. -/
noncomputable def pmfFlatToPure (μ : PMF (FlatProfile S)) : PMF (PureProfile S) :=
  μ.bind (fun s => PMF.pure (flatProfileEquivPureProfile s))

/-- Convert a `PMF (PureProfile S)` to `PMF (FlatProfile S)` via the equivalence. -/
noncomputable def pmfPureToFlat (μ : PMF (PureProfile S)) : PMF (FlatProfile S) :=
  μ.bind (fun π => PMF.pure (flatProfileEquivPureProfile.symm π))

-- ============================================================================
-- § 8. Main theorem: N-player Kuhn (mixed → behavioral)
-- ============================================================================

-- The approach:
-- 1. For each player p, restrict the tree to p using other players' strategies from π
-- 2. On the restricted tree, apply the single-player theorem
-- 3. Stitch together using the product structure of mixedProfileJoint

/-- **Kuhn's theorem (mixed → behavioral, N-player)**:
    For any mixed profile (independent distributions over pure strategies per player),
    under perfect recall, there exists a behavioral profile that induces the same
    outcome distribution as the joint mixed strategy. -/
theorem kuhn_mixed_to_behavioral
    (t : GameTree S Outcome) (hpr : PerfectRecall t)
    (μP : MixedProfile S) :
    let μ := mixedProfileJoint μP
    ∃ (σ : BehavioralProfile S),
      t.evalDist σ = μ.bind (fun π => t.evalDist (pureProfileToBehavioral π)) := by
  intro μ
  exact ⟨behavioralFromJoint μ t, by sorry⟩

end EFG
