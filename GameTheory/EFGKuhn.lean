import GameTheory.EFG
import GameTheory.PMFProduct
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Kuhn's Theorem — Behavioral ↔ Mixed Strategy Equivalence

Kuhn's theorem states that behavioral and mixed strategies are outcome-equivalent
in extensive-form games with perfect recall.

- **Behavioral→Mixed** (§5): The product PMF over independently sampled actions
  induces the same outcome. Requires `NoInfoSetRepeat` (no info set appears
  both at a decision node and in its subtrees), which follows from perfect recall.
- **Mixed→Behavioral** (§6): Requires perfect recall. The conditional behavioral
  strategy induces the same outcome.

## Key definitions

- `GameTree.infoSets` — Finset of info-set IDs used in a tree
- `FinPureStrategy` — pure strategy restricted to a finite set of info sets
- `productBehavioral` — product PMF from a behavioral strategy
- `NoInfoSetRepeat` — no info set repeats on a root-to-leaf path
- `mixedToBehavioral` — conditional behavioral strategy from a mixed strategy
-/

namespace EFG

variable {ι : Type} {S : InfoStructure ι}

-- ============================================================================
-- § 1. GameTree.infoSets
-- ============================================================================

/-- Collect the info-set IDs that appear at decision nodes in the tree. -/
def GameTree.infoSets : GameTree ι S → Finset Nat
  | .terminal _ => ∅
  | .chance _n _μ next => Finset.biUnion Finset.univ (fun b => (next b).infoSets)
  | .decision I next => insert I (Finset.biUnion Finset.univ (fun a => (next a).infoSets))

@[simp] theorem infoSets_terminal (p : ι → ℝ) :
    (GameTree.terminal (S := S) p).infoSets = ∅ := rfl

@[simp] theorem infoSets_chance (n : Nat) (μ : PMF (Fin (n + 1)))
    (next : Fin (n + 1) → GameTree ι S) :
    (GameTree.chance n μ next).infoSets =
    Finset.biUnion Finset.univ (fun b => (next b).infoSets) := rfl

@[simp] theorem infoSets_decision (I : Nat)
    (next : Fin (S.arity I) → GameTree ι S) :
    (GameTree.decision I next).infoSets =
    insert I (Finset.biUnion Finset.univ (fun a => (next a).infoSets)) := rfl

/-- If `DecisionNodeIn I t`, then `I ∈ t.infoSets`. -/
theorem mem_infoSets_of_DecisionNodeIn {I : Nat} {t : GameTree ι S}
    (h : DecisionNodeIn I t) : I ∈ t.infoSets := by
  induction h with
  | root next => exact Finset.mem_insert_self I _
  | in_chance _n _μ _next b _ ih =>
    exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ b, ih⟩
  | in_decision I' _next a _ ih =>
    exact Finset.mem_insert.mpr
      (Or.inr (Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a, ih⟩))

/-- If `I ∈ t.infoSets`, then `DecisionNodeIn I t`. -/
theorem DecisionNodeIn_of_mem_infoSets {I : Nat} {t : GameTree ι S}
    (h : I ∈ t.infoSets) : DecisionNodeIn I t := by
  induction t with
  | terminal _ => simp [GameTree.infoSets] at h
  | chance _n _μ next ih =>
    obtain ⟨b, _, hb⟩ := Finset.mem_biUnion.mp h
    exact .in_chance _ _ _ b (ih b hb)
  | decision I' next ih =>
    rcases Finset.mem_insert.mp h with rfl | hmem
    · exact .root next
    · obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp hmem
      exact .in_decision I' next a (ih a ha)

/-- Info sets of a subtree under a chance node are a subset. -/
theorem infoSets_chance_sub {n : Nat} {μ : PMF (Fin (n + 1))}
    {next : Fin (n + 1) → GameTree ι S} (b : Fin (n + 1)) :
    (next b).infoSets ⊆ (GameTree.chance n μ next).infoSets := by
  intro I hI
  exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ b, hI⟩

/-- Info sets of a subtree under a decision node are a subset. -/
theorem infoSets_decision_sub {I : Nat}
    {next : Fin (S.arity I) → GameTree ι S} (a : Fin (S.arity I)) :
    (next a).infoSets ⊆ (GameTree.decision I next).infoSets := by
  intro J hJ
  exact Finset.mem_insert.mpr
    (Or.inr (Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a, hJ⟩))

-- ============================================================================
-- § 2. Evaluation depends only on used info sets
-- ============================================================================

/-- Two behavioral strategies that agree on used info sets produce the same
    outcome distribution. -/
theorem evalDist_eq_of_agree (t : GameTree ι S)
    (σ₁ σ₂ : BehavioralStrategy S)
    (h : ∀ I ∈ t.infoSets, σ₁ I = σ₂ I) :
    t.evalDist σ₁ = t.evalDist σ₂ := by
  induction t with
  | terminal _ => rfl
  | chance _n _μ next ih =>
    simp only [GameTree.evalDist]
    congr 1; funext b
    exact ih b (fun I hI => h I (infoSets_chance_sub b hI))
  | decision I next ih =>
    simp only [GameTree.evalDist]
    have hI : I ∈ (GameTree.decision I next).infoSets := Finset.mem_insert_self I _
    rw [h I hI]
    congr 1; funext a
    exact ih a (fun J hJ => h J (infoSets_decision_sub a hJ))

/-- Profile version: two behavioral profiles that agree on used info sets
    for the relevant player produce the same outcome distribution. -/
theorem evalDistProfile_eq_of_agree (t : GameTree ι S)
    (σ₁ σ₂ : BehavioralProfile ι S)
    (h : ∀ I ∈ t.infoSets, σ₁ (S.player I) I = σ₂ (S.player I) I) :
    t.evalDistProfile σ₁ = t.evalDistProfile σ₂ := by
  induction t with
  | terminal _ => rfl
  | chance _n _μ next ih =>
    simp only [GameTree.evalDistProfile]
    congr 1; funext b
    exact ih b (fun I hI => h I (infoSets_chance_sub b hI))
  | decision I next ih =>
    simp only [GameTree.evalDistProfile]
    have hI : I ∈ (GameTree.decision I next).infoSets := Finset.mem_insert_self I _
    rw [h I hI]
    congr 1; funext a
    exact ih a (fun J hJ => h J (infoSets_decision_sub a hJ))

-- ============================================================================
-- § 3. Finite restricted strategies
-- ============================================================================

/-- Pure strategy restricted to info sets in `used`. Fintype via Pi.fintype. -/
def FinPureStrategy (S : InfoStructure ι) (used : Finset Nat) :=
  (I : used) → Fin (S.arity I.val)

instance instFintypeFinPureStrategy (used : Finset Nat) :
    Fintype (FinPureStrategy S used) :=
  Pi.instFintype

/-- Extend a finite pure strategy to a full strategy.
    Uses default action 0 for unused info sets. -/
def FinPureStrategy.toFull {used : Finset Nat}
    (s : FinPureStrategy S used) : PureStrategy S :=
  fun I => if h : I ∈ used then s ⟨I, h⟩ else ⟨0, S.arity_pos I⟩

/-- Restrict a full pure strategy to a finite set of info sets. -/
def PureStrategy.restrict (σ : PureStrategy S) (used : Finset Nat) :
    FinPureStrategy S used :=
  fun I => σ I.val

/-- Round-trip: restrict then extend agrees on used info sets. -/
theorem toFull_restrict_eq (σ : PureStrategy S) {used : Finset Nat}
    (I : Nat) (hI : I ∈ used) :
    (σ.restrict used).toFull I = σ I := by
  simp [FinPureStrategy.toFull, PureStrategy.restrict, hI]

/-- Evaluating a pure strategy (as behavioral via PMF.pure) depends only on
    info sets in the tree. -/
theorem evalDist_pure_eq_of_agree_on_infoSets (t : GameTree ι S)
    (s₁ s₂ : PureStrategy S)
    (h : ∀ I ∈ t.infoSets, s₁ I = s₂ I) :
    t.evalDist (fun I => PMF.pure (s₁ I)) = t.evalDist (fun I => PMF.pure (s₂ I)) :=
  evalDist_eq_of_agree t _ _ (fun I hI => by rw [h I hI])

/-- Evaluating a FinPureStrategy.toFull as behavioral agrees with
    evaluating the original full strategy, when restricted to the tree's info sets. -/
theorem evalDist_toFull_restrict (t : GameTree ι S) (σ : PureStrategy S) :
    t.evalDist (fun I => PMF.pure ((σ.restrict t.infoSets).toFull I)) =
    t.evalDist (fun I => PMF.pure (σ I)) :=
  evalDist_pure_eq_of_agree_on_infoSets t _ σ
    (fun I hI => toFull_restrict_eq σ I hI)

-- ============================================================================
-- § 4. Product PMF (via NFG.pmfPi)
-- ============================================================================

/-- Product PMF: independently sample each info set from a behavioral strategy.
    Uses `pmfPi` from NFG.lean: assigns weight `∏ I, σ I (s I)` to profile `s`. -/
noncomputable def productBehavioral (σ : BehavioralStrategy S) (used : Finset Nat) :
    PMF (FinPureStrategy S used) :=
  pmfPi (fun (I : used) => σ I.val)

@[simp] theorem productBehavioral_apply (σ : BehavioralStrategy S) (used : Finset Nat)
    (s : FinPureStrategy S used) :
    (productBehavioral σ used) s = ∏ I : used, σ I.val (s I) := by
  unfold productBehavioral
  exact pmfPi_apply _ s

/-- Factor the product PMF at coordinate `I`: if `g(a, s)` doesn't depend on
    the `I`-th coordinate of `s`, then the product bind factors into
    `(σ I).bind` composed with the full product bind.
    Wrapper around `NFG.pmfPi_bind_factor`. -/
theorem productBehavioral_bind_factor (σ : BehavioralStrategy S)
    (used : Finset Nat) (I : Nat) (hI : I ∈ used) {β : Type}
    (g : Fin (S.arity I) → FinPureStrategy S used → PMF β)
    (hg : ∀ a (s₁ s₂ : FinPureStrategy S used),
          (∀ J : ↥used, J ≠ ⟨I, hI⟩ → s₁ J = s₂ J) → g a s₁ = g a s₂) :
    (productBehavioral σ used).bind (fun s => g (s ⟨I, hI⟩) s) =
    (σ I).bind (fun a => (productBehavioral σ used).bind (fun s => g a s)) := by
  exact pmfPi_bind_factor (fun J : ↥used => σ J.val) ⟨I, hI⟩ g hg

-- ============================================================================
-- § 4b. NoInfoSetRepeat
-- ============================================================================

/-- No info set appears both at a decision node and in its subtrees.
    This ensures the product PMF factorizes correctly at decision nodes.
    Follows from `PerfectRecall` (proved below). -/
def NoInfoSetRepeat : GameTree ι S → Prop
  | .terminal _ => True
  | .chance _n _μ next => ∀ b, NoInfoSetRepeat (next b)
  | .decision I next =>
      (∀ a, I ∉ (next a).infoSets) ∧ (∀ a, NoInfoSetRepeat (next a))

theorem NoInfoSetRepeat_terminal (p : ι → ℝ) :
    NoInfoSetRepeat (GameTree.terminal (S := S) p) := trivial

theorem NoInfoSetRepeat_chance_sub {n : Nat} {μ : PMF (Fin (n + 1))}
    {next : Fin (n + 1) → GameTree ι S}
    (h : NoInfoSetRepeat (GameTree.chance n μ next)) (b : Fin (n + 1)) :
    NoInfoSetRepeat (next b) := h b

theorem NoInfoSetRepeat_decision_root {I : Nat}
    {next : Fin (S.arity I) → GameTree ι S}
    (h : NoInfoSetRepeat (GameTree.decision I next)) (a : Fin (S.arity I)) :
    I ∉ (next a).infoSets := h.1 a

theorem NoInfoSetRepeat_decision_sub {I : Nat}
    {next : Fin (S.arity I) → GameTree ι S}
    (h : NoInfoSetRepeat (GameTree.decision I next)) (a : Fin (S.arity I)) :
    NoInfoSetRepeat (next a) := h.2 a

/-- Every `DecisionNodeIn` witness yields a `ReachBy` path. -/
theorem DecisionNodeIn_to_ReachBy {I : Nat} {t : GameTree ι S}
    (h : DecisionNodeIn I t) :
    ∃ (hist : List HistoryStep) (next : Fin (S.arity I) → GameTree ι S),
      ReachBy hist t (.decision I next) := by
  induction h with
  | root next => exact ⟨[], next, .here _⟩
  | in_chance n μ f b _ ih =>
    obtain ⟨hist, next, hr⟩ := ih
    exact ⟨.chance b.val :: hist, next, .chance b hr⟩
  | in_decision I' f a _ ih =>
    obtain ⟨hist, next, hr⟩ := ih
    exact ⟨.action I' a.val :: hist, next, .action a hr⟩

/-- Perfect recall implies no info set repeats on paths.
    Proof: if info set I appears at the root and in subtree `next a`, then
    the player history at the root is `[]` while at the inner occurrence it
    starts with `(I, a)` — contradicting perfect recall. -/
theorem PerfectRecall_implies_NoInfoSetRepeat [DecidableEq ι]
    (t : GameTree ι S) (hpr : PerfectRecall t) : NoInfoSetRepeat t := by
  induction t with
  | terminal _ => trivial
  | chance n μ next ih =>
    intro b
    apply ih b
    intro h₁ h₂ J next₁ next₂ hr₁ hr₂
    have := hpr (.chance b.val :: h₁) (.chance b.val :: h₂) J next₁ next₂
      (.chance b hr₁) (.chance b hr₂)
    simpa [playerHistory] using this
  | decision I next ih =>
    refine ⟨fun a hmem => ?_, fun a => ?_⟩
    · -- I ∉ (next a).infoSets: by contradiction via perfect recall
      obtain ⟨hist, next₂, hr₂⟩ :=
        DecisionNodeIn_to_ReachBy (DecisionNodeIn_of_mem_infoSets hmem)
      have key := hpr [] (.action I a.val :: hist) I next next₂
        (.here _) (.action a hr₂)
      simp [playerHistory] at key
    · -- NoInfoSetRepeat (next a): perfect recall propagates to subtrees
      apply ih a
      intro h₁ h₂ J next₁ next₂ hr₁ hr₂
      have key := hpr (.action I a.val :: h₁) (.action I a.val :: h₂) J next₁ next₂
        (.action a hr₁) (.action a hr₂)
      simp only [playerHistory] at key
      by_cases heq : S.player I = S.player J <;> simp_all

-- ============================================================================
-- § 5. Behavioral → Mixed
-- ============================================================================

/-- Generalized behavioral→mixed: works for any `used ⊇ t.infoSets`.
    The product PMF over `used` info sets, when composed with deterministic
    evaluation, equals behavioral evaluation.

    Uses `pmfPi_bind_factor` (from PMFProduct.lean) for the decision node case
    and `NoInfoSetRepeat` for the independence condition. -/
theorem behavioral_to_mixed_aux (σ : BehavioralStrategy S) (t : GameTree ι S)
    (used : Finset Nat) (hsub : t.infoSets ⊆ used) (hnr : NoInfoSetRepeat t) :
    (productBehavioral σ used).bind
      (fun s => t.evalDist (fun I => PMF.pure (s.toFull I))) =
    t.evalDist σ := by
  induction t with
  | terminal p =>
    -- (prod σ used).bind (fun _ => PMF.pure p) = PMF.pure p
    simp only [GameTree.evalDist]
    exact PMF.bind_const_pure _ p
  | chance n μ next ih =>
    -- Swap μ.bind and product.bind, then apply IH per branch
    simp only [GameTree.evalDist]
    rw [show (productBehavioral σ used).bind
          (fun s => μ.bind (fun b => (next b).evalDist (fun I => PMF.pure (s.toFull I)))) =
        μ.bind (fun b => (productBehavioral σ used).bind
          (fun s => (next b).evalDist (fun I => PMF.pure (s.toFull I))))
      from PMF.bind_comm _ _ _]
    congr 1; funext b
    exact ih b (fun I hI => hsub (infoSets_chance_sub b hI))
      (NoInfoSetRepeat_chance_sub hnr b)
  | decision I next ih =>
    -- Factor the product at coordinate I using productBehavioral_bind_factor
    simp only [GameTree.evalDist]
    have hI : I ∈ used := hsub (Finset.mem_insert_self I _)
    -- Simplify: PMF.pure(s.toFull I).bind f = f (s.toFull I)
    conv_lhs => arg 2; ext s; rw [PMF.pure_bind]
    -- Rewrite s.toFull I = s ⟨I, hI⟩
    conv_lhs =>
      arg 2; ext s
      rw [show s.toFull I = s ⟨I, hI⟩ from by simp [FinPureStrategy.toFull, hI]]
    -- Apply productBehavioral_bind_factor
    -- Independence: g a s₁ = g a s₂ when s₁, s₂ agree on all coords ≠ I
    have hindep : ∀ (a : Fin (S.arity I)) (s₁ s₂ : FinPureStrategy S used),
        (∀ J : ↥used, J ≠ ⟨I, hI⟩ → s₁ J = s₂ J) →
        (next a).evalDist (fun J => PMF.pure (s₁.toFull J)) =
        (next a).evalDist (fun J => PMF.pure (s₂.toFull J)) := by
      intro a s₁ s₂ hagree
      apply evalDist_eq_of_agree; intro J hJ
      have hJI : J ≠ I := by intro heq; subst heq; exact NoInfoSetRepeat_decision_root hnr a hJ
      have hJused : J ∈ used := hsub (infoSets_decision_sub a hJ)
      change PMF.pure (s₁.toFull J) = PMF.pure (s₂.toFull J)
      congr 1; simp only [FinPureStrategy.toFull, dif_pos hJused]
      exact hagree ⟨J, hJused⟩ (fun heq => hJI (congrArg Subtype.val heq))
    rw [productBehavioral_bind_factor σ used I hI _ hindep]
    congr 1; funext a
    exact ih a (fun J hJ => hsub (infoSets_decision_sub a hJ))
      (NoInfoSetRepeat_decision_sub hnr a)

/-- Behavioral→Mixed: the product PMF over the tree's info sets induces the
    same outcome distribution as behavioral play.
    Requires `NoInfoSetRepeat` (implied by `PerfectRecall`). -/
theorem behavioral_to_mixed (σ : BehavioralStrategy S) (t : GameTree ι S)
    (hnr : NoInfoSetRepeat t) :
    (productBehavioral σ t.infoSets).bind
      (fun s => t.evalDist (fun I => PMF.pure (s.toFull I))) =
    t.evalDist σ :=
  behavioral_to_mixed_aux σ t t.infoSets Finset.Subset.rfl hnr

-- ============================================================================
-- § 6. Mixed → Behavioral (needs perfect recall)
-- ============================================================================

/-- Whether pure strategy `s` reaches a decision node with info set `I` in tree `t`.
    At each decision node, follows the action prescribed by `s.toFull`. At chance
    nodes, reaches `I` if any branch does (conservative: considers all outcomes). -/
def FinPureStrategy.reachesInfoSet {used : Finset Nat}
    (s : FinPureStrategy S used) (t : GameTree ι S) (I : Nat) : Prop :=
  match t with
  | .terminal _ => False
  | .chance _n _μ next => ∃ b, s.reachesInfoSet (next b) I
  | .decision I' next =>
      I = I' ∨ s.reachesInfoSet (next (s.toFull I')) I

open Classical in
/-- Probability that a distribution over finite pure strategies reaches info set `I`. -/
noncomputable def reachProb {used : Finset Nat}
    (μ : PMF (FinPureStrategy S used)) (t : GameTree ι S) (I : Nat) : ENNReal :=
  ∑ s : FinPureStrategy S used,
    if s.reachesInfoSet t I then μ s else 0

open Classical in
/-- Construct a behavioral strategy from a mixed strategy by conditioning.
    At info set `I`: σ(a) = Pr[plan(I) = a ∧ reach(I)] / Pr[reach(I)].
    When reach probability is 0, default to the first action. -/
noncomputable def mixedToBehavioral {used : Finset Nat}
    (μ : PMF (FinPureStrategy S used)) (t : GameTree ι S) :
    BehavioralStrategy S :=
  fun I =>
    if hI : I ∈ used then
      let pReach := reachProb μ t I
      if hpR : pReach = 0 then PMF.pure ⟨0, S.arity_pos I⟩
      else
        PMF.ofFintype (fun a =>
          (∑ s : FinPureStrategy S used,
            if s.reachesInfoSet t I ∧ s ⟨I, hI⟩ = a then μ s else 0) / pReach)
          (by -- sum-to-one from conditional probability
            simp only []
            simp_rw [div_eq_mul_inv]
            rw [← Finset.sum_mul]
            conv_lhs => arg 1; rw [Finset.sum_comm]
            -- Collapse inner sum: for each s, ∑ a, if(reach ∧ s(I)=a) = if(reach) then μ s else 0
            have hcollapse : ∀ s : FinPureStrategy S used,
                (∑ a : Fin (S.arity I),
                  if s.reachesInfoSet t I ∧ s ⟨I, hI⟩ = a then (μ s : ENNReal) else 0) =
                if s.reachesInfoSet t I then μ s else 0 := by
              intro s
              by_cases hr : s.reachesInfoSet t I
              · simp only [hr, true_and, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
              · simp [hr]
            simp_rw [hcollapse]
            -- Now: pReach * pReach⁻¹ = 1
            have hpReach_le : pReach ≤ 1 := by
              calc pReach
                  = ∑ s, if s.reachesInfoSet t I then (μ s : ENNReal) else 0 := rfl
                _ ≤ ∑ s, μ s := Finset.sum_le_sum fun s _ => by split_ifs <;> simp
                _ = 1 := by
                    have h := PMF.tsum_coe μ
                    rwa [tsum_eq_sum (s := Finset.univ)
                      (fun x hx => absurd (Finset.mem_univ x) hx)] at h
            exact ENNReal.mul_inv_cancel hpR
              (ne_of_lt (lt_of_le_of_lt hpReach_le (by simp))))
    else PMF.pure ⟨0, S.arity_pos I⟩

/-- `reachesInfoSet` implies membership in `infoSets`. -/
theorem reachesInfoSet_mem_infoSets {used : Finset Nat}
    (s : FinPureStrategy S used) (t : GameTree ι S) (I : Nat)
    (h : s.reachesInfoSet t I) : I ∈ t.infoSets := by
  induction t with
  | terminal _ => exact absurd h (by simp [FinPureStrategy.reachesInfoSet])
  | chance _n _μ next ih =>
    simp only [FinPureStrategy.reachesInfoSet] at h
    obtain ⟨b, hb⟩ := h
    exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ b, ih b hb⟩
  | decision I' next ih =>
    simp only [FinPureStrategy.reachesInfoSet] at h
    rcases h with rfl | hsub
    · exact Finset.mem_insert_self I _
    · exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_biUnion.mpr
          ⟨s.toFull I', Finset.mem_univ _, ih (s.toFull I') hsub⟩))

/-- Under single-player perfect recall, an info set J ≠ I appears in at most one
    subtree of a decision node I. -/
theorem infoSet_unique_subtree [DecidableEq ι]
    {I : Nat} {next : Fin (S.arity I) → GameTree ι S}
    (hpr : PerfectRecall (GameTree.decision I next))
    {J : Nat} (hsp : S.player I = S.player J)
    (_hJI : J ≠ I)
    (a a' : Fin (S.arity I))
    (ha : J ∈ (next a).infoSets) (ha' : J ∈ (next a').infoSets) :
    a = a' := by
  -- Get ReachBy paths to J from both subtrees
  obtain ⟨hist₁, next₁, hr₁⟩ :=
    DecisionNodeIn_to_ReachBy (DecisionNodeIn_of_mem_infoSets ha)
  obtain ⟨hist₂, next₂, hr₂⟩ :=
    DecisionNodeIn_to_ReachBy (DecisionNodeIn_of_mem_infoSets ha')
  -- Build paths from root: go through action a and a' respectively
  have pr₁ := ReachBy.action a hr₁
  have pr₂ := ReachBy.action a' hr₂
  -- By perfect recall, player histories must be equal
  have key := hpr _ _ J next₁ next₂ pr₁ pr₂
  -- Player history starts with (I, a) resp (I, a') since player I = player J
  simp only [playerHistory, hsp, ite_true, List.cons.injEq, Prod.mk.injEq] at key
  exact Fin.ext key.1.2

/-- Under single-player perfect recall + NoInfoSetRepeat, reaching J ∈ (next a).infoSets
    from `decision I next` requires `s.toFull I = a`. -/
theorem reach_decision_forces_action [DecidableEq ι]
    {I : Nat} {next : Fin (S.arity I) → GameTree ι S} {used : Finset Nat}
    (s : FinPureStrategy S used) (J : Nat) (a : Fin (S.arity I))
    (hJI : J ≠ I)
    (hJa : J ∈ (next a).infoSets)
    (hreach : s.reachesInfoSet (GameTree.decision I next) J)
    (hpr : PerfectRecall (GameTree.decision I next))
    (hnr : NoInfoSetRepeat (GameTree.decision I next))
    (hsp : S.player J = S.player I) :
    s.toFull I = a := by
  simp only [FinPureStrategy.reachesInfoSet] at hreach
  rcases hreach with rfl | hsub
  · exact absurd rfl hJI
  · -- s reaches J in next (s.toFull I), so J ∈ (next (s.toFull I)).infoSets
    have hJa' := reachesInfoSet_mem_infoSets s _ J hsub
    -- By uniqueness, s.toFull I = a
    exact infoSet_unique_subtree hpr hsp.symm hJI _ a hJa' hJa

/-- Under single-player perfect recall, reaching J through a decision node I
    decomposes as: s.toFull I = a ∧ reachesInfoSet in subtree. -/
theorem reachesInfoSet_decision_iff [DecidableEq ι]
    {I : Nat} {next : Fin (S.arity I) → GameTree ι S} {used : Finset Nat}
    (s : FinPureStrategy S used) (J : Nat) (a : Fin (S.arity I))
    (hJI : J ≠ I) (hJa : J ∈ (next a).infoSets)
    (hpr : PerfectRecall (GameTree.decision I next))
    (hnr : NoInfoSetRepeat (GameTree.decision I next))
    (hsp : S.player J = S.player I) :
    s.reachesInfoSet (GameTree.decision I next) J ↔
    (s.toFull I = a ∧ s.reachesInfoSet (next a) J) := by
  constructor
  · intro h
    have ha := reach_decision_forces_action s J a hJI hJa h hpr hnr hsp
    refine ⟨ha, ?_⟩
    simp only [FinPureStrategy.reachesInfoSet] at h
    rcases h with rfl | hsub
    · exact absurd rfl hJI
    · rw [← ha]; exact hsub
  · intro ⟨ha, hr⟩
    simp only [FinPureStrategy.reachesInfoSet]
    exact Or.inr (by rw [ha]; exact hr)

/-- Mixed→Behavioral (single-player / MDP version): under perfect recall
    for a single player, the conditional behavioral strategy induces the same
    outcome as the mixed strategy.

    NOTE: The general game-theoretic per-player version follows by fixing other
    players' strategies and applying this to the resulting single-player game.
    The original multi-player statement (without hsp) is false — a behavioral
    strategy cannot reproduce cross-player correlations in a mixed strategy. -/
theorem mixed_to_behavioral [DecidableEq ι]
    (t : GameTree ι S) (hpr : PerfectRecall t)
    (μ : PMF (FinPureStrategy S t.infoSets))
    (p : ι) (hsp : ∀ I ∈ t.infoSets, S.player I = p) :
    t.evalDist (mixedToBehavioral μ t) =
    μ.bind (fun s => t.evalDist (fun I => PMF.pure (s.toFull I))) := by
  have hnr := PerfectRecall_implies_NoInfoSetRepeat t hpr
  induction t with
  | terminal payoff =>
    simp only [GameTree.evalDist]
    exact (PMF.bind_const_pure μ payoff).symm
  | chance n μ_ch next ih =>
    simp only [GameTree.evalDist]
    -- LHS: μ_ch.bind (fun b => (next b).evalDist (mixedToBehavioral μ (chance n μ_ch next)))
    -- Apply IH to each branch
    conv_lhs => arg 2; ext b; rw [ih b
      (by intro h₁ h₂ J next₁ next₂ hr₁ hr₂
          exact hpr (.chance b.val :: h₁) (.chance b.val :: h₂) J next₁ next₂
            (.chance b hr₁) (.chance b hr₂) |> by simpa [playerHistory])
      (fun I hI => hsp I (infoSets_chance_sub b hI))
      (NoInfoSetRepeat_chance_sub hnr b)]
    -- Now: μ_ch.bind (fun b => μ.bind (fun s => ...)) = μ.bind (fun s => μ_ch.bind (fun b => ...))
    exact (PMF.bind_comm μ_ch μ _).symm
  | decision I next ih =>
    sorry

-- ============================================================================
-- § 7. Combined Kuhn's theorem
-- ============================================================================

/-- Kuhn's theorem: behavioral and mixed strategies are outcome-equivalent
    in games with perfect recall.

    Forward direction (behavioral→mixed): given behavioral σ, the product PMF
    induces the same outcome.

    Backward direction (mixed→behavioral): given a distribution over finite
    pure strategies, the conditional behavioral strategy induces the same outcome. -/
theorem kuhn_equiv [DecidableEq ι]
    (t : GameTree ι S) (hpr : PerfectRecall t)
    (p : ι) (hsp : ∀ I ∈ t.infoSets, S.player I = p) :
    -- Direction 1: every behavioral strategy has an equivalent mixed strategy
    (∀ σ : BehavioralStrategy S,
      ∃ μ : PMF (FinPureStrategy S t.infoSets),
        μ.bind (fun s => t.evalDist (fun I => PMF.pure (s.toFull I))) =
        t.evalDist σ) ∧
    -- Direction 2: every mixed strategy has an equivalent behavioral strategy
    (∀ μ : PMF (FinPureStrategy S t.infoSets),
      ∃ σ : BehavioralStrategy S,
        t.evalDist σ =
        μ.bind (fun s => t.evalDist (fun I => PMF.pure (s.toFull I)))) := by
  have hnr := PerfectRecall_implies_NoInfoSetRepeat t hpr
  exact ⟨
    fun σ => ⟨productBehavioral σ t.infoSets,
      behavioral_to_mixed σ t hnr⟩,
    fun μ => ⟨mixedToBehavioral μ t,
      mixed_to_behavioral t hpr μ p hsp⟩
  ⟩

end EFG
