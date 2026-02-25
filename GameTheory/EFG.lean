import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import GameTheory.SolutionConcepts

/-!
# Extensive-Form Games (EFG)

Extensive-form game trees parameterized by an `InfoStructure` that maps
info-set IDs to player + action arity.

Design:
- `InfoStructure` maps info-set ids to player + arity (with `arity_pos`)
- `GameTree` decision nodes store only the info-set id `I`
- Strategy types are cleanly per-info-set with no `0 < n` guards
- Chance nodes use `Fin (n+1)` branches, so well-formedness is structural
- Evaluation functions have no `dif` guards

## Scope-outs

- **Kuhn's theorem** — see `EFGKuhn.lean`
- **Subgame perfection / sequential equilibrium** — needs belief systems
-/

namespace EFG

-- ============================================================================
-- § 1. InfoStructure
-- ============================================================================

/-- Maps each information-set id to a player and action arity.
    `arity_pos` guarantees every info set has at least one action. -/
structure InfoStructure (ι : Type) where
  player : Nat → ι
  arity : Nat → Nat
  arity_pos : ∀ I, 0 < arity I

-- ============================================================================
-- § 2. GameTree
-- ============================================================================

/-- An extensive-form game tree parameterized by an `InfoStructure`.
    - `terminal` is a leaf with a payoff function.
    - `chance n μ next` is a nature node with `n+1` branches (always ≥ 1),
      distribution `μ`, and subtrees indexed by `Fin (n+1)`.
    - `decision I next` is a player decision node at info set `I`,
      with `S.arity I` actions. Player and arity come from `S`. -/
inductive GameTree (ι : Type) (S : InfoStructure ι) where
  | terminal (payoff : ι → ℝ)
  | chance (n : Nat) (μ : PMF (Fin (n + 1))) (next : Fin (n + 1) → GameTree ι S)
  | decision (I : Nat) (next : Fin (S.arity I) → GameTree ι S)

-- ============================================================================
-- § 3. Strategy types
-- ============================================================================

/-- A pure strategy: at each info set `I`, pick an action in `Fin (S.arity I)`. -/
def PureStrategy (S : InfoStructure ι) := (I : Nat) → Fin (S.arity I)

/-- A behavioral strategy: at each info set `I`, a distribution over actions. -/
def BehavioralStrategy (S : InfoStructure ι) := (I : Nat) → PMF (Fin (S.arity I))

/-- A behavioral strategy profile: each player has their own behavioral strategy. -/
abbrev BehavioralProfile (ι : Type) (S : InfoStructure ι) := ι → BehavioralStrategy S

/-- A pure strategy profile: each player has their own pure strategy. -/
abbrev PureProfile (ι : Type) (S : InfoStructure ι) := ι → PureStrategy S

-- ============================================================================
-- § 4. WFTree
-- ============================================================================

/-- Well-formedness predicate for a game tree.
    No `n > 0` guards needed: chance uses `Fin (n+1)` (always ≥ 1),
    decisions use `S.arity I` (positive by `arity_pos`). -/
inductive WFTree : GameTree ι S → Prop where
  | terminal : ∀ p, WFTree (.terminal p)
  | chance : ∀ n μ next,
      (∀ b, WFTree (next b)) →
      WFTree (.chance n μ next)
  | decision : ∀ I next,
      (∀ a, WFTree (next a)) →
      WFTree (.decision I next)

/-- Every `GameTree` is well-formed: the well-formedness conditions are
    built into the type structure (`arity_pos` for decisions,
    `Fin (n+1)` for chance). -/
theorem allWFTree {ι : Type} {S : InfoStructure ι} (t : GameTree ι S) : WFTree t := by
  induction t with
  | terminal => constructor
  | chance _ _ _ ih => constructor; exact ih
  | decision _ _ ih => constructor; exact ih

-- ============================================================================
-- § 5. Evaluation (no `dif` guards)
-- ============================================================================

/-- Evaluate a game tree under a pure strategy. No guards needed. -/
noncomputable def GameTree.evalTotal {ι : Type} {S : InfoStructure ι}
    (σ : PureStrategy S) : GameTree ι S → (ι → ℝ)
  | .terminal payoff => payoff
  | .chance n μ next => fun i =>
      ∑ b : Fin (n + 1), (μ b).toReal * (next b).evalTotal σ i
  | .decision I next => (next (σ I)).evalTotal σ

/-- Evaluate under a behavioral strategy, returning a PMF over payoffs. -/
noncomputable def GameTree.evalDist {ι : Type} {S : InfoStructure ι}
    (σ : BehavioralStrategy S) : GameTree ι S → PMF (GameTheory.Payoff ι)
  | .terminal payoff => PMF.pure payoff
  | .chance _n μ next => μ.bind (fun b => (next b).evalDist σ)
  | .decision I next => (σ I).bind (fun a => (next a).evalDist σ)

/-- Evaluate under a per-player pure strategy profile. -/
noncomputable def GameTree.evalTotalProfile {ι : Type} {S : InfoStructure ι}
    (σ : PureProfile ι S) : GameTree ι S → (ι → ℝ)
  | .terminal payoff => payoff
  | .chance n μ next => fun i =>
      ∑ b : Fin (n + 1), (μ b).toReal * (next b).evalTotalProfile σ i
  | .decision I next => (next (σ (S.player I) I)).evalTotalProfile σ

/-- Expected utility under a pure strategy, fuel-free. -/
noncomputable def GameTree.euPure {ι : Type} {S : InfoStructure ι}
    (σ : PureStrategy S) (who : ι) (t : GameTree ι S) : ℝ :=
  t.evalTotal σ who

/-- Evaluate under a per-player behavioral profile. -/
noncomputable def GameTree.evalDistProfile {ι : Type} {S : InfoStructure ι}
    (σ : BehavioralProfile ι S) : GameTree ι S → PMF (GameTheory.Payoff ι)
  | .terminal payoff => PMF.pure payoff
  | .chance _n μ next => μ.bind (fun b => (next b).evalDistProfile σ)
  | .decision I next => (σ (S.player I) I).bind (fun a => (next a).evalDistProfile σ)

-- ============================================================================
-- § 6. Simp lemmas
-- ============================================================================

@[simp] theorem evalTotal_terminal {ι : Type} {S : InfoStructure ι}
    (σ : PureStrategy S) (payoff : ι → ℝ) :
    (GameTree.terminal (S := S) payoff).evalTotal σ = payoff := rfl

@[simp] theorem evalTotal_decision {ι : Type} {S : InfoStructure ι}
    (σ : PureStrategy S) (I : Nat) (next : Fin (S.arity I) → GameTree ι S) :
    (GameTree.decision I next).evalTotal σ = (next (σ I)).evalTotal σ := rfl

@[simp] theorem evalTotal_chance {ι : Type} {S : InfoStructure ι}
    (σ : PureStrategy S) (n : Nat) (μ : PMF (Fin (n + 1)))
    (next : Fin (n + 1) → GameTree ι S) :
    (GameTree.chance n μ next).evalTotal σ = fun i =>
    ∑ b : Fin (n + 1), (μ b).toReal * (next b).evalTotal σ i := rfl

@[simp] theorem euPure_eq_evalTotal {ι : Type} {S : InfoStructure ι}
    (σ : PureStrategy S) (who : ι) (t : GameTree ι S) :
    t.euPure σ who = t.evalTotal σ who := rfl

@[simp] theorem evalTotalProfile_terminal {ι : Type} {S : InfoStructure ι}
    (σ : PureProfile ι S) (payoff : ι → ℝ) :
    (GameTree.terminal (S := S) payoff).evalTotalProfile σ = payoff := rfl

@[simp] theorem evalTotalProfile_decision {ι : Type} {S : InfoStructure ι}
    (σ : PureProfile ι S) (I : Nat) (next : Fin (S.arity I) → GameTree ι S) :
    (GameTree.decision I next).evalTotalProfile σ =
    (next (σ (S.player I) I)).evalTotalProfile σ := rfl

@[simp] theorem evalDist_terminal {ι : Type} {S : InfoStructure ι}
    (σ : BehavioralStrategy S) (payoff : GameTheory.Payoff ι) :
    (GameTree.terminal (S := S) payoff).evalDist σ = PMF.pure payoff := rfl

@[simp] theorem evalDist_chance {ι : Type} {S : InfoStructure ι}
    (σ : BehavioralStrategy S)
    (n : Nat) (μ : PMF (Fin (n + 1))) (next : Fin (n + 1) → GameTree ι S) :
    (GameTree.chance n μ next).evalDist σ =
    μ.bind (fun b => (next b).evalDist σ) := rfl

@[simp] theorem evalDist_decision {ι : Type} {S : InfoStructure ι}
    (σ : BehavioralStrategy S)
    (I : Nat) (next : Fin (S.arity I) → GameTree ι S) :
    (GameTree.decision I next).evalDist σ =
    (σ I).bind (fun a => (next a).evalDist σ) := rfl

@[simp] theorem evalDistProfile_terminal {ι : Type} {S : InfoStructure ι}
    (σ : BehavioralProfile ι S) (payoff : GameTheory.Payoff ι) :
    (GameTree.terminal (S := S) payoff).evalDistProfile σ = PMF.pure payoff := rfl

@[simp] theorem evalDistProfile_chance {ι : Type} {S : InfoStructure ι}
    (σ : BehavioralProfile ι S)
    (n : Nat) (μ : PMF (Fin (n + 1))) (next : Fin (n + 1) → GameTree ι S) :
    (GameTree.chance n μ next).evalDistProfile σ =
    μ.bind (fun b => (next b).evalDistProfile σ) := rfl

@[simp] theorem evalDistProfile_decision {ι : Type} {S : InfoStructure ι}
    (σ : BehavioralProfile ι S)
    (I : Nat) (next : Fin (S.arity I) → GameTree ι S) :
    (GameTree.decision I next).evalDistProfile σ =
    (σ (S.player I) I).bind (fun a => (next a).evalDistProfile σ) := rfl

/-- A constant per-player profile agrees with joint strategy evaluation. -/
theorem evalDistProfile_const {ι : Type} {S : InfoStructure ι}
    (σ : BehavioralStrategy S) (t : GameTree ι S) :
    t.evalDistProfile (fun _ => σ) = t.evalDist σ := by
  induction t with
  | terminal _ => rfl
  | chance _n _μ next ih =>
    simp only [GameTree.evalDistProfile, GameTree.evalDist]
    congr 1; funext b; exact ih b
  | decision I next ih =>
    simp only [GameTree.evalDistProfile, GameTree.evalDist]
    congr 1; funext a; exact ih a

/-- A constant per-player pure profile agrees with joint pure strategy evaluation. -/
theorem evalTotalProfile_const {ι : Type} {S : InfoStructure ι}
    (σ : PureStrategy S) (t : GameTree ι S) :
    t.evalTotalProfile (fun _ => σ) = t.evalTotal σ := by
  induction t with
  | terminal _ => rfl
  | chance _n _μ next ih =>
    simp only [GameTree.evalTotalProfile, GameTree.evalTotal]
    funext i; congr 1; funext b; congr 1; exact congrFun (ih b) i
  | decision I next ih =>
    simp only [GameTree.evalTotalProfile, GameTree.evalTotal]
    exact ih _

/-- EFG outcome kernel: behavioral strategy → PMF over payoffs. -/
noncomputable def GameTree.toKernel {ι : Type} {S : InfoStructure ι}
    (t : GameTree ι S) :
    GameTheory.Kernel (BehavioralStrategy S) (GameTheory.Payoff ι) :=
  fun σ => t.evalDist σ

-- ============================================================================
-- § 7. DecisionNodeIn
-- ============================================================================

/-- A decision node with info set `I` appears somewhere inside a `GameTree`. -/
inductive DecisionNodeIn (I : Nat) : GameTree ι S → Prop where
  | root (next) : DecisionNodeIn I (.decision I next)
  | in_chance (n μ next b) : DecisionNodeIn I (next b) →
      DecisionNodeIn I (.chance n μ next)
  | in_decision (I' next a) : DecisionNodeIn I (next a) →
      DecisionNodeIn I (.decision I' next)

/-- No decision node can appear inside a terminal tree. -/
theorem DecisionNodeIn_terminal_false {ι : Type} {S : InfoStructure ι}
    {I : Nat} {payoff : ι → ℝ}
    (h : DecisionNodeIn I (GameTree.terminal (S := S) payoff)) : False := by
  cases h

/-- Inversion for `DecisionNodeIn` on a chance node. -/
theorem DecisionNodeIn_chance_inv {ι : Type} {S : InfoStructure ι}
    {I : Nat} {n : Nat} {μ : PMF (Fin (n + 1))}
    {next : Fin (n + 1) → GameTree ι S}
    (h : DecisionNodeIn I (.chance n μ next)) :
    ∃ b, DecisionNodeIn I (next b) := by
  cases h with
  | in_chance _ _ _ b hsub => exact ⟨b, hsub⟩

/-- Inversion for `DecisionNodeIn` on a decision node. -/
theorem DecisionNodeIn_decision_inv {ι : Type} {S : InfoStructure ι}
    {I I' : Nat} {next : Fin (S.arity I') → GameTree ι S}
    (h : DecisionNodeIn I (.decision I' next)) :
    (I = I') ∨ ∃ a, DecisionNodeIn I (next a) := by
  cases h with
  | root _ => exact Or.inl rfl
  | in_decision _ _ a hsub => exact Or.inr ⟨a, hsub⟩

-- ============================================================================
-- § 8. Swap theorems
-- ============================================================================

/-- Swapping two independent decision nodes preserves the outcome distribution. -/
theorem swap_decisions {ι : Type} {S : InfoStructure ι}
    (σ : BehavioralStrategy S) (I₁ I₂ : Nat)
    (grid : Fin (S.arity I₁) → Fin (S.arity I₂) → GameTree ι S) :
    (GameTree.decision I₁ (fun i =>
      GameTree.decision I₂ (fun j => grid i j))).evalDist σ =
    (GameTree.decision I₂ (fun j =>
      GameTree.decision I₁ (fun i => grid i j))).evalDist σ := by
  simp only [evalDist_decision]
  exact PMF.bind_comm (σ I₁) (σ I₂) (fun i j => (grid i j).evalDist σ)

/-- Swapping a chance node and a decision node preserves the outcome distribution. -/
theorem swap_chance_decision {ι : Type} {S : InfoStructure ι}
    (σ : BehavioralStrategy S) (I : Nat)
    (nc : Nat) (μ : PMF (Fin (nc + 1)))
    (grid : Fin (nc + 1) → Fin (S.arity I) → GameTree ι S) :
    (GameTree.chance nc μ (fun c =>
      GameTree.decision I (fun d => grid c d))).evalDist σ =
    (GameTree.decision I (fun d =>
      GameTree.chance nc μ (fun c => grid c d))).evalDist σ := by
  simp only [evalDist_chance, evalDist_decision]
  exact PMF.bind_comm μ (σ I) (fun c d => (grid c d).evalDist σ)

/-- Swapping two independent chance nodes preserves the outcome distribution. -/
theorem swap_chances {ι : Type} {S : InfoStructure ι}
    (σ : BehavioralStrategy S)
    (n₁ n₂ : Nat) (μ₁ : PMF (Fin (n₁ + 1))) (μ₂ : PMF (Fin (n₂ + 1)))
    (grid : Fin (n₁ + 1) → Fin (n₂ + 1) → GameTree ι S) :
    (GameTree.chance n₁ μ₁ (fun c₁ =>
      GameTree.chance n₂ μ₂ (fun c₂ => grid c₁ c₂))).evalDist σ =
    (GameTree.chance n₂ μ₂ (fun c₂ =>
      GameTree.chance n₁ μ₁ (fun c₁ => grid c₁ c₂))).evalDist σ := by
  simp only [evalDist_chance]
  exact PMF.bind_comm μ₁ μ₂ (fun c₁ c₂ => (grid c₁ c₂).evalDist σ)

-- ============================================================================
-- § 9. toKernelGame + IsNashBehavioral
-- ============================================================================

/-- Convert an EFG game tree to a kernel-based game with per-player strategies. -/
noncomputable def GameTree.toKernelGame {ι : Type} [DecidableEq ι]
    {S : InfoStructure ι} (t : GameTree ι S) : GameTheory.KernelGame ι where
  Strategy := fun _ => BehavioralStrategy S
  Outcome := GameTheory.Payoff ι
  payoff := id
  outcomeKernel := fun σ => t.evalDistProfile σ

/-- Behavioral Nash equilibrium for an EFG tree. -/
def GameTree.IsNashBehavioral {ι : Type} [DecidableEq ι]
    {S : InfoStructure ι} (t : GameTree ι S)
    (σ : BehavioralProfile ι S) : Prop :=
  t.toKernelGame.IsNash σ

-- ============================================================================
-- § 10. Perfect recall
-- ============================================================================

/-- A single step in a play history. -/
inductive HistoryStep where
  | chance (idx : Nat)
  | action (I : Nat) (act : Nat)
  deriving DecidableEq

/-- Reachability: `ReachBy h root target` means following history `h` from
    `root` leads to `target`. History is cons-based (earliest step first). -/
inductive ReachBy {ι : Type} {S : InfoStructure ι} :
    List HistoryStep → GameTree ι S → GameTree ι S → Prop where
  | here (t) : ReachBy [] t t
  | chance {n μ next rest s} (b : Fin (n + 1)) :
      ReachBy rest (next b) s →
      ReachBy (.chance b.val :: rest) (.chance n μ next) s
  | action {I next rest s} (a : Fin (S.arity I)) :
      ReachBy rest (next a) s →
      ReachBy (.action I a.val :: rest) (.decision I next) s

/-- Extract the subsequence of actions by player `who` from a history. -/
def playerHistory [DecidableEq ι] (S : InfoStructure ι) (who : ι) :
    List HistoryStep → List (Nat × Nat)
  | [] => []
  | .action I act :: rest =>
      if S.player I = who then (I, act) :: playerHistory S who rest
      else playerHistory S who rest
  | .chance _ :: rest => playerHistory S who rest

/-- Perfect recall: any two paths to nodes in the same info set `I`
    must have the same player-`I`-owner action history. -/
def PerfectRecall [DecidableEq ι] {S : InfoStructure ι}
    (t : GameTree ι S) : Prop :=
  ∀ (h₁ h₂ : List HistoryStep) (I : Nat)
    (next₁ next₂ : Fin (S.arity I) → GameTree ι S),
    ReachBy h₁ t (.decision I next₁) →
    ReachBy h₂ t (.decision I next₂) →
    playerHistory S (S.player I) h₁ = playerHistory S (S.player I) h₂

-- ============================================================================
-- § 11. Structural lemmas
-- ============================================================================

/-- Terminal trees have perfect recall (vacuously). -/
theorem PerfectRecall_terminal [DecidableEq ι] {S : InfoStructure ι}
    (payoff : ι → ℝ) : PerfectRecall (GameTree.terminal (S := S) payoff) := by
  intro h₁ h₂ I next₁ next₂ hr₁ _hr₂
  -- No ReachBy from a terminal to a decision node: all constructors require
  -- the root to be chance/decision, or h=[] with root=target (but terminal ≠ decision)
  nomatch hr₁

/-- If each info set appears at most once in the tree, then perfect recall holds.
    (No repeated info sets ⇒ all paths to same info set are the same path.) -/
theorem PerfectRecall_single_infoSet [DecidableEq ι] {S : InfoStructure ι}
    (t : GameTree ι S)
    (huniq : ∀ (h₁ h₂ : List HistoryStep) (I : Nat)
      (next₁ next₂ : Fin (S.arity I) → GameTree ι S),
      ReachBy h₁ t (.decision I next₁) →
      ReachBy h₂ t (.decision I next₂) →
      h₁ = h₂ ∧ HEq next₁ next₂) :
    PerfectRecall t := by
  intro h₁ h₂ I next₁ next₂ hr₁ hr₂
  obtain ⟨rfl, _⟩ := huniq h₁ h₂ I next₁ next₂ hr₁ hr₂
  rfl

/-- No path from a terminal node can reach a decision node. -/
theorem ReachBy_terminal_absurd {ι : Type} {S : InfoStructure ι}
    {h : List HistoryStep} {p : ι → ℝ} {I : Nat}
    {next : Fin (S.arity I) → GameTree ι S}
    (hr : ReachBy h (.terminal (S := S) p) (.decision I next)) : False := by
  nomatch hr

/-- Inversion for `ReachBy` from a decision node to a decision node. -/
theorem ReachBy_decision_inv {ι : Type} {S : InfoStructure ι}
    {h : List HistoryStep} {I₀ I : Nat}
    {f : Fin (S.arity I₀) → GameTree ι S}
    {next : Fin (S.arity I) → GameTree ι S}
    (hr : ReachBy h (.decision I₀ f) (.decision I next)) :
    (h = [] ∧ I₀ = I ∧ HEq f next) ∨
    (∃ (a : Fin (S.arity I₀)) (rest : List HistoryStep),
      h = .action I₀ a.val :: rest ∧
      ReachBy rest (f a) (.decision I next)) := by
  cases hr with
  | here => exact Or.inl ⟨rfl, rfl, HEq.rfl⟩
  | action a hr' => exact Or.inr ⟨a, _, rfl, hr'⟩

/-- Inversion for `ReachBy` from a chance node to a decision node. -/
theorem ReachBy_chance_inv' {ι : Type} {S : InfoStructure ι}
    {h : List HistoryStep} {n : Nat} {μ : PMF (Fin (n + 1))}
    {f : Fin (n + 1) → GameTree ι S} {I : Nat}
    {next : Fin (S.arity I) → GameTree ι S}
    (hr : ReachBy h (.chance n μ f) (.decision I next)) :
    ∃ (b : Fin (n + 1)) (rest : List HistoryStep),
      h = .chance b.val :: rest ∧
      ReachBy rest (f b) (.decision I next) := by
  cases hr with
  | chance b hr' => exact ⟨b, _, rfl, hr'⟩

/-- Concatenation lemma: if `ReachBy h₁ root mid` and `ReachBy h₂ mid target`,
    then `ReachBy (h₁ ++ h₂) root target`. This is the key compositionality property
    showing that cons-based histories compose cleanly. -/
theorem ReachBy_append {ι : Type} {S : InfoStructure ι}
    {h₁ h₂ : List HistoryStep}
    {root mid target : GameTree ι S}
    (hr₁ : ReachBy h₁ root mid) (hr₂ : ReachBy h₂ mid target) :
    ReachBy (h₁ ++ h₂) root target := by
  induction hr₁ with
  | here _ => exact hr₂
  | chance b _ ih => exact .chance b (ih hr₂)
  | action a _ ih => exact .action a (ih hr₂)

/-- Splitting lemma: if `ReachBy (h₁ ++ h₂) root target`, then there exists
    a `mid` such that `ReachBy h₁ root mid` and `ReachBy h₂ mid target`. -/
theorem ReachBy_split {ι : Type} {S : InfoStructure ι}
    (h₁ h₂ : List HistoryStep)
    {root target : GameTree ι S}
    (hr : ReachBy (h₁ ++ h₂) root target) :
    ∃ mid, ReachBy h₁ root mid ∧ ReachBy h₂ mid target := by
  induction h₁ generalizing root with
  | nil => exact ⟨root, .here root, hr⟩
  | cons step rest ih =>
    match hr with
    | .chance b htail =>
      obtain ⟨mid, hmid₁, hmid₂⟩ := ih htail
      exact ⟨mid, .chance b hmid₁, hmid₂⟩
    | .action a htail =>
      obtain ⟨mid, hmid₁, hmid₂⟩ := ih htail
      exact ⟨mid, .action a hmid₁, hmid₂⟩

/-- `playerHistory` distributes over concatenation. -/
theorem playerHistory_append [DecidableEq ι] (S : InfoStructure ι) (who : ι)
    (h₁ h₂ : List HistoryStep) :
    playerHistory S who (h₁ ++ h₂) =
    playerHistory S who h₁ ++ playerHistory S who h₂ := by
  induction h₁ with
  | nil => rfl
  | cons step rest ih =>
    cases step with
    | chance idx =>
      simp only [playerHistory, List.cons_append]
      exact ih
    | action I act =>
      simp only [playerHistory, List.cons_append]
      split <;> simp_all

-- Kuhn's theorem (behavioral ↔ mixed strategy equivalence) is in EFGKuhn.lean.
-- It uses `FinPureStrategy` (finite restricted strategies) instead of `PureProfile`
-- (which ranges over all Nat and cannot support a PMF).

end EFG
