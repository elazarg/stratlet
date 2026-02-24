import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import GameTheory.SolutionConcepts

/-!
# Extensive-Form Games (EFG)

Classical extensive-form game representation using `Fin`-indexed game trees
with terminal nodes, chance nodes (carrying `PMF`), and decision nodes.

Provides:
- `GameTree` — the tree type (terminal / chance / decision)
- `BehavioralStrategy`, `BehavioralProfile`, `PureStrategy`, `PureProfile`
- `evalDist`, `evalDistProfile`, `evalTotal` — evaluation functions
- `toKernelGame` — conversion to `KernelGame`
- `IsNashBehavioral` — behavioral Nash equilibrium (= `KernelGame.IsNash`)
- Swap theorems (`swap_decisions`, `swap_chance_decision`, `swap_chances`)

## Scope-outs

- **`WFTree`**: structural well-formedness (n > 0). Not required by `evalDist`
  (which handles n=0 defensively). Would be needed for reachability reasoning.
- **`InfoSetConsistent`**: the standard game-theoretic requirement that nodes
  in the same information set agree on player and arity. Would be needed for
  Kuhn's theorem (behavioral ↔ mixed equivalence under perfect recall).
- **Subgame perfection / sequential equilibrium** — needs belief systems.
- **Kuhn's theorem** — needs a perfect-recall predicate on top of `InfoSetConsistent`.
-/

namespace EFG

/-- An extensive-form game tree.
  - `ι` is the type of players.
  - `terminal` is a leaf with a payoff function.
  - `chance n μ next` is a nature node with `n` branches, distribution `μ`,
    and subtrees indexed by `Fin n`.
  - `decision infoSetId player n next` is a player decision node with `n` actions,
    identified by information set `infoSetId`, subtrees indexed by `Fin n`.

    **Information sets**: `infoSetId` groups decision nodes that a player cannot
    distinguish. All nodes sharing an `infoSetId` must belong to the same player
    and have the same action arity (see `InfoSetConsistent`). A behavioral
    strategy assigns a mixed action to each `infoSetId`, not to each tree node.

    **`n = 0` caveat**: The type allows `n = 0` (no actions), but `WFTree`
    excludes it. Evaluation functions handle `n = 0` defensively by returning
    a default payoff. -/
inductive GameTree (ι : Type) where
  | terminal (payoff : ι → ℝ)
  | chance (n : Nat) (μ : PMF (Fin n)) (next : Fin n → GameTree ι)
  | decision (infoSetId : Nat) (player : ι) (n : Nat) (next : Fin n → GameTree ι)

/-- A pure strategy: at information set `infoSetId` with `n > 0` actions, pick one.
    The `0 < n` guard ensures `Fin n` is inhabited, making `PureStrategy` inhabited.

    Strategies are indexed per-information-set, not per-tree-node: all nodes
    in the same information set receive the same action. -/
def PureStrategy := (infoSetId : Nat) → (n : Nat) → 0 < n → Fin n

/-- A behavioral strategy: at information set `infoSetId` with `n > 0` actions,
    return a distribution over `Fin n`.
    The `0 < n` guard ensures `PMF (Fin n)` is inhabited, making
    `BehavioralStrategy` inhabited.

    Strategies are indexed per-information-set, not per-tree-node. -/
def BehavioralStrategy := (infoSetId : Nat) → (n : Nat) → 0 < n → PMF (Fin n)

/-! ## Per-player strategy profiles

In game theory, each player has their own strategy; the strategy profile
is the tuple of per-player strategies. The joint `BehavioralStrategy` type
is convenient for evaluation but does not decompose by player.
-/

/-- A behavioral strategy profile: each player has their own behavioral strategy. -/
abbrev BehavioralProfile (ι : Type) := ι → BehavioralStrategy

/-- A pure strategy profile: each player has their own pure strategy. -/
abbrev PureProfile (ι : Type) := ι → PureStrategy

/-! ## Well-formedness -/

/-- Well-formedness predicate for a game tree.
    Chance well-formedness (weights sum to 1) is guaranteed by `PMF`. -/
inductive WFTree {ι : Type} : GameTree ι → Prop where
  | terminal : ∀ p, WFTree (.terminal p)
  | chance : ∀ n μ next,
      n > 0 →
      (∀ b, WFTree (next b)) →
      WFTree (.chance n μ next)
  | decision : ∀ infoSetId pl n next,
      n > 0 →
      (∀ a, WFTree (next a)) →
      WFTree (.decision infoSetId pl n next)

/-! ## Basic properties -/

/-- Count the number of immediate children (branches/actions) at the root. -/
def GameTree.rootArity {ι : Type} : GameTree ι → Nat
  | .terminal _ => 0
  | .chance n _ _ => n
  | .decision _ _ n _ => n

/-- Check whether a tree is a terminal node. -/
def GameTree.isTerminal {ι : Type} : GameTree ι → Bool
  | .terminal _ => true
  | _ => false

/-! ## Total evaluation (fuel-free) -/

/-- Evaluate a game tree under a pure strategy. Total, no fuel needed. -/
noncomputable def GameTree.evalTotal {ι : Type} (σ : PureStrategy) :
    GameTree ι → (ι → ℝ)
  | .terminal payoff => payoff
  | .chance n μ next => fun i =>
      ∑ b : Fin n, (μ b).toReal * (next b).evalTotal σ i
  | .decision infoSetId _player n next =>
      if h : 0 < n then (next (σ infoSetId n h)).evalTotal σ
      else fun _ => 0

/-- Expected utility under a pure strategy, fuel-free. -/
noncomputable def GameTree.euPure {ι : Type}
    (σ : PureStrategy) (who : ι) (t : GameTree ι) : ℝ :=
  t.evalTotal σ who

/-! ## Simp lemmas for total evaluation -/

@[simp] theorem evalTotal_terminal {ι : Type}
    (σ : PureStrategy) (payoff : ι → ℝ) :
    (GameTree.terminal payoff).evalTotal σ = payoff := rfl

@[simp] theorem euPure_eq_evalTotal {ι : Type}
    (σ : PureStrategy) (who : ι) (t : GameTree ι) :
    t.euPure σ who = t.evalTotal σ who := rfl

/-! ## Decision node reachability and information set consistency -/

/-- A decision node with given `infoSetId`, `player`, and `arity` appears
    somewhere inside a `GameTree`. -/
inductive DecisionNodeIn {ι : Type} (infoSetId : Nat) (player : ι) (arity : Nat)
    : GameTree ι → Prop where
  | root (next : Fin arity → GameTree ι) :
      DecisionNodeIn infoSetId player arity (.decision infoSetId player arity next)
  | in_chance (n : Nat) (μ : PMF (Fin n)) (next : Fin n → GameTree ι)
      (b : Fin n) (h : DecisionNodeIn infoSetId player arity (next b)) :
      DecisionNodeIn infoSetId player arity (.chance n μ next)
  | in_decision (infoSetId' : Nat) (player' : ι) (n : Nat) (next : Fin n → GameTree ι)
      (a : Fin n) (h : DecisionNodeIn infoSetId player arity (next a)) :
      DecisionNodeIn infoSetId player arity (.decision infoSetId' player' n next)

/-- No decision node can appear inside a terminal tree. -/
theorem DecisionNodeIn_terminal_false {ι : Type} {infoSetId : Nat} {player : ι}
    {arity : Nat} {payoff : ι → ℝ}
    (h : DecisionNodeIn infoSetId player arity (.terminal payoff)) : False := by
  cases h

/-- Inversion for `DecisionNodeIn` on a chance node:
    the node must be inside one of the branches. -/
theorem DecisionNodeIn_chance_inv {ι : Type} {infoSetId : Nat} {player : ι}
    {arity : Nat} {n : Nat} {μ : PMF (Fin n)} {next : Fin n → GameTree ι}
    (h : DecisionNodeIn infoSetId player arity (.chance n μ next)) :
    ∃ b : Fin n, DecisionNodeIn infoSetId player arity (next b) := by
  cases h with
  | in_chance _ _ _ b hsub => exact ⟨b, hsub⟩

/-- Inversion for `DecisionNodeIn` on a decision node:
    either it is the root, or it is inside one of the subtrees. -/
theorem DecisionNodeIn_decision_inv {ι : Type} {infoSetId : Nat} {player : ι}
    {arity : Nat} {infoSetId' : Nat} {player' : ι} {n : Nat}
    {next : Fin n → GameTree ι}
    (h : DecisionNodeIn infoSetId player arity (.decision infoSetId' player' n next)) :
    (infoSetId = infoSetId' ∧ player = player' ∧ n = arity) ∨
    ∃ a : Fin n, DecisionNodeIn infoSetId player arity (next a) := by
  cases h with
  | root _ => exact Or.inl ⟨rfl, rfl, rfl⟩
  | in_decision _ _ _ _ a hsub => exact Or.inr ⟨a, hsub⟩

/-- An EFG tree has consistent information sets: all decision nodes with
    the same `infoSetId` agree on player and action arity. -/
def InfoSetConsistent {ι : Type} (t : GameTree ι) : Prop :=
  ∀ infoSetId (p₁ p₂ : ι) (a₁ a₂ : Nat),
    DecisionNodeIn infoSetId p₁ a₁ t → DecisionNodeIn infoSetId p₂ a₂ t →
    p₁ = p₂ ∧ a₁ = a₂

/-! ## PMF-based evaluation (outcome distribution) -/

/-- Evaluate a game tree under a PMF behavioral strategy, returning a PMF over payoffs. -/
noncomputable def GameTree.evalDist {ι : Type}
    (σ : BehavioralStrategy) : GameTree ι → PMF (GameTheory.Payoff ι)
  | .terminal payoff => PMF.pure payoff
  | .chance _n μ next => μ.bind (fun b => (next b).evalDist σ)
  | .decision infoSetId _player n next =>
      if h : 0 < n then (σ infoSetId n h).bind (fun a => (next a).evalDist σ)
      else PMF.pure (fun _ => 0)

/-- EFG game tree as an outcome kernel: behavioral strategy → PMF over payoffs. -/
noncomputable def GameTree.toKernel {ι : Type} (t : GameTree ι) :
    GameTheory.Kernel BehavioralStrategy (GameTheory.Payoff ι) :=
  fun σ => t.evalDist σ

/-! ### Simp lemmas for evalDist -/

@[simp] theorem evalDist_terminal {ι : Type} (σ : BehavioralStrategy)
    (payoff : GameTheory.Payoff ι) :
    (GameTree.terminal payoff).evalDist σ = PMF.pure payoff := rfl

@[simp] theorem evalDist_chance {ι : Type} (σ : BehavioralStrategy)
    (n : Nat) (μ : PMF (Fin n)) (next : Fin n → GameTree ι) :
    (GameTree.chance n μ next).evalDist σ =
    μ.bind (fun b => (next b).evalDist σ) := rfl

@[simp] theorem evalDist_decision {ι : Type} (σ : BehavioralStrategy)
    (infoSetId : Nat) (p : ι) (n : Nat) (next : Fin n → GameTree ι) (hn : 0 < n) :
    (GameTree.decision infoSetId p n next).evalDist σ =
    (σ infoSetId n hn).bind (fun a => (next a).evalDist σ) := by
  simp [GameTree.evalDist, dif_pos hn]

/-! ## Per-player profile evaluation -/

/-- Evaluate under a per-player behavioral profile. At each decision node,
    uses the owning player's strategy. This is the standard game-theoretic
    evaluation where each player independently chooses a strategy. -/
noncomputable def GameTree.evalDistProfile {ι : Type}
    (σ : BehavioralProfile ι) : GameTree ι → PMF (GameTheory.Payoff ι)
  | .terminal payoff => PMF.pure payoff
  | .chance _n μ next => μ.bind (fun b => (next b).evalDistProfile σ)
  | .decision infoSetId player n next =>
      if h : 0 < n then (σ player infoSetId n h).bind (fun a => (next a).evalDistProfile σ)
      else PMF.pure (fun _ => 0)

/-- Evaluate under a per-player pure profile. -/
noncomputable def GameTree.evalTotalProfile {ι : Type}
    (σ : PureProfile ι) : GameTree ι → (ι → ℝ)
  | .terminal payoff => payoff
  | .chance n μ next => fun i =>
      ∑ b : Fin n, (μ b).toReal * (next b).evalTotalProfile σ i
  | .decision infoSetId player n next =>
      if h : 0 < n then (next (σ player infoSetId n h)).evalTotalProfile σ
      else fun _ => 0

/-! ### Simp lemmas for evalDistProfile -/

@[simp] theorem evalDistProfile_terminal {ι : Type} (σ : BehavioralProfile ι)
    (payoff : GameTheory.Payoff ι) :
    (GameTree.terminal payoff).evalDistProfile σ = PMF.pure payoff := rfl

@[simp] theorem evalDistProfile_chance {ι : Type} (σ : BehavioralProfile ι)
    (n : Nat) (μ : PMF (Fin n)) (next : Fin n → GameTree ι) :
    (GameTree.chance n μ next).evalDistProfile σ =
    μ.bind (fun b => (next b).evalDistProfile σ) := rfl

@[simp] theorem evalDistProfile_decision {ι : Type} (σ : BehavioralProfile ι)
    (infoSetId : Nat) (p : ι) (n : Nat) (next : Fin n → GameTree ι) (hn : 0 < n) :
    (GameTree.decision infoSetId p n next).evalDistProfile σ =
    (σ p infoSetId n hn).bind (fun a => (next a).evalDistProfile σ) := by
  simp [GameTree.evalDistProfile, dif_pos hn]

/-- A constant per-player profile (everyone uses the same strategy) agrees
    with the joint strategy evaluation. -/
theorem evalDistProfile_const {ι : Type} (σ : BehavioralStrategy) (t : GameTree ι) :
    t.evalDistProfile (fun _ => σ) = t.evalDist σ := by
  induction t with
  | terminal _ => rfl
  | chance _n _μ next ih =>
    simp only [GameTree.evalDistProfile, GameTree.evalDist]
    congr 1; funext b; exact ih b
  | decision infoSetId _player n next ih =>
    simp only [GameTree.evalDistProfile, GameTree.evalDist]
    split
    · congr 1; funext a; exact ih a
    · rfl

/-! ## GameTree → KernelGame conversion -/

/-- Convert an EFG game tree to a kernel-based game with per-player strategies.
    Each player independently chooses a `BehavioralStrategy`; the outcome
    distribution is given by `evalDistProfile`. -/
noncomputable def GameTree.toKernelGame {ι : Type} [DecidableEq ι]
    (t : GameTree ι) : GameTheory.KernelGame ι where
  Strategy := fun _ => BehavioralStrategy
  Outcome := GameTheory.Payoff ι
  payoff := id
  outcomeKernel := fun σ => t.evalDistProfile σ

/-! ### Swap theorems -/

/-- Swap stated directly in terms of PMF.bind. -/
theorem swap_bind (p : PMF α) (q : PMF β) (f : α → β → PMF γ) :
    p.bind (fun a => q.bind (fun b => f a b)) =
    q.bind (fun b => p.bind (fun a => f a b)) :=
  PMF.bind_comm p q f

/-- Swapping two independent decision nodes preserves the outcome distribution.
    Proof: immediate from `PMF.bind_comm` (Fubini for finite distributions). -/
theorem swap_decisions {ι : Type} (σ : BehavioralStrategy)
    (infoSetId₁ infoSetId₂ : Nat) (p₁ p₂ : ι) (n₁ n₂ : Nat)
    (grid : Fin n₁ → Fin n₂ → GameTree ι)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) :
    (GameTree.decision infoSetId₁ p₁ n₁ (fun i =>
      GameTree.decision infoSetId₂ p₂ n₂ (fun j => grid i j))).evalDist σ =
    (GameTree.decision infoSetId₂ p₂ n₂ (fun j =>
      GameTree.decision infoSetId₁ p₁ n₁ (fun i => grid i j))).evalDist σ := by
  simp only [evalDist_decision _ _ _ _ _ hn₁, evalDist_decision _ _ _ _ _ hn₂]
  exact PMF.bind_comm (σ infoSetId₁ n₁ hn₁) (σ infoSetId₂ n₂ hn₂)
    (fun i j => (grid i j).evalDist σ)

/-- Swapping a chance node and a decision node preserves the outcome distribution. -/
theorem swap_chance_decision {ι : Type} (σ : BehavioralStrategy)
    (infoSetId : Nat) (p : ι) (nc nd : Nat) (μ : PMF (Fin nc))
    (grid : Fin nc → Fin nd → GameTree ι)
    (hnd : 0 < nd) :
    (GameTree.chance nc μ (fun c =>
      GameTree.decision infoSetId p nd (fun d => grid c d))).evalDist σ =
    (GameTree.decision infoSetId p nd (fun d =>
      GameTree.chance nc μ (fun c => grid c d))).evalDist σ := by
  simp only [evalDist_chance, evalDist_decision _ _ _ _ _ hnd]
  exact PMF.bind_comm μ (σ infoSetId nd hnd) (fun c d => (grid c d).evalDist σ)

/-- Swapping two independent chance nodes preserves the outcome distribution. -/
theorem swap_chances {ι : Type} (σ : BehavioralStrategy)
    (n₁ n₂ : Nat) (μ₁ : PMF (Fin n₁)) (μ₂ : PMF (Fin n₂))
    (grid : Fin n₁ → Fin n₂ → GameTree ι) :
    (GameTree.chance n₁ μ₁ (fun c₁ =>
      GameTree.chance n₂ μ₂ (fun c₂ => grid c₁ c₂))).evalDist σ =
    (GameTree.chance n₂ μ₂ (fun c₂ =>
      GameTree.chance n₁ μ₁ (fun c₁ => grid c₁ c₂))).evalDist σ := by
  simp only [evalDist_chance]
  exact PMF.bind_comm μ₁ μ₂ (fun c₁ c₂ => (grid c₁ c₂).evalDist σ)

/-! ## Behavioral Nash equilibrium -/

/-- Behavioral Nash equilibrium for an EFG tree. Defined as `KernelGame.IsNash`
    on the per-player behavioral profile kernel game. -/
def GameTree.IsNashBehavioral {ι : Type} [DecidableEq ι] (t : GameTree ι)
    (σ : BehavioralProfile ι) : Prop :=
  t.toKernelGame.IsNash σ

end EFG
