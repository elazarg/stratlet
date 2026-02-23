import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import GameTheory.OutcomeKernel

/-!
# Extensive-Form Games (EFG)

Classical extensive-form game representation using `Fin`-indexed game trees
with terminal nodes, chance nodes (carrying `PMF`), and decision nodes.
-/

namespace EFG

/-- An extensive-form game tree.
  - `ι` is the type of players.
  - `terminal` is a leaf with a payoff function.
  - `chance n μ next` is a nature node with `n` branches, distribution `μ`,
    and subtrees indexed by `Fin n`.
  - `decision pid player n next` is a player decision node with `n` actions,
    identified by `pid`, subtrees indexed by `Fin n`. -/
inductive GameTree (ι : Type) where
  | terminal (payoff : ι → ℝ)
  | chance (n : Nat) (μ : PMF (Fin n)) (next : Fin n → GameTree ι)
  | decision (pid : Nat) (player : ι) (n : Nat) (next : Fin n → GameTree ι)

/-- A pure strategy: maps each decision-point id to an action index. -/
def PureStrategy := Nat → Nat

/-- A behavioral strategy: at decision point `pid` with `n` actions, choose `Fin n`. -/
def BehavioralStrategy := (pid : Nat) → (n : Nat) → PMF (Fin n)

/-! ## Well-formedness -/

/-- Well-formedness predicate for a game tree.
    Chance well-formedness (weights sum to 1) is guaranteed by `PMF`. -/
inductive WFTree {ι : Type} : GameTree ι → Prop where
  | terminal : ∀ p, WFTree (.terminal p)
  | chance : ∀ n μ next,
      n > 0 →
      (∀ b, WFTree (next b)) →
      WFTree (.chance n μ next)
  | decision : ∀ pid pl n next,
      n > 0 →
      (∀ a, WFTree (next a)) →
      WFTree (.decision pid pl n next)

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
  | .decision pid _player n next =>
      if h : σ pid < n then (next ⟨σ pid, h⟩).evalTotal σ
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

/-- A decision node with given `pid`, `player`, and `arity` appears
    somewhere inside a `GameTree`. -/
inductive DecisionNodeIn {ι : Type} (pid : Nat) (player : ι) (arity : Nat)
    : GameTree ι → Prop where
  | root (next : Fin arity → GameTree ι) :
      DecisionNodeIn pid player arity (.decision pid player arity next)
  | in_chance (n : Nat) (μ : PMF (Fin n)) (next : Fin n → GameTree ι)
      (b : Fin n) (h : DecisionNodeIn pid player arity (next b)) :
      DecisionNodeIn pid player arity (.chance n μ next)
  | in_decision (pid' : Nat) (player' : ι) (n : Nat) (next : Fin n → GameTree ι)
      (a : Fin n) (h : DecisionNodeIn pid player arity (next a)) :
      DecisionNodeIn pid player arity (.decision pid' player' n next)

/-- No decision node can appear inside a terminal tree. -/
theorem DecisionNodeIn_terminal_false {ι : Type} {pid : Nat} {player : ι}
    {arity : Nat} {payoff : ι → ℝ}
    (h : DecisionNodeIn pid player arity (.terminal payoff)) : False := by
  cases h

/-- Inversion for `DecisionNodeIn` on a chance node:
    the node must be inside one of the branches. -/
theorem DecisionNodeIn_chance_inv {ι : Type} {pid : Nat} {player : ι}
    {arity : Nat} {n : Nat} {μ : PMF (Fin n)} {next : Fin n → GameTree ι}
    (h : DecisionNodeIn pid player arity (.chance n μ next)) :
    ∃ b : Fin n, DecisionNodeIn pid player arity (next b) := by
  cases h with
  | in_chance _ _ _ b hsub => exact ⟨b, hsub⟩

/-- Inversion for `DecisionNodeIn` on a decision node:
    either it is the root, or it is inside one of the subtrees. -/
theorem DecisionNodeIn_decision_inv {ι : Type} {pid : Nat} {player : ι}
    {arity : Nat} {pid' : Nat} {player' : ι} {n : Nat}
    {next : Fin n → GameTree ι}
    (h : DecisionNodeIn pid player arity (.decision pid' player' n next)) :
    (pid = pid' ∧ player = player' ∧ n = arity) ∨
    ∃ a : Fin n, DecisionNodeIn pid player arity (next a) := by
  cases h with
  | root _ => exact Or.inl ⟨rfl, rfl, rfl⟩
  | in_decision _ _ _ _ a hsub => exact Or.inr ⟨a, hsub⟩

/-- An EFG tree has consistent information sets: all decision nodes with
    the same `pid` agree on player and action arity. -/
def InfoSetConsistent {ι : Type} (t : GameTree ι) : Prop :=
  ∀ pid (p₁ p₂ : ι) (a₁ a₂ : Nat),
    DecisionNodeIn pid p₁ a₁ t → DecisionNodeIn pid p₂ a₂ t →
    p₁ = p₂ ∧ a₁ = a₂

/-! ## PMF-based evaluation (outcome distribution) -/

/-- Evaluate a game tree under a PMF behavioral strategy, returning a PMF over payoffs. -/
noncomputable def GameTree.evalDist {ι : Type}
    (σ : BehavioralStrategy) : GameTree ι → PMF (GameTheory.Payoff ι)
  | .terminal payoff => PMF.pure payoff
  | .chance _n μ next => μ.bind (fun b => (next b).evalDist σ)
  | .decision pid _player n next => (σ pid n).bind (fun a => (next a).evalDist σ)

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
    (pid : Nat) (p : ι) (n : Nat) (next : Fin n → GameTree ι) :
    (GameTree.decision pid p n next).evalDist σ =
    (σ pid n).bind (fun a => (next a).evalDist σ) := rfl

/-! ### Swap theorems -/

/-- Swap stated directly in terms of PMF.bind. -/
theorem swap_bind (p : PMF α) (q : PMF β) (f : α → β → PMF γ) :
    p.bind (fun a => q.bind (fun b => f a b)) =
    q.bind (fun b => p.bind (fun a => f a b)) :=
  PMF.bind_comm p q f

/-- Swapping two independent decision nodes preserves the outcome distribution.
    Proof: immediate from `PMF.bind_comm` (Fubini for finite distributions). -/
theorem swap_decisions {ι : Type} (σ : BehavioralStrategy)
    (pid₁ pid₂ : Nat) (p₁ p₂ : ι) (n₁ n₂ : Nat)
    (grid : Fin n₁ → Fin n₂ → GameTree ι) :
    (GameTree.decision pid₁ p₁ n₁ (fun i =>
      GameTree.decision pid₂ p₂ n₂ (fun j => grid i j))).evalDist σ =
    (GameTree.decision pid₂ p₂ n₂ (fun j =>
      GameTree.decision pid₁ p₁ n₁ (fun i => grid i j))).evalDist σ := by
  simp only [evalDist_decision]
  exact PMF.bind_comm (σ pid₁ n₁) (σ pid₂ n₂) (fun i j => (grid i j).evalDist σ)

/-- Swapping a chance node and a decision node preserves the outcome distribution. -/
theorem swap_chance_decision {ι : Type} (σ : BehavioralStrategy)
    (pid : Nat) (p : ι) (nc nd : Nat) (μ : PMF (Fin nc))
    (grid : Fin nc → Fin nd → GameTree ι) :
    (GameTree.chance nc μ (fun c =>
      GameTree.decision pid p nd (fun d => grid c d))).evalDist σ =
    (GameTree.decision pid p nd (fun d =>
      GameTree.chance nc μ (fun c => grid c d))).evalDist σ := by
  simp only [evalDist_chance, evalDist_decision]
  exact PMF.bind_comm μ (σ pid nd) (fun c d => (grid c d).evalDist σ)

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

end EFG
