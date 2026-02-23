import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.List.Basic

/-!
# Extensive-Form Games (EFG)

Classical extensive-form game representation using game trees
with terminal nodes, chance nodes, and decision nodes.
-/

namespace EFG

/-- An extensive-form game tree.
  - `ι` is the type of players.
  - `terminal` is a leaf with a payoff function.
  - `chance` is a nature node with weighted branches.
  - `decision` is a player node identified by `pid`, with a list of actions (subtrees). -/
inductive GameTree (ι : Type) where
  | terminal (payoff : ι → ℝ)
  | chance (branches : List (GameTree ι × NNReal))
  | decision (pid : Nat) (player : ι) (actions : List (GameTree ι))

/-- An information set: groups decision nodes for a player
    where the player cannot distinguish between them.
    Currently unused — the infoset consistency property is expressed
    via `DecisionNodeIn` and `InfoSetConsistent` instead. -/
structure InformationSet (ι : Type) where
  player : ι
  actionCount : Nat
  members : List Nat

/-- A pure strategy: maps each decision-point id to an action index. -/
def PureStrategy := Nat → Nat

/-- A behavioral strategy: maps each decision-point id to a distribution
    over actions (list of non-negative reals). -/
def BehavioralStrategy := Nat → List NNReal

/-- Well-formedness predicate for a game tree. -/
inductive WFTree {ι : Type} : GameTree ι → Prop where
  | terminal : ∀ p, WFTree (.terminal p)
  | chance : ∀ bs,
      bs ≠ [] →
      (bs.map Prod.snd).sum = 1 →
      (∀ bt ∈ bs, WFTree bt.1) →
      WFTree (.chance bs)
  | decision : ∀ pid pl acts,
      acts ≠ [] →
      (∀ a ∈ acts, WFTree a) →
      WFTree (.decision pid pl acts)

/-- Count the number of immediate children (branches/actions) at the root. -/
def GameTree.rootArity {ι : Type} : GameTree ι → Nat
  | .terminal _ => 0
  | .chance bs => bs.length
  | .decision _ _ acts => acts.length

/-- Check whether a tree is a terminal node. -/
def GameTree.isTerminal {ι : Type} : GameTree ι → Bool
  | .terminal _ => true
  | _ => false

/-- Finitely supported distribution over payoff functions. -/
abbrev PayoffDist (ι : Type) := List ((ι → ℝ) × NNReal)

namespace PayoffDist
def pure {ι} (u : ι → ℝ) : PayoffDist ι := [(u, 1)]
def zero {ι} : PayoffDist ι := []
def scale {ι} (w : NNReal) (d : PayoffDist ι) : PayoffDist ι :=
  d.map (fun (u,p) => (u, w * p))
def append {ι} (d₁ d₂ : PayoffDist ι) : PayoffDist ι := d₁ ++ d₂
end PayoffDist

/-- Tree-to-probability semantics: resolve a `GameTree` to a payoff distribution
    given a behavioral strategy. -/
noncomputable def GameTree.evalDist {ι : Type}
    (σ : BehavioralStrategy) : GameTree ι → PayoffDist ι
  | .terminal payoff => PayoffDist.pure payoff
  | .chance branches => go_chance branches
  | .decision pid _player actions => go_decision (σ pid) actions
where
  go_chance : List (GameTree ι × NNReal) → PayoffDist ι
    | [] => []
    | (t, w) :: rest =>
        PayoffDist.append (PayoffDist.scale w (GameTree.evalDist σ t))
                          (go_chance rest)
  go_decision : List NNReal → List (GameTree ι) → PayoffDist ι
    | _, [] => []
    | [], _ :: _ => []          -- strategy missing weights: treat as zero
    | w :: ws, t :: ts =>
        PayoffDist.append (PayoffDist.scale w (GameTree.evalDist σ t))
                          (go_decision ws ts)

noncomputable def GameTree.EUdist {ι : Type}
    (t : GameTree ι) (σ : BehavioralStrategy) (who : ι) : ℝ :=
  ((t.evalDist σ).map (fun (uw : (ι → ℝ) × NNReal) => (uw.2 : ℝ) * (uw.1 who))).sum

/-! ## Depth of a game tree -/

/-- The depth (max path length from root to terminal) of a game tree. -/
def GameTree.depth {ι : Type} : GameTree ι → Nat
  | .terminal _ => 0
  | .chance branches => 1 + go_pairs branches
  | .decision _ _ actions => 1 + go_list actions
where
  go_pairs : List (GameTree ι × NNReal) → Nat
    | [] => 0
    | ⟨t, _⟩ :: rest => max t.depth (go_pairs rest)
  go_list : List (GameTree ι) → Nat
    | [] => 0
    | t :: rest => max t.depth (go_list rest)

/-! ## Total evaluation (fuel-free) -/

/-- Evaluate a game tree under a pure strategy. Total, no fuel needed.
    Uses `where` clauses for structural recursion through nested lists. -/
noncomputable def GameTree.evalTotal {ι : Type} (σ : PureStrategy) :
    GameTree ι → (ι → ℝ)
  | .terminal payoff => payoff
  | .chance branches => fun i => go_chance i branches
  | .decision pid _player actions => go_nth (σ pid) actions
where
  go_chance (i : ι) : List (GameTree ι × NNReal) → ℝ
    | [] => 0
    | ⟨t, w⟩ :: rest => (w : ℝ) * t.evalTotal σ i + go_chance i rest
  go_nth : Nat → List (GameTree ι) → (ι → ℝ)
    | _, [] => fun _ => 0
    | 0, t :: _ => t.evalTotal σ
    | n + 1, _ :: rest => go_nth n rest

/-- Expected utility under a pure strategy, fuel-free. -/
noncomputable def GameTree.euPure {ι : Type}
    (σ : PureStrategy) (who : ι) (t : GameTree ι) : ℝ :=
  t.evalTotal σ who

/-- Total expected utility under a behavioral strategy. No fuel needed. -/
noncomputable def GameTree.euBehavioral {ι : Type}
    (σ : BehavioralStrategy) (who : ι) : GameTree ι → ℝ
  | .terminal payoff => payoff who
  | .chance branches => go_chance branches
  | .decision pid _player actions => go_decision (σ pid) actions
where
  go_chance : List (GameTree ι × NNReal) → ℝ
    | [] => 0
    | ⟨t, w⟩ :: rest => (w : ℝ) * t.euBehavioral σ who + go_chance rest
  go_decision : List NNReal → List (GameTree ι) → ℝ
    | _, [] => 0
    | [], _ :: _ => 0
    | w :: wrest, t :: trest =>
        (w : ℝ) * t.euBehavioral σ who + go_decision wrest trest

/-! ## Simp lemmas for total evaluation -/

@[simp] theorem evalTotal_terminal {ι : Type}
    (σ : PureStrategy) (payoff : ι → ℝ) :
    (GameTree.terminal payoff).evalTotal σ = payoff := by
  simp [GameTree.evalTotal]

@[simp] theorem euBehavioral_terminal {ι : Type}
    (σ : BehavioralStrategy) (who : ι) (payoff : ι → ℝ) :
    (GameTree.terminal payoff).euBehavioral σ who = payoff who := by
  simp [GameTree.euBehavioral]

@[simp] theorem euPure_eq_evalTotal {ι : Type}
    (σ : PureStrategy) (who : ι) (t : GameTree ι) :
    t.euPure σ who = t.evalTotal σ who := rfl

/-! ## Decision node reachability and information set consistency -/

/-- A decision node with given `pid`, `player`, and `arity` appears
    somewhere inside a `GameTree`. -/
inductive DecisionNodeIn {ι : Type} (pid : Nat) (player : ι) (arity : Nat)
    : GameTree ι → Prop where
  | root (acts : List (GameTree ι)) (hlen : acts.length = arity) :
      DecisionNodeIn pid player arity (.decision pid player acts)
  | in_chance (branches : List (GameTree ι × NNReal))
      (t : GameTree ι) (w : NNReal) (hmem : (t, w) ∈ branches)
      (h : DecisionNodeIn pid player arity t) :
      DecisionNodeIn pid player arity (.chance branches)
  | in_decision (pid' : Nat) (player' : ι) (acts : List (GameTree ι))
      (t : GameTree ι) (hmem : t ∈ acts)
      (h : DecisionNodeIn pid player arity t) :
      DecisionNodeIn pid player arity (.decision pid' player' acts)

/-- No decision node can appear inside a terminal tree. -/
theorem DecisionNodeIn_terminal_false {ι : Type} {pid : Nat} {player : ι}
    {arity : Nat} {payoff : ι → ℝ}
    (h : DecisionNodeIn pid player arity (.terminal payoff)) : False := by
  cases h

/-- Inversion for `DecisionNodeIn` on a chance node:
    the node must be inside one of the branches. -/
theorem DecisionNodeIn_chance_inv {ι : Type} {pid : Nat} {player : ι}
    {arity : Nat} {branches : List (GameTree ι × NNReal)}
    (h : DecisionNodeIn pid player arity (.chance branches)) :
    ∃ t w, (t, w) ∈ branches ∧ DecisionNodeIn pid player arity t := by
  cases h with
  | in_chance _ t w hmem hsub => exact ⟨t, w, hmem, hsub⟩

/-- Inversion for `DecisionNodeIn` on a decision node:
    either it is the root, or it is inside one of the subtrees. -/
theorem DecisionNodeIn_decision_inv {ι : Type} {pid : Nat} {player : ι}
    {arity : Nat} {pid' : Nat} {player' : ι} {acts : List (GameTree ι)}
    (h : DecisionNodeIn pid player arity (.decision pid' player' acts)) :
    (pid = pid' ∧ player = player' ∧ acts.length = arity) ∨
    ∃ t, t ∈ acts ∧ DecisionNodeIn pid player arity t := by
  cases h with
  | root _ hlen => exact Or.inl ⟨rfl, rfl, hlen⟩
  | in_decision _ _ _ t hmem hsub => exact Or.inr ⟨t, hmem, hsub⟩

/-- An EFG tree has consistent information sets: all decision nodes with
    the same `pid` agree on player and action arity. -/
def InfoSetConsistent {ι : Type} (t : GameTree ι) : Prop :=
  ∀ pid (p₁ p₂ : ι) (a₁ a₂ : Nat),
    DecisionNodeIn pid p₁ a₁ t → DecisionNodeIn pid p₂ a₂ t →
    p₁ = p₂ ∧ a₁ = a₂

end EFG
