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
    where the player cannot distinguish between them. -/
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

/-! ## Pure strategy evaluator -/

/-- Evaluate a game tree under a pure strategy with bounded recursion depth.
    Terminal nodes return immediately regardless of fuel. -/
noncomputable def GameTree.evalAux {ι : Type} (σ : PureStrategy) : Nat → GameTree ι → (ι → ℝ)
  | _, .terminal payoff => payoff
  | 0, _ => fun _ => 0
  | n + 1, .chance branches =>
      fun i => (branches.map (fun ⟨t, w⟩ => (w : ℝ) * (GameTree.evalAux σ n t i))).sum
  | n + 1, .decision pid _player actions =>
      match actions[σ pid]? with
      | some t => GameTree.evalAux σ n t
      | none => fun _ => 0

/-- Evaluate with sufficient fuel (1000 levels deep). -/
noncomputable def GameTree.eval {ι : Type} (σ : PureStrategy) (t : GameTree ι) : (ι → ℝ) :=
  GameTree.evalAux σ 1000 t

/-- Expected utility under a pure strategy. -/
noncomputable def GameTree.EU {ι : Type} (t : GameTree ι) (σ : PureStrategy) (who : ι) : ℝ :=
  t.eval σ who

/-! ## Structural recursive EU on GameTree -/

/-- Expected utility computed structurally on a `GameTree`, given a
    behavioral strategy. No fuel needed.

    Uses fuel internally to work around nested-inductive termination.
    The fuel is set high enough (depth of the tree) to be transparent. -/
noncomputable def GameTree.euStructAux
    {ι : Type} (σ : BehavioralStrategy) (who : ι) : Nat → GameTree ι → ℝ
  | _, .terminal payoff => payoff who
  | 0, _ => 0
  | n + 1, .chance branches =>
      (branches.map fun (t, w) => (w : ℝ) * GameTree.euStructAux σ who n t).sum
  | n + 1, .decision pid _player actions =>
      let weights := σ pid
      let pairs := actions.zip weights
      (pairs.map fun (t, w) => (w : ℝ) * GameTree.euStructAux σ who n t).sum

/-- Expected utility under a behavioral strategy. Uses 1000 levels of fuel. -/
noncomputable def GameTree.euStruct
    {ι : Type} (σ : BehavioralStrategy) (who : ι) (t : GameTree ι) : ℝ :=
  GameTree.euStructAux σ who 1000 t

@[simp] theorem GameTree.euStructAux_terminal
    {ι : Type} (σ : BehavioralStrategy) (who : ι) (n : Nat) (payoff : ι → ℝ) :
    GameTree.euStructAux σ who n (.terminal payoff) = payoff who := by
  cases n <;> rfl

/-! ## Simp lemmas -/

@[simp] theorem eval_terminal {ι : Type} (σ : PureStrategy) (payoff : ι → ℝ) :
    (GameTree.terminal payoff).eval σ = payoff := by
  simp [GameTree.eval, GameTree.evalAux]

end EFG
