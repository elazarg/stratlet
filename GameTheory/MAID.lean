import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import GameTheory.OutcomeKernel

/-!
# Multi-Agent Influence Diagrams (MAID)

Structural representation of multi-agent decision problems
as directed acyclic graphs with decision, chance, and utility nodes.
-/

namespace MAID

/-- The kind of a node in a MAID. -/
inductive NodeKind where
  | chance
  | decision (agent : Nat)
  | utility (agent : Nat)
deriving DecidableEq, Repr

/-- A node in a MAID. -/
structure Node where
  id : Nat
  kind : NodeKind
  parents : List Nat
  /-- Domain cardinality (number of distinct values this node can take).
      Utility nodes: 1 (no domain values).
      Decision nodes: number of available actions (game-specific).
      Chance nodes: number of outcomes in the distribution. -/
  domainSize : Nat
deriving Repr

/-- The node list is in topological order: every parent id of node `i`
    belongs to a node that appears earlier in the list. -/
def TopologicalOrder (nodes : List Node) : Prop :=
  ∀ (i : Fin nodes.length), ∀ pid ∈ (nodes[i]).parents,
    ∃ (j : Fin nodes.length), j.val < i.val ∧ (nodes[j]).id = pid

/-- A multi-agent influence diagram. -/
structure Diagram where
  nodes : List Node
  nodup_ids : (nodes.map Node.id).Nodup
  parents_exist : ∀ n ∈ nodes, ∀ pid ∈ n.parents,
    ∃ m ∈ nodes, m.id = pid
  acyclic : TopologicalOrder nodes

/-- A conditional policy maps (decision node id, parent assignment) to a PMF over values. -/
def CondPolicy := Nat → (Nat → Nat) → PMF Nat

/-- Get all decision nodes for a given agent. -/
def Diagram.decisionNodes (m : Diagram) (agent : Nat) : List Node :=
  m.nodes.filter fun n =>
    match n.kind with
    | .decision a => a == agent
    | _ => false

/-- Get all utility nodes for a given agent. -/
def Diagram.utilityNodes (m : Diagram) (agent : Nat) : List Node :=
  m.nodes.filter fun n =>
    match n.kind with
    | .utility a => a == agent
    | _ => false

/-- The set of agents mentioned in a MAID. -/
def Diagram.agents (m : Diagram) : List Nat :=
  (m.nodes.filterMap fun n =>
    match n.kind with
    | .decision a => some a
    | .utility a => some a
    | .chance => none).dedup

/-- Look up a node by id. -/
def Diagram.findNode (m : Diagram) (nid : Nat) : Option Node :=
  m.nodes.find? (fun n => n.id == nid)

/-! ## Well-formedness predicates -/

/-- A function from full assignments is *local* to `parents` if it depends
    only on values at the listed parent nodes. This is the fundamental
    MAID discipline: CPDs and policies must not read future or
    non-parent values. -/
def LocalTo (parents : List Nat) (f : (Nat → Nat) → α) : Prop :=
  ∀ a₁ a₂, (∀ p ∈ parents, a₁ p = a₂ p) → f a₁ = f a₂

/-- A `PMF Nat` is supported within `{0, ..., n-1}`. -/
def DomainBounded (n : Nat) (d : PMF Nat) : Prop :=
  ∀ v, d v ≠ 0 → v < n

/-! ## MAID direct semantics -/

/-- A MAID with full semantic data for evaluation.

    **Locality contract**: `chanceCPD` and `utilityFn` receive the full
    assignment `Nat → Nat`, but a well-formed model must only depend on
    parent values (see `MAIDModel.WellFormed`). Nothing in the type
    enforces this; it is a proof obligation. -/
structure MAIDModel where
  diagram : Diagram
  /-- Conditional distribution for chance nodes, given parent values. -/
  chanceCPD : Nat → (Nat → Nat) → PMF Nat
  /-- Utility function for utility nodes, given parent values. -/
  utilityFn : Nat → (Nat → Nat) → ℝ

/-- Well-formedness: all semantic functions respect the DAG's locality
    discipline (depend only on parent values) and domain bounds. -/
structure MAIDModel.WellFormed (m : MAIDModel) : Prop where
  chance_local : ∀ n ∈ m.diagram.nodes, n.kind = .chance →
    LocalTo n.parents (m.chanceCPD n.id)
  chance_bounded : ∀ n ∈ m.diagram.nodes, n.kind = .chance →
    ∀ assign, DomainBounded n.domainSize (m.chanceCPD n.id assign)
  utility_local : ∀ n ∈ m.diagram.nodes, ∀ a, n.kind = .utility a →
    LocalTo n.parents (m.utilityFn n.id)
  utility_domain : ∀ n ∈ m.diagram.nodes, ∀ a, n.kind = .utility a →
    n.domainSize = 1

/-- A conditional policy respects the MAID's structure. -/
structure CondPolicy.Admissible (d : Diagram) (π : CondPolicy) : Prop where
  local_ : ∀ n ∈ d.nodes, ∀ a, n.kind = .decision a →
    LocalTo n.parents (π n.id)
  bounded : ∀ n ∈ d.nodes, ∀ a, n.kind = .decision a →
    ∀ assign, DomainBounded n.domainSize (π n.id assign)

/-- Full assignment: maps node IDs to values. -/
abbrev Assign := Nat → Nat

/-- Joint PMF over full assignments, built by folding over nodes in
    topological order. Each node draws a value from its CPD or policy
    and extends the assignment. -/
noncomputable def MAIDModel.evalAssignDist (m : MAIDModel) (π : CondPolicy)
    : PMF Assign :=
  let step (acc : PMF Assign) (node : Node) : PMF Assign :=
    acc.bind (fun assign =>
      let nodeDist := match node.kind with
        | .chance => m.chanceCPD node.id assign
        | .decision _ => π node.id assign
        | .utility _ => PMF.pure 0
      nodeDist.bind (fun v => PMF.pure (Function.update assign node.id v)))
  m.diagram.nodes.foldl step (PMF.pure (fun _ => 0))

/-- Extract payoffs from an assignment. -/
noncomputable def MAIDModel.payoffOf (m : MAIDModel) (assign : Assign)
    : GameTheory.Payoff Nat :=
  fun agent =>
    (m.diagram.utilityNodes agent).map (fun u => m.utilityFn u.id assign)
      |>.sum

/-- Evaluate a MAID under a policy by building the joint distribution
    over assignments and mapping to payoff vectors. -/
noncomputable def MAIDModel.evalDist (m : MAIDModel) (π : CondPolicy)
    : PMF (GameTheory.Payoff Nat) :=
  (m.evalAssignDist π).bind (fun assign => PMF.pure (m.payoffOf assign))

/-- MAID as an outcome kernel. -/
noncomputable def MAIDModel.toKernel (m : MAIDModel)
    : GameTheory.Kernel CondPolicy (GameTheory.Payoff Nat) :=
  fun π => m.evalDist π

end MAID
