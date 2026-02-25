import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import GameTheory.SolutionConcepts

/-!
# Multi-Agent Influence Diagrams (MAID)

Structural representation of multi-agent decision problems
as directed acyclic graphs with decision, chance, and utility nodes.

Organized in three layers:

## § 1. Core (pure structure)
- `NodeKind`, `Node`, `Diagram`
- Graph queries (`findNode`, `decisionNodes`, `utilityNodes`, `agents`)
- Structural well-formedness (`TopologicalOrder`, `acyclic`, `parents_exist`, `nodup_ids`)
- No PMF, no ℝ, no policies, no semantics.

## § 2. Semantics (evaluation, locality, admissibility)
- `LocalTo`, `DomainBounded`
- `CondPolicy`, `CondPolicy.Admissible`
- `MAIDModel`, `MAIDModel.WellFormed`
- `evalAssignDist`, `payoffOf`, `evalDist`

## § 3. Game (KernelGame bridge + solution concepts)
- `toKernel`, `toKernelGame`
- `eu`, `IsNash`
- All imports of `GameTheory.SolutionConcepts` are used here only.

## Scope-outs

- **d-separation / s-reachability** — graph-algorithmic, orthogonal to game semantics
- **Structural equilibrium** — needs relevance graph
- **Order-independence theorem** — `evalAssignDist` depends only on the partial
  order (DAG), not on the chosen topological ordering. Statement is clear;
  proof (adjacent-swap commutation under independence) is deferred.
-/

namespace MAID

-- ============================================================================
-- § 1. Core — pure structure
-- ============================================================================

/-- The kind of a node in a MAID. -/
inductive NodeKind where
  | chance
  | decision (agent : Nat)
  | utility (agent : Nat)
deriving DecidableEq, Repr

/-- A node in a MAID.

    **Observed parents** (`obsParents`): for decision nodes, these are the
    parent nodes whose values are observable at decision time. A decision
    node may have causal parents that are not observed (imperfect information).
    For chance and utility nodes, `obsParents` should equal `parents`.

    Invariant: `obsParents ⊆ parents` (enforced by `Diagram`). -/
structure Node where
  id : Nat
  kind : NodeKind
  parents : List Nat
  /-- Parent nodes whose values are observed at this node.
      For decision nodes, this may be a strict subset of `parents`,
      modeling imperfect information. For chance/utility nodes,
      this should equal `parents`. -/
  obsParents : List Nat
  /-- Domain cardinality (number of distinct values this node can take).
      Utility nodes: 1 (no domain values).
      Decision nodes: number of available actions (game-specific).
      Chance nodes: number of outcomes in the distribution. -/
  domainSize : Nat
deriving Repr

/-- Convenience constructor: a node where all parents are observed. -/
def Node.mk' (id : Nat) (kind : NodeKind) (parents : List Nat) (domainSize : Nat) : Node :=
  { id, kind, parents, obsParents := parents, domainSize }

/-- Extract the owning agent of a decision node, if applicable. -/
def Node.decisionAgent (n : Node) : Option Nat :=
  match n.kind with
  | .decision a => some a
  | _ => none

/-- Extract the owning agent of a node (decision or utility), if applicable. -/
def Node.agent (n : Node) : Option Nat :=
  match n.kind with
  | .decision a => some a
  | .utility a => some a
  | .chance => none

/-- The node list is in topological order: every parent id of node `i`
    belongs to a node that appears earlier in the list. -/
def TopologicalOrder (nodes : List Node) : Prop :=
  ∀ (i : Fin nodes.length), ∀ pid ∈ (nodes[i]).parents,
    ∃ (j : Fin nodes.length), j.val < i.val ∧ (nodes[j]).id = pid

/-- A multi-agent influence diagram.

    Structural invariants:
    - `nodup_ids`: node IDs are unique.
    - `parents_exist`: every parent reference points to an existing node.
    - `acyclic`: nodes are in topological order.
    - `obs_sub_parents`: observed parents are a subset of parents.
    - `domain_pos`: chance and decision nodes have positive domain size.
    - `utility_domain`: utility nodes have domain size 1.
    - `parents_nodup`: parent lists have no duplicates. -/
structure Diagram where
  nodes : List Node
  nodup_ids : (nodes.map Node.id).Nodup
  parents_exist : ∀ n ∈ nodes, ∀ pid ∈ n.parents,
    ∃ m ∈ nodes, m.id = pid
  acyclic : TopologicalOrder nodes
  obs_sub_parents : ∀ n ∈ nodes, ∀ pid ∈ n.obsParents, pid ∈ n.parents
  domain_pos : ∀ n ∈ nodes, match n.kind with
    | .chance | .decision _ => 0 < n.domainSize | .utility _ => True
  utility_domain : ∀ n ∈ nodes, ∀ a, n.kind = .utility a → n.domainSize = 1
  parents_nodup : ∀ n ∈ nodes, n.parents.Nodup

/-- Get all decision nodes for a given agent. -/
def Diagram.decisionNodes (d : Diagram) (agent : Nat) : List Node :=
  d.nodes.filter fun n =>
    match n.kind with
    | .decision a => a == agent
    | _ => false

/-- Get all utility nodes for a given agent. -/
def Diagram.utilityNodes (d : Diagram) (agent : Nat) : List Node :=
  d.nodes.filter fun n =>
    match n.kind with
    | .utility a => a == agent
    | _ => false

/-- The set of agents mentioned in a MAID. -/
def Diagram.agents (d : Diagram) : List Nat :=
  (d.nodes.filterMap Node.agent).dedup

/-- Look up a node by id. -/
def Diagram.findNode (d : Diagram) (nid : Nat) : Option Node :=
  d.nodes.find? (fun n => n.id == nid)

-- ============================================================================
-- § 2. Semantics — evaluation, locality, admissibility
-- ============================================================================

/-! ### Well-formedness predicates -/

/-- A function from full assignments is *local* to `ids` if it depends
    only on values at the listed node IDs. This is the fundamental
    MAID discipline: CPDs and policies must not read future or
    non-parent values. -/
def LocalTo (ids : List Nat) (f : (Nat → Nat) → α) : Prop :=
  ∀ a₁ a₂, (∀ p ∈ ids, a₁ p = a₂ p) → f a₁ = f a₂

/-- A `PMF Nat` is supported within `{0, ..., n-1}`. -/
def DomainBounded (n : Nat) (d : PMF Nat) : Prop :=
  ∀ v, d v ≠ 0 → v < n

/-! ### Policies -/

/-- A conditional policy maps (decision node id, full assignment) to a PMF over values.

    **Design note**: `CondPolicy` is intentionally permissive — it accepts any
    `(Nat → Nat) → PMF Nat` regardless of locality or domain bounds. This is
    deliberate: `Admissible` is the enforcement point where locality (only
    reads observed-parent values) and domain bounds (support ⊆ `{0, ..., domainSize-1}`)
    are checked. Unlike `EFG.BehavioralStrategy`, there is no emptiness problem
    here: `PMF Nat` is always inhabited (e.g., via `PMF.pure 0`).

    This type represents a **joint** policy over all decision nodes. For
    per-agent decomposition, see `mergeCondPolicies`. -/
def CondPolicy := Nat → (Nat → Nat) → PMF Nat

/-- A conditional policy respects the MAID's structure.
    This is the enforcement point for the two key MAID discipline constraints:
    - **Locality**: the policy for each decision node depends only on
      *observed* parent values (not all causal parents).
    - **Domain bounds**: the policy's support stays within `{0, ..., domainSize-1}`. -/
structure CondPolicy.Admissible (d : Diagram) (π : CondPolicy) : Prop where
  local_ : ∀ n ∈ d.nodes, ∀ a, n.kind = .decision a →
    LocalTo n.obsParents (π n.id)
  bounded : ∀ n ∈ d.nodes, ∀ a, n.kind = .decision a →
    ∀ assign, DomainBounded n.domainSize (π n.id assign)

/-! ### Per-agent policy decomposition -/

/-- Merge per-agent policies into a joint `CondPolicy`.
    At each decision node, dispatches to the owning agent's policy.
    For non-decision nodes (or nodes not found in the diagram),
    returns a default point mass at 0. -/
noncomputable def mergeCondPolicies (d : Diagram) (σ : Nat → CondPolicy) : CondPolicy :=
  fun nodeId assign =>
    match (d.findNode nodeId).bind Node.decisionAgent with
    | some agent => σ agent nodeId assign
    | none => PMF.pure 0

/-! ### Full assignment type -/

/-- Full assignment: maps node IDs to values. -/
abbrev Assign := Nat → Nat

/-! ### MAID model -/

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

/-! ### Evaluation -/

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

/-! ### Locality lemma for payoffs -/

/-- `payoffOf` for a given agent depends only on the values at the
    parents of that agent's utility nodes, provided `utility_local` holds. -/
theorem MAIDModel.payoffOf_local (m : MAIDModel) (wf : m.WellFormed)
    (agent : Nat) :
    LocalTo
      ((m.diagram.utilityNodes agent).flatMap Node.parents)
      (fun assign => m.payoffOf assign agent) := by
  intro a₁ a₂ heq
  simp only [payoffOf]
  congr 1
  rw [List.map_inj_left]
  intro u hu
  have hmem : u ∈ m.diagram.nodes :=
    List.mem_filter.mp hu |>.1
  have hkind : ∃ a, u.kind = .utility a := by
    obtain ⟨_, hf⟩ := List.mem_filter.mp hu
    match u.kind, hf with
    | .utility a, _ => exact ⟨a, rfl⟩
  obtain ⟨a, hka⟩ := hkind
  exact wf.utility_local u hmem a hka a₁ a₂ (fun p hp => heq p (by
    exact List.mem_flatMap.mpr ⟨u, hu, hp⟩))

-- ============================================================================
-- § 3. Game — KernelGame bridge + solution concepts
-- ============================================================================

/-- MAID as an outcome kernel. -/
noncomputable def MAIDModel.toKernel (m : MAIDModel)
    : GameTheory.Kernel CondPolicy (GameTheory.Payoff Nat) :=
  fun π => m.evalDist π

/-! ### MAID → KernelGame conversion -/

/-- Convert a MAID model to a kernel-based game with per-agent strategies.
    Each agent independently chooses a `CondPolicy`; the joint policy is
    assembled via `mergeCondPolicies` which dispatches each decision node
    to its owning agent's policy. -/
noncomputable def MAIDModel.toKernelGame (m : MAIDModel) :
    GameTheory.KernelGame Nat where
  Strategy := fun _ => CondPolicy
  Outcome := Assign
  utility := m.payoffOf
  outcomeKernel := fun σ => m.evalAssignDist (mergeCondPolicies m.diagram σ)

/-! ### Solution concepts -/

/-- Expected utility for agent `who` under per-agent policies. -/
noncomputable def MAIDModel.eu (m : MAIDModel) (σ : Nat → CondPolicy) (who : Nat) : ℝ :=
  m.toKernelGame.eu σ who

/-- Nash equilibrium for a MAID: no agent can improve EU by unilaterally
    changing their conditional policy. -/
def MAIDModel.IsNash (m : MAIDModel) (σ : Nat → CondPolicy) : Prop :=
  m.toKernelGame.IsNash σ

end MAID
