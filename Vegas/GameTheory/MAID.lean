import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.NNReal.Basic

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
deriving Repr

/-- A multi-agent influence diagram. -/
structure Diagram where
  nodes : List Node
  nodup_ids : (nodes.map Node.id).Nodup
  parents_exist : ∀ n ∈ nodes, ∀ pid ∈ n.parents,
    ∃ m ∈ nodes, m.id = pid
  acyclic : Prop

/-- A policy maps decision node ids to distributions over values
    (represented as lists of non-negative rationals). -/
def Policy := Nat → List NNReal

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

end MAID
