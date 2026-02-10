/-!
# Multi-Agent Influence Diagrams (MAID)

Classical MAID representation for reasoning about
strategic interactions with partial information.
This module will connect the DAG-style let-calculus
(LetProtocol.Dag) to the MAID formalism.

Status: stub.
-/

namespace MAID

/-- A decision node in a MAID. -/
structure DecisionNode where
  agent : Nat
  id : Nat
deriving Repr

/-- A multi-agent influence diagram. -/
structure Diagram where
  decisions : List DecisionNode

end MAID
