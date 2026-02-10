/-!
# Extensive-Form Games (EFG)

Classical extensive-form game representation.
This module will connect the strategic let-calculus
(LetProtocol) to classical game-theory structures.

Status: stub.
-/

namespace EFG

/-- An extensive-form game tree node. -/
structure Node where
  id : Nat
deriving Repr

/-- An extensive-form game. -/
structure Game where
  nodes : List Node

end EFG
