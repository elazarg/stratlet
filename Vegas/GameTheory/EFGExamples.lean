import Vegas.GameTheory.EFG

/-!
# EFG Examples

Example extensive-form game trees with payoff evaluations.
-/

namespace EFG

/-- Sequential game: P0 (pid=0) picks L/R, then P1 (pid=1) picks L/R.
    Payoffs: (LL)=(3,3), (LR)=(0,0), (RL)=(0,0), (RR)=(1,1) -/
def seqTree : GameTree Nat :=
  .decision 0 0 [
    -- P0 picks Left
    .decision 1 1 [
      .terminal (fun i => if i == 0 then 3 else 3),   -- LL
      .terminal (fun i => if i == 0 then 0 else 0)    -- LR
    ],
    -- P0 picks Right
    .decision 1 1 [
      .terminal (fun i => if i == 0 then 0 else 0),   -- RL
      .terminal (fun i => if i == 0 then 1 else 1)    -- RR
    ]
  ]

/-- Strategy: always pick action 0 (Left). -/
def alwaysLeft : PureStrategy := fun _ => 0

/-- Strategy: always pick action 1 (Right). -/
def alwaysRight : PureStrategy := fun _ => 1

/-- Under (Left, Left), seqTree yields payoff 3 for P0. -/
private noncomputable example :
    GameTree.evalAux alwaysLeft 1000 seqTree 0 = 3 := by
  simp only [seqTree, alwaysLeft, GameTree.evalAux,
    List.getElem?_cons_zero]
  norm_num

/-- Under (Left, Left), seqTree yields payoff 3 for P1. -/
private noncomputable example :
    GameTree.evalAux alwaysLeft 1000 seqTree 1 = 3 := by
  simp only [seqTree, alwaysLeft, GameTree.evalAux,
    List.getElem?_cons_zero]
  norm_num

/-- Under (Right, Right), seqTree yields payoff 1 for P0. -/
private noncomputable example :
    GameTree.evalAux alwaysRight 1000 seqTree 0 = 1 := by
  simp only [seqTree, alwaysRight, GameTree.evalAux,
    List.getElem?_cons_succ, List.getElem?_cons_zero]
  norm_num

/-- Under (Right, Right), seqTree yields payoff 1 for P1. -/
private noncomputable example :
    GameTree.evalAux alwaysRight 1000 seqTree 1 = 1 := by
  simp only [seqTree, alwaysRight, GameTree.evalAux,
    List.getElem?_cons_succ, List.getElem?_cons_zero]
  norm_num

end EFG
