import GameTheory.EFG

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

/-! ## Golden trees -/

/-- Matching pennies: P0 picks H(0)/T(1), P1 picks H(0)/T(1).
    P1 cannot observe P0's choice (same pid=1 for both subtrees = imperfect info).
    P0 wins if choices match; P1 wins if they differ. -/
def matchingPenniesTree : GameTree Nat :=
  .decision 0 0 [
    -- P0 picks Heads
    .decision 1 1 [
      .terminal (fun i => if i == 0 then 1 else -1),   -- HH: P0 wins
      .terminal (fun i => if i == 0 then -1 else 1)    -- HT: P1 wins
    ],
    -- P0 picks Tails
    .decision 1 1 [
      .terminal (fun i => if i == 0 then -1 else 1),   -- TH: P1 wins
      .terminal (fun i => if i == 0 then 1 else -1)    -- TT: P0 wins
    ]
  ]

/-- Hidden decision: chance 50/50, then P0 guesses blind.
    Chance node splits, then P0 (pid=1) decides without seeing chance outcome.
    Same pid=1 in both branches = imperfect info. -/
noncomputable def hiddenDecTree : GameTree Nat :=
  .chance [
    -- Nature picks Left
    (.decision 1 0 [
      .terminal (fun i => if i == 0 then 1 else 0),   -- correct guess
      .terminal (fun i => if i == 0 then 0 else 0)    -- wrong guess
    ], (2⁻¹ : NNReal)),
    -- Nature picks Right
    (.decision 1 0 [
      .terminal (fun i => if i == 0 then 0 else 0),   -- wrong guess
      .terminal (fun i => if i == 0 then 1 else 0)    -- correct guess
    ], (2⁻¹ : NNReal))
  ]

/-! ## WFTree proofs for golden trees -/

theorem seqTree_wf : WFTree seqTree :=
  .decision 0 0 _ (by decide) fun a ha => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
    rcases ha with rfl | rfl <;>
      exact .decision 1 1 _ (by decide) (fun b hb => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
        rcases hb with rfl | rfl <;> exact .terminal _)

theorem matchingPenniesTree_wf : WFTree matchingPenniesTree :=
  .decision 0 0 _ (by decide) fun a ha => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
    rcases ha with rfl | rfl <;>
      exact .decision 1 1 _ (by decide) (fun b hb => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
        rcases hb with rfl | rfl <;> exact .terminal _)

/-! ## evalTotal EU proofs -/

/-- Under (Left, Left), seqTree yields payoff 3 for P0 via evalTotal. -/
private noncomputable example :
    seqTree.euPure alwaysLeft 0 = 3 := by
  simp only [seqTree, alwaysLeft, GameTree.euPure, GameTree.evalTotal,
    GameTree.evalTotal.go_nth]
  norm_num

/-- Under (Right, Right), seqTree yields payoff 1 for P0 via evalTotal. -/
private noncomputable example :
    seqTree.euPure alwaysRight 0 = 1 := by
  simp only [seqTree, alwaysRight, GameTree.euPure, GameTree.evalTotal,
    GameTree.evalTotal.go_nth]
  norm_num

end EFG
