import GameTheory.EFG
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# EFG Examples

Example extensive-form game trees with payoff evaluations.
-/

namespace EFG

/-- Sequential game: P0 (pid=0) picks L/R, then P1 (pid=1) picks L/R.
    Payoffs: (LL)=(3,3), (LR)=(0,0), (RL)=(0,0), (RR)=(1,1) -/
noncomputable def seqTree : GameTree Nat :=
  .decision 0 0 2 fun
    | 0 => .decision 1 1 2 fun
      | 0 => .terminal (fun i => if i == 0 then 3 else 3)   -- LL
      | 1 => .terminal (fun i => if i == 0 then 0 else 0)   -- LR
    | 1 => .decision 1 1 2 fun
      | 0 => .terminal (fun i => if i == 0 then 0 else 0)   -- RL
      | 1 => .terminal (fun i => if i == 0 then 1 else 1)   -- RR

/-- Strategy: always pick action 0 (Left). -/
def alwaysLeft : PureStrategy := fun _ => 0

/-- Strategy: always pick action 1 (Right). -/
def alwaysRight : PureStrategy := fun _ => 1

/-! ## Golden trees -/

/-- Matching pennies: P0 picks H(0)/T(1), P1 picks H(0)/T(1).
    P1 cannot observe P0's choice (same pid=1 for both subtrees = imperfect info).
    P0 wins if choices match; P1 wins if they differ. -/
noncomputable def matchingPenniesTree : GameTree Nat :=
  .decision 0 0 2 fun
    | 0 => .decision 1 1 2 fun   -- P0 picks Heads
      | 0 => .terminal (fun i => if i == 0 then 1 else -1)   -- HH: P0 wins
      | 1 => .terminal (fun i => if i == 0 then -1 else 1)   -- HT: P1 wins
    | 1 => .decision 1 1 2 fun   -- P0 picks Tails
      | 0 => .terminal (fun i => if i == 0 then -1 else 1)   -- TH: P1 wins
      | 1 => .terminal (fun i => if i == 0 then 1 else -1)   -- TT: P0 wins

/-- Uniform PMF on `Fin 2` (coin flip). -/
noncomputable def coinFlip : PMF (Fin 2) :=
  PMF.ofFintype (fun _ => (2 : ENNReal)⁻¹) (by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num))

/-- Hidden decision: chance 50/50, then P0 guesses blind.
    Chance node splits, then P0 (pid=1) decides without seeing chance outcome.
    Same pid=1 in both branches = imperfect info. -/
noncomputable def hiddenDecTree : GameTree Nat :=
  .chance 2 coinFlip fun
    | 0 => .decision 1 0 2 fun   -- Nature picks Left
      | 0 => .terminal (fun i => if i == 0 then 1 else 0)   -- correct guess
      | 1 => .terminal (fun i => if i == 0 then 0 else 0)   -- wrong guess
    | 1 => .decision 1 0 2 fun   -- Nature picks Right
      | 0 => .terminal (fun i => if i == 0 then 0 else 0)   -- wrong guess
      | 1 => .terminal (fun i => if i == 0 then 1 else 0)   -- correct guess

/-! ## WFTree proofs -/

theorem seqTree_wf : WFTree seqTree := by
  apply WFTree.decision _ _ _ _ (by norm_num)
  intro a; fin_cases a <;>
    exact WFTree.decision _ _ _ _ (by norm_num)
      (fun b => by fin_cases b <;> exact WFTree.terminal _)

theorem matchingPenniesTree_wf : WFTree matchingPenniesTree := by
  apply WFTree.decision _ _ _ _ (by norm_num)
  intro a; fin_cases a <;>
    exact WFTree.decision _ _ _ _ (by norm_num)
      (fun b => by fin_cases b <;> exact WFTree.terminal _)

/-! ## evalTotal EU proofs -/

/-- Under (Left, Left), seqTree yields payoff 3 for P0 via evalTotal. -/
private noncomputable example :
    seqTree.euPure alwaysLeft 0 = 3 := by
  simp only [seqTree, alwaysLeft, GameTree.euPure, GameTree.evalTotal]
  norm_num

/-- Under (Right, Right), seqTree yields payoff 1 for P0 via evalTotal. -/
private noncomputable example :
    seqTree.euPure alwaysRight 0 = 1 := by
  simp only [seqTree, alwaysRight, GameTree.euPure, GameTree.evalTotal]
  norm_num

end EFG
