import GameTheory.EFG
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# EFG Examples

Example extensive-form game trees with payoff evaluations.
-/

namespace EFG

/-- Sequential game: P0 (infoSet=0) picks L/R, then P1 (infoSet=1) picks L/R.
    Payoffs: (LL)=(3,3), (LR)=(0,0), (RL)=(0,0), (RR)=(1,1) -/
noncomputable def seqTree : GameTree Nat :=
  .decision 0 0 2 fun
    | 0 => .decision 1 1 2 fun
      | 0 => .terminal (fun i => if i == 0 then 3 else 3)   -- LL
      | 1 => .terminal (fun i => if i == 0 then 0 else 0)   -- LR
    | 1 => .decision 1 1 2 fun
      | 0 => .terminal (fun i => if i == 0 then 0 else 0)   -- RL
      | 1 => .terminal (fun i => if i == 0 then 1 else 1)   -- RR

/-- Strategy: always pick the first action. -/
def alwaysFirst : PureStrategy := fun _ _ h => ⟨0, h⟩

/-- Strategy: always pick the last action. -/
def alwaysLast : PureStrategy := fun _ n h => ⟨n - 1, Nat.sub_lt h Nat.one_pos⟩

/-! ## Golden trees -/

/-- Matching pennies: P0 picks H(0)/T(1), P1 picks H(0)/T(1).
    P1 cannot observe P0's choice (same infoSetId=1 for both subtrees = imperfect info).
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
    Chance node splits, then P0 (infoSet=1) decides without seeing chance outcome.
    Same infoSetId=1 in both branches = imperfect info. -/
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

theorem hiddenDecTree_wf : WFTree hiddenDecTree := by
  apply WFTree.chance _ _ _ (by norm_num)
  intro b; fin_cases b <;>
    exact WFTree.decision _ _ _ _ (by norm_num)
      (fun a => by fin_cases a <;> exact WFTree.terminal _)

/-! ## evalTotal EU proofs -/

/-- Under alwaysFirst (pick action 0), seqTree yields payoff 3 for P0 via evalTotal. -/
private noncomputable example :
    seqTree.euPure alwaysFirst 0 = 3 := by
  simp only [seqTree, alwaysFirst, GameTree.euPure, GameTree.evalTotal]
  norm_num

/-- Under alwaysLast (pick last action), seqTree yields payoff 1 for P0 via evalTotal. -/
private noncomputable example :
    seqTree.euPure alwaysLast 0 = 1 := by
  simp only [seqTree, alwaysLast, GameTree.euPure, GameTree.evalTotal]
  norm_num

/-! ## InfoSetConsistent proofs -/

/-- All decision nodes in seqTree have (infoSetId=0,player=0,arity=2)
    or (infoSetId=1,player=1,arity=2). -/
private theorem seqTree_nodes : ∀ isId p a, DecisionNodeIn isId p a seqTree →
    (isId = 0 ∧ p = 0 ∧ a = 2) ∨ (isId = 1 ∧ p = 1 ∧ a = 2) := by
  intro isId p a h
  simp only [seqTree] at h
  rcases DecisionNodeIn_decision_inv h with ⟨rfl, rfl, rfl⟩ | ⟨b, hb⟩
  · left; exact ⟨rfl, rfl, rfl⟩
  · right
    fin_cases b <;> {
      rcases DecisionNodeIn_decision_inv hb with ⟨rfl, rfl, rfl⟩ | ⟨a', ha⟩
      · exact ⟨rfl, rfl, rfl⟩
      · fin_cases a' <;> cases ha
    }

theorem seqTree_infoset_consistent : InfoSetConsistent seqTree := by
  intro isId p₁ p₂ a₁ a₂ h₁ h₂
  have c₁ := seqTree_nodes isId p₁ a₁ h₁
  have c₂ := seqTree_nodes isId p₂ a₂ h₂
  rcases c₁ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    rcases c₂ with ⟨h, rfl, rfl⟩ | ⟨h, rfl, rfl⟩ <;>
    first | exact ⟨rfl, rfl⟩ | exact absurd h (by omega)

/-- All decision nodes in matchingPenniesTree have
    (infoSetId=0,player=0,arity=2) or (infoSetId=1,player=1,arity=2). -/
private theorem matchingPenniesTree_nodes :
    ∀ isId p a, DecisionNodeIn isId p a matchingPenniesTree →
    (isId = 0 ∧ p = 0 ∧ a = 2) ∨ (isId = 1 ∧ p = 1 ∧ a = 2) := by
  intro isId p a h
  simp only [matchingPenniesTree] at h
  rcases DecisionNodeIn_decision_inv h with ⟨rfl, rfl, rfl⟩ | ⟨b, hb⟩
  · left; exact ⟨rfl, rfl, rfl⟩
  · right
    fin_cases b <;> {
      rcases DecisionNodeIn_decision_inv hb with ⟨rfl, rfl, rfl⟩ | ⟨a', ha⟩
      · exact ⟨rfl, rfl, rfl⟩
      · fin_cases a' <;> cases ha
    }

theorem matchingPenniesTree_infoset_consistent :
    InfoSetConsistent matchingPenniesTree := by
  intro isId p₁ p₂ a₁ a₂ h₁ h₂
  have c₁ := matchingPenniesTree_nodes isId p₁ a₁ h₁
  have c₂ := matchingPenniesTree_nodes isId p₂ a₂ h₂
  rcases c₁ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    rcases c₂ with ⟨h, rfl, rfl⟩ | ⟨h, rfl, rfl⟩ <;>
    first | exact ⟨rfl, rfl⟩ | exact absurd h (by omega)

/-- All decision nodes in hiddenDecTree have (infoSetId=1,player=0,arity=2). -/
private theorem hiddenDecTree_nodes : ∀ isId p a, DecisionNodeIn isId p a hiddenDecTree →
    isId = 1 ∧ p = 0 ∧ a = 2 := by
  intro isId p a h
  simp only [hiddenDecTree] at h
  rcases DecisionNodeIn_chance_inv h with ⟨b, hb⟩
  fin_cases b <;> {
    rcases DecisionNodeIn_decision_inv hb with ⟨rfl, rfl, rfl⟩ | ⟨a', ha⟩
    · exact ⟨rfl, rfl, rfl⟩
    · fin_cases a' <;> cases ha
  }

theorem hiddenDecTree_infoset_consistent : InfoSetConsistent hiddenDecTree := by
  intro isId p₁ p₂ a₁ a₂ h₁ h₂
  obtain ⟨_, rfl, rfl⟩ := hiddenDecTree_nodes isId p₁ a₁ h₁
  obtain ⟨_, rfl, rfl⟩ := hiddenDecTree_nodes isId p₂ a₂ h₂
  exact ⟨rfl, rfl⟩

end EFG
