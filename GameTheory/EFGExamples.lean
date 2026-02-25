import GameTheory.EFG2
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# EFG2 Examples

Example extensive-form game trees using the InfoStructure-based redesign.
No `InfoSetConsistent` proofs needed — consistency is structural.
-/

namespace EFG2

/-! ## InfoStructures for the examples -/

@[reducible] private def seqArity : Nat → Nat
  | 0 | 1 => 2
  | _ => 1

private theorem seqArity_pos : ∀ I, 0 < seqArity I := by
  intro I; unfold seqArity; split <;> omega

@[reducible] private def hdArity : Nat → Nat
  | 1 => 2
  | _ => 1

private theorem hdArity_pos : ∀ I, 0 < hdArity I := by
  intro I; unfold hdArity; split <;> omega

/-- Info structure for seqTree: infoSet 0 → player 0, arity 2;
    infoSet 1 → player 1, arity 2; everything else defaults. -/
abbrev seqInfoS : InfoStructure Nat where
  player | 0 => 0 | _ => 1
  arity := seqArity
  arity_pos := seqArity_pos

/-- Same info structure as seqInfoS (matching pennies has the same shape). -/
abbrev mpInfoS : InfoStructure Nat where
  player | 0 => 0 | _ => 1
  arity := seqArity
  arity_pos := seqArity_pos

/-- Info structure for hiddenDecTree: infoSet 1 → player 0, arity 2. -/
abbrev hdInfoS : InfoStructure Nat where
  player := fun _ => 0
  arity := hdArity
  arity_pos := hdArity_pos

/-! ## Example trees -/

/-- Sequential game: P0 (infoSet=0) picks L/R, then P1 (infoSet=1) picks L/R.
    Payoffs: (LL)=(3,3), (LR)=(0,0), (RL)=(0,0), (RR)=(1,1) -/
noncomputable abbrev seqTree : GameTree Nat seqInfoS :=
  .decision 0 fun
    | 0 => .decision 1 fun
      | 0 => .terminal (fun i => if i == 0 then 3 else 3)
      | 1 => .terminal (fun i => if i == 0 then 0 else 0)
    | 1 => .decision 1 fun
      | 0 => .terminal (fun i => if i == 0 then 0 else 0)
      | 1 => .terminal (fun i => if i == 0 then 1 else 1)

/-- Matching pennies: P0 picks H(0)/T(1), P1 picks H(0)/T(1).
    P1 cannot observe P0's choice (same infoSet=1 = imperfect info). -/
noncomputable abbrev matchingPenniesTree : GameTree Nat mpInfoS :=
  .decision 0 fun
    | 0 => .decision 1 fun
      | 0 => .terminal (fun i => if i == 0 then 1 else -1)
      | 1 => .terminal (fun i => if i == 0 then -1 else 1)
    | 1 => .decision 1 fun
      | 0 => .terminal (fun i => if i == 0 then -1 else 1)
      | 1 => .terminal (fun i => if i == 0 then 1 else -1)

/-- Uniform PMF on `Fin 2` (coin flip). -/
noncomputable def coinFlip : PMF (Fin 2) :=
  PMF.ofFintype (fun _ => (2 : ENNReal)⁻¹) (by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_ofNat]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num))

/-- Hidden decision: chance 50/50, then P0 guesses blind.
    Same infoSet=1 in both branches = imperfect info. -/
noncomputable abbrev hiddenDecTree : GameTree Nat hdInfoS :=
  .chance 1 coinFlip fun
    | 0 => .decision 1 fun
      | 0 => .terminal (fun i => if i == 0 then 1 else 0)
      | 1 => .terminal (fun i => if i == 0 then 0 else 0)
    | 1 => .decision 1 fun
      | 0 => .terminal (fun i => if i == 0 then 0 else 0)
      | 1 => .terminal (fun i => if i == 0 then 1 else 0)

/-! ## WFTree proofs -/

theorem seqTree_wf : WFTree seqTree := allWFTree seqTree
theorem matchingPenniesTree_wf : WFTree matchingPenniesTree := allWFTree matchingPenniesTree
theorem hiddenDecTree_wf : WFTree hiddenDecTree := allWFTree hiddenDecTree

/-! ## evalTotal EU proofs -/

/-- Strategy: always pick the first action. -/
def alwaysFirst : PureStrategy seqInfoS :=
  fun _ => ⟨0, seqInfoS.arity_pos _⟩

/-- Strategy: always pick the last action. -/
def alwaysLast : PureStrategy seqInfoS := fun I =>
  ⟨seqInfoS.arity I - 1,
   Nat.sub_lt (seqInfoS.arity_pos I) Nat.one_pos⟩

/-- Under alwaysFirst, seqTree yields payoff 3 for P0. -/
private noncomputable example :
    seqTree.evalTotal alwaysFirst 0 = 3 := by
  simp only [alwaysFirst, GameTree.evalTotal, seqInfoS, seqArity]
  norm_num

/-- Under alwaysLast, seqTree yields payoff 1 for P0. -/
private noncomputable example :
    seqTree.evalTotal alwaysLast 0 = 1 := by
  simp only [alwaysLast, GameTree.evalTotal, seqInfoS, seqArity]
  norm_num

/-! ## Perfect recall proofs

For these small trees, perfect recall is proved by exhaustive case analysis
on `ReachBy` paths. Each info set appears at most once per root-to-leaf
path, so any two paths to the same info set have identical player
histories. -/

/-- Helper: in seqTree, all playerHistories to any reachable decision node are []. -/
private theorem seqTree_playerHistory_nil :
    ∀ h I (next : Fin (seqInfoS.arity I) → GameTree Nat seqInfoS),
    ReachBy h seqTree (.decision I next) →
    playerHistory seqInfoS (seqInfoS.player I) h = [] := by
  intro h I next hr
  -- seqTree is .decision 0 f
  rcases ReachBy_decision_inv hr with ⟨rfl, rfl, _⟩ | ⟨a, rest, rfl, hr'⟩
  · -- h = [], I = 0: playerHistory _ _ [] = []
    rfl
  · -- h = .action 0 a :: rest, hr' : ReachBy rest (subtree a) (.decision I next)
    -- subtree a is .decision 1 _, so invert again
    fin_cases a <;> (
      rcases ReachBy_decision_inv hr' with ⟨rfl, rfl, _⟩ | ⟨b, rest', rfl, hr''⟩
      · -- rest = [], I = 1
        -- playerHistory seqInfoS 1 [.action 0 _]
        -- player 0 = 0 ≠ 1, so filtered → []
        simp [playerHistory]
      · -- hr'' from a terminal to .decision — impossible
        fin_cases b <;> exact absurd hr'' (by intro h; nomatch h))

/-- seqTree has perfect recall. -/
theorem seqTree_perfectRecall : PerfectRecall seqTree := by
  intro h₁ h₂ I next₁ next₂ hr₁ hr₂
  rw [seqTree_playerHistory_nil h₁ I next₁ hr₁,
      seqTree_playerHistory_nil h₂ I next₂ hr₂]

/-- Helper: in matchingPenniesTree, all playerHistories to any reachable decision node are []. -/
private theorem mpTree_playerHistory_nil :
    ∀ h I (next : Fin (mpInfoS.arity I) → GameTree Nat mpInfoS),
    ReachBy h matchingPenniesTree (.decision I next) →
    playerHistory mpInfoS (mpInfoS.player I) h = [] := by
  intro h I next hr
  rcases ReachBy_decision_inv hr with ⟨rfl, rfl, _⟩ | ⟨a, rest, rfl, hr'⟩
  · rfl
  · fin_cases a <;> (
      rcases ReachBy_decision_inv hr' with ⟨rfl, rfl, _⟩ | ⟨b, rest', rfl, hr''⟩
      · simp [playerHistory]
      · fin_cases b <;> exact absurd hr'' (by intro h; nomatch h))

/-- matchingPenniesTree has perfect recall. -/
theorem matchingPenniesTree_perfectRecall :
    PerfectRecall matchingPenniesTree := by
  intro h₁ h₂ I next₁ next₂ hr₁ hr₂
  rw [mpTree_playerHistory_nil h₁ I next₁ hr₁,
      mpTree_playerHistory_nil h₂ I next₂ hr₂]

/-- Helper: in hiddenDecTree, all playerHistories to any reachable decision node are []. -/
private theorem hdTree_playerHistory_nil :
    ∀ h I (next : Fin (hdInfoS.arity I) → GameTree Nat hdInfoS),
    ReachBy h hiddenDecTree (.decision I next) →
    playerHistory hdInfoS (hdInfoS.player I) h = [] := by
  intro h I next hr
  -- hiddenDecTree is .chance 1 coinFlip f
  rcases ReachBy_chance_inv' hr with ⟨b, rest, rfl, hr'⟩
  -- hr' : ReachBy rest (f b) (.decision I next), f b is .decision 1 _
  fin_cases b <;> (
    rcases ReachBy_decision_inv hr' with ⟨rfl, rfl, _⟩ | ⟨a, rest', rfl, hr''⟩
    · -- rest = [], I = 1, h = [.chance _]
      -- playerHistory hdInfoS 0 [.chance _] = [] (chance steps filtered)
      simp [playerHistory]
    · -- hr'' from terminal to decision — impossible
      fin_cases a <;> exact absurd hr'' (by intro h; nomatch h))

/-- hiddenDecTree has perfect recall. -/
theorem hiddenDecTree_perfectRecall :
    PerfectRecall hiddenDecTree := by
  intro h₁ h₂ I next₁ next₂ hr₁ hr₂
  rw [hdTree_playerHistory_nil h₁ I next₁ hr₁,
      hdTree_playerHistory_nil h₂ I next₂ hr₂]

end EFG2
