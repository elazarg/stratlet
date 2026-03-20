import Vegas.GameProperties
import GameTheory.Concepts.PotentialGame
import GameTheory.Concepts.Rationalizability
import GameTheory.Concepts.WelfareTheorems
import GameTheory.Concepts.ZeroSum
import GameTheory.Concepts.ConstantSum
import GameTheory.Concepts.Minimax
import GameTheory.Concepts.SecurityStrategy
import GameTheory.Concepts.PriceOfAnarchy
import GameTheory.Theorems.Minimax

/-!
# Vegas structural game-theory corollaries

Corollaries for structural properties and finite-game theorems on Vegas games.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Every exact-potential Vegas game is an ordinal-potential Vegas game. -/
theorem IsExactPotential.toOrdinal (p : VegasCore P L Γ)
    (env : VEnv L Γ) (hd : NormalizedDists p)
    {Φ : StrategyProfile p env hd → ℝ}
    (hΦ : IsExactPotential p env hd Φ) :
    IsOrdinalPotential p env hd Φ := by
  simpa [IsExactPotential, IsOrdinalPotential] using
    (KernelGame.IsExactPotential.toOrdinal
      (G := Game p env hd) hΦ)

/-- A maximizer of a Vegas exact potential is Vegas Nash. -/
theorem IsExactPotential.nash_of_maximizer (p : VegasCore P L Γ)
    (env : VEnv L Γ) (hd : NormalizedDists p)
    {Φ : StrategyProfile p env hd → ℝ}
    (hΦ : IsExactPotential p env hd Φ)
    {σ : StrategyProfile p env hd}
    (hmax : ∀ τ : StrategyProfile p env hd, Φ σ ≥ Φ τ) :
    IsNash p env hd σ := by
  simpa [IsExactPotential, IsNash] using
    (KernelGame.IsExactPotential.nash_of_maximizer
      (G := Game p env hd) hΦ hmax)

/-- A maximizer of a Vegas ordinal potential is Vegas Nash. -/
theorem IsOrdinalPotential.nash_of_maximizer (p : VegasCore P L Γ)
    (env : VEnv L Γ) (hd : NormalizedDists p)
    {Φ : StrategyProfile p env hd → ℝ}
    (hΦ : IsOrdinalPotential p env hd Φ)
    {σ : StrategyProfile p env hd}
    (hmax : ∀ τ : StrategyProfile p env hd, Φ σ ≥ Φ τ) :
    IsNash p env hd σ := by
  simpa [IsOrdinalPotential, IsNash] using
    (KernelGame.IsOrdinalPotential.nash_of_maximizer
      (G := Game p env hd) hΦ hmax)

/-- In a Vegas ordinal-potential game, Nash is equivalent to local optimality
of the potential. -/
theorem IsOrdinalPotential.isNash_iff_local_maximizer (p : VegasCore P L Γ)
    (env : VEnv L Γ) (hd : NormalizedDists p)
    {Φ : StrategyProfile p env hd → ℝ}
    (hΦ : IsOrdinalPotential p env hd Φ)
    {σ : StrategyProfile p env hd} :
    IsNash p env hd σ ↔
      ∀ who (s' : Strategy p env hd who), Φ σ ≥ Φ (Function.update σ who s') := by
  simpa [IsOrdinalPotential, IsNash, Strategy] using
    (KernelGame.IsOrdinalPotential.isNash_iff_local_maximizer
      (G := Game p env hd) hΦ
      (σ := σ))

/-- Surviving round `n + 1` of Vegas rationalizability implies surviving round `n`. -/
theorem Survives.prev {p : VegasCore P L Γ}
    {env : VEnv L Γ} {hd : NormalizedDists p}
    {n : ℕ} {who : P} {s : Strategy p env hd who}
    (h : Survives p env hd (n + 1) who s) :
    Survives p env hd n who s := by
  simpa [Survives] using
    (KernelGame.Survives.prev (G := Game p env hd) h)

/-- Vegas survival is monotone in the round number. -/
theorem Survives.mono {p : VegasCore P L Γ}
    {env : VEnv L Γ} {hd : NormalizedDists p}
    {m n : ℕ} (hmn : m ≤ n)
    {who : P} {s : Strategy p env hd who}
    (h : Survives p env hd n who s) :
    Survives p env hd m who s := by
  simpa [Survives] using
    (KernelGame.Survives.mono (G := Game p env hd) hmn h)

/-- Vegas Nash strategies survive all rounds of iterated strict-dominance elimination. -/
theorem IsNash.survives {p : VegasCore P L Γ}
    {env : VEnv L Γ} {hd : NormalizedDists p}
    {σ : StrategyProfile p env hd} (hN : IsNash p env hd σ) :
    ∀ (n : ℕ) (who : P), Survives p env hd n who (σ who) := by
  simpa [IsNash, Survives] using
    (KernelGame.IsNash.survives (G := Game p env hd) hN)

/-- Vegas Nash strategies are rationalizable. -/
theorem IsNash.isRationalizable {p : VegasCore P L Γ}
    {env : VEnv L Γ} {hd : NormalizedDists p}
    {σ : StrategyProfile p env hd} (hN : IsNash p env hd σ) (who : P) :
    IsRationalizable p env hd who (σ who) := by
  simpa [IsNash, IsRationalizable] using
    (KernelGame.IsNash.isRationalizable
      (G := Game p env hd) hN who)

/-- A Vegas dominant strategy survives all rounds of elimination under a
dominant profile witness. -/
theorem IsDominant.survives {p : VegasCore P L Γ}
    {env : VEnv L Γ} {hd : NormalizedDists p}
    {who : P} {s : Strategy p env hd who}
    (hdom : IsDominant p env hd who s)
    (σ₀ : StrategyProfile p env hd) (hσ₀ : σ₀ who = s)
    (hdom_all : ∀ j, IsDominant p env hd j (σ₀ j)) :
    ∀ n, Survives p env hd n who s := by
  simpa [IsDominant, Survives] using
    (KernelGame.IsDominant.survives
      (G := Game p env hd) hdom σ₀ hσ₀ hdom_all)

/-- A Vegas rationalizable strategy is not globally strictly dominated. -/
theorem IsRationalizable.not_globally_dominated {p : VegasCore P L Γ}
    {env : VEnv L Γ} {hd : NormalizedDists p}
    {who : P} {s : Strategy p env hd who}
    (hs : IsRationalizable p env hd who s) :
    ¬ ∃ t : Strategy p env hd who,
      ∀ (σ : StrategyProfile p env hd),
        eu p env hd (Function.update σ who t) who >
          eu p env hd (Function.update σ who s) who := by
  simpa [IsRationalizable, Strategy, StrategyProfile, eu] using
    (KernelGame.IsRationalizable.not_globally_dominated
      (G := Game p env hd) hs)

/-- Vegas guarantees are monotone in the guaranteed value. -/
theorem Guarantees.mono {p : VegasCore P L Γ}
    {env : VEnv L Γ} {hd : NormalizedDists p}
    {who : P} {s : Strategy p env hd who} {v v' : ℝ}
    (hv : v' ≤ v) (hg : Guarantees p env hd who s v) :
    Guarantees p env hd who s v' := by
  simpa [Guarantees] using
    (KernelGame.Guarantees.mono
      (G := Game p env hd) hv hg)

/-- In 2-player Vegas games, saddle points are exactly Nash equilibria. -/
theorem isSaddlePoint_iff_isNash
    (p : VegasCore (Fin 2) L Γ) (env : VEnv L Γ)
    (hd : NormalizedDists p) (σ : StrategyProfile p env hd) :
    IsSaddlePoint p env hd σ ↔ IsNash p env hd σ := by
  simpa [IsSaddlePoint, IsNash] using
    (KernelGame.isSaddlePoint_iff_isNash
      (G := Game p env hd) σ)

/-- Worst-case EU is a lower bound on Vegas expected utility. -/
theorem worstCaseEU_le (p : VegasCore P L Γ)
    (env : VEnv L Γ) (hd : NormalizedDists p)
    [Fintype (StrategyProfile p env hd)]
    [∀ who, Fintype (Strategy p env hd who)]
    [∀ who, Nonempty (Strategy p env hd who)]
    [Nonempty (StrategyProfile p env hd)]
    (who : P) (s : Strategy p env hd who) (σ : StrategyProfile p env hd) :
    worstCaseEU p env hd who s ≤ eu p env hd (Function.update σ who s) who := by
  classical
  have hupd :
      @Function.update P (Game p env hd).Strategy (Classical.decEq P) σ who s =
        Function.update σ who s := by
    funext i
    by_cases hi : i = who <;> simp [Function.update, hi]
  simpa [worstCaseEU, eu, hupd] using
    (KernelGame.worstCaseEU_le
      (G := Game p env hd) who s σ)

/-- Vegas guarantees are equivalent to worst-case EU lower bounds. -/
theorem guarantees_iff_worstCaseEU_ge (p : VegasCore P L Γ)
    (env : VEnv L Γ) (hd : NormalizedDists p)
    [Fintype (StrategyProfile p env hd)]
    [∀ who, Fintype (Strategy p env hd who)]
    [∀ who, Nonempty (Strategy p env hd who)]
    [Nonempty (StrategyProfile p env hd)]
    (who : P) (s : Strategy p env hd who) (v : ℝ) :
    Guarantees p env hd who s v ↔ worstCaseEU p env hd who s ≥ v := by
  simpa [Guarantees, worstCaseEU] using
    (KernelGame.guarantees_iff_worstCaseEU_ge
      (G := Game p env hd) who s v)

/-- In a Vegas Nash equilibrium, each player's EU is at least their security level. -/
theorem nash_eu_ge_securityLevel (p : VegasCore P L Γ)
    (env : VEnv L Γ) (hd : NormalizedDists p)
    [Fintype (StrategyProfile p env hd)]
    [∀ who, Fintype (Strategy p env hd who)]
    [∀ who, Nonempty (Strategy p env hd who)]
    [Nonempty (StrategyProfile p env hd)]
    {σ : StrategyProfile p env hd}
    (hN : IsNash p env hd σ) (who : P) :
    eu p env hd σ who ≥ securityLevel p env hd who := by
  classical
  simp only [securityLevel]
  apply Finset.sup'_le
  intro s _
  calc
    worstCaseEU p env hd who s ≤ eu p env hd (Function.update σ who s) who :=
      worstCaseEU_le p env hd who s σ
    _ ≤ eu p env hd σ who := by
      have hdev : eu p env hd σ who ≥ eu p env hd (Function.update σ who s) who := by
        simpa [IsNash, eu] using hN who s
      linarith

/-- A Vegas dominant strategy achieves at least the security level. -/
theorem IsDominant.eu_ge_securityLevel (p : VegasCore P L Γ)
    (env : VEnv L Γ) (hd : NormalizedDists p)
    [Fintype (StrategyProfile p env hd)]
    [∀ who, Fintype (Strategy p env hd who)]
    [∀ who, Nonempty (Strategy p env hd who)]
    [Nonempty (StrategyProfile p env hd)]
    {who : P} {s : Strategy p env hd who}
    (hdom : IsDominant p env hd who s)
    (σ : StrategyProfile p env hd) :
    eu p env hd (Function.update σ who s) who ≥ securityLevel p env hd who := by
  classical
  simp only [securityLevel]
  apply Finset.sup'_le
  intro t _
  calc
    worstCaseEU p env hd who t ≤ eu p env hd (Function.update σ who t) who :=
      worstCaseEU_le p env hd who t σ
    _ ≤ eu p env hd (Function.update σ who s) who := by
      have hle : eu p env hd (Function.update σ who s) who ≥
          eu p env hd (Function.update σ who t) who := by
        simpa [IsDominant, eu] using hdom σ t
      linarith

/-- Worst-case EU gives a Vegas guarantee. -/
theorem worstCaseEU_guarantees (p : VegasCore P L Γ)
    (env : VEnv L Γ) (hd : NormalizedDists p)
    [Fintype (StrategyProfile p env hd)]
    [∀ who, Fintype (Strategy p env hd who)]
    [∀ who, Nonempty (Strategy p env hd who)]
    [Nonempty (StrategyProfile p env hd)]
    (who : P) (s : Strategy p env hd who) :
    ∀ σ : StrategyProfile p env hd,
      eu p env hd (Function.update σ who s) who ≥ worstCaseEU p env hd who s := by
  classical
  intro σ
  have hupd :
      @Function.update P (Game p env hd).Strategy (Classical.decEq P) σ who s =
        Function.update σ who s := by
    funext i
    by_cases hi : i = who <;> simp [Function.update, hi]
  simpa [eu, worstCaseEU, hupd] using
    (KernelGame.worstCaseEU_guarantees
      (G := Game p env hd) who s σ)

/-- Any uniform lower bound on Vegas expected utility is bounded by the security level. -/
theorem le_securityLevel_of_forall_eu_ge (p : VegasCore P L Γ)
    (env : VEnv L Γ) (hd : NormalizedDists p)
    [Fintype (StrategyProfile p env hd)]
    [∀ who, Fintype (Strategy p env hd who)]
    [∀ who, Nonempty (Strategy p env hd who)]
    [Nonempty (StrategyProfile p env hd)]
    (who : P) (s : Strategy p env hd who) (v : ℝ)
    (hg : ∀ σ : StrategyProfile p env hd,
      eu p env hd (Function.update σ who s) who ≥ v) :
    v ≤ securityLevel p env hd who := by
  classical
  have hg' : ∀ σ : StrategyProfile p env hd,
      (Game p env hd).eu
        (@Function.update P (Game p env hd).Strategy (Classical.decEq P) σ who s) who ≥ v := by
    intro σ
    have hupd :
        @Function.update P (Game p env hd).Strategy (Classical.decEq P) σ who s =
          Function.update σ who s := by
      funext i
      by_cases hi : i = who <;> simp [Function.update, hi]
    simpa [eu, hupd] using hg σ
  simpa [securityLevel] using
    (KernelGame.le_securityLevel_of_forall_eu_ge
      (G := Game p env hd) who s v hg')

/-- A Vegas security strategy exists under the finite hypotheses of `GameTheory`. -/
theorem exists_securityStrategy (p : VegasCore P L Γ)
    (env : VEnv L Γ) (hd : NormalizedDists p)
    [Fintype (StrategyProfile p env hd)]
    [∀ who, Fintype (Strategy p env hd who)]
    [∀ who, Nonempty (Strategy p env hd who)]
    [Nonempty (StrategyProfile p env hd)]
    (who : P) :
    ∃ s : Strategy p env hd who, worstCaseEU p env hd who s = securityLevel p env hd who := by
  simpa [worstCaseEU, securityLevel] using
    (KernelGame.exists_securityStrategy
      (G := Game p env hd) who)

/-- In a Vegas team game, social welfare is a scalar multiple of any player's EU. -/
theorem IsTeamGame.socialWelfare_eq [Fintype P] [Inhabited P]
    (p : VegasCore P L Γ) (env : VEnv L Γ)
    (hd : NormalizedDists p) (hteam : IsTeamGame p env hd)
    (σ : StrategyProfile p env hd) (i : P) :
    socialWelfare p env hd σ = Fintype.card P * eu p env hd σ i := by
  simpa [IsTeamGame, socialWelfare, eu] using
    (KernelGame.IsTeamGame.socialWelfare_eq
      (G := Game p env hd) hteam σ i)

/-- Nonnegative Vegas expected utilities imply nonnegative social welfare. -/
theorem socialWelfare_nonneg_of_nonneg_eu [Fintype P]
    (p : VegasCore P L Γ) (env : VEnv L Γ)
    (hd : NormalizedDists p) {σ : StrategyProfile p env hd}
    (h : ∀ i, eu p env hd σ i ≥ 0) :
    socialWelfare p env hd σ ≥ 0 := by
  simpa [socialWelfare, eu] using
    (KernelGame.socialWelfare_nonneg_of_nonneg_eu
      (G := Game p env hd) h)

/-- In a Vegas zero-sum game with finite outcome space, social welfare is zero. -/
theorem IsZeroSum.socialWelfare_eq_zero [Fintype P]
    (p : VegasCore P L Γ) (env : VEnv L Γ)
    (hd : NormalizedDists p) [Finite (Outcome P)]
    (hzs : IsZeroSum p env hd) (σ : StrategyProfile p env hd) :
    socialWelfare p env hd σ = 0 := by
  let _ : Fintype (Outcome P) := Fintype.ofFinite (Outcome P)
  let _ : Fintype (toKernelGame p env hd).Outcome := by
    simpa [toKernelGame] using (inferInstance : Fintype (Outcome P))
  simpa [IsZeroSum, socialWelfare] using
    (KernelGame.IsZeroSum.socialWelfare_eq_zero
      (G := toKernelGame p env hd) hzs σ)

/-- In a 2-player Vegas zero-sum game with finite outcome space, one player's
EU is the negation of the other's. -/
theorem IsZeroSum.eu_neg
    (p : VegasCore (Fin 2) L Γ) (env : VEnv L Γ)
    (hd : NormalizedDists p) [Finite (Outcome (Fin 2))]
    (hzs : IsZeroSum p env hd) (σ : StrategyProfile p env hd) :
    eu p env hd σ 0 = - eu p env hd σ 1 := by
  let _ : Fintype (Outcome (Fin 2)) := Fintype.ofFinite (Outcome (Fin 2))
  let _ : Fintype (toKernelGame p env hd).Outcome := by
    simpa [toKernelGame] using (inferInstance : Fintype (Outcome (Fin 2)))
  simpa [IsZeroSum, eu] using
    (KernelGame.IsZeroSum.eu_neg
      (G := toKernelGame p env hd) hzs σ)

/-- In a Vegas constant-sum game with finite outcome space, social welfare is constant. -/
theorem IsConstantSum.socialWelfare_eq [Fintype P]
    (p : VegasCore P L Γ) (env : VEnv L Γ)
    (hd : NormalizedDists p) [Finite (Outcome P)]
    {c : ℝ} (hcs : IsConstantSum p env hd c) (σ : StrategyProfile p env hd) :
    socialWelfare p env hd σ = c := by
  let _ : Fintype (Outcome P) := Fintype.ofFinite (Outcome P)
  let _ : Fintype (toKernelGame p env hd).Outcome := by
    simpa [toKernelGame] using (inferInstance : Fintype (Outcome P))
  simpa [IsConstantSum, socialWelfare] using
    (KernelGame.IsConstantSum.socialWelfare_eq
      (G := toKernelGame p env hd) hcs σ)

/-- In a 2-player Vegas constant-sum game, player 0's EU is determined by player 1's. -/
theorem IsConstantSum.eu_determined
    (p : VegasCore (Fin 2) L Γ) (env : VEnv L Γ)
    (hd : NormalizedDists p) [Finite (Outcome (Fin 2))]
    {c : ℝ} (hcs : IsConstantSum p env hd c) (σ : StrategyProfile p env hd) :
    eu p env hd σ 0 = c - eu p env hd σ 1 := by
  let _ : Fintype (Outcome (Fin 2)) := Fintype.ofFinite (Outcome (Fin 2))
  let _ : Fintype (toKernelGame p env hd).Outcome := by
    simpa [toKernelGame] using (inferInstance : Fintype (Outcome (Fin 2)))
  simpa [IsConstantSum, eu] using
    (KernelGame.IsConstantSum.eu_determined
      (G := toKernelGame p env hd) hcs σ)

/-- A Vegas zero-sum game is a Vegas constant-sum game with constant `0`. -/
theorem IsZeroSum.isConstantSum_zero [Fintype P]
    (p : VegasCore P L Γ) (env : VEnv L Γ)
    (hd : NormalizedDists p) (hzs : IsZeroSum p env hd) :
    IsConstantSum p env hd 0 := by
  simpa [IsZeroSum, IsConstantSum] using
    (KernelGame.IsZeroSum.isConstantSum_zero
      (G := toKernelGame p env hd) hzs)

/-- In a 2-player Vegas constant-sum game, all Nash equilibria give the same EU. -/
theorem IsConstantSum.nash_eu_eq
    (p : VegasCore (Fin 2) L Γ) (env : VEnv L Γ)
    (hd : NormalizedDists p) [Finite (Outcome (Fin 2))]
    {c : ℝ} (hcs : IsConstantSum p env hd c)
    {σ τ : StrategyProfile p env hd}
    (hNσ : IsNash p env hd σ) (hNτ : IsNash p env hd τ) :
    eu p env hd σ 0 = eu p env hd τ 0 := by
  let _ : Fintype (Outcome (Fin 2)) := Fintype.ofFinite (Outcome (Fin 2))
  let _ : Fintype (toKernelGame p env hd).Outcome := by
    simpa [toKernelGame] using (inferInstance : Fintype (Outcome (Fin 2)))
  simpa [IsConstantSum, IsNash, eu] using
    (KernelGame.IsConstantSum.nash_eu_eq
      (G := toKernelGame p env hd) hcs hNσ hNτ)

/-- Social welfare is bounded above by the Vegas optimal welfare. -/
theorem welfare_le_optimal [Fintype P]
    (p : VegasCore P L Γ) (env : VEnv L Γ)
    (hd : NormalizedDists p) (σ : StrategyProfile p env hd)
    (hbdd : BddAbove (Set.range (fun τ => socialWelfare p env hd τ))) :
    socialWelfare p env hd σ ≤ optimalWelfare p env hd := by
  simpa [socialWelfare, optimalWelfare] using
    (KernelGame.welfare_le_optimal
      (G := toKernelGame p env hd) σ hbdd)

/-- In a Vegas team game, Pareto-efficient profiles are Nash under the same
hypotheses as in `GameTheory`. -/
theorem IsTeamGame.pareto_isNash [Fintype P] [Inhabited P]
    (p : VegasCore P L Γ) (env : VEnv L Γ)
    (hd : NormalizedDists p) (hteam : IsTeamGame p env hd)
    {σ : StrategyProfile p env hd} (hpareto : IsParetoEfficient p env hd σ)
    (hmax : ∀ τ : StrategyProfile p env hd,
      socialWelfare p env hd σ ≥ socialWelfare p env hd τ) :
    IsNash p env hd σ := by
  simpa [IsTeamGame, IsParetoEfficient, IsNash, socialWelfare] using
    (KernelGame.IsTeamGame.pareto_isNash
      (G := toKernelGame p env hd) hteam hpareto hmax)

/-- Worst Vegas Nash welfare is at most best Vegas Nash welfare. -/
theorem worstNashWelfare_le_bestNashWelfare [Fintype P]
    (p : VegasCore P L Γ) (env : VEnv L Γ)
    (hd : NormalizedDists p)
    [Fintype (StrategyProfile p env hd)] [Nonempty (StrategyProfile p env hd)]
    (hN : ∃ σ : StrategyProfile p env hd, IsNash p env hd σ) :
    worstNashWelfare p env hd hN ≤ bestNashWelfare p env hd hN := by
  simpa [worstNashWelfare, bestNashWelfare, IsNash] using
    (KernelGame.worstNashWelfare_le_bestNashWelfare
      (G := Game p env hd) (by simpa [IsNash] using hN))

/-- Best Vegas Nash welfare is at most Vegas optimal welfare. -/
theorem bestNashWelfare_le_optimalWelfare [Fintype P]
    (p : VegasCore P L Γ) (env : VEnv L Γ)
    (hd : NormalizedDists p)
    [Fintype (StrategyProfile p env hd)] [Nonempty (StrategyProfile p env hd)]
    (hN : ∃ σ : StrategyProfile p env hd, IsNash p env hd σ) :
    bestNashWelfare p env hd hN ≤ optimalWelfare p env hd := by
  have h :=
    KernelGame.bestNashWelfare_le_optimalWelfare
      (G := Game p env hd) (by simpa [IsNash] using hN)
        (by simp)
  simpa [bestNashWelfare, optimalWelfare] using h

/-- In a 2-player Vegas zero-sum game, player 1 cannot lower player 0's EU at Nash. -/
theorem IsZeroSum.nash_p0_optimal
    (p : VegasCore (Fin 2) L Γ) (env : VEnv L Γ)
    (hd : NormalizedDists p) [Finite (Outcome (Fin 2))]
    (hzs : IsZeroSum p env hd) {σ : StrategyProfile p env hd}
    (hN : IsNash p env hd σ) (s₁ : Strategy p env hd 1) :
    eu p env hd (Function.update σ 1 s₁) 0 ≥ eu p env hd σ 0 := by
  let _ : Fintype (Outcome (Fin 2)) := Fintype.ofFinite (Outcome (Fin 2))
  let _ : Fintype (toKernelGame p env hd).Outcome := by
    simpa [toKernelGame] using (inferInstance : Fintype (Outcome (Fin 2)))
  simpa [IsZeroSum, IsNash, eu, Strategy] using
    (KernelGame.IsZeroSum.nash_p0_optimal
      (G := toKernelGame p env hd) hzs hN s₁)

/-- In a 2-player Vegas game, player 0 cannot improve at Nash. -/
theorem nash_p0_cap
    (p : VegasCore (Fin 2) L Γ) (env : VEnv L Γ)
    (hd : NormalizedDists p) {σ : StrategyProfile p env hd}
    (hN : IsNash p env hd σ) (s₀ : Strategy p env hd 0) :
    eu p env hd σ 0 ≥ eu p env hd (Function.update σ 0 s₀) 0 := by
  simpa [IsNash, eu, Strategy] using
    (KernelGame.nash_p0_cap
      (G := toKernelGame p env hd) hN s₀)

/-- In a 2-player Vegas zero-sum game, all Nash equilibria give the same value. -/
theorem IsZeroSum.nash_eu_eq
    (p : VegasCore (Fin 2) L Γ) (env : VEnv L Γ)
    (hd : NormalizedDists p) [Finite (Outcome (Fin 2))]
    (hzs : IsZeroSum p env hd) {σ τ : StrategyProfile p env hd}
    (hNσ : IsNash p env hd σ) (hNτ : IsNash p env hd τ) :
    eu p env hd σ 0 = eu p env hd τ 0 := by
  let _ : Fintype (Outcome (Fin 2)) := Fintype.ofFinite (Outcome (Fin 2))
  let _ : Fintype (toKernelGame p env hd).Outcome := by
    simpa [toKernelGame] using (inferInstance : Fintype (Outcome (Fin 2)))
  simpa [IsZeroSum, IsNash, eu] using
    (KernelGame.IsZeroSum.nash_eu_eq
      (G := toKernelGame p env hd) hzs hNσ hNτ)

/-- In a 2-player Vegas zero-sum game, Nash equilibria are interchangeable. -/
theorem IsZeroSum.nash_interchangeable
    (p : VegasCore (Fin 2) L Γ) (env : VEnv L Γ)
    (hd : NormalizedDists p) [Finite (Outcome (Fin 2))]
    (hzs : IsZeroSum p env hd) {σ τ : StrategyProfile p env hd}
    (hNσ : IsNash p env hd σ) (hNτ : IsNash p env hd τ) :
    IsNash p env hd (Function.update σ 1 (τ 1)) := by
  let _ : Fintype (Outcome (Fin 2)) := Fintype.ofFinite (Outcome (Fin 2))
  let _ : Fintype (toKernelGame p env hd).Outcome := by
    simpa [toKernelGame] using (inferInstance : Fintype (Outcome (Fin 2)))
  simpa [IsZeroSum, IsNash, StrategyProfile] using
    (KernelGame.IsZeroSum.nash_interchangeable
      (G := toKernelGame p env hd) hzs hNσ hNτ)

/-- Zero-sum is preserved by the mixed extension of the Vegas kernel game. -/
theorem mixedExtension_isZeroSum [Fintype P]
    (p : VegasCore P L Γ) (env : VEnv L Γ)
    (hd : NormalizedDists p) [∀ who, Fintype (Strategy p env hd who)]
    (hzs : IsZeroSum p env hd) :
    (Game p env hd).mixedExtension.IsZeroSum := by
  simpa [IsZeroSum] using
    (KernelGame.mixedExtension_isZeroSum
      (G := Game p env hd) hzs)

/-- Von Neumann minimax for Vegas, under the same finite hypotheses as in `GameTheory`. -/
theorem von_neumann_minimax
    (p : VegasCore (Fin 2) L Γ) (env : VEnv L Γ)
    (hd : NormalizedDists p)
    [Finite (Outcome (Fin 2))]
    [∀ who, Fintype (Strategy p env hd who)]
    [∀ who, Nonempty (Strategy p env hd who)]
    (hzs : IsZeroSum p env hd) :
    ∃ (v : ℝ) (σ : MixedStrategyProfile p env hd),
      IsMixedNash p env hd σ ∧
      mixedEu p env hd σ 0 = v ∧
      (∀ s₁, mixedEu p env hd (Function.update σ 1 s₁) 0 ≥ v) ∧
      (∀ s₀, mixedEu p env hd (Function.update σ 0 s₀) 0 ≤ v) := by
  let _ : Fintype (Outcome (Fin 2)) := Fintype.ofFinite (Outcome (Fin 2))
  let _ : Fintype (Game p env hd).Outcome := by
    simpa [Game] using (inferInstance : Fintype (Outcome (Fin 2)))
  simpa [MixedStrategyProfile, IsMixedNash, mixedEu, IsZeroSum] using
    (KernelGame.von_neumann_minimax
      (G := Game p env hd) hzs)

end Vegas
