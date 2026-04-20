import Vegas.GameProperties
import GameTheory.Concepts.CorrelatedNashMixed
import GameTheory.Concepts.DominanceSolvability
import GameTheory.Concepts.IndividualRationality
import GameTheory.Concepts.PotentialGame
import GameTheory.Concepts.Rationalizability
import GameTheory.Concepts.WelfareTheorems
import GameTheory.Concepts.ZeroSum
import GameTheory.Concepts.ConstantSum
import GameTheory.Concepts.Minimax
import GameTheory.Concepts.SecurityStrategy
import GameTheory.Concepts.PriceOfAnarchy
import GameTheory.Theorems.CorrelatedEqExistence
import GameTheory.Theorems.Minimax
import GameTheory.Theorems.NashExistence
import GameTheory.Theorems.NashExistenceMixed

/-!
# Vegas structural game-theory corollaries

Corollaries for structural properties and finite-game theorems on Vegas games.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Every exact-potential Vegas game is an ordinal-potential Vegas game. -/
theorem IsExactPotential.toOrdinal (g : WFProgram P L)
    {Φ : StrategyProfile g → ℝ}
    (hΦ : IsExactPotential g Φ) :
    IsOrdinalPotential g Φ := by
  simpa [IsExactPotential, IsOrdinalPotential] using
    (KernelGame.IsExactPotential.toOrdinal (G := Game g) hΦ)

/-- A maximizer of a Vegas exact potential is Vegas Nash. -/
theorem IsExactPotential.nash_of_maximizer (g : WFProgram P L)
    {Φ : StrategyProfile g → ℝ}
    (hΦ : IsExactPotential g Φ)
    {σ : StrategyProfile g}
    (hmax : ∀ τ : StrategyProfile g, Φ σ ≥ Φ τ) :
    IsNash g σ := by
  simpa [IsExactPotential, IsNash] using
    (KernelGame.IsExactPotential.nash_of_maximizer (G := Game g) hΦ hmax)

/-- A maximizer of a Vegas ordinal potential is Vegas Nash. -/
theorem IsOrdinalPotential.nash_of_maximizer (g : WFProgram P L)
    {Φ : StrategyProfile g → ℝ}
    (hΦ : IsOrdinalPotential g Φ)
    {σ : StrategyProfile g}
    (hmax : ∀ τ : StrategyProfile g, Φ σ ≥ Φ τ) :
    IsNash g σ := by
  simpa [IsOrdinalPotential, IsNash] using
    (KernelGame.IsOrdinalPotential.nash_of_maximizer (G := Game g) hΦ hmax)

/-- In a finite exact-potential Vegas game, a Nash equilibrium exists. -/
theorem exact_potential_nash_exists (g : WFProgram P L)
    [Finite (StrategyProfile g)] [Nonempty (StrategyProfile g)]
    {Φ : StrategyProfile g → ℝ}
    (hΦ : IsExactPotential g Φ) :
    ∃ σ : StrategyProfile g, IsNash g σ := by
  let _ : Fintype (StrategyProfile g) := Fintype.ofFinite (StrategyProfile g)
  simpa [IsExactPotential, IsNash] using
    (KernelGame.exact_potential_nash_exists (G := Game g) hΦ)

/-- If every player has a dominant Vegas strategy, a Vegas Nash equilibrium
exists. -/
theorem nash_of_all_have_dominant (g : WFProgram P L)
    (h : ∀ who, ∃ s : Strategy g who, IsDominant g who s) :
    ∃ σ : StrategyProfile g, IsNash g σ := by
  simpa [IsDominant, IsNash] using
    (KernelGame.nash_of_all_have_dominant (G := Game g) h)

/-- Weakening the reservation utility preserves Vegas individual rationality. -/
theorem IsIndividuallyRational.mono {g : WFProgram P L}
    {r r' : P → ℝ} {σ : StrategyProfile g}
    (hIR : IsIndividuallyRational g r σ)
    (hle : ∀ who, r' who ≤ r who) :
    IsIndividuallyRational g r' σ := by
  simpa [IsIndividuallyRational] using
    (KernelGame.IsIndividuallyRational.mono (G := Game g) hIR hle)

/-- A Vegas Pareto improvement preserves individual rationality. -/
theorem IsIndividuallyRational.of_pareto_dominates {g : WFProgram P L}
    {r : P → ℝ} {σ τ : StrategyProfile g}
    (hdom : ParetoDominates g σ τ)
    (hIR : IsIndividuallyRational g r τ) :
    IsIndividuallyRational g r σ := by
  simpa [ParetoDominates, IsIndividuallyRational] using
    (KernelGame.IsIndividuallyRational.of_pareto_dominates (G := Game g) hdom hIR)

/-- IR with respect to two reservation functions implies IR with respect to
their pointwise max. -/
theorem IsIndividuallyRational.sup {g : WFProgram P L}
    {r₁ r₂ : P → ℝ} {σ : StrategyProfile g}
    (h1 : IsIndividuallyRational g r₁ σ)
    (h2 : IsIndividuallyRational g r₂ σ) :
    IsIndividuallyRational g (fun who => max (r₁ who) (r₂ who)) σ := by
  simpa [IsIndividuallyRational] using
    (KernelGame.IsIndividuallyRational.sup (G := Game g) h1 h2)

/-- A dominance-solvable Vegas game carries a canonical dominant profile. -/
theorem IsDominanceSolvable.isNash (g : WFProgram P L)
    (h : IsDominanceSolvable g) :
    IsNash g (IsDominanceSolvable.dominantProfile g h) := by
  simpa [IsDominanceSolvable, IsNash, IsDominanceSolvable.dominantProfile] using
    (KernelGame.IsDominanceSolvable.isNash (G := Game g) h)

/-- In a dominance-solvable Vegas game, every Nash equilibrium equals the
dominant profile. -/
theorem IsDominanceSolvable.nash_unique (g : WFProgram P L)
    (h : IsDominanceSolvable g)
    {σ : StrategyProfile g} (hN : IsNash g σ) :
    σ = IsDominanceSolvable.dominantProfile g h := by
  simpa [IsDominanceSolvable, IsNash, IsDominanceSolvable.dominantProfile] using
    (KernelGame.IsDominanceSolvable.nash_unique (G := Game g) h hN)

/-- A dominance-solvable Vegas game has a unique Nash equilibrium. -/
theorem IsDominanceSolvable.exists_unique_nash (g : WFProgram P L)
    (h : IsDominanceSolvable g) :
    ∃! σ : StrategyProfile g, IsNash g σ := by
  simpa [IsDominanceSolvable, IsNash] using
    (KernelGame.IsDominanceSolvable.exists_unique_nash (G := Game g) h)

/-- In a Vegas ordinal-potential game, Nash is equivalent to local optimality
of the potential. -/
theorem IsOrdinalPotential.isNash_iff_local_maximizer (g : WFProgram P L)
    {Φ : StrategyProfile g → ℝ}
    (hΦ : IsOrdinalPotential g Φ)
    {σ : StrategyProfile g} :
    IsNash g σ ↔
      ∀ who (s' : Strategy g who), Φ σ ≥ Φ (Function.update σ who s') := by
  simpa [IsOrdinalPotential, IsNash, Strategy] using
    (KernelGame.IsOrdinalPotential.isNash_iff_local_maximizer
      (G := Game g) hΦ (σ := σ))

/-- Surviving round `n + 1` of Vegas rationalizability implies surviving round `n`. -/
theorem Survives.prev {g : WFProgram P L}
    {n : ℕ} {who : P} {s : Strategy g who}
    (h : Survives g (n + 1) who s) :
    Survives g n who s := by
  simpa [Survives] using
    (KernelGame.Survives.prev (G := Game g) h)

/-- Vegas survival is monotone in the round number. -/
theorem Survives.mono {g : WFProgram P L}
    {m n : ℕ} (hmn : m ≤ n)
    {who : P} {s : Strategy g who}
    (h : Survives g n who s) :
    Survives g m who s := by
  simpa [Survives] using
    (KernelGame.Survives.mono (G := Game g) hmn h)

/-- Vegas Nash strategies survive all rounds of iterated strict-dominance elimination. -/
theorem IsNash.survives {g : WFProgram P L}
    {σ : StrategyProfile g} (hN : IsNash g σ) :
    ∀ (n : ℕ) (who : P), Survives g n who (σ who) := by
  simpa [IsNash, Survives] using
    (KernelGame.IsNash.survives (G := Game g) hN)

/-- Vegas Nash strategies are rationalizable. -/
theorem IsNash.isRationalizable {g : WFProgram P L}
    {σ : StrategyProfile g} (hN : IsNash g σ) (who : P) :
    IsRationalizable g who (σ who) := by
  simpa [IsNash, IsRationalizable] using
    (KernelGame.IsNash.isRationalizable (G := Game g) hN who)

/-- A Vegas dominant strategy survives all rounds of elimination under a
dominant profile witness. -/
theorem IsDominant.survives {g : WFProgram P L}
    {who : P} {s : Strategy g who}
    (hdom : IsDominant g who s)
    (σ₀ : StrategyProfile g) (hσ₀ : σ₀ who = s)
    (hdom_all : ∀ j, IsDominant g j (σ₀ j)) :
    ∀ n, Survives g n who s := by
  simpa [IsDominant, Survives] using
    (KernelGame.IsDominant.survives (G := Game g) hdom σ₀ hσ₀ hdom_all)

/-- A Vegas rationalizable strategy is not globally strictly dominated. -/
theorem IsRationalizable.not_globally_dominated {g : WFProgram P L}
    {who : P} {s : Strategy g who}
    (hs : IsRationalizable g who s) :
    ¬ ∃ t : Strategy g who,
      ∀ (σ : StrategyProfile g),
        eu g (Function.update σ who t) who >
          eu g (Function.update σ who s) who := by
  simpa [IsRationalizable, Strategy, StrategyProfile, eu] using
    (KernelGame.IsRationalizable.not_globally_dominated (G := Game g) hs)

/-- Vegas guarantees are monotone in the guaranteed value. -/
theorem Guarantees.mono {g : WFProgram P L}
    {who : P} {s : Strategy g who} {v v' : ℝ}
    (hv : v' ≤ v) (hg : Guarantees g who s v) :
    Guarantees g who s v' := by
  simpa [Guarantees] using
    (KernelGame.Guarantees.mono (G := Game g) hv hg)

/-- In 2-player Vegas games, saddle points are exactly Nash equilibria. -/
theorem isSaddlePoint_iff_isNash (g : WFProgram (Fin 2) L)
    (σ : StrategyProfile g) :
    IsSaddlePoint g σ ↔ IsNash g σ := by
  simpa [IsSaddlePoint, IsNash] using
    (KernelGame.isSaddlePoint_iff_isNash (G := Game g) σ)

/-- Worst-case EU is a lower bound on Vegas expected utility. -/
theorem worstCaseEU_le (g : WFProgram P L)
    [Fintype (StrategyProfile g)]
    [∀ who, Fintype (Strategy g who)]
    [∀ who, Nonempty (Strategy g who)]
    [Nonempty (StrategyProfile g)]
    (who : P) (s : Strategy g who) (σ : StrategyProfile g) :
    worstCaseEU g who s ≤ eu g (Function.update σ who s) who := by
  classical
  have hupd :
      @Function.update P (Game g).Strategy (Classical.decEq P) σ who s =
        Function.update σ who s := by
    funext i
    by_cases hi : i = who <;> simp [Function.update, hi]
  simpa [worstCaseEU, eu, hupd] using
    (KernelGame.worstCaseEU_le (G := Game g) who s σ)

/-- Vegas guarantees are equivalent to worst-case EU lower bounds. -/
theorem guarantees_iff_worstCaseEU_ge (g : WFProgram P L)
    [Fintype (StrategyProfile g)]
    [∀ who, Fintype (Strategy g who)]
    [∀ who, Nonempty (Strategy g who)]
    [Nonempty (StrategyProfile g)]
    (who : P) (s : Strategy g who) (v : ℝ) :
    Guarantees g who s v ↔ worstCaseEU g who s ≥ v := by
  simpa [Guarantees, worstCaseEU] using
    (KernelGame.guarantees_iff_worstCaseEU_ge (G := Game g) who s v)

/-- In a Vegas Nash equilibrium, each player's EU is at least their security level. -/
theorem nash_eu_ge_securityLevel (g : WFProgram P L)
    [Fintype (StrategyProfile g)]
    [∀ who, Fintype (Strategy g who)]
    [∀ who, Nonempty (Strategy g who)]
    [Nonempty (StrategyProfile g)]
    {σ : StrategyProfile g}
    (hN : IsNash g σ) (who : P) :
    eu g σ who ≥ securityLevel g who := by
  classical
  simp only [securityLevel]
  apply Finset.sup'_le
  intro s _
  calc
    worstCaseEU g who s ≤ eu g (Function.update σ who s) who :=
      worstCaseEU_le g who s σ
    _ ≤ eu g σ who := by
      have hdev : eu g σ who ≥ eu g (Function.update σ who s) who := by
        simpa [IsNash, eu] using hN who s
      linarith

/-- A Vegas dominant strategy achieves at least the security level. -/
theorem IsDominant.eu_ge_securityLevel (g : WFProgram P L)
    [Fintype (StrategyProfile g)]
    [∀ who, Fintype (Strategy g who)]
    [∀ who, Nonempty (Strategy g who)]
    [Nonempty (StrategyProfile g)]
    {who : P} {s : Strategy g who}
    (hdom : IsDominant g who s)
    (σ : StrategyProfile g) :
    eu g (Function.update σ who s) who ≥ securityLevel g who := by
  classical
  simp only [securityLevel]
  apply Finset.sup'_le
  intro t _
  calc
    worstCaseEU g who t ≤ eu g (Function.update σ who t) who :=
      worstCaseEU_le g who t σ
    _ ≤ eu g (Function.update σ who s) who := by
      have hle : eu g (Function.update σ who s) who ≥
          eu g (Function.update σ who t) who := by
        simpa [IsDominant, eu] using hdom σ t
      linarith

/-- Worst-case EU gives a Vegas guarantee. -/
theorem worstCaseEU_guarantees (g : WFProgram P L)
    [Fintype (StrategyProfile g)]
    [∀ who, Fintype (Strategy g who)]
    [∀ who, Nonempty (Strategy g who)]
    [Nonempty (StrategyProfile g)]
    (who : P) (s : Strategy g who) :
    ∀ σ : StrategyProfile g,
      eu g (Function.update σ who s) who ≥ worstCaseEU g who s := by
  classical
  intro σ
  have hupd :
      @Function.update P (Game g).Strategy (Classical.decEq P) σ who s =
        Function.update σ who s := by
    funext i
    by_cases hi : i = who <;> simp [Function.update, hi]
  simpa [eu, worstCaseEU, hupd] using
    (KernelGame.worstCaseEU_guarantees (G := Game g) who s σ)

/-- Any uniform lower bound on Vegas expected utility is bounded by the security level. -/
theorem le_securityLevel_of_forall_eu_ge (g : WFProgram P L)
    [Fintype (StrategyProfile g)]
    [∀ who, Fintype (Strategy g who)]
    [∀ who, Nonempty (Strategy g who)]
    [Nonempty (StrategyProfile g)]
    (who : P) (s : Strategy g who) (v : ℝ)
    (hg : ∀ σ : StrategyProfile g,
      eu g (Function.update σ who s) who ≥ v) :
    v ≤ securityLevel g who := by
  classical
  have hg' : ∀ σ : StrategyProfile g,
      (Game g).eu
        (@Function.update P (Game g).Strategy (Classical.decEq P) σ who s) who ≥ v := by
    intro σ
    have hupd :
        @Function.update P (Game g).Strategy (Classical.decEq P) σ who s =
          Function.update σ who s := by
      funext i
      by_cases hi : i = who <;> simp [Function.update, hi]
    simpa [eu, hupd] using hg σ
  simpa [securityLevel] using
    (KernelGame.le_securityLevel_of_forall_eu_ge (G := Game g) who s v hg')

/-- A Vegas security strategy exists under the finite hypotheses of `GameTheory`. -/
theorem exists_securityStrategy (g : WFProgram P L)
    [Fintype (StrategyProfile g)]
    [∀ who, Fintype (Strategy g who)]
    [∀ who, Nonempty (Strategy g who)]
    [Nonempty (StrategyProfile g)]
    (who : P) :
    ∃ s : Strategy g who, worstCaseEU g who s = securityLevel g who := by
  simpa [worstCaseEU, securityLevel] using
    (KernelGame.exists_securityStrategy (G := Game g) who)

/-- A finite Vegas game admits a mixed Nash equilibrium. -/
theorem mixed_nash_exists [Fintype P] (g : WFProgram P L)
    [∀ who, Fintype (Strategy g who)]
    [∀ who, Nonempty (Strategy g who)]
    [Finite (Outcome P)] :
    ∃ σ : MixedStrategyProfile g, IsMixedNash g σ := by
  let _ : Fintype (Outcome P) := Fintype.ofFinite (Outcome P)
  let _ : Fintype (Game g).Outcome := by
    simpa [Game] using (inferInstance : Fintype (Outcome P))
  simpa [MixedStrategyProfile, IsMixedNash] using
    (KernelGame.mixed_nash_exists (G := Game g))

/-- A Vegas mixed Nash profile induces a correlated equilibrium on pure Vegas
profiles. -/
theorem mixed_nash_isCorrelatedEq [Fintype P] (g : WFProgram P L)
    [∀ who, Fintype (Strategy g who)]
    [Finite (Outcome P)]
    (σ : MixedStrategyProfile g)
    (hN : IsMixedNash g σ) :
    IsCorrelatedEq g (Math.PMFProduct.pmfPi σ) := by
  let _ : Fintype (Outcome P) := Fintype.ofFinite (Outcome P)
  let _ : Fintype (Game g).Outcome := by
    simpa [Game] using (inferInstance : Fintype (Outcome P))
  simpa [MixedStrategyProfile, IsMixedNash, IsCorrelatedEq] using
    (KernelGame.mixed_nash_isCorrelatedEq (G := Game g) σ hN)

/-- A Vegas mixed Nash profile induces a coarse correlated equilibrium. -/
theorem mixed_nash_isCoarseCorrelatedEq [Fintype P] (g : WFProgram P L)
    [∀ who, Fintype (Strategy g who)]
    [Finite (Outcome P)]
    (σ : MixedStrategyProfile g)
    (hN : IsMixedNash g σ) :
    IsCoarseCorrelatedEq g (Math.PMFProduct.pmfPi σ) := by
  let _ : Fintype (Outcome P) := Fintype.ofFinite (Outcome P)
  let _ : Fintype (Game g).Outcome := by
    simpa [Game] using (inferInstance : Fintype (Outcome P))
  simpa [MixedStrategyProfile, IsMixedNash, IsCoarseCorrelatedEq] using
    (KernelGame.mixed_nash_isCoarseCorrelatedEq (G := Game g) σ hN)

/-- Every finite Vegas game has a correlated equilibrium. -/
theorem correlatedEq_exists (g : WFProgram P L)
    [Finite P]
    [∀ who, Finite (Strategy g who)]
    [∀ who, Nonempty (Strategy g who)]
    [Finite (Outcome P)] :
    ∃ μ : CorrelatedProfile g, IsCorrelatedEq g μ := by
  let _ : Fintype P := Fintype.ofFinite P
  let _ : ∀ who, Fintype (Strategy g who) := by
    intro who
    exact Fintype.ofFinite (Strategy g who)
  let _ : Fintype (Outcome P) := Fintype.ofFinite (Outcome P)
  let _ : Fintype (Game g).Outcome := by
    simpa [Game] using (inferInstance : Fintype (Outcome P))
  simpa [CorrelatedProfile, IsCorrelatedEq] using
    (KernelGame.correlatedEq_exists (G := Game g))

/-- Every finite Vegas game has a coarse correlated equilibrium. -/
theorem coarseCorrelatedEq_exists (g : WFProgram P L)
    [Finite P]
    [∀ who, Finite (Strategy g who)]
    [∀ who, Nonempty (Strategy g who)]
    [Finite (Outcome P)] :
    ∃ μ : CorrelatedProfile g, IsCoarseCorrelatedEq g μ := by
  let _ : Fintype P := Fintype.ofFinite P
  let _ : ∀ who, Fintype (Strategy g who) := by
    intro who
    exact Fintype.ofFinite (Strategy g who)
  let _ : Fintype (Outcome P) := Fintype.ofFinite (Outcome P)
  let _ : Fintype (Game g).Outcome := by
    simpa [Game] using (inferInstance : Fintype (Outcome P))
  simpa [CorrelatedProfile, IsCoarseCorrelatedEq] using
    (KernelGame.coarseCorrelatedEq_exists (G := Game g))

/-- In a Vegas team game, social welfare is a scalar multiple of any player's EU. -/
theorem IsTeamGame.socialWelfare_eq [Fintype P] [Inhabited P]
    (g : WFProgram P L) (hteam : IsTeamGame g)
    (σ : StrategyProfile g) (i : P) :
    socialWelfare g σ = Fintype.card P * eu g σ i := by
  simpa [IsTeamGame, socialWelfare, eu] using
    (KernelGame.IsTeamGame.socialWelfare_eq (G := Game g) hteam σ i)

/-- Nonnegative Vegas expected utilities imply nonnegative social welfare. -/
theorem socialWelfare_nonneg_of_nonneg_eu [Fintype P]
    (g : WFProgram P L) {σ : StrategyProfile g}
    (h : ∀ i, eu g σ i ≥ 0) :
    socialWelfare g σ ≥ 0 := by
  simpa [socialWelfare, eu] using
    (KernelGame.socialWelfare_nonneg_of_nonneg_eu (G := Game g) h)

/-- In a Vegas zero-sum game with finite outcome space, social welfare is zero. -/
theorem IsZeroSum.socialWelfare_eq_zero [Fintype P]
    (g : WFProgram P L) [Finite (Outcome P)]
    (hzs : IsZeroSum g) (σ : StrategyProfile g) :
    socialWelfare g σ = 0 := by
  let _ : Fintype (Outcome P) := Fintype.ofFinite (Outcome P)
  let _ : Fintype (toKernelGame g).Outcome := by
    simpa [toKernelGame] using (inferInstance : Fintype (Outcome P))
  simpa [IsZeroSum, socialWelfare] using
    (KernelGame.IsZeroSum.socialWelfare_eq_zero
      (G := toKernelGame g) hzs σ)

/-- In a 2-player Vegas zero-sum game with finite outcome space, one player's
EU is the negation of the other's. -/
theorem IsZeroSum.eu_neg
    (g : WFProgram (Fin 2) L) [Finite (Outcome (Fin 2))]
    (hzs : IsZeroSum g) (σ : StrategyProfile g) :
    eu g σ 0 = - eu g σ 1 := by
  let _ : Fintype (Outcome (Fin 2)) := Fintype.ofFinite (Outcome (Fin 2))
  let _ : Fintype (toKernelGame g).Outcome := by
    simpa [toKernelGame] using (inferInstance : Fintype (Outcome (Fin 2)))
  simpa [IsZeroSum, eu] using
    (KernelGame.IsZeroSum.eu_neg (G := toKernelGame g) hzs σ)

/-- In a Vegas constant-sum game with finite outcome space, social welfare is constant. -/
theorem IsConstantSum.socialWelfare_eq [Fintype P]
    (g : WFProgram P L) [Finite (Outcome P)]
    {c : ℝ} (hcs : IsConstantSum g c) (σ : StrategyProfile g) :
    socialWelfare g σ = c := by
  let _ : Fintype (Outcome P) := Fintype.ofFinite (Outcome P)
  let _ : Fintype (toKernelGame g).Outcome := by
    simpa [toKernelGame] using (inferInstance : Fintype (Outcome P))
  simpa [IsConstantSum, socialWelfare] using
    (KernelGame.IsConstantSum.socialWelfare_eq
      (G := toKernelGame g) hcs σ)

/-- In a 2-player Vegas constant-sum game, player 0's EU is determined by player 1's. -/
theorem IsConstantSum.eu_determined
    (g : WFProgram (Fin 2) L) [Finite (Outcome (Fin 2))]
    {c : ℝ} (hcs : IsConstantSum g c) (σ : StrategyProfile g) :
    eu g σ 0 = c - eu g σ 1 := by
  let _ : Fintype (Outcome (Fin 2)) := Fintype.ofFinite (Outcome (Fin 2))
  let _ : Fintype (toKernelGame g).Outcome := by
    simpa [toKernelGame] using (inferInstance : Fintype (Outcome (Fin 2)))
  simpa [IsConstantSum, eu] using
    (KernelGame.IsConstantSum.eu_determined
      (G := toKernelGame g) hcs σ)

/-- A Vegas zero-sum game is a Vegas constant-sum game with constant `0`. -/
theorem IsZeroSum.isConstantSum_zero [Fintype P]
    (g : WFProgram P L) (hzs : IsZeroSum g) :
    IsConstantSum g 0 := by
  simpa [IsZeroSum, IsConstantSum] using
    (KernelGame.IsZeroSum.isConstantSum_zero (G := toKernelGame g) hzs)

/-- In a 2-player Vegas constant-sum game, all Nash equilibria give the same EU. -/
theorem IsConstantSum.nash_eu_eq
    (g : WFProgram (Fin 2) L) [Finite (Outcome (Fin 2))]
    {c : ℝ} (hcs : IsConstantSum g c)
    {σ τ : StrategyProfile g}
    (hNσ : IsNash g σ) (hNτ : IsNash g τ) :
    eu g σ 0 = eu g τ 0 := by
  let _ : Fintype (Outcome (Fin 2)) := Fintype.ofFinite (Outcome (Fin 2))
  let _ : Fintype (toKernelGame g).Outcome := by
    simpa [toKernelGame] using (inferInstance : Fintype (Outcome (Fin 2)))
  simpa [IsConstantSum, IsNash, eu] using
    (KernelGame.IsConstantSum.nash_eu_eq
      (G := toKernelGame g) hcs hNσ hNτ)

/-- Social welfare is bounded above by the Vegas optimal welfare. -/
theorem welfare_le_optimal [Fintype P]
    (g : WFProgram P L) (σ : StrategyProfile g)
    (hbdd : BddAbove (Set.range (fun τ => socialWelfare g τ))) :
    socialWelfare g σ ≤ optimalWelfare g := by
  simpa [socialWelfare, optimalWelfare] using
    (KernelGame.welfare_le_optimal (G := toKernelGame g) σ hbdd)

/-- In a Vegas team game, Pareto-efficient profiles are Nash under the same
hypotheses as in `GameTheory`. -/
theorem IsTeamGame.pareto_isNash [Fintype P] [Inhabited P]
    (g : WFProgram P L) (hteam : IsTeamGame g)
    {σ : StrategyProfile g} (hpareto : IsParetoEfficient g σ)
    (hmax : ∀ τ : StrategyProfile g,
      socialWelfare g σ ≥ socialWelfare g τ) :
    IsNash g σ := by
  simpa [IsTeamGame, IsParetoEfficient, IsNash, socialWelfare] using
    (KernelGame.IsTeamGame.pareto_isNash
      (G := toKernelGame g) hteam hpareto hmax)

/-- Worst Vegas Nash welfare is at most best Vegas Nash welfare. -/
theorem worstNashWelfare_le_bestNashWelfare [Fintype P]
    (g : WFProgram P L)
    [Fintype (StrategyProfile g)] [Nonempty (StrategyProfile g)]
    (hN : ∃ σ : StrategyProfile g, IsNash g σ) :
    worstNashWelfare g hN ≤ bestNashWelfare g hN := by
  simpa [worstNashWelfare, bestNashWelfare, IsNash] using
    (KernelGame.worstNashWelfare_le_bestNashWelfare
      (G := Game g) (by simpa [IsNash] using hN))

/-- Best Vegas Nash welfare is at most Vegas optimal welfare. -/
theorem bestNashWelfare_le_optimalWelfare [Fintype P]
    (g : WFProgram P L)
    [Fintype (StrategyProfile g)] [Nonempty (StrategyProfile g)]
    (hN : ∃ σ : StrategyProfile g, IsNash g σ) :
    bestNashWelfare g hN ≤ optimalWelfare g := by
  have h :=
    KernelGame.bestNashWelfare_le_optimalWelfare
      (G := Game g) (by simpa [IsNash] using hN) (by simp)
  simpa [bestNashWelfare, optimalWelfare] using h

/-- In a 2-player Vegas zero-sum game, player 1 cannot lower player 0's EU at Nash. -/
theorem IsZeroSum.nash_p0_optimal
    (g : WFProgram (Fin 2) L) [Finite (Outcome (Fin 2))]
    (hzs : IsZeroSum g) {σ : StrategyProfile g}
    (hN : IsNash g σ) (s₁ : Strategy g 1) :
    eu g (Function.update σ 1 s₁) 0 ≥ eu g σ 0 := by
  let _ : Fintype (Outcome (Fin 2)) := Fintype.ofFinite (Outcome (Fin 2))
  let _ : Fintype (toKernelGame g).Outcome := by
    simpa [toKernelGame] using (inferInstance : Fintype (Outcome (Fin 2)))
  simpa [IsZeroSum, IsNash, eu, Strategy] using
    (KernelGame.IsZeroSum.nash_p0_optimal
      (G := toKernelGame g) hzs hN s₁)

/-- In a 2-player Vegas game, player 0 cannot improve at Nash. -/
theorem nash_p0_cap
    (g : WFProgram (Fin 2) L) {σ : StrategyProfile g}
    (hN : IsNash g σ) (s₀ : Strategy g 0) :
    eu g σ 0 ≥ eu g (Function.update σ 0 s₀) 0 := by
  simpa [IsNash, eu, Strategy] using
    (KernelGame.nash_p0_cap (G := toKernelGame g) hN s₀)

/-- In a 2-player Vegas zero-sum game, all Nash equilibria give the same value. -/
theorem IsZeroSum.nash_eu_eq
    (g : WFProgram (Fin 2) L) [Finite (Outcome (Fin 2))]
    (hzs : IsZeroSum g) {σ τ : StrategyProfile g}
    (hNσ : IsNash g σ) (hNτ : IsNash g τ) :
    eu g σ 0 = eu g τ 0 := by
  let _ : Fintype (Outcome (Fin 2)) := Fintype.ofFinite (Outcome (Fin 2))
  let _ : Fintype (toKernelGame g).Outcome := by
    simpa [toKernelGame] using (inferInstance : Fintype (Outcome (Fin 2)))
  simpa [IsZeroSum, IsNash, eu] using
    (KernelGame.IsZeroSum.nash_eu_eq
      (G := toKernelGame g) hzs hNσ hNτ)

/-- In a 2-player Vegas zero-sum game, Nash equilibria are interchangeable. -/
theorem IsZeroSum.nash_interchangeable
    (g : WFProgram (Fin 2) L) [Finite (Outcome (Fin 2))]
    (hzs : IsZeroSum g) {σ τ : StrategyProfile g}
    (hNσ : IsNash g σ) (hNτ : IsNash g τ) :
    IsNash g (Function.update σ 1 (τ 1)) := by
  let _ : Fintype (Outcome (Fin 2)) := Fintype.ofFinite (Outcome (Fin 2))
  let _ : Fintype (toKernelGame g).Outcome := by
    simpa [toKernelGame] using (inferInstance : Fintype (Outcome (Fin 2)))
  simpa [IsZeroSum, IsNash, StrategyProfile] using
    (KernelGame.IsZeroSum.nash_interchangeable
      (G := toKernelGame g) hzs hNσ hNτ)

/-- Zero-sum is preserved by the mixed extension of the Vegas kernel game. -/
theorem mixedExtension_isZeroSum [Fintype P]
    (g : WFProgram P L)
    [∀ who, Fintype (Strategy g who)]
    (hzs : IsZeroSum g) :
    (Game g).mixedExtension.IsZeroSum := by
  simpa [IsZeroSum] using
    (KernelGame.mixedExtension_isZeroSum (G := Game g) hzs)

/-- Von Neumann minimax for Vegas, under the same finite hypotheses as in `GameTheory`. -/
theorem von_neumann_minimax
    (g : WFProgram (Fin 2) L)
    [Finite (Outcome (Fin 2))]
    [∀ who, Fintype (Strategy g who)]
    [∀ who, Nonempty (Strategy g who)]
    (hzs : IsZeroSum g) :
    ∃ (v : ℝ) (σ : MixedStrategyProfile g),
      IsMixedNash g σ ∧
      mixedEu g σ 0 = v ∧
      (∀ s₁, mixedEu g (Function.update σ 1 s₁) 0 ≥ v) ∧
      (∀ s₀, mixedEu g (Function.update σ 0 s₀) 0 ≤ v) := by
  let _ : Fintype (Outcome (Fin 2)) := Fintype.ofFinite (Outcome (Fin 2))
  let _ : Fintype (Game g).Outcome := by
    simpa [Game] using (inferInstance : Fintype (Outcome (Fin 2)))
  simpa [MixedStrategyProfile, IsMixedNash, mixedEu, IsZeroSum] using
    (KernelGame.von_neumann_minimax (G := Game g) hzs)

end Vegas
