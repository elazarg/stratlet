import Vegas.Strategic
import GameTheory.Concepts.SolutionConcepts
import GameTheory.Core.GameProperties

/-!
# Vegas equilibrium wrappers

Game-theoretic vocabulary for Vegas programs, defined by transport through the
`toKernelGame` strategic bridge. The entire user-facing game-theory API
consumes a `WFProgram` bundle rather than a raw `(program, env,
NormalizedDists)` triplet: the bundle carries the full well-formedness
obligations (`WF`, `NormalizedDists`, `Legal`) needed to ensure a coherent
game interpretation.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

noncomputable def Game (g : WFProgram P L) : GameTheory.KernelGame P :=
  toKernelGame g

/-- Strategy profiles for a Vegas program are exactly the profiles of its
kernel-game image. -/
def StrategyProfile (g : WFProgram P L) : Type :=
  KernelGame.Profile (Game g)

/-- A single player's Vegas strategy is the corresponding strategy in the
kernel-game image. -/
def Strategy (g : WFProgram P L) (who : P) : Type :=
  (Game g).Strategy who

/-- Correlated profiles for a Vegas program are profile distributions on its
strategy-profile space. -/
def CorrelatedProfile (g : WFProgram P L) : Type :=
  PMF (StrategyProfile g)

instance instFintypeGameStrategy (g : WFProgram P L)
    [∀ who, Fintype (Strategy g who)] :
    ∀ who, Fintype ((Game g).Strategy who) := by
  intro who
  let I : Fintype (Strategy g who) := inferInstance
  simpa [Strategy] using I

instance instNonemptyGameStrategy (g : WFProgram P L)
    [∀ who, Nonempty (Strategy g who)] :
    ∀ who, Nonempty ((Game g).Strategy who) := by
  intro who
  let I : Nonempty (Strategy g who) := inferInstance
  simpa [Strategy] using I

instance instFintypeGameProfile (g : WFProgram P L)
    [Fintype (StrategyProfile g)] :
    Fintype (KernelGame.Profile (Game g)) := by
  let I : Fintype (StrategyProfile g) := inferInstance
  simpa [StrategyProfile] using I

instance instNonemptyGameProfile (g : WFProgram P L)
    [Nonempty (StrategyProfile g)] :
    Nonempty (KernelGame.Profile (Game g)) := by
  let I : Nonempty (StrategyProfile g) := inferInstance
  simpa [StrategyProfile] using I

/-- Expected utility for a Vegas strategy profile, via `toKernelGame`. -/
noncomputable def eu (g : WFProgram P L)
    (σ : StrategyProfile g) (who : P) : ℝ :=
  (Game g).eu σ who

/-- Correlated expected utility for a Vegas correlated profile, via
`toKernelGame`. -/
noncomputable def correlatedEu (g : WFProgram P L)
    (μ : CorrelatedProfile g) (who : P) : ℝ :=
  (Game g).correlatedEu μ who

/-- EU weak preference on Vegas outcome distributions. -/
def euPref (g : WFProgram P L) :
    P → PMF (Outcome P) → PMF (Outcome P) → Prop :=
  (Game g).euPref

/-- EU strict preference on Vegas outcome distributions. -/
def euStrictPref (g : WFProgram P L) :
    P → PMF (Outcome P) → PMF (Outcome P) → Prop :=
  (Game g).euStrictPref

/-- Nash equilibrium for a Vegas program, via `toKernelGame`. -/
def IsNash (g : WFProgram P L) (σ : StrategyProfile g) : Prop :=
  (Game g).IsNash σ

/-- Preference-parameterized Nash equilibrium for a Vegas program. -/
def IsNashFor (g : WFProgram P L)
    (pref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (σ : StrategyProfile g) : Prop :=
  (Game g).IsNashFor pref σ

/-- Best response for a player in a Vegas program. -/
def IsBestResponse (g : WFProgram P L)
    (who : P) (σ : StrategyProfile g) (s : Strategy g who) : Prop :=
  (Game g).IsBestResponse who σ s

/-- Preference-parameterized best response for a player in a Vegas program. -/
def IsBestResponseFor (g : WFProgram P L)
    (pref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (who : P) (σ : StrategyProfile g) (s : Strategy g who) : Prop :=
  (Game g).IsBestResponseFor pref who σ s

/-- Dominant strategy for a player in a Vegas program. -/
def IsDominant (g : WFProgram P L) (who : P) (s : Strategy g who) : Prop :=
  (Game g).IsDominant who s

/-- Preference-parameterized dominant strategy for a player in a Vegas program. -/
def IsDominantFor (g : WFProgram P L)
    (pref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (who : P) (s : Strategy g who) : Prop :=
  (Game g).IsDominantFor pref who s

/-- Strict Nash equilibrium for a Vegas program. -/
def IsStrictNash (g : WFProgram P L) (σ : StrategyProfile g) : Prop :=
  (Game g).IsStrictNash σ

/-- Preference-parameterized strict Nash equilibrium for a Vegas program. -/
def IsStrictNashFor (g : WFProgram P L)
    (spref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (σ : StrategyProfile g) : Prop :=
  (Game g).IsStrictNashFor spref σ

/-- Strictly dominant strategy for a player in a Vegas program. -/
def IsStrictDominant (g : WFProgram P L)
    (who : P) (s : Strategy g who) : Prop :=
  (Game g).IsStrictDominant who s

/-- Preference-parameterized strictly dominant strategy for a Vegas player. -/
def IsStrictDominantFor (g : WFProgram P L)
    (spref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (who : P) (s : Strategy g who) : Prop :=
  (Game g).IsStrictDominantFor spref who s

/-- Weak dominance between two Vegas strategies for one player. -/
def WeaklyDominates (g : WFProgram P L)
    (who : P) (s t : Strategy g who) : Prop :=
  (Game g).WeaklyDominates who s t

/-- Preference-parameterized weak dominance between two Vegas strategies. -/
def WeaklyDominatesFor (g : WFProgram P L)
    (pref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (who : P) (s t : Strategy g who) : Prop :=
  (Game g).WeaklyDominatesFor pref who s t

/-- Strict dominance between two Vegas strategies for one player. -/
def StrictlyDominates (g : WFProgram P L)
    (who : P) (s t : Strategy g who) : Prop :=
  (Game g).StrictlyDominates who s t

/-- Preference-parameterized strict dominance between two Vegas strategies. -/
def StrictlyDominatesFor (g : WFProgram P L)
    (spref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (who : P) (s t : Strategy g who) : Prop :=
  (Game g).StrictlyDominatesFor spref who s t

/-- Pareto dominance for Vegas strategy profiles. -/
def ParetoDominates (g : WFProgram P L) (σ τ : StrategyProfile g) : Prop :=
  (Game g).ParetoDominates σ τ

/-- Preference-parameterized Pareto dominance for Vegas strategy profiles. -/
def ParetoDominatesFor (g : WFProgram P L)
    (pref spref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (σ τ : StrategyProfile g) : Prop :=
  (Game g).ParetoDominatesFor pref spref σ τ

/-- Pareto efficiency for Vegas strategy profiles. -/
def IsParetoEfficient (g : WFProgram P L) (σ : StrategyProfile g) : Prop :=
  (Game g).IsParetoEfficient σ

/-- Preference-parameterized Pareto efficiency for Vegas strategy profiles. -/
def IsParetoEfficientFor (g : WFProgram P L)
    (pref spref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (σ : StrategyProfile g) : Prop :=
  (Game g).IsParetoEfficientFor pref spref σ

/-- Social welfare of a Vegas strategy profile, via `toKernelGame`. -/
noncomputable def socialWelfare [Fintype P] (g : WFProgram P L)
    (σ : StrategyProfile g) : ℝ :=
  (Game g).socialWelfare σ

/-- Correlated equilibrium for a Vegas correlated profile. -/
def IsCorrelatedEq (g : WFProgram P L) (μ : CorrelatedProfile g) : Prop :=
  (Game g).IsCorrelatedEq μ

/-- Coarse correlated equilibrium for a Vegas correlated profile. -/
def IsCoarseCorrelatedEq (g : WFProgram P L) (μ : CorrelatedProfile g) : Prop :=
  (Game g).IsCoarseCorrelatedEq μ

/-- Preference-parameterized correlated equilibrium for a Vegas correlated
profile. -/
def IsCorrelatedEqFor (g : WFProgram P L)
    (pref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (μ : CorrelatedProfile g) : Prop :=
  (Game g).IsCorrelatedEqFor pref μ

/-- Preference-parameterized coarse correlated equilibrium for a Vegas
correlated profile. -/
def IsCoarseCorrelatedEqFor (g : WFProgram P L)
    (pref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (μ : CorrelatedProfile g) : Prop :=
  (Game g).IsCoarseCorrelatedEqFor pref μ

end Vegas
