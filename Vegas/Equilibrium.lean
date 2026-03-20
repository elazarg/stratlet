import Vegas.Strategic
import GameTheory.Concepts.SolutionConcepts
import GameTheory.Core.GameProperties

/-!
# Vegas equilibrium wrappers

Game-theoretic vocabulary for Vegas programs, defined by transport through the
`toKernelGame` strategic bridge.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

noncomputable def Game (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p) :
    GameTheory.KernelGame P :=
  toKernelGame p env hd

/-- Strategy profiles for a Vegas program are exactly the profiles of its
kernel-game image. -/
def StrategyProfile (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p) : Type :=
  KernelGame.Profile (Game p env hd)

/-- A single player's Vegas strategy is the corresponding strategy in the
kernel-game image. -/
def Strategy (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p) (who : P) : Type :=
  (Game p env hd).Strategy who

/-- Correlated profiles for a Vegas program are profile distributions on its
strategy-profile space. -/
def CorrelatedProfile (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p) : Type :=
  PMF (StrategyProfile p env hd)

instance instFintypeGameStrategy (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    [∀ who, Fintype (Strategy p env hd who)] :
    ∀ who, Fintype ((Game p env hd).Strategy who) := by
  intro who
  let I : Fintype (Strategy p env hd who) := inferInstance
  simpa [Strategy] using I

instance instNonemptyGameStrategy (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    [∀ who, Nonempty (Strategy p env hd who)] :
    ∀ who, Nonempty ((Game p env hd).Strategy who) := by
  intro who
  let I : Nonempty (Strategy p env hd who) := inferInstance
  simpa [Strategy] using I

instance instFintypeGameProfile (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    [Fintype (StrategyProfile p env hd)] :
    Fintype (KernelGame.Profile (Game p env hd)) := by
  let I : Fintype (StrategyProfile p env hd) := inferInstance
  simpa [StrategyProfile] using I

instance instNonemptyGameProfile (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    [Nonempty (StrategyProfile p env hd)] :
    Nonempty (KernelGame.Profile (Game p env hd)) := by
  let I : Nonempty (StrategyProfile p env hd) := inferInstance
  simpa [StrategyProfile] using I

/-- Expected utility for a Vegas strategy profile, via `toKernelGame`. -/
noncomputable def eu (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (σ : StrategyProfile p env hd) (who : P) : ℝ :=
  (Game p env hd).eu σ who

/-- Correlated expected utility for a Vegas correlated profile, via
`toKernelGame`. -/
noncomputable def correlatedEu (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (μ : CorrelatedProfile p env hd) (who : P) : ℝ :=
  (Game p env hd).correlatedEu μ who

/-- EU weak preference on Vegas outcome distributions. -/
def euPref (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p) :
    P → PMF (Outcome P) → PMF (Outcome P) → Prop :=
  (Game p env hd).euPref

/-- EU strict preference on Vegas outcome distributions. -/
def euStrictPref (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p) :
    P → PMF (Outcome P) → PMF (Outcome P) → Prop :=
  (Game p env hd).euStrictPref

/-- Nash equilibrium for a Vegas program, via `toKernelGame`. -/
def IsNash (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (σ : StrategyProfile p env hd) : Prop :=
  (Game p env hd).IsNash σ

/-- Preference-parameterized Nash equilibrium for a Vegas program. -/
def IsNashFor (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (pref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (σ : StrategyProfile p env hd) : Prop :=
  (Game p env hd).IsNashFor pref σ

/-- Best response for a player in a Vegas program. -/
def IsBestResponse (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (who : P) (σ : StrategyProfile p env hd)
    (s : Strategy p env hd who) : Prop :=
  (Game p env hd).IsBestResponse who σ s

/-- Preference-parameterized best response for a player in a Vegas program. -/
def IsBestResponseFor (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (pref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (who : P) (σ : StrategyProfile p env hd)
    (s : Strategy p env hd who) : Prop :=
  (Game p env hd).IsBestResponseFor pref who σ s

/-- Dominant strategy for a player in a Vegas program. -/
def IsDominant (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (who : P) (s : Strategy p env hd who) : Prop :=
  (Game p env hd).IsDominant who s

/-- Preference-parameterized dominant strategy for a player in a Vegas program. -/
def IsDominantFor (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (pref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (who : P) (s : Strategy p env hd who) : Prop :=
  (Game p env hd).IsDominantFor pref who s

/-- Strict Nash equilibrium for a Vegas program. -/
def IsStrictNash (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (σ : StrategyProfile p env hd) : Prop :=
  (Game p env hd).IsStrictNash σ

/-- Preference-parameterized strict Nash equilibrium for a Vegas program. -/
def IsStrictNashFor (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (spref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (σ : StrategyProfile p env hd) : Prop :=
  (Game p env hd).IsStrictNashFor spref σ

/-- Strictly dominant strategy for a player in a Vegas program. -/
def IsStrictDominant (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (who : P) (s : Strategy p env hd who) : Prop :=
  (Game p env hd).IsStrictDominant who s

/-- Preference-parameterized strictly dominant strategy for a Vegas player. -/
def IsStrictDominantFor (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (spref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (who : P) (s : Strategy p env hd who) : Prop :=
  (Game p env hd).IsStrictDominantFor spref who s

/-- Weak dominance between two Vegas strategies for one player. -/
def WeaklyDominates (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (who : P) (s t : Strategy p env hd who) : Prop :=
  (Game p env hd).WeaklyDominates who s t

/-- Preference-parameterized weak dominance between two Vegas strategies. -/
def WeaklyDominatesFor (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (pref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (who : P) (s t : Strategy p env hd who) : Prop :=
  (Game p env hd).WeaklyDominatesFor pref who s t

/-- Strict dominance between two Vegas strategies for one player. -/
def StrictlyDominates (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (who : P) (s t : Strategy p env hd who) : Prop :=
  (Game p env hd).StrictlyDominates who s t

/-- Preference-parameterized strict dominance between two Vegas strategies. -/
def StrictlyDominatesFor (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (spref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (who : P) (s t : Strategy p env hd who) : Prop :=
  (Game p env hd).StrictlyDominatesFor spref who s t

/-- Pareto dominance for Vegas strategy profiles. -/
def ParetoDominates (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (σ τ : StrategyProfile p env hd) : Prop :=
  (Game p env hd).ParetoDominates σ τ

/-- Preference-parameterized Pareto dominance for Vegas strategy profiles. -/
def ParetoDominatesFor (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (pref spref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (σ τ : StrategyProfile p env hd) : Prop :=
  (Game p env hd).ParetoDominatesFor pref spref σ τ

/-- Pareto efficiency for Vegas strategy profiles. -/
def IsParetoEfficient (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (σ : StrategyProfile p env hd) : Prop :=
  (Game p env hd).IsParetoEfficient σ

/-- Preference-parameterized Pareto efficiency for Vegas strategy profiles. -/
def IsParetoEfficientFor (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (pref spref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (σ : StrategyProfile p env hd) : Prop :=
  (Game p env hd).IsParetoEfficientFor pref spref σ

/-- Social welfare of a Vegas strategy profile, via `toKernelGame`. -/
noncomputable def socialWelfare [Fintype P] (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (σ : StrategyProfile p env hd) : ℝ :=
  (Game p env hd).socialWelfare σ

/-- Correlated equilibrium for a Vegas correlated profile. -/
def IsCorrelatedEq (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (μ : CorrelatedProfile p env hd) : Prop :=
  (Game p env hd).IsCorrelatedEq μ

/-- Coarse correlated equilibrium for a Vegas correlated profile. -/
def IsCoarseCorrelatedEq (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (μ : CorrelatedProfile p env hd) : Prop :=
  (Game p env hd).IsCoarseCorrelatedEq μ

/-- Preference-parameterized correlated equilibrium for a Vegas correlated
profile. -/
def IsCorrelatedEqFor (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (pref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (μ : CorrelatedProfile p env hd) : Prop :=
  (Game p env hd).IsCorrelatedEqFor pref μ

/-- Preference-parameterized coarse correlated equilibrium for a Vegas
correlated profile. -/
def IsCoarseCorrelatedEqFor (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (pref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (μ : CorrelatedProfile p env hd) : Prop :=
  (Game p env hd).IsCoarseCorrelatedEqFor pref μ

end Vegas
