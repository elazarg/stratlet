import Vegas.Equilibrium
import GameTheory.Concepts.ApproximateNash
import GameTheory.Concepts.DominanceSolvability
import GameTheory.Concepts.Rationalizability
import GameTheory.Concepts.SecurityStrategy
import GameTheory.Concepts.Minimax
import GameTheory.Concepts.PriceOfAnarchy

/-!
# Vegas game-theoretic properties

Core game-theoretic property definitions for Vegas programs, transported through
the local `toKernelGame` bridge. All declarations consume a `WFProgram` bundle.

Corollaries and derived theorems live under `Vegas/Corollaries/`.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

def IsεNash (g : WFProgram P L) (ε : ℝ) (σ : StrategyProfile g) : Prop :=
  (Game g).IsεNash ε σ

def IsεBestResponse (g : WFProgram P L)
    (ε : ℝ) (who : P) (σ : StrategyProfile g) (s : Strategy g who) : Prop :=
  (Game g).IsεBestResponse ε who σ s

def Survives (g : WFProgram P L) (n : ℕ) (who : P)
    (s : Strategy g who) : Prop :=
  (Game g).Survives n who s

def IsRationalizable (g : WFProgram P L) (who : P)
    (s : Strategy g who) : Prop :=
  (Game g).IsRationalizable who s

def IsIndividuallyRational (g : WFProgram P L)
    (r : P → ℝ) (σ : StrategyProfile g) : Prop :=
  (Game g).IsIndividuallyRational r σ

def IsDominanceSolvable (g : WFProgram P L) : Prop :=
  (Game g).IsDominanceSolvable

noncomputable def IsDominanceSolvable.dominantProfile
    (g : WFProgram P L)
    (h : IsDominanceSolvable g) : StrategyProfile g :=
  KernelGame.IsDominanceSolvable.dominantProfile (G := Game g) h

def IsExactPotential (g : WFProgram P L)
    (Φ : StrategyProfile g → ℝ) : Prop :=
  (Game g).IsExactPotential Φ

def IsOrdinalPotential (g : WFProgram P L)
    (Φ : StrategyProfile g → ℝ) : Prop :=
  (Game g).IsOrdinalPotential Φ

def Guarantees (g : WFProgram P L)
    (who : P) (s : Strategy g who) (v : ℝ) : Prop :=
  (Game g).Guarantees who s v

def IsSaddlePoint
    (g : WFProgram (Fin 2) L)
    (σ : StrategyProfile g) : Prop :=
  (Game g).IsSaddlePoint σ

def MixedStrategy (g : WFProgram P L) (who : P) : Type :=
  PMF (Strategy g who)

def MixedStrategyProfile [Fintype P] (g : WFProgram P L)
    [∀ who, Fintype (Strategy g who)] : Type :=
  KernelGame.Profile (Game g).mixedExtension

def IsMixedNash [Fintype P] (g : WFProgram P L)
    [∀ who, Fintype (Strategy g who)]
    (σ : MixedStrategyProfile g) : Prop :=
  (Game g).mixedExtension.IsNash σ

noncomputable def mixedEu [Fintype P] (g : WFProgram P L)
    [∀ who, Fintype (Strategy g who)]
    (σ : MixedStrategyProfile g) (who : P) : ℝ :=
  (Game g).mixedExtension.eu σ who

noncomputable def worstCaseEU (g : WFProgram P L)
    [Fintype (StrategyProfile g)]
    [∀ who, Fintype (Strategy g who)]
    [∀ who, Nonempty (Strategy g who)]
    [Nonempty (StrategyProfile g)]
    (who : P) (s : Strategy g who) : ℝ :=
  (Game g).worstCaseEU who s

noncomputable def securityLevel (g : WFProgram P L)
    [Fintype (StrategyProfile g)]
    [∀ who, Fintype (Strategy g who)]
    [∀ who, Nonempty (Strategy g who)]
    [Nonempty (StrategyProfile g)]
    (who : P) : ℝ :=
  (Game g).securityLevel who

def IsConstantSum [Fintype P] (g : WFProgram P L) (c : ℝ) : Prop :=
  (Game g).IsConstantSum c

def IsZeroSum [Fintype P] (g : WFProgram P L) : Prop :=
  (Game g).IsZeroSum

def IsTeamGame [Fintype P] (g : WFProgram P L) : Prop :=
  (Game g).IsTeamGame

noncomputable def optimalWelfare [Fintype P] (g : WFProgram P L) : ℝ :=
  (Game g).optimalWelfare

noncomputable def bestNashWelfare [Fintype P] (g : WFProgram P L)
    [Fintype (StrategyProfile g)] [Nonempty (StrategyProfile g)]
    (hN : ∃ σ : StrategyProfile g, IsNash g σ) : ℝ :=
  (Game g).bestNashWelfare <| by
    simpa [IsNash] using hN

noncomputable def worstNashWelfare [Fintype P] (g : WFProgram P L)
    [Fintype (StrategyProfile g)] [Nonempty (StrategyProfile g)]
    (hN : ∃ σ : StrategyProfile g, IsNash g σ) : ℝ :=
  (Game g).worstNashWelfare <| by
    simpa [IsNash] using hN

end Vegas
