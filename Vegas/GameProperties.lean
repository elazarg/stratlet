import Vegas.Equilibrium
import GameTheory.Concepts.ApproximateNash
import GameTheory.Concepts.Rationalizability
import GameTheory.Concepts.SecurityStrategy
import GameTheory.Concepts.Minimax
import GameTheory.Concepts.PriceOfAnarchy

/-!
# Vegas game-theoretic properties

Core game-theoretic property definitions for Vegas programs, transported through
the local `toKernelGame` bridge.

Corollaries and derived theorems live under `Vegas/Corollaries/`.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

def IsεNash (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (ε : ℝ) (σ : StrategyProfile p env hd) : Prop :=
  (Game p env hd).IsεNash ε σ

def IsεBestResponse (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (ε : ℝ) (who : P) (σ : StrategyProfile p env hd)
    (s : Strategy p env hd who) : Prop :=
  (Game p env hd).IsεBestResponse ε who σ s

def Survives (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (n : ℕ) (who : P) (s : Strategy p env hd who) : Prop :=
  (Game p env hd).Survives n who s

def IsRationalizable (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (who : P) (s : Strategy p env hd who) : Prop :=
  (Game p env hd).IsRationalizable who s

def IsIndividuallyRational (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (r : P → ℝ) (σ : StrategyProfile p env hd) : Prop :=
  (Game p env hd).IsIndividuallyRational r σ

def IsExactPotential (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (Φ : StrategyProfile p env hd → ℝ) : Prop :=
  (Game p env hd).IsExactPotential Φ

def IsOrdinalPotential (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (Φ : StrategyProfile p env hd → ℝ) : Prop :=
  (Game p env hd).IsOrdinalPotential Φ

def Guarantees (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (who : P) (s : Strategy p env hd who) (v : ℝ) : Prop :=
  (Game p env hd).Guarantees who s v

def IsSaddlePoint
    (p : VegasCore (Fin 2) L Γ) (env : VEnv (Player := Fin 2) L Γ)
    (hd : NormalizedDists p)
    (σ : StrategyProfile p env hd) : Prop :=
  (Game p env hd).IsSaddlePoint σ

def MixedStrategy (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (who : P) : Type :=
  PMF (Strategy p env hd who)

def MixedStrategyProfile [Fintype P]
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p)
    [∀ who, Fintype (Strategy p env hd who)] : Type :=
  KernelGame.Profile (Game p env hd).mixedExtension

def IsMixedNash [Fintype P]
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p)
    [∀ who, Fintype (Strategy p env hd who)]
    (σ : MixedStrategyProfile p env hd) : Prop :=
  (Game p env hd).mixedExtension.IsNash σ

noncomputable def mixedEu [Fintype P]
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p)
    [∀ who, Fintype (Strategy p env hd who)]
    (σ : MixedStrategyProfile p env hd) (who : P) : ℝ :=
  (Game p env hd).mixedExtension.eu σ who

noncomputable def worstCaseEU (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    [Fintype (StrategyProfile p env hd)]
    [∀ who, Fintype (Strategy p env hd who)]
    [∀ who, Nonempty (Strategy p env hd who)]
    [Nonempty (StrategyProfile p env hd)]
    (who : P) (s : Strategy p env hd who) : ℝ :=
  (Game p env hd).worstCaseEU who s

noncomputable def securityLevel (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    [Fintype (StrategyProfile p env hd)]
    [∀ who, Fintype (Strategy p env hd who)]
    [∀ who, Nonempty (Strategy p env hd who)]
    [Nonempty (StrategyProfile p env hd)]
    (who : P) : ℝ :=
  (Game p env hd).securityLevel who

def IsConstantSum [Fintype P] (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (c : ℝ) : Prop :=
  (Game p env hd).IsConstantSum c

def IsZeroSum [Fintype P] (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p) : Prop :=
  (Game p env hd).IsZeroSum

def IsTeamGame [Fintype P] (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p) : Prop :=
  (Game p env hd).IsTeamGame

noncomputable def optimalWelfare [Fintype P] (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p) : ℝ :=
  (Game p env hd).optimalWelfare

noncomputable def bestNashWelfare [Fintype P] (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    [Fintype (StrategyProfile p env hd)] [Nonempty (StrategyProfile p env hd)]
    (hN : ∃ σ : StrategyProfile p env hd, IsNash p env hd σ) : ℝ :=
  (Game p env hd).bestNashWelfare <| by
    simpa [IsNash] using hN

noncomputable def worstNashWelfare [Fintype P] (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    [Fintype (StrategyProfile p env hd)] [Nonempty (StrategyProfile p env hd)]
    (hN : ∃ σ : StrategyProfile p env hd, IsNash p env hd σ) : ℝ :=
  (Game p env hd).worstNashWelfare <| by
    simpa [IsNash] using hN

end Vegas
