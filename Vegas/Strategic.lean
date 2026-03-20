import GameTheory.Core.KernelGame
import Vegas.BigStep
import Vegas.Strategies

/-!
# Strategic semantics bridge

Vegas's `outcomeDist` produces `FDist (Outcome P)` — a Finsupp-based weighted
distribution over outcomes. This file packages normalized behavioral Vegas
profiles as `KernelGame`s.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Vegas denotational semantics as a `KernelGame` whose strategies are
behavioral Vegas strategies indexed by actual player views. -/
noncomputable def toKernelGame (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p) : GameTheory.KernelGame P where
  Strategy := BehavioralStrategy (P := P) (L := L)
  Outcome := Outcome P
  utility := fun o i => (o i : ℝ)
  outcomeKernel := fun σ =>
    let prof := BehavioralProfile.toOperationalProfile (P := P) (L := L) σ
    (outcomeDist prof p env).toPMF
      (outcomeDist_totalWeight_eq_one hd
        (BehavioralProfile.toOperationalProfile_normalizedOn (P := P) (L := L) σ p))

@[simp] theorem toKernelGame_outcomeKernel
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p)
    (σ : BehavioralProfile (P := P) (L := L)) :
    (toKernelGame p env hd).outcomeKernel σ =
      (outcomeDist (BehavioralProfile.toOperationalProfile (P := P) (L := L) σ) p env).toPMF
        (outcomeDist_totalWeight_eq_one hd
          (BehavioralProfile.toOperationalProfile_normalizedOn (P := P) (L := L) σ p)) := rfl

@[simp] theorem toKernelGame_udist (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (σ : BehavioralProfile (P := P) (L := L)) :
    (toKernelGame p env hd).udist σ =
      ((outcomeDist (BehavioralProfile.toOperationalProfile (P := P) (L := L) σ) p env).toPMF
        (outcomeDist_totalWeight_eq_one hd
          (BehavioralProfile.toOperationalProfile_normalizedOn (P := P) (L := L) σ p))).bind
        (fun o => PMF.pure (fun i => (o i : ℝ))) := rfl

/-- Expected utility in the kernel game matches Vegas expected payoff. -/
theorem toKernelGame_eu (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (σ : BehavioralProfile (P := P) (L := L)) (who : P) :
    (toKernelGame p env hd).eu σ who =
      (outcomeDist (BehavioralProfile.toOperationalProfile (P := P) (L := L) σ) p env).sum
        (fun o w => (w : ℝ) * (o who : ℝ)) := by
  let hnorm :=
    outcomeDist_totalWeight_eq_one (env := env) hd
      (BehavioralProfile.toOperationalProfile_normalizedOn (P := P) (L := L) σ p)
  simpa [GameTheory.KernelGame.eu, toKernelGame, hnorm,
    NNRat.toNNReal_coe_real] using
    (FDist.expect_toPMF_eq_sum
      (d := outcomeDist (BehavioralProfile.toOperationalProfile (P := P) (L := L) σ) p env)
      (h := hnorm)
      (f := fun o => (o who : ℝ)))

end Vegas
