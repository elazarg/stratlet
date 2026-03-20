import GameTheory.Core.KernelGame
import Vegas.BigStep

/-!
# Strategic semantics bridge

Vegas's `outcomeDist` produces `FDist (Outcome P)` — a Finsupp-based weighted
distribution over outcomes. This file connects them to probability theory
and packages normalized Vegas programs as `KernelGame`s.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A player's Vegas strategy component, bundled with normalization. -/
structure PlayerStrategy (who : P) where
  commit : {Γ : VCtx P L} → {b : L.Ty} → (x : VarId) →
    (R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool) →
    CommitKernel P L who Γ b
  normalized : {Γ : VCtx P L} → {b : L.Ty} → (x : VarId) →
    (R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool) →
    (env : Env L.Val (eraseVCtx Γ)) →
    FDist.totalWeight (commit x R env) = 1

/-- Assemble per-player strategy components into a Vegas `Profile`. -/
def toProfile (σ : ∀ who, PlayerStrategy (P := P) (L := L) who) :
    Profile P L where
  commit := fun who x R env => (σ who).commit x R env

/-- Bundled player strategies are normalized on every Vegas program. -/
theorem toProfile_normalizedOn (σ : ∀ who, PlayerStrategy (P := P) (L := L) who)
    (p : VegasCore P L Γ) :
    (toProfile σ).NormalizedOn p := by
  induction p with
  | ret u => trivial
  | letExpr x e k ih => exact ih
  | sample x τ m D' k ih => exact ih
  | commit x who R k ih =>
      exact ⟨(fun env => (σ who).normalized x R env), ih⟩
  | reveal y who x hx k ih => exact ih

/-- Vegas denotational semantics as a `KernelGame`. -/
noncomputable def toKernelGame (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p) : GameTheory.KernelGame P where
  Strategy := PlayerStrategy (P := P) (L := L)
  Outcome := Outcome P
  utility := fun o i => (o i : ℝ)
  outcomeKernel := fun σ =>
    let prof := toProfile σ
    (outcomeDist prof p env).toPMF
      (outcomeDist_totalWeight_eq_one hd (toProfile_normalizedOn σ p))

@[simp] theorem toKernelGame_outcomeKernel
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p)
    (σ : ∀ who, PlayerStrategy (P := P) (L := L) who) :
    (toKernelGame p env hd).outcomeKernel σ =
      (outcomeDist (toProfile σ) p env).toPMF
        (outcomeDist_totalWeight_eq_one hd (toProfile_normalizedOn σ p)) := rfl

@[simp] theorem toKernelGame_udist (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (σ : ∀ who, PlayerStrategy (P := P) (L := L) who) :
    (toKernelGame p env hd).udist σ =
      ((outcomeDist (toProfile σ) p env).toPMF
        (outcomeDist_totalWeight_eq_one hd (toProfile_normalizedOn σ p))).bind
        (fun o => PMF.pure (fun i => (o i : ℝ))) := rfl

/-- Expected utility in the restricted kernel game matches Vegas expected payoff. -/
theorem toKernelGame_eu (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ) (hd : NormalizedDists p)
    (σ : ∀ who, PlayerStrategy (P := P) (L := L) who) (who : P) :
    (toKernelGame p env hd).eu σ who =
      (outcomeDist (toProfile σ) p env).sum
        (fun o w => (w : ℝ) * (o who : ℝ)) := by
  let hnorm :=
    outcomeDist_totalWeight_eq_one (env := env) hd (toProfile_normalizedOn σ p)
  simpa [GameTheory.KernelGame.eu, toKernelGame, hnorm,
    NNRat.toNNReal_coe_real] using
    (FDist.expect_toPMF_eq_sum
      (d := outcomeDist (toProfile σ) p env)
      (h := hnorm)
      (f := fun o => (o who : ℝ)))

end Vegas
