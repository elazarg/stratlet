import GameTheory.Core.KernelGame
import Vegas.BigStep
import Vegas.ViewKernel

/-!
# Strategic semantics bridge

Vegas's `outcomeDist` produces `FDist (Outcome P)` — a Finsupp-based weighted
distribution over outcomes. This file packages a fixed program's local
behavioral strategy space as a `KernelGame`.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A normalized behavioral choice rule for one fixed commit site. -/
structure ProgramBehavioralKernel
    (who : P) (Γ : VCtx P L) (b : L.Ty) where
  run : BehavioralKernel (P := P) (L := L) who Γ b
  normalized : ∀ view, FDist.totalWeight (run view) = 1

/-- Player-`who` behavioral strategies for the fixed program `p`: one
normalized behavioral choice rule for each commit site of `p` owned by `who`. -/
def ProgramBehavioralStrategy (who : P) :
    {Γ : VCtx P L} → VegasCore P L Γ → Type
  | _, .ret _ => PUnit
  | _, .letExpr _ _ k => ProgramBehavioralStrategy who k
  | _, .sample _ _ k => ProgramBehavioralStrategy who k
  | Γ, .commit _ owner (b := b) _ k =>
      if owner = who then
        ProgramBehavioralKernel (P := P) (L := L) who Γ b × ProgramBehavioralStrategy who k
      else
        ProgramBehavioralStrategy who k
  | _, .reveal _ _ _ _ k => ProgramBehavioralStrategy who k

/-- Joint behavioral strategy profile for the fixed program `p`. -/
abbrev ProgramBehavioralProfile {Γ : VCtx P L} (p : VegasCore P L Γ) : Type :=
  ∀ who, ProgramBehavioralStrategy (P := P) (L := L) who p

namespace ProgramBehavioralStrategy

/-- Extract the current player's behavioral decision rule at the head commit site. -/
def headKernel
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (σ : ProgramBehavioralStrategy (P := P) (L := L) who (.commit x who R k)) :
    BehavioralKernel (P := P) (L := L) who Γ b := by
  let σ' : ProgramBehavioralKernel (P := P) (L := L) who Γ b ×
      ProgramBehavioralStrategy (P := P) (L := L) who k := by
    simpa [ProgramBehavioralStrategy] using σ
  exact σ'.1.run

/-- Normalization of the current player's behavioral rule at the head commit site. -/
theorem headKernel_normalized
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (σ : ProgramBehavioralStrategy (P := P) (L := L) who (.commit x who R k))
    (view : ViewEnv (P := P) (L := L) who Γ) :
    FDist.totalWeight (headKernel (P := P) (L := L) σ view) = 1 := by
  let σ' : ProgramBehavioralKernel (P := P) (L := L) who Γ b ×
      ProgramBehavioralStrategy (P := P) (L := L) who k := by
    simpa [ProgramBehavioralStrategy] using σ
  exact σ'.1.normalized view

/-- Drop the head commit-site choice rule from the acting player's strategy. -/
def tailOwn
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (σ : ProgramBehavioralStrategy (P := P) (L := L) who (.commit x who R k)) :
    ProgramBehavioralStrategy (P := P) (L := L) who k := by
  let σ' : ProgramBehavioralKernel (P := P) (L := L) who Γ b ×
      ProgramBehavioralStrategy (P := P) (L := L) who k := by
    simpa [ProgramBehavioralStrategy] using σ
  exact σ'.2

end ProgramBehavioralStrategy

namespace ProgramBehavioralProfile

/-- Drop the head commit site from a behavioral profile. -/
def tail
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (σ : ProgramBehavioralProfile (P := P) (L := L) (.commit x who R k)) :
    ProgramBehavioralProfile (P := P) (L := L) k :=
  fun i =>
    by
      by_cases h : who = i
      · subst h
        exact ProgramBehavioralStrategy.tailOwn (P := P) (L := L) (σ who)
      · simpa [ProgramBehavioralStrategy, h] using σ i

end ProgramBehavioralProfile

/-- Evaluate a fixed-program behavioral profile directly, threading the
continuation profile through the program structure. -/
noncomputable def outcomeDistBehavioral :
    {Γ : VCtx P L} →
      (p : VegasCore P L Γ) →
      ProgramBehavioralProfile (P := P) (L := L) p →
      VEnv (Player := P) L Γ →
      FDist (Outcome P)
  | _, .ret payoffs, _, env =>
      FDist.pure (evalPayoffs payoffs env)
  | _, .letExpr x e k, σ, env =>
      outcomeDistBehavioral k σ <|
        VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _)
          (L.eval e (VEnv.erasePubEnv env)) env
  | _, .sample x D' k, σ, env =>
      FDist.bind
        (L.evalDist D' (VEnv.eraseSampleEnv env))
        (fun v =>
          outcomeDistBehavioral k σ
            (VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _) v env))
  | _, .commit x who (b := b) _ k, σ, env =>
      let κ := ProgramBehavioralStrategy.headKernel (P := P) (L := L) (σ who)
      FDist.bind
        (κ (projectViewEnv (P := P) (L := L) who (VEnv.eraseEnv env)))
        (fun v =>
          outcomeDistBehavioral k (ProgramBehavioralProfile.tail (P := P) (L := L) σ)
            (VEnv.cons (Player := P) (L := L) (x := x)
              (τ := .hidden who b) v env))
  | _, .reveal y _who _x (b := b) hx k, σ, env =>
      let v : L.Val b := VEnv.get (Player := P) (L := L) env hx
      outcomeDistBehavioral k σ
        (VEnv.cons (Player := P) (L := L) (x := y) (τ := .pub b) v env)

theorem outcomeDistBehavioral_totalWeight_eq_one
    {Γ : VCtx P L} {p : VegasCore P L Γ}
    {σ : ProgramBehavioralProfile (P := P) (L := L) p}
    {env : VEnv (Player := P) L Γ}
    (hd : NormalizedDists p) :
    (outcomeDistBehavioral p σ env).totalWeight = 1 := by
  induction p with
  | ret u =>
      simp [outcomeDistBehavioral, FDist.totalWeight_pure]
  | letExpr x e k ih =>
      exact ih hd
  | sample x D' k ih =>
      simp only [outcomeDistBehavioral]
      exact FDist.totalWeight_bind_of_normalized (hd.1 _) (fun _ _ => ih hd.2)
  | commit x who R k ih =>
      simp only [outcomeDistBehavioral]
      exact FDist.totalWeight_bind_of_normalized
        (ProgramBehavioralStrategy.headKernel_normalized (P := P) (L := L) (σ who) _)
        (fun _ _ => ih (σ := ProgramBehavioralProfile.tail (P := P) (L := L) σ) hd)
  | reveal y who x hx k ih =>
      exact ih hd

/-- Vegas denotational semantics as a `KernelGame` whose strategies are the
fixed program's local behavioral strategies. -/
noncomputable def toKernelGame (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p) : GameTheory.KernelGame P where
  Strategy := fun who => ProgramBehavioralStrategy (P := P) (L := L) who p
  Outcome := Outcome P
  utility := fun o i => (o i : ℝ)
  outcomeKernel := fun σ =>
    (outcomeDistBehavioral p σ env).toPMF
      (outcomeDistBehavioral_totalWeight_eq_one (P := P) (L := L) (p := p) (σ := σ) hd)

@[simp] theorem toKernelGame_outcomeKernel
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p)
    (σ : ProgramBehavioralProfile (P := P) (L := L) p) :
    (toKernelGame p env hd).outcomeKernel σ =
      (outcomeDistBehavioral p σ env).toPMF
        (outcomeDistBehavioral_totalWeight_eq_one
          (P := P) (L := L) (p := p) (σ := σ) hd) := rfl

@[simp] theorem toKernelGame_udist
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p)
    (σ : ProgramBehavioralProfile (P := P) (L := L) p) :
    (toKernelGame p env hd).udist σ =
      ((outcomeDistBehavioral p σ env).toPMF
        (outcomeDistBehavioral_totalWeight_eq_one
          (P := P) (L := L) (p := p) (σ := σ) hd)).bind
        (fun o => PMF.pure (fun i => (o i : ℝ))) := rfl

/-- Expected utility in the kernel game matches Vegas expected payoff. -/
theorem toKernelGame_eu
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p)
    (σ : ProgramBehavioralProfile (P := P) (L := L) p) (who : P) :
    (toKernelGame p env hd).eu σ who =
      (outcomeDistBehavioral p σ env).sum
        (fun o w => (w : ℝ) * (o who : ℝ)) := by
  let hnorm :=
    outcomeDistBehavioral_totalWeight_eq_one
      (P := P) (L := L) (p := p) (σ := σ) (env := env) hd
  simpa [GameTheory.KernelGame.eu, toKernelGame, hnorm,
    NNRat.toNNReal_coe_real] using
    (FDist.expect_toPMF_eq_sum
      (d := outcomeDistBehavioral p σ env)
      (h := hnorm)
      (f := fun o => (o who : ℝ)))

end Vegas
