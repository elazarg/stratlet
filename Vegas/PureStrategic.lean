import GameTheory.Core.KernelGame
import GameTheory.Concepts.SolutionConcepts
import GameTheory.Core.GameProperties
import Vegas.Finite
import Vegas.BigStep
import Vegas.Strategic

/-!
# Fixed-Program Pure Strategic Form

This file defines a finite pure strategic form for a fixed Vegas program.

Unlike a global policy space over all contexts and guards, `ProgramPureStrategy
who p` contains one deterministic choice rule for each commit site of the fixed
program `p` owned by `who`.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Player-`who` pure strategies for the fixed program `p`: one deterministic
choice rule for each commit site of `p` owned by `who`. -/
def ProgramPureStrategy (who : P) :
    {Γ : VCtx P L} → VegasCore P L Γ → Type
  | _, .ret _ => PUnit
  | _, .letExpr _ _ k => ProgramPureStrategy who k
  | _, .sample _ _ _ _ k => ProgramPureStrategy who k
  | Γ, .commit _ owner (b := b) _ k =>
      if owner = who then
        PureKernel (P := P) (L := L) who Γ b × ProgramPureStrategy who k
      else
        ProgramPureStrategy who k
  | _, .reveal _ _ _ _ k => ProgramPureStrategy who k

/-- Joint pure strategy profile for the fixed program `p`. -/
abbrev ProgramPureProfile {Γ : VCtx P L} (p : VegasCore P L Γ) : Type :=
  ∀ who, ProgramPureStrategy (P := P) (L := L) who p

namespace ProgramPureStrategy

/-- Extract the current player's decision rule at the head commit site. -/
def headKernel
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (σ : ProgramPureStrategy (P := P) (L := L) who (.commit x who R k)) :
    PureKernel (P := P) (L := L) who Γ b := by
  let σ' : PureKernel (P := P) (L := L) who Γ b ×
      ProgramPureStrategy (P := P) (L := L) who k := by
    simpa [ProgramPureStrategy] using σ
  exact σ'.1

/-- Drop the head commit-site choice rule from the acting player's strategy. -/
def tailOwn
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (σ : ProgramPureStrategy (P := P) (L := L) who (.commit x who R k)) :
    ProgramPureStrategy (P := P) (L := L) who k := by
  let σ' : PureKernel (P := P) (L := L) who Γ b ×
      ProgramPureStrategy (P := P) (L := L) who k := by
    simpa [ProgramPureStrategy] using σ
  exact σ'.2

noncomputable instance instFintype
    (LF : FiniteValuation L) (who : P) :
    {Γ : VCtx P L} → (p : VegasCore P L Γ) →
      Fintype (ProgramPureStrategy (P := P) (L := L) who p)
  | _, .ret _ => inferInstanceAs (Fintype PUnit)
  | _, .letExpr _ _ k => instFintype LF who k
  | _, .sample _ _ _ _ k => instFintype LF who k
  | Γ, .commit _ owner (b := b) _ k =>
      match decEq owner who with
      | isTrue h =>
          let _ : Fintype (ViewEnv (P := P) (L := L) who Γ) :=
            Vegas.Env.instFintype
              (L := L) (LF := LF) (Γ := eraseVCtx (viewVCtx who Γ))
          let _ : Fintype (L.Val b) := LF.fintypeVal b
          let _ : Fintype (PureKernel (P := P) (L := L) who Γ b) := by
            classical
            dsimp [PureKernel]
            exact @Pi.instFintype
              (ViewEnv (P := P) (L := L) who Γ)
              (fun _ => L.Val b)
              (Classical.decEq _)
              inferInstance
              (fun _ => LF.fintypeVal b)
          let _ : Fintype (ProgramPureStrategy (P := P) (L := L) who k) :=
            instFintype LF who k
          by
            simpa [ProgramPureStrategy, h] using
              inferInstanceAs
                (Fintype (PureKernel (P := P) (L := L) who Γ b ×
                  ProgramPureStrategy (P := P) (L := L) who k))
      | isFalse h =>
          by
            simpa [ProgramPureStrategy, h] using instFintype LF who k
  | _, .reveal _ _ _ _ k => instFintype LF who k

end ProgramPureStrategy

namespace ProgramPureProfile

/-- Drop the head commit site from a pure profile. -/
def tail
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (σ : ProgramPureProfile (P := P) (L := L) (.commit x who R k)) :
    ProgramPureProfile (P := P) (L := L) k :=
  fun i =>
    by
      by_cases h : who = i
      · subst h
        exact ProgramPureStrategy.tailOwn (P := P) (L := L) (σ who)
      · simpa [ProgramPureStrategy, h] using σ i

noncomputable instance instFintype
    (LF : FiniteValuation L) [Fintype P]
    {Γ : VCtx P L} (p : VegasCore P L Γ) :
    Fintype (ProgramPureProfile (P := P) (L := L) p) := by
  classical
  dsimp [ProgramPureProfile]
  exact @Pi.instFintype
    P
    (fun who => ProgramPureStrategy (P := P) (L := L) who p)
    inferInstance
    inferInstance
    (fun who => ProgramPureStrategy.instFintype (P := P) (L := L) LF who p)

end ProgramPureProfile

namespace ProgramBehavioralKernel

/-- Turn a deterministic local rule into a normalized behavioral local rule. -/
noncomputable def ofPure
    {who : P} {Γ : VCtx P L} {b : L.Ty}
    (κ : PureKernel (P := P) (L := L) who Γ b) :
    ProgramBehavioralKernel (P := P) (L := L) who Γ b :=
  { run := fun view => FDist.pure (κ view)
    normalized := by
      intro view
      simp [FDist.totalWeight_pure] }

@[simp] theorem run_ofPure
    {who : P} {Γ : VCtx P L} {b : L.Ty}
    (κ : PureKernel (P := P) (L := L) who Γ b)
    (view : ViewEnv (P := P) (L := L) who Γ) :
    (ofPure (P := P) (L := L) κ).run view = FDist.pure (κ view) := rfl

end ProgramBehavioralKernel

namespace ProgramPureProfile

/-- Lift a fixed-program pure profile to the corresponding fixed-program
behavioral profile. -/
noncomputable def toBehavioral :
    {Γ : VCtx P L} →
      (p : VegasCore P L Γ) →
      ProgramPureProfile (P := P) (L := L) p →
      ProgramBehavioralProfile (P := P) (L := L) p
  | _, .ret _, _ => fun _ => PUnit.unit
  | _, .letExpr _ _ k, σ => toBehavioral k σ
  | _, .sample _ _ _ _ k, σ => toBehavioral k σ
  | _, .commit _ who R k, σ =>
      fun i =>
        by
          by_cases h : who = i
          · subst h
            simpa [ProgramBehavioralStrategy] using
              (ProgramBehavioralKernel.ofPure (P := P) (L := L)
                (ProgramPureStrategy.headKernel (P := P) (L := L) (σ who)),
               toBehavioral k (tail (P := P) (L := L) σ) who)
          · simpa [ProgramBehavioralStrategy, h] using
              toBehavioral k (tail (P := P) (L := L) σ) i
  | _, .reveal _ _ _ _ k, σ => toBehavioral k σ

@[simp] theorem tail_toBehavioral
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (σ : ProgramPureProfile (P := P) (L := L) (.commit x who R k)) :
    ProgramBehavioralProfile.tail (P := P) (L := L) (toBehavioral (.commit x who R k) σ) =
      toBehavioral k (tail (P := P) (L := L) σ) := by
  funext i
  by_cases h : who = i
  · subst h
    simp [toBehavioral, ProgramBehavioralProfile.tail, ProgramBehavioralStrategy.tailOwn]
  · simp [toBehavioral, ProgramBehavioralProfile.tail, h]

end ProgramPureProfile

/-- Evaluate a fixed-program pure profile directly, threading the continuation
profile through the program structure. -/
noncomputable def outcomeDistPure :
    {Γ : VCtx P L} →
      (p : VegasCore P L Γ) →
      ProgramPureProfile (P := P) (L := L) p →
      VEnv (Player := P) L Γ →
      FDist (Outcome P)
  | _, .ret payoffs, _, env =>
      FDist.pure (evalPayoffs payoffs env)
  | _, .letExpr x e k, σ, env =>
      outcomeDistPure k σ <|
        VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _)
          (L.eval e (VEnv.erasePubEnv env)) env
  | _, .sample x τ m D' k, σ, env =>
      FDist.bind
        (L.evalDist D' (VEnv.eraseDistEnv τ m env))
        (fun v =>
          outcomeDistPure k σ
            (VEnv.cons (Player := P) (L := L) (x := x) (τ := τ) v env))
  | _, .commit x who (b := b) _ k, σ, env =>
      let s := ProgramPureStrategy.headKernel (P := P) (L := L) (σ who)
      let v := s (projectViewEnv (P := P) (L := L) who (VEnv.eraseEnv env))
      outcomeDistPure k (ProgramPureProfile.tail (P := P) (L := L) σ)
        (VEnv.cons (Player := P) (L := L) (x := x)
          (τ := .hidden who b) v env)
  | _, .reveal y _who _x (b := b) hx k, σ, env =>
      let v : L.Val b := VEnv.get (Player := P) (L := L) env hx
      outcomeDistPure k σ
        (VEnv.cons (Player := P) (L := L) (x := y) (τ := .pub b) v env)

theorem outcomeDistPure_totalWeight_eq_one
    {Γ : VCtx P L} {p : VegasCore P L Γ}
    {σ : ProgramPureProfile (P := P) (L := L) p}
    {env : VEnv (Player := P) L Γ}
    (hd : NormalizedDists p) :
    (outcomeDistPure p σ env).totalWeight = 1 := by
  induction p with
  | ret u =>
      simp [outcomeDistPure, FDist.totalWeight_pure]
  | letExpr x e k ih =>
      exact ih hd
  | sample x τ m D' k ih =>
      simp only [outcomeDistPure]
      exact FDist.totalWeight_bind_of_normalized (hd.1 _) (fun _ _ => ih hd.2)
  | commit x who R k ih =>
      simpa [outcomeDistPure] using
        ih (σ := ProgramPureProfile.tail (P := P) (L := L) σ) hd
  | reveal y who x hx k ih =>
      exact ih hd

/-- Running the local behavioral lift of a fixed-program pure profile yields
the same outcome distribution as the pure strategic semantics. -/
theorem outcomeDistBehavioral_toBehavioral_eq_outcomeDistPure
    {Γ : VCtx P L} (p : VegasCore P L Γ)
    (σ : ProgramPureProfile (P := P) (L := L) p)
    (env : VEnv (Player := P) L Γ) :
    outcomeDistBehavioral p (ProgramPureProfile.toBehavioral (P := P) (L := L) p σ) env =
      outcomeDistPure p σ env := by
  induction p with
  | ret u =>
      rfl
  | letExpr x e k ih =>
      simpa [outcomeDistBehavioral, outcomeDistPure, ProgramPureProfile.toBehavioral] using
        ih σ _
  | sample x τ m D' k ih =>
      simp only [outcomeDistBehavioral, outcomeDistPure]
      congr
      funext v
      exact ih σ _
  | commit x who R k ih =>
      simp only [outcomeDistBehavioral, outcomeDistPure]
      have hhead :
          ProgramBehavioralStrategy.headKernel (P := P) (L := L)
              ((ProgramPureProfile.toBehavioral
                  (P := P) (L := L) (.commit x who R k) σ) who)
              (projectViewEnv (P := P) (L := L) who (VEnv.eraseEnv env)) =
            FDist.pure
              ((ProgramPureStrategy.headKernel (P := P) (L := L) (σ who))
                (projectViewEnv (P := P) (L := L) who (VEnv.eraseEnv env))) := by
        simp [ProgramPureProfile.toBehavioral, ProgramBehavioralStrategy.headKernel,
          ProgramBehavioralKernel.ofPure, ProgramPureStrategy.headKernel]
      rw [hhead, FDist.pure_bind]
      simpa [ProgramPureProfile.tail_toBehavioral] using
        ih (ProgramPureProfile.tail (P := P) (L := L) σ)
          (VEnv.cons (Player := P) (L := L) (x := x) (τ := .hidden who _)
            ((ProgramPureStrategy.headKernel (P := P) (L := L) (σ who))
              (projectViewEnv (P := P) (L := L) who (VEnv.eraseEnv env))) env)
  | reveal y who x hx k ih =>
      simpa [outcomeDistBehavioral, outcomeDistPure, ProgramPureProfile.toBehavioral] using
        ih σ _

/-- Fixed-program pure strategic form of a Vegas program. -/
noncomputable def toStrategicKernelGame
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p) : GameTheory.KernelGame P where
  Strategy := fun who => ProgramPureStrategy (P := P) (L := L) who p
  Outcome := Outcome P
  utility := fun o i => (o i : ℝ)
  outcomeKernel := fun σ =>
    (outcomeDistPure p σ env).toPMF
      (outcomeDistPure_totalWeight_eq_one (P := P) (L := L) (p := p) (σ := σ) hd)

@[simp] theorem toStrategicKernelGame_outcomeKernel
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p)
    (σ : ProgramPureProfile (P := P) (L := L) p) :
    (toStrategicKernelGame p env hd).outcomeKernel σ =
      (outcomeDistPure p σ env).toPMF
        (outcomeDistPure_totalWeight_eq_one
          (P := P) (L := L) (p := p) (σ := σ) hd) := rfl

/-- Expected utility in the fixed-program pure strategic form matches the Vegas
expected payoff computed from `outcomeDistPure`. -/
theorem toStrategicKernelGame_eu
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p)
    (σ : ProgramPureProfile (P := P) (L := L) p) (who : P) :
    (toStrategicKernelGame p env hd).eu σ who =
      (outcomeDistPure p σ env).sum
        (fun o w => (w : ℝ) * (o who : ℝ)) := by
  let hnorm :=
    outcomeDistPure_totalWeight_eq_one
      (P := P) (L := L) (p := p) (σ := σ) (env := env) hd
  simpa [GameTheory.KernelGame.eu, toStrategicKernelGame, hnorm,
    NNRat.toNNReal_coe_real] using
    (FDist.expect_toPMF_eq_sum
      (d := outcomeDistPure p σ env)
      (h := hnorm)
      (f := fun o => (o who : ℝ)))

/-- The local behavioral lift of a fixed-program pure profile has the same
outcome kernel as the fixed-program pure strategic form. -/
theorem toKernelGame_outcomeKernel_eq_toStrategicKernelGame_toBehavioral
    {Γ : VCtx P L} (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p)
    (σ : ProgramPureProfile (P := P) (L := L) p) :
    (toKernelGame p env hd).outcomeKernel (ProgramPureProfile.toBehavioral (P := P) (L := L) p σ) =
      (toStrategicKernelGame p env hd).outcomeKernel σ := by
  have hout :=
    outcomeDistBehavioral_toBehavioral_eq_outcomeDistPure
      (P := P) (L := L) p σ env
  rw [toKernelGame_outcomeKernel, toStrategicKernelGame_outcomeKernel]
  simp [hout]

/-- The local behavioral lift of a fixed-program pure profile has the same
expected utility as the fixed-program pure strategic form. -/
theorem toKernelGame_eu_eq_toStrategicKernelGame_toBehavioral
    {Γ : VCtx P L} (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p)
    (σ : ProgramPureProfile (P := P) (L := L) p)
    (who : P) :
    (toKernelGame p env hd).eu (ProgramPureProfile.toBehavioral (P := P) (L := L) p σ) who =
      (toStrategicKernelGame p env hd).eu σ who := by
  have hout :=
    outcomeDistBehavioral_toBehavioral_eq_outcomeDistPure
      (P := P) (L := L) p σ env
  rw [toKernelGame_eu, toStrategicKernelGame_eu]
  simp [hout]

/-- Pure Nash equilibrium of the fixed-program Vegas strategic form. -/
def IsPureNash
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p)
    (σ : ProgramPureProfile (P := P) (L := L) p) : Prop :=
  (toStrategicKernelGame p env hd).IsNash σ

/-- Pure dominant strategy in the fixed-program Vegas strategic form. -/
def IsPureDominant
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p)
    (who : P) (s : ProgramPureStrategy (P := P) (L := L) who p) : Prop :=
  (toStrategicKernelGame p env hd).IsDominant who s

/-- Pure best response in the fixed-program Vegas strategic form. -/
def IsPureBestResponse
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p)
    (who : P) (σ : ProgramPureProfile (P := P) (L := L) p)
    (s : ProgramPureStrategy (P := P) (L := L) who p) : Prop :=
  (toStrategicKernelGame p env hd).IsBestResponse who σ s

/-- Pure strict Nash equilibrium of the fixed-program Vegas strategic form. -/
def IsPureStrictNash
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p)
    (σ : ProgramPureProfile (P := P) (L := L) p) : Prop :=
  (toStrategicKernelGame p env hd).IsStrictNash σ

/-- Exact potential for the fixed-program Vegas strategic form. -/
def IsPureExactPotential
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p)
    (Φ : ProgramPureProfile (P := P) (L := L) p → ℝ) : Prop :=
  (toStrategicKernelGame p env hd).IsExactPotential Φ

/-- Ordinal potential for the fixed-program Vegas strategic form. -/
def IsPureOrdinalPotential
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p)
    (Φ : ProgramPureProfile (P := P) (L := L) p → ℝ) : Prop :=
  (toStrategicKernelGame p env hd).IsOrdinalPotential Φ

end Vegas
