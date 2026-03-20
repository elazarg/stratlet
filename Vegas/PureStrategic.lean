import GameTheory.Core.KernelGame
import GameTheory.Concepts.SolutionConcepts
import GameTheory.Concepts.BestResponse
import GameTheory.Concepts.NashProperties
import GameTheory.Concepts.PotentialGame
import GameTheory.Concepts.PotentialFIP
import GameTheory.Theorems.NashExistence
import Vegas.Finite
import Vegas.BigStep
import Vegas.Strategic

/-!
# Fixed-Program Pure Strategic Form

This file defines a finite pure strategic form for a fixed Vegas program.

Unlike `Vegas.PureStrategy` in `Vegas.Strategies`, which is a global policy
space over all contexts and guards, `ProgramPureStrategy p who` contains one
deterministic choice rule for each commit site of the fixed program `p` owned
by `who`.
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

namespace PureProfile

/-- A global pure Vegas profile agrees with a fixed-program pure profile when
they choose the same action at every commit site encountered in the program. -/
def AgreesOnProgram
    (π : PureProfile (P := P) (L := L)) :
    {Γ : VCtx P L} →
      (p : VegasCore P L Γ) →
      ProgramPureProfile (P := P) (L := L) p → Prop
  | _, .ret _, _ => True
  | _, .letExpr _ _ k, σ => AgreesOnProgram π k σ
  | _, .sample _ _ _ _ k, σ => AgreesOnProgram π k σ
  | _, .commit x who R k, σ =>
      (π who).commit x R = ProgramPureStrategy.headKernel (P := P) (L := L) (σ who) ∧
      AgreesOnProgram π k (ProgramPureProfile.tail (P := P) (L := L) σ)
  | _, .reveal _ _ _ _ k, σ => AgreesOnProgram π k σ

end PureProfile

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

/-- If a global pure Vegas profile agrees with a fixed-program pure profile on
the commit sites of `p`, then both induce the same outcome distribution on `p`. -/
theorem outcomeDist_eq_outcomeDistPure_of_agrees
    (π : PureProfile (P := P) (L := L))
    {Γ : VCtx P L} {p : VegasCore P L Γ}
    {σ : ProgramPureProfile (P := P) (L := L) p}
    {env : VEnv (Player := P) L Γ}
    (hag : PureProfile.AgreesOnProgram (P := P) (L := L) π p σ) :
    outcomeDist π.toOperationalProfile p env = outcomeDistPure p σ env := by
  induction p with
  | ret u =>
      rfl
  | letExpr x e k ih =>
      simpa [outcomeDist, outcomeDistPure] using ih hag
  | sample x τ m D' k ih =>
      simp only [outcomeDist, outcomeDistPure, ih hag]
  | commit x who R k ih =>
      rcases hag with ⟨hhead, htail⟩
      simp only [outcomeDist, outcomeDistPure]
      rw [show
          π.toOperationalProfile.commit who x R (VEnv.eraseEnv env) =
            FDist.pure
              ((ProgramPureStrategy.headKernel (P := P) (L := L) (σ who))
                (projectViewEnv (P := P) (L := L) who (VEnv.eraseEnv env))) by
            simp [PureProfile.toOperationalProfile, PureProfile.toBehavioral,
              BehavioralProfile.toOperationalProfile, BehavioralStrategy.toOperationalKernel,
              PureStrategy.toBehavioral, hhead]]
      simpa [FDist.pure_bind] using ih htail
  | reveal y who x hx k ih =>
      simpa [outcomeDist, outcomeDistPure] using ih hag

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

/-- If a global pure Vegas profile agrees with a fixed-program pure profile on
`p`, then the ordinary behavioral `toKernelGame` and the fixed-program pure
`toStrategicKernelGame` have the same outcome kernel on these profiles. -/
theorem toKernelGame_outcomeKernel_eq_toStrategicKernelGame_of_agrees
    (π : PureProfile (P := P) (L := L))
    {Γ : VCtx P L} (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p)
    (σ : ProgramPureProfile (P := P) (L := L) p)
    (hag : PureProfile.AgreesOnProgram (P := P) (L := L) π p σ) :
    (toKernelGame p env hd).outcomeKernel π.toBehavioral =
      (toStrategicKernelGame p env hd).outcomeKernel σ := by
  have hout :
      outcomeDist π.toBehavioral.toOperationalProfile p env = outcomeDistPure p σ env := by
    simpa [PureProfile.toOperationalProfile] using
      outcomeDist_eq_outcomeDistPure_of_agrees (P := P) (L := L) π hag
  rw [toKernelGame_outcomeKernel, toStrategicKernelGame_outcomeKernel]
  simp [hout]

/-- Under agreement on the commit sites of `p`, the ordinary behavioral Vegas
kernel game and the fixed-program pure strategic form assign the same expected
utility. -/
theorem toKernelGame_eu_eq_toStrategicKernelGame_eu_of_agrees
    (π : PureProfile (P := P) (L := L))
    {Γ : VCtx P L} (p : VegasCore P L Γ)
    (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p)
    (σ : ProgramPureProfile (P := P) (L := L) p)
    (hag : PureProfile.AgreesOnProgram (P := P) (L := L) π p σ)
    (who : P) :
    (toKernelGame p env hd).eu π.toBehavioral who =
      (toStrategicKernelGame p env hd).eu σ who := by
  have hout :
      outcomeDist π.toBehavioral.toOperationalProfile p env = outcomeDistPure p σ env := by
    simpa [PureProfile.toOperationalProfile] using
      outcomeDist_eq_outcomeDistPure_of_agrees (P := P) (L := L) π hag
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

/-- If every player has a dominant pure strategy for the fixed program,
then the program has a pure Nash equilibrium. -/
theorem pure_nash_of_all_have_dominant
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p)
    (h : ∀ who, ∃ s : ProgramPureStrategy (P := P) (L := L) who p,
      IsPureDominant p env hd who s) :
    ∃ σ : ProgramPureProfile (P := P) (L := L) p, IsPureNash p env hd σ := by
  simpa [IsPureDominant, IsPureNash] using
    (GameTheory.KernelGame.nash_of_all_have_dominant
      (G := toStrategicKernelGame p env hd) h)

/-- Pure Nash equilibrium is exactly everyone playing a pure best response. -/
theorem isPureNash_iff_bestResponse
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p)
    (σ : ProgramPureProfile (P := P) (L := L) p) :
    IsPureNash p env hd σ ↔
      ∀ who, IsPureBestResponse p env hd who σ (σ who) := by
  simpa [IsPureNash, IsPureBestResponse] using
    (GameTheory.KernelGame.isNash_iff_bestResponse
      (G := toStrategicKernelGame p env hd) σ)

/-- Any pure dominant strategy is a pure best response against every profile. -/
theorem pure_dominant_isBestResponse
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p)
    (who : P)
    (s : ProgramPureStrategy (P := P) (L := L) who p)
    (σ : ProgramPureProfile (P := P) (L := L) p)
    (hdom : IsPureDominant p env hd who s) :
    IsPureBestResponse p env hd who σ s := by
  simpa [IsPureDominant, IsPureBestResponse] using
    (GameTheory.KernelGame.dominant_isBestResponse
      (G := toStrategicKernelGame p env hd) who s σ hdom)

/-- In the fixed-program pure strategic form, pure Nash is equivalent to there
being no strictly improving pure unilateral deviation. -/
theorem isPureNash_iff_no_improving
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p)
    {σ : ProgramPureProfile (P := P) (L := L) p} :
    IsPureNash p env hd σ ↔
      ¬ ∃ (who : P) (s' : ProgramPureStrategy (P := P) (L := L) who p),
        (toStrategicKernelGame p env hd).eu (Function.update σ who s') who >
          (toStrategicKernelGame p env hd).eu σ who := by
  simpa [IsPureNash] using
    (GameTheory.KernelGame.isNash_iff_no_improving
      (G := toStrategicKernelGame p env hd) (σ := σ))

/-- Replacing a pure Nash action with another pure best response preserves the
deviator's expected utility. -/
theorem pure_nash_update_bestResponse_eu_eq
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p)
    {σ : ProgramPureProfile (P := P) (L := L) p}
    (hN : IsPureNash p env hd σ)
    {who : P} {s' : ProgramPureStrategy (P := P) (L := L) who p}
    (hbr : IsPureBestResponse p env hd who σ s') :
    (toStrategicKernelGame p env hd).eu (Function.update σ who s') who =
      (toStrategicKernelGame p env hd).eu σ who := by
  simpa [IsPureNash, IsPureBestResponse] using
    (GameTheory.KernelGame.isNash_update_bestResponse
      (G := toStrategicKernelGame p env hd) hN hbr)

/-- Every exact potential on the fixed-program pure strategic form is also an
ordinal potential. -/
theorem IsPureExactPotential.toOrdinal
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p)
    {Φ : ProgramPureProfile (P := P) (L := L) p → ℝ}
    (hΦ : IsPureExactPotential p env hd Φ) :
    IsPureOrdinalPotential p env hd Φ := by
  simpa [IsPureExactPotential, IsPureOrdinalPotential] using
    (GameTheory.KernelGame.IsExactPotential.toOrdinal
      (G := toStrategicKernelGame p env hd) hΦ)

/-- A global maximizer of an exact potential is a pure Nash equilibrium. -/
theorem IsPureExactPotential.nash_of_maximizer
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p)
    {Φ : ProgramPureProfile (P := P) (L := L) p → ℝ}
    (hΦ : IsPureExactPotential p env hd Φ)
    {σ : ProgramPureProfile (P := P) (L := L) p}
    (hmax : ∀ τ : ProgramPureProfile (P := P) (L := L) p, Φ σ ≥ Φ τ) :
    IsPureNash p env hd σ := by
  simpa [IsPureExactPotential, IsPureNash] using
    (GameTheory.KernelGame.IsExactPotential.nash_of_maximizer
      (G := toStrategicKernelGame p env hd) hΦ hmax)

/-- A global maximizer of an ordinal potential is a pure Nash equilibrium. -/
theorem IsPureOrdinalPotential.nash_of_maximizer
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p)
    {Φ : ProgramPureProfile (P := P) (L := L) p → ℝ}
    (hΦ : IsPureOrdinalPotential p env hd Φ)
    {σ : ProgramPureProfile (P := P) (L := L) p}
    (hmax : ∀ τ : ProgramPureProfile (P := P) (L := L) p, Φ σ ≥ Φ τ) :
    IsPureNash p env hd σ := by
  simpa [IsPureOrdinalPotential, IsPureNash] using
    (GameTheory.KernelGame.IsOrdinalPotential.nash_of_maximizer
      (G := toStrategicKernelGame p env hd) hΦ hmax)

/-- A strict global maximizer of an exact potential is a pure strict Nash
equilibrium. -/
theorem IsPureExactPotential.strictNash_of_strict_maximizer
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p)
    {Φ : ProgramPureProfile (P := P) (L := L) p → ℝ}
    (hΦ : IsPureExactPotential p env hd Φ)
    {σ : ProgramPureProfile (P := P) (L := L) p}
    (hmax : ∀ τ : ProgramPureProfile (P := P) (L := L) p, τ ≠ σ → Φ σ > Φ τ) :
    IsPureStrictNash p env hd σ := by
  intro who s' hs'
  have hpot := hΦ who σ s'
  have hne : Function.update σ who s' ≠ σ := by
    intro h
    apply hs'
    have := congr_fun h who
    simpa [Function.update] using this
  have hlt := hmax _ hne
  linarith

/-- In the fixed-program pure strategic form, exact-potential Nash equilibria
are exactly the local maximizers of the potential. -/
theorem IsPureExactPotential.isNash_iff_local_maximizer
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p)
    {Φ : ProgramPureProfile (P := P) (L := L) p → ℝ}
    (hΦ : IsPureExactPotential p env hd Φ)
    {σ : ProgramPureProfile (P := P) (L := L) p} :
    IsPureNash p env hd σ ↔
      ∀ who (s' : ProgramPureStrategy (P := P) (L := L) who p),
        Φ σ ≥ Φ (Function.update σ who s') := by
  constructor
  · intro hN who s'
    have hpot := hΦ who σ s'
    have hge := hN who s'
    linarith
  · intro hmax who s'
    have hpot := hΦ who σ s'
    have hge := hmax who s'
    linarith

/-- In the fixed-program pure strategic form, ordinal-potential Nash
equilibria are exactly the local maximizers of the potential. -/
theorem IsPureOrdinalPotential.isNash_iff_local_maximizer
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p)
    {Φ : ProgramPureProfile (P := P) (L := L) p → ℝ}
    (hΦ : IsPureOrdinalPotential p env hd Φ)
    {σ : ProgramPureProfile (P := P) (L := L) p} :
    IsPureNash p env hd σ ↔
      ∀ who (s' : ProgramPureStrategy (P := P) (L := L) who p),
        Φ σ ≥ Φ (Function.update σ who s') := by
  simpa [IsPureOrdinalPotential, IsPureNash] using
    (GameTheory.KernelGame.IsOrdinalPotential.isNash_iff_local_maximizer
      (G := toStrategicKernelGame p env hd) hΦ
      (σ := σ))

/-- An exact potential on the fixed-program pure strategic form guarantees a
pure Nash equilibrium, provided the pure profile space is nonempty. -/
theorem pure_exact_potential_nash_exists
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p)
    (LF : FiniteValuation L) [Finite P]
    {Φ : ProgramPureProfile (P := P) (L := L) p → ℝ}
    (hΦ : IsPureExactPotential p env hd Φ)
    [Nonempty (ProgramPureProfile (P := P) (L := L) p)] :
    ∃ σ : ProgramPureProfile (P := P) (L := L) p, IsPureNash p env hd σ := by
  let _ : Fintype P := Fintype.ofFinite P
  let _ : Fintype (ProgramPureProfile (P := P) (L := L) p) :=
    ProgramPureProfile.instFintype (P := P) (L := L) LF p
  let _ : Fintype ((toStrategicKernelGame p env hd).Profile) :=
    ProgramPureProfile.instFintype (P := P) (L := L) LF p
  let _ : Nonempty ((toStrategicKernelGame p env hd).Profile) :=
    inferInstanceAs (Nonempty (ProgramPureProfile (P := P) (L := L) p))
  simpa [IsPureExactPotential, IsPureNash] using
    (GameTheory.KernelGame.exact_potential_nash_exists
      (G := toStrategicKernelGame p env hd) (Φ := Φ) hΦ)

end Vegas
