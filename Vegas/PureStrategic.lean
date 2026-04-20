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
  | _, .sample _ _ k => ProgramPureStrategy who k
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
  | _, .sample _ _ k => instFintype LF who k
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

/-! ## Guard-legality for pure strategies -/

/-- A per-commit pure-kernel legality predicate: at every erased
environment, the action chosen by the kernel (on `who`'s view of that
environment) satisfies the commit's guard. -/
def PureKernel.IsLegalAt
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    (κ : PureKernel (P := P) (L := L) who Γ b)
    (R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool) : Prop :=
  ∀ ρ : Env L.Val (eraseVCtx Γ),
    evalGuard (Player := P) (L := L) R
      (κ (projectViewEnv (P := P) (L := L) who ρ)) ρ = true

/-- A pure strategy is guard-legal when every kernel at every owned
commit site satisfies `IsLegalAt` for that commit's guard. -/
def ProgramPureStrategy.IsLegal : {who : P} →
    {Γ : VCtx P L} → (p : VegasCore P L Γ) →
    ProgramPureStrategy (P := P) (L := L) who p → Prop
  | _, _, .ret _, _ => True
  | who, _, .letExpr _ _ k, σ =>
      ProgramPureStrategy.IsLegal (who := who) k σ
  | who, _, .sample _ _ k, σ =>
      ProgramPureStrategy.IsLegal (who := who) k σ
  | who, _, .commit _x owner (b := b) R k, σ => by
      by_cases h : owner = who
      · let σ' : PureKernel (P := P) (L := L) owner _ b ×
                 ProgramPureStrategy (P := P) (L := L) owner k := by
          subst h
          simpa [ProgramPureStrategy] using σ
        exact σ'.1.IsLegalAt R
              ∧ ProgramPureStrategy.IsLegal (who := owner) k σ'.2
      · let σ' : ProgramPureStrategy (P := P) (L := L) who k := by
          simpa [ProgramPureStrategy, h] using σ
        exact ProgramPureStrategy.IsLegal (who := who) k σ'
  | who, _, .reveal _ _ _ _ k, σ =>
      ProgramPureStrategy.IsLegal (who := who) k σ

/-- A pure profile is legal when every player's strategy is legal. -/
def ProgramPureProfile.IsLegal {Γ : VCtx P L} {p : VegasCore P L Γ}
    (σ : ProgramPureProfile (P := P) (L := L) p) : Prop :=
  ∀ who, (σ who).IsLegal p

/-- Guard-legal pure strategies over a `WFProgram` bundle. -/
abbrev LegalProgramPureStrategy (g : WFProgram P L) (who : P) : Type :=
  { s : ProgramPureStrategy (P := P) (L := L) who g.prog //
    s.IsLegal g.prog }

/-- Guard-legal joint pure profile over a `WFProgram` bundle. -/
abbrev LegalProgramPureProfile (g : WFProgram P L) : Type :=
  ∀ who, LegalProgramPureStrategy g who

/-- Classical `Fintype` on the per-player guard-legal pure strategy
subtype. Requires `FiniteValuation L` (to enumerate strategies) and
uses `Classical.dec` for decidability of the legality predicate. -/
@[reducible] noncomputable def LegalProgramPureStrategy.instFintype
    (g : WFProgram P L) (LF : FiniteValuation L) (who : P) :
    Fintype (LegalProgramPureStrategy g who) := by
  classical
  let _ : Fintype (ProgramPureStrategy (P := P) (L := L) who g.prog) :=
    ProgramPureStrategy.instFintype (L := L) LF who g.prog
  exact Subtype.fintype _

/-- Classical `Fintype` on the joint guard-legal pure profile. The
profile is a `Pi` over players, each factor a legal-strategy
`Fintype`. -/
@[reducible] noncomputable def LegalProgramPureProfile.instFintype
    (g : WFProgram P L) (LF : FiniteValuation L) [Fintype P] :
    Fintype (LegalProgramPureProfile g) := by
  classical
  have h : ∀ who, Fintype (LegalProgramPureStrategy g who) := fun who =>
    LegalProgramPureStrategy.instFintype g LF who
  exact Pi.instFintype

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
  | _, .sample _ _ k, σ => toBehavioral k σ
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
  | _, .sample x D' k, σ, env =>
      FDist.bind
        (L.evalDist D' (VEnv.eraseSampleEnv env))
        (fun v =>
          outcomeDistPure k σ
            (VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _) v env))
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
  | sample x D' k ih =>
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
  | sample x D' k ih =>
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

/-- Lifting a legal pure profile through `toBehavioral` yields a legal
behavioral profile. At each commit site, the pure kernel's legality
gives `evalGuard R (κ view) ρ = true`; the behavioral kernel produced by
`ofPure κ` has singleton support `{κ view}`, so its support is contained
in the guard-admissible set. -/
theorem ProgramPureProfile.toBehavioral_IsLegal :
    {Γ : VCtx P L} → (p : VegasCore P L Γ) →
    (σ : ProgramPureProfile (P := P) (L := L) p) →
    σ.IsLegal →
    (ProgramPureProfile.toBehavioral (P := P) (L := L) p σ).IsLegal
  | _, .ret _, _, _ => fun _ => trivial
  | _, .letExpr _ _ k, σ, hσ =>
      toBehavioral_IsLegal k σ hσ
  | _, .sample _ _ k, σ, hσ =>
      toBehavioral_IsLegal k σ hσ
  | _, .reveal _ _ _ _ k, σ, hσ =>
      toBehavioral_IsLegal k σ hσ
  | _, .commit x who_c (b := b) R k, σ, hσ => by
      -- Legality of the tail profile, for recursive application.
      have htail : (ProgramPureProfile.tail (P := P) (L := L) σ).IsLegal := by
        intro j
        by_cases hj : who_c = j
        · subst hj
          have hσ_who : (σ who_c).IsLegal (.commit x who_c R k) := hσ who_c
          dsimp [ProgramPureStrategy.IsLegal] at hσ_who
          dsimp [ProgramPureProfile.tail]
          split at hσ_who
          · rename_i h
            -- `h : who_c = who_c`, so tail call reduces to `tailOwn`.
            split
            · rename_i h2
              exact hσ_who.2
            · exact absurd rfl ‹_›
          · exact absurd rfl ‹_›
        · have hσ_j : (σ j).IsLegal (.commit x who_c R k) := hσ j
          dsimp [ProgramPureStrategy.IsLegal] at hσ_j
          dsimp [ProgramPureProfile.tail]
          split at hσ_j
          · rename_i h
            exact absurd h hj
          · split
            · rename_i h2
              exact absurd h2 hj
            · exact hσ_j
      -- Legality for each individual player.
      intro i
      by_cases hi : who_c = i
      · -- Owner branch at the commit site.
        subst hi
        have hσ_who : (σ who_c).IsLegal (.commit x who_c R k) := hσ who_c
        dsimp [ProgramPureProfile.toBehavioral, ProgramPureStrategy.IsLegal,
          ProgramBehavioralStrategy.IsLegal] at hσ_who ⊢
        split at hσ_who
        · rename_i h_owner_eq
          split
          · rename_i h_owner_eq2
            refine ⟨?_, ?_⟩
            · intro ρ
              simp only [cast_cast, cast_eq, ProgramBehavioralKernel.run_ofPure,
                FDist.Supported_pure]
              exact hσ_who.1 ρ
            · have hrec := toBehavioral_IsLegal k _ htail who_c
              simpa using hrec
          · exact absurd rfl ‹_›
        · exact absurd rfl ‹_›
      · -- Non-owner branch.
        dsimp [ProgramPureProfile.toBehavioral, ProgramBehavioralStrategy.IsLegal]
        split
        · rename_i h_who_c_eq_i
          exact absurd h_who_c_eq_i hi
        · have hrec := toBehavioral_IsLegal k _ htail i
          simpa using hrec

/-- Lift a legal pure profile to a legal behavioral profile. -/
noncomputable def LegalProgramPureProfile.toBehavioral
    {g : WFProgram P L} (σ : LegalProgramPureProfile g) :
    LegalProgramBehavioralProfile g :=
  let rawPure : ProgramPureProfile g.prog := fun i => (σ i).val
  let rawPureLegal : ProgramPureProfile.IsLegal rawPure := fun i => (σ i).2
  let rawBeh : ProgramBehavioralProfile g.prog :=
    ProgramPureProfile.toBehavioral g.prog rawPure
  let rawBehLegal : ProgramBehavioralProfile.IsLegal rawBeh :=
    ProgramPureProfile.toBehavioral_IsLegal g.prog rawPure rawPureLegal
  fun i => ⟨rawBeh i, rawBehLegal i⟩

/-- Fixed-program pure strategic form of a Vegas program. -/
noncomputable def toStrategicKernelGame (g : WFProgram P L) : GameTheory.KernelGame P where
  Strategy := LegalProgramPureStrategy g
  Outcome := Outcome P
  utility := fun o i => (o i : ℝ)
  outcomeKernel := fun σ =>
    (outcomeDistPure g.prog (fun i => (σ i).val) g.env).toPMF
      (outcomeDistPure_totalWeight_eq_one
        (P := P) (L := L) (p := g.prog) (σ := fun i => (σ i).val)
        g.normalized)

@[simp] theorem toStrategicKernelGame_outcomeKernel
    (g : WFProgram P L)
    (σ : LegalProgramPureProfile g) :
    (toStrategicKernelGame g).outcomeKernel σ =
      (outcomeDistPure g.prog (fun i => (σ i).val) g.env).toPMF
        (outcomeDistPure_totalWeight_eq_one
          (P := P) (L := L) (p := g.prog) (σ := fun i => (σ i).val)
          g.normalized) := rfl

@[simp] theorem toStrategicKernelGame_Strategy (g : WFProgram P L) :
    (toStrategicKernelGame g).Strategy = LegalProgramPureStrategy g := rfl

/-- Expected utility in the fixed-program pure strategic form matches the Vegas
expected payoff computed from `outcomeDistPure`. -/
theorem toStrategicKernelGame_eu
    (g : WFProgram P L)
    (σ : LegalProgramPureProfile g) (who : P) :
    (toStrategicKernelGame g).eu σ who =
      (outcomeDistPure g.prog (fun i => (σ i).val) g.env).sum
        (fun o w => (w : ℝ) * (o who : ℝ)) := by
  let hnorm :=
    outcomeDistPure_totalWeight_eq_one
      (P := P) (L := L) (p := g.prog) (σ := fun i => (σ i).val)
      (env := g.env) g.normalized
  simpa [GameTheory.KernelGame.eu, toStrategicKernelGame, hnorm,
    NNRat.toNNReal_coe_real] using
    (FDist.expect_toPMF_eq_sum
      (d := outcomeDistPure g.prog (fun i => (σ i).val) g.env)
      (h := hnorm)
      (f := fun o => (o who : ℝ)))

/-- The legal behavioral lift of a legal pure profile has the same outcome
kernel as the fixed-program pure strategic form. -/
theorem toKernelGame_outcomeKernel_eq_toStrategicKernelGame_toBehavioral
    (g : WFProgram P L)
    (σ : LegalProgramPureProfile g) :
    (toKernelGame g).outcomeKernel
        (LegalProgramPureProfile.toBehavioral σ) =
      (toStrategicKernelGame g).outcomeKernel σ := by
  have heq :
      outcomeDistBehavioral g.prog
          (fun i => ((LegalProgramPureProfile.toBehavioral (g := g) σ) i).val)
          g.env =
        outcomeDistPure g.prog (fun i => (σ i).val) g.env :=
    outcomeDistBehavioral_toBehavioral_eq_outcomeDistPure
      (P := P) (L := L) (p := g.prog)
      (σ := fun i => (σ i).val) (env := g.env)
  simp only [toKernelGame_outcomeKernel, toStrategicKernelGame_outcomeKernel, heq]

/-- The legal behavioral lift of a legal pure profile has the same expected
utility as the fixed-program pure strategic form. -/
theorem toKernelGame_eu_eq_toStrategicKernelGame_toBehavioral
    (g : WFProgram P L)
    (σ : LegalProgramPureProfile g) (who : P) :
    (toKernelGame g).eu
        (LegalProgramPureProfile.toBehavioral σ) who =
      (toStrategicKernelGame g).eu σ who := by
  have heq :
      outcomeDistBehavioral g.prog
          (fun i => ((LegalProgramPureProfile.toBehavioral (g := g) σ) i).val)
          g.env =
        outcomeDistPure g.prog (fun i => (σ i).val) g.env :=
    outcomeDistBehavioral_toBehavioral_eq_outcomeDistPure
      (P := P) (L := L) (p := g.prog)
      (σ := fun i => (σ i).val) (env := g.env)
  rw [toKernelGame_eu, toStrategicKernelGame_eu, heq]

/-- Pure Nash equilibrium of the fixed-program Vegas strategic form. -/
def IsPureNash (g : WFProgram P L) (σ : LegalProgramPureProfile g) : Prop :=
  (toStrategicKernelGame g).IsNash σ

/-- Pure dominant strategy in the fixed-program Vegas strategic form. -/
def IsPureDominant (g : WFProgram P L)
    (who : P) (s : LegalProgramPureStrategy g who) : Prop :=
  (toStrategicKernelGame g).IsDominant who s

/-- Pure best response in the fixed-program Vegas strategic form. -/
def IsPureBestResponse (g : WFProgram P L)
    (who : P) (σ : LegalProgramPureProfile g)
    (s : LegalProgramPureStrategy g who) : Prop :=
  (toStrategicKernelGame g).IsBestResponse who σ s

/-- Pure strict Nash equilibrium of the fixed-program Vegas strategic form. -/
def IsPureStrictNash (g : WFProgram P L)
    (σ : LegalProgramPureProfile g) : Prop :=
  (toStrategicKernelGame g).IsStrictNash σ

/-- Exact potential for the fixed-program Vegas strategic form. -/
def IsPureExactPotential (g : WFProgram P L)
    (Φ : LegalProgramPureProfile g → ℝ) : Prop :=
  (toStrategicKernelGame g).IsExactPotential Φ

/-- Ordinal potential for the fixed-program Vegas strategic form. -/
def IsPureOrdinalPotential (g : WFProgram P L)
    (Φ : LegalProgramPureProfile g → ℝ) : Prop :=
  (toStrategicKernelGame g).IsOrdinalPotential Φ

end Vegas
