import Math.PMFProduct
import GameTheory.Languages.MAID.Kuhn
import Vegas.MAID.PerfectRecall
import Vegas.MAID.Bridge

/-!
# Vegas Kuhn Theorem via VegasMAID

The Vegas Kuhn theorem: for a Vegas program compiled through VegasMAID,
every product mixed strategy over pure Vegas strategies is outcome-equivalent
to some PMF-valued behavioral profile.

## Proof outline (via VegasMAID)

1. Compile to VegasMAID: `compiledStruct B p env ...`
2. Perfect recall: `compiledStruct_perfectRecallV` (from factored observation)
3. Apply MAID `kuhn_mixed_to_behavioral` → behavioral MAID policy `pol`
4. Reverse bridge: `reflectPolicyV` → Vegas behavioral `σ`
5. Pure bridge: connect RHS through `compilePureProfileV`
6. Chain equalities
-/

namespace Vegas

open MAID Math.PMFProduct

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-! ## Auxiliary: compile pure strategies to MAID -/

private noncomputable def defaultPureStrategy
    (B : MAIDBackend Player L) :
    {Γ : VCtx Player L} → (p : VegasCore Player L Γ) →
    (i : Player) → ProgramPureStrategy i p
  | _, .ret _, _ => PUnit.unit
  | _, .letExpr _ _ k, i => defaultPureStrategy B k i
  | _, .sample _ _ k, i => defaultPureStrategy B k i
  | Γ, .commit (b := b) _ owner _ k, i => by
    by_cases h : owner = i
    · subst h
      simp only [ProgramPureStrategy]
      exact ⟨fun _ =>
        MAIDValuation.defaultVal L B.toMAIDValuation b,
        defaultPureStrategy B k owner⟩
    · simpa [ProgramPureStrategy, h] using
        defaultPureStrategy B k i
  | _, .reveal _ _ _ _ k, i => defaultPureStrategy B k i

/-- Compile a Vegas per-player pure strategy to a MAID per-player
pure strategy. -/
noncomputable def compilePureStrategyV
    (B : MAIDBackend Player L) {Γ : VCtx Player L}
    (p : VegasCore Player L Γ) (env : VEnv L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (hfresh : FreshBindings p)
    (hpub : ∀ y who b, VHasVar Γ y (.hidden who b) → False)
    (who : Player)
    (s : ProgramPureStrategy who p) :
    PureStrategy (fp := B.fintypePlayer)
      (compiledStruct B p env hl hd hfresh hpub) who :=
  haveI := B.fintypePlayer
  compilePureProfileV B p env hl hd hfresh hpub
    (fun i => if h : i = who then h ▸ s
      else defaultPureStrategy B p i) who

/-- The compiled MAID pure policy from a full Vegas pure profile decomposes
into per-player compiled strategies. -/
theorem compilePureProfileV_eq_mk
    (B : MAIDBackend Player L) {Γ : VCtx Player L}
    (p : VegasCore Player L Γ) (env : VEnv L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (hfresh : FreshBindings p)
    (hpub : ∀ y who b, VHasVar Γ y (.hidden who b) → False)
    (π : ProgramPureProfile p) :
    compilePureProfileV B p env hl hd hfresh hpub π =
      fun who => compilePureStrategyV B p env hl hd hfresh hpub who (π who) := by
  funext who
  simp only [compilePureStrategyV]
  exact compilePureProfileV_player_indep B p env hl hd hfresh hpub
    π (fun i => if h : i = who then h ▸ π who else defaultPureStrategy B p i)
    who (by simp)

/-! ## RHS connection: MAID mixed = Vegas mixed -/

/-- The RHS of MAID Kuhn, mapped through `extractOutcomeV`, equals the
Vegas mixed outcome distribution when the MAID pure strategies correspond
to compiled Vegas pure strategies. -/
theorem maid_kuhn_rhs_eq_vegas_mixedV
    (B : MAIDBackend Player L)
    (LF : FiniteValuation L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ) (env : VEnv L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (hfresh : FreshBindings p)
    (hpub : ∀ y who b, VHasVar Γ y (.hidden who b) → False)
    (hnodup : (Γ.map Prod.fst).Nodup)
    (μ : ∀ who, PMF (ProgramPureStrategy who p)) :
    let _ : ∀ who, Fintype (ProgramPureStrategy who p) :=
      fun who => ProgramPureStrategy.instFintype LF who p
    let S := compiledStruct B p env hl hd hfresh hpub
    let sem := vegasMAIDSem B p env hl hd hfresh hpub
    let extract := extractOutcomeV B p env hl hd hfresh hpub
    let μ_maid : ∀ who, PMF (PureStrategy (fp := B.fintypePlayer) S who) :=
      fun who => (μ who).map (compilePureStrategyV B p env hl hd hfresh hpub who)
    (@pmfPi _ _ _ B.fintypePlayer _ μ_maid).bind (fun π_maid =>
      PMF.map extract (frontierEval (fp := B.fintypePlayer) S sem
        (pureToPolicy (fp := B.fintypePlayer) π_maid))) =
    (@pmfPi _ _ _ B.fintypePlayer _ μ).bind (fun π =>
      (outcomeDistPure p π env).toPMF (outcomeDistPure_totalWeight_eq_one hd)) := by
  intro _instFin S sem extract μ_maid
  letI := B.fintypePlayer
  -- Key: pmfPi of mapped marginals commutes with bind
  have hpi : (pmfPi μ_maid).bind (fun π_maid =>
      PMF.map extract (frontierEval S sem (pureToPolicy π_maid))) =
    (pmfPi μ).bind (fun π =>
      PMF.map extract (frontierEval S sem (pureToPolicy
        (fun who => compilePureStrategyV B p env hl hd hfresh hpub who (π who))))) := by
    exact pmfPi_map_bind μ (fun who => compilePureStrategyV B p env hl hd hfresh hpub who) _
  rw [hpi]; congr 1; funext π
  -- For each fixed π, relate compiled strategy to compilePureProfileV
  rw [← compilePureProfileV_eq_mk B p env hl hd hfresh hpub π]
  exact vegasMAID_pure_bridge B p env hl hd hfresh hpub hnodup π

/-! ## Main theorem -/

/-- **Vegas Kuhn theorem (mixed → behavioral) via VegasMAID**: under the
preconditions that the program is legal, has normalized distributions, has
fresh bindings, and has no hidden variables in scope, every product mixed
strategy over pure Vegas strategies is outcome-equivalent to some PMF-valued
behavioral profile.

This version uses the VegasMAID factored-observation compilation, where
`obsParents = parents` eliminates the obs-config injectivity problem. -/
theorem vegas_kuhn_mixed_to_behavioralV
    (B : MAIDBackend Player L)
    (LF : FiniteValuation L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ) (env : VEnv L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (hfresh : FreshBindings p)
    (hpub : ∀ y who b, VHasVar Γ y (.hidden who b) → False)
    (hnodup : (Γ.map Prod.fst).Nodup)
    (μ : ∀ who, PMF (ProgramPureStrategy who p)) :
    let _ : ∀ who, Fintype (ProgramPureStrategy who p) :=
      fun who => ProgramPureStrategy.instFintype LF who p
    ∃ σ : ProgramBehavioralProfilePMF p,
      outcomeDistBehavioralPMF p hd σ env =
        (@pmfPi _ _ _ B.fintypePlayer _ μ).bind (fun π =>
          (outcomeDistPure p π env).toPMF
            (outcomeDistPure_totalWeight_eq_one hd)) := by
  intro _instFinStrat
  -- Step 1: Set up the compiled VegasMAID
  let S := compiledStruct B p env hl hd hfresh hpub
  let sem := vegasMAIDSem B p env hl hd hfresh hpub
  let extract := extractOutcomeV B p env hl hd hfresh hpub
  -- Step 2: Perfect recall from factored observation
  have hPR : S.PerfectRecall (fp := B.fintypePlayer) :=
    compiledStruct_perfectRecallV B p env hl hd hfresh hpub
  -- Step 3: Build MAID mixed strategy from Vegas mixed strategy
  let μ_maid : ∀ who, PMF (PureStrategy (fp := B.fintypePlayer) S who) :=
    fun who => (μ who).map (compilePureStrategyV B p env hl hd hfresh hpub who)
  -- Step 4: Apply MAID Kuhn (mixed → behavioral)
  letI := B.fintypePlayer
  obtain ⟨pol, hpol⟩ :=
    GameTheory.Languages.MAID.kuhn_mixed_to_behavioral S sem hPR μ_maid
  -- Step 5: Reflect MAID policy to Vegas behavioral profile
  let σ := reflectPolicyV B p env hl hd hfresh hpub pol
  use σ
  -- Step 6: Chain the bridges
  -- Goal: outcomeDistBehavioralPMF p hd σ env = (pmfPi μ).bind (fun π => ...)
  -- From reverse bridge:
  --   PMF.map extract (frontierEval S sem pol) = outcomeDistBehavioralPMF p hd σ env
  have hrev := vegasMAID_reverse_bridge B p env hl hd hfresh hpub hnodup pol
  -- From MAID Kuhn: frontierEval S sem pol = (pmfPi μ_maid).bind (...)
  -- So: PMF.map extract (frontierEval S sem pol) =
  --     (pmfPi μ_maid).bind (fun π_maid =>
  --       PMF.map extract (frontierEval S sem (pureToPolicy π_maid)))
  -- From maid_kuhn_rhs_eq_vegas_mixedV:
  --   (pmfPi μ_maid).bind (...) = (pmfPi μ).bind (fun π => (outcomeDistPure p π env).toPMF ...)
  have hrhs := maid_kuhn_rhs_eq_vegas_mixedV B LF p env hl hd hfresh hpub hnodup μ
  -- Chain: σ's behavioral dist = extract ∘ frontierEval = extract ∘ MAID-mixed = Vegas-mixed
  rw [← hrev]
  rw [hpol]
  -- Goal should now be about PMF.map extract ((pmfPi μ_maid).bind ...)
  -- = (pmfPi μ).bind (fun π => (outcomeDistPure p π env).toPMF ...)
  rw [PMF.map_bind]
  exact hrhs

end Vegas
