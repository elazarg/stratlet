import Vegas.MAID.DefsV
import Vegas.PureStrategic
import GameTheory.Languages.MAID.SOS
import GameTheory.Languages.MAID.FrontierEval

/-!
# Bridge Theorems for VegasMAID

Reverse bridge: any MAID policy reflects to a Vegas behavioral profile with same outcome.
Pure bridge: compiled pure profile → MAID evaluation = Vegas pure evaluation.
-/

namespace Vegas

open MAID

variable {Player : Type} [DecidableEq Player] {L : IExpr} {B : MAIDBackend Player L}

/-! ## PMF fold bridge -/

/-- **PMF fold bridge**: the MAID evaluation folded through `evalStep` and
mapped through outcome extraction equals `nativeOutcomeDistPMFV` applied
to the reflected policy.

This is the core inductive proof, by structural induction on `p : VegasCore`.
With VegasMAID's `obsParents = parents`, the commit case's obs-config
injectivity problem is eliminated. -/
private theorem pmfFoldBridgeV
    (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (hfresh : FreshBindings p)
    (ρ : RawNodeEnv L → VEnv (Player := Player) L Γ)
    (st₀ : MAIDCompileState Player L B)
    (hvars : st₀.VarsSubCtx Γ)
    (hρ_deps : ∀ j, j ∉ (st₀.ctxDeps Γ : Finset Nat) → InsensitiveTo ρ j)
    (hρ_var : EnvRespectsLookupDeps st₀ ρ)
    (hρ_readers : ViewDeterminesRaw st₀ Γ ρ)
    (hρ_readval : EnvReadValAtDeps st₀ Γ ρ)
    (hnodup : (Γ.map Prod.fst).Nodup) :
    letI := B.fintypePlayer
    let st := MAIDCompileState.ofProg B p hl hd ρ st₀
    let S := st.toStruct
    let sem := MAIDCompileState.toSem st
    let extract : TAssign (fp := B.fintypePlayer) S → Outcome Player :=
      fun a => extractOutcomeAux B p ρ st₀.nextId (rawOfTAssign st a)
    ∀ (pol : Policy (fp := B.fintypePlayer) S)
      (a₀ : TAssign (fp := B.fintypePlayer) S),
      PMF.map extract
        ((List.finRange st.nextId).drop st₀.nextId |>.foldl
          (evalStep S sem pol) (PMF.pure a₀)) =
      nativeOutcomeDistPMFV B p hd
        (reflectPolicyAuxV B p hl hd ρ st₀ pol)
        ρ st₀.nextId (rawOfTAssign st a₀) := by
  sorry

/-! ## Reverse bridge -/

/-- **Reverse bridge**: any MAID policy can be reflected to a Vegas PMF behavioral
profile that produces the same outcome distribution via `frontierEval`. -/
theorem vegasMAID_reverse_bridge
    (B : MAIDBackend Player L) {Γ : VCtx Player L}
    (p : VegasCore Player L Γ) (env : VEnv (Player := Player) L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (hfresh : FreshBindings p)
    (hpub : ∀ y who b, VHasVar (L := L) Γ y (.hidden who b) → False)
    (pol : Policy (fp := B.fintypePlayer) (compiledStruct B p env hl hd hfresh hpub)) :
    let S := compiledStruct B p env hl hd hfresh hpub
    let sem := vegasMAIDSem B p env hl hd hfresh hpub
    let σ := reflectPolicyV B p env hl hd hfresh hpub pol
    PMF.map (extractOutcomeV B p env hl hd hfresh hpub)
      (frontierEval (fp := B.fintypePlayer) S sem pol) =
    outcomeDistBehavioralPMF p hd σ env := by
  intro S sem σ
  letI := B.fintypePlayer
  -- Step 1: frontierEval = evalAssignDist
  rw [MAID.frontierEval_eq_evalAssignDist]
  -- Step 2: evalAssignDist = evalFold along natural order
  let st := compiledState B p env hl hd
  have hnat := compiled_naturalOrderV st
  rw [MAID.evalAssignDist_eq_evalFold S sem pol hnat.toTopologicalOrder]
  -- Step 3: Apply fold bridge
  have hbridge := pmfFoldBridgeV B p hl hd hfresh (fun _ => env) .empty
    (fun _ h => by simp [MAIDCompileState.empty] at h)
    (fun j hj => by intro raw tv; rfl)
    (envRespectsLookupDeps_const (B := B) .empty env)
    (fun who raw₁ raw₂ _ _ _ _ i hi => by
      simp only [MAIDCompileState.viewDeps, MAIDCompileState.empty] at hi
      exact absurd hi (by
        have := MAIDCompileState.depsOfVars_lt MAIDCompileState.empty
          ((viewVCtx who _).map Prod.fst) i hi
        simp [MAIDCompileState.empty] at this))
    (fun x who' bt hx hne => absurd hne (by
      simp [MAIDCompileState.empty, MAIDCompileState.lookupDeps,
        MAIDCompileState.lookupDepsAux, Finset.not_nonempty_empty]))
    sorry -- hnodup: (Γ.map Prod.fst).Nodup — need FreshBindings or WF
    pol (defaultAssign S)
  rw [show (MAIDCompileState.empty (B := B) (Player := Player) (L := L)).nextId = 0 from rfl,
    List.drop_zero] at hbridge
  -- Step 4: Connect fold → nativeOutcomeDistPMFV → outcomeDistBehavioralPMF
  have hnative := nativeOutcomeDistPMFV_eq B p hd
    (reflectPolicyAuxV B p hl hd (fun _ => env) .empty pol)
    (fun _ => env) 0
    (fun nid _ raw tv => rfl)
  -- evalFold = foldl along the natural order
  have hfold : evalFold S sem pol hnat.toTopologicalOrder =
      (List.finRange st.nextId).foldl (evalStep S sem pol)
        (PMF.pure (defaultAssign S)) := by
    rfl
  rw [hfold]
  exact hbridge.trans (hnative _)

/-! ## Pure bridge -/

/-- **Pure bridge**: compiling a Vegas pure profile to a MAID pure policy and
evaluating gives the same outcome distribution as Vegas pure evaluation. -/
theorem vegasMAID_pure_bridge
    (B : MAIDBackend Player L) {Γ : VCtx Player L}
    (p : VegasCore Player L Γ) (env : VEnv (Player := Player) L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (hfresh : FreshBindings p)
    (hpub : ∀ y who b, VHasVar (L := L) Γ y (.hidden who b) → False)
    (π : ProgramPureProfile (P := Player) (L := L) p) :
    let S := compiledStruct B p env hl hd hfresh hpub
    let sem := vegasMAIDSem B p env hl hd hfresh hpub
    PMF.map (extractOutcomeV B p env hl hd hfresh hpub)
      (frontierEval (fp := B.fintypePlayer) S sem
        (pureToPolicy (fp := B.fintypePlayer)
          (compilePureProfileV B p env hl hd hfresh hpub π))) =
    (outcomeDistPure p π env).toPMF (outcomeDistPure_totalWeight_eq_one hd) := by
  sorry

end Vegas
