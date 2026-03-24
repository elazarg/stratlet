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
  letI := B.fintypePlayer
  dsimp only
  induction p generalizing st₀ with
  | ret u =>
    rename_i Γ'
    intro pol a₀
    let st := MAIDCompileState.ofProg B (.ret u) hl hd ρ st₀
    let extract := fun a => extractOutcomeAux B (.ret u) ρ st₀.nextId (rawOfTAssign st a)
    -- All new nodes are utility; evalStep at utility preserves PMF.map extract
    have hutility : ∀ nd ∈ (List.finRange st.nextId).drop st₀.nextId,
        ∃ who, (st.descAt nd).kind = .utility who :=
      fun nd hnd => by
        have hge : st₀.nextId ≤ nd.val := by
          rcases List.mem_iff_getElem.mp hnd with ⟨i, hi, hget⟩
          have := congrArg Fin.val hget; rw [List.getElem_drop] at this; simp at this; omega
        exact MAIDCompileState.addUtilityNodes_all_utility
          (st := st₀) (deps := st₀.ctxDeps Γ') (hdeps := st₀.depsOfVars_lt _)
          (ufn := fun who raw => ((evalPayoffs u (ρ raw)) who : ℝ))
          (players := Finset.univ.toList) (i := nd) hge
    have hstep : ∀ (nd : Fin st.nextId)
        (hwho : ∃ who, (st.descAt nd).kind = .utility who) (acc : PMF (TAssign st.toStruct)),
        PMF.map extract (evalStep st.toStruct (MAIDCompileState.toSem st) pol acc nd) =
        PMF.map extract acc := by
      intro nd hwho acc
      simp only [evalStep, PMF.map_bind]
      congr 1; funext a
      obtain ⟨w, hw⟩ := hwho
      have hkind : st.toStruct.kind nd = .utility w := by
        simp only [toStruct_kind]; exact hw
      conv_lhs => rw [show (fun a_1 => PMF.map extract (PMF.pure (updateAssign a nd a_1))) =
        (fun a_1 => PMF.pure (extract (updateAssign a nd a_1))) from
        funext fun v => PMF.pure_map extract (updateAssign a nd v)]
      simp only [nodeDist]
      split
      · rename_i hk; simp only [toStruct_kind] at hk; rw [hk] at hw; exact absurd hw (by simp)
      · rename_i p hk; simp only [toStruct_kind] at hk; rw [hk] at hw; exact absurd hw (by simp)
      · simp only [PMF.pure_bind, Function.comp]
        exact congrArg PMF.pure (congrArg (extractOutcomeAux B (.ret u) ρ st₀.nextId)
          (rawOfTAssign_updateAssign_utility st a nd _ ⟨w, hw⟩))
    have hfold : ∀ (nodes : List (Fin st.nextId))
        (hnodes : ∀ nd ∈ nodes, ∃ who, (st.descAt nd).kind = .utility who)
        (acc : PMF (TAssign st.toStruct)),
        PMF.map extract (List.foldl (evalStep st.toStruct
          (MAIDCompileState.toSem st) pol) acc nodes) =
        PMF.map extract acc := by
      intro nodes hnodes acc
      induction nodes generalizing acc with
      | nil => rfl
      | cons nd rest ih_nodes =>
        simp only [List.foldl_cons]
        rw [ih_nodes (fun nd' hnd' => hnodes nd' (List.mem_cons.mpr (.inr hnd')))
          (evalStep st.toStruct (MAIDCompileState.toSem st) pol acc nd)]
        exact hstep nd (hnodes nd (List.mem_cons.mpr (.inl rfl))) acc
    rw [hfold _ hutility, PMF.pure_map]
    simp [extract, extractOutcomeAux, nativeOutcomeDistPMFV]; rfl
  | letExpr x e k ih =>
    rename_i Γ' b
    intro pol a₀
    have hxΓ : Fresh x Γ' := hfresh.1
    have hxvars : x ∉ st₀.vars.map Prod.fst := fun hxmem => hxΓ (hvars x hxmem)
    let ρ' : RawNodeEnv L → VEnv (Player := Player) L ((x, .pub b) :: Γ') :=
      fun raw => VEnv.cons (L := L) (x := x) (τ := .pub b)
        (L.eval e (VEnv.erasePubEnv (ρ raw))) (ρ raw)
    let st₁ := st₀.addVar x (.pub b) (st₀.pubCtxDeps Γ') (st₀.depsOfVars_lt _)
    have hρ'_deps : ∀ j, j ∉ st₁.ctxDeps ((x, .pub b) :: Γ') → InsensitiveTo ρ' j := by
      intro j hj raw tv
      rw [st₀.ctxDeps_letExpr_step x hxΓ hxvars] at hj
      have hρj := hρ_deps j hj raw tv
      simp only [ρ', hρj]
    have hρ'_var : EnvRespectsLookupDeps st₁ ρ' := by
      intro y τ hy j hj raw tv
      cases hy with
      | here =>
          have hj' : j ∉ st₀.pubCtxDeps Γ' := by
            simpa [st₁, st₀.lookupDeps_addVar_eq_self_of_fresh x (.pub b)
              (st₀.pubCtxDeps Γ') (st₀.depsOfVars_lt _) hxvars] using hj
          exact Vegas.eval_pubExpr_insensitive_of_pubCtxDeps st₀ ρ hρ_var e j hj' raw tv
      | there hy' =>
          have hxy : y ≠ x := fun hEq => hxΓ (hEq.symm ▸ hy'.mem_map_fst)
          have hj' : j ∉ st₀.lookupDeps y := by
            simpa [st₁, st₀.lookupDeps_addVar_eq_of_ne x (.pub b)
              (st₀.pubCtxDeps Γ') (st₀.depsOfVars_lt _) hxy] using hj
          simpa [ρ', VEnv.get, VEnv.cons_get_there] using hρ_var hy' j hj' raw tv
    have hρ'_readers : ViewDeterminesRaw st₁ ((x, .pub b) :: Γ') ρ' := by
      intro who raw₁ raw₂ hout hnot_vd htyped hview i hi
      have hview_old := projectViewEnv_cons_eq
        (List.nodup_cons.mpr ⟨hxΓ, hnodup⟩) hview
      have hVD : st₁.viewDeps who ((x, .pub b) :: Γ') = st₀.viewDeps who Γ' := by
        unfold MAIDCompileState.viewDeps
        simp only [viewVCtx, canSee, ite_true, List.map_cons, MAIDCompileState.depsOfVars]
        rw [st₀.lookupDeps_addVar_eq_self_of_fresh x (.pub b) (st₀.pubCtxDeps Γ')
            (st₀.depsOfVars_lt _) hxvars,
          st₀.depsOfVars_addVar_eq_of_not_mem x (.pub b) _ _ _
            (fun hmem => hxΓ (viewVCtx_map_fst_sub hmem))]
        exact Finset.union_eq_right.mpr (st₀.depsOfVars_subset_of_subset _ _
          erasePubVCtx_map_fst_sub_viewVCtx)
      apply hρ_readers who raw₁ raw₂
      · intro j hj; exact hout j (by
          simp [st₁, MAIDCompileState.addVar] at hj ⊢; exact hj)
      · intro j hj hjlt
        exact hnot_vd j (fun hmem => hj (hVD ▸ hmem))
          (by simp [st₁, MAIDCompileState.addVar]; exact hjlt)
      · intro j hj hjlt
        exact htyped j (hVD ▸ hj) (by simp [st₁, MAIDCompileState.addVar]; exact hjlt)
      · exact hview_old
      · rwa [hVD] at hi
    exact ih hl hd hfresh.2 ρ' st₁
      (st₀.VarsSubCtx_letExpr_step hvars x hxΓ) hρ'_deps hρ'_var hρ'_readers
      (fun y who' bt hy hne_deps => by
        cases hy with
        | there hy' =>
          have hne : y ≠ x := fun h => hxΓ (h.symm ▸ hy'.mem_map_fst)
          have hne_deps' : (st₀.lookupDeps y).Nonempty := by
            rwa [show st₁.lookupDeps y = st₀.lookupDeps y from by
              simp [st₁, st₀.lookupDeps_addVar_eq_of_ne x (.pub b)
                (st₀.pubCtxDeps Γ') (st₀.depsOfVars_lt _) hne]] at hne_deps
          rcases hρ_readval y who' bt hy' hne_deps' with ⟨j, hjlt, hld, hdesc_j, hget⟩
          exact ⟨j, hjlt, by simp [st₁, st₀.lookupDeps_addVar_eq_of_ne x (.pub b)
            (st₀.pubCtxDeps Γ') (st₀.depsOfVars_lt _) hne, hld], hdesc_j,
            fun raw => by simpa [ρ', VEnv.get, VEnv.cons_get_there] using hget raw⟩)
      (List.nodup_cons.mpr ⟨hxΓ, hnodup⟩) pol a₀
  | sample x τ m D' k ih => sorry
  | commit x who_commit R k ih => sorry
  | reveal y who_r x_r hx k ih => sorry

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
