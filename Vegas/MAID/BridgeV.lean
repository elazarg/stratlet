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
  | sample x τ m D' k ih =>
    rename_i Γ'
    intro pol a₀
    have hxΓ : Fresh x Γ' := hfresh.1
    have hxvars : x ∉ st₀.vars.map Prod.fst := fun hxmem => hxΓ (hvars x hxmem)
    let deps := st₀.ctxDeps Γ'
    let id := st₀.nextId
    let cpdFDist : RawNodeEnv L → FDist (L.Val τ.base) := fun raw =>
      L.evalDist D' (VEnv.eraseDistEnv τ m (ρ raw))
    let cpdNorm : ∀ raw, FDist.totalWeight (cpdFDist raw) = 1 := fun raw => hd.1 _
    let nd : CompiledNode Player L B := .chance τ.base deps cpdFDist cpdNorm
    have hndeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st₀.nextId := by
      intro d hd'
      have hd'' : d ∈ deps := by
        simpa [CompiledNode.parents, CompiledNode.obsParents] using hd'
      exact st₀.depsOfVars_lt _ d hd''
    let stNode := (st₀.addNode nd hndeps).2
    let st₁ := stNode.addVar x τ ({id}) (by
      intro d hd'; have := Finset.mem_singleton.mp hd'; subst d
      exact Nat.lt_succ_self id)
    let ρ' : RawNodeEnv L → VEnv (Player := Player) L ((x, τ) :: Γ') :=
      fun raw => VEnv.cons (MAIDCompileState.readVal (B := B) raw τ.base id) (ρ raw)
    have hvars₁ : st₁.VarsSubCtx ((x, τ) :: Γ') := by
      simpa [st₁, stNode, nd, deps, id] using
        st₀.VarsSubCtx_addNode_addVar_singleton_step hvars nd hndeps x τ hxΓ
    have hctx₁ : st₁.ctxDeps ((x, τ) :: Γ') = {id} ∪ st₀.ctxDeps Γ' := by
      simpa [st₁, stNode, nd, deps, id] using
        st₀.ctxDeps_addNode_addVar_singleton_cons_eq_of_fresh nd hndeps x τ hxΓ hxvars
    have hρ'_deps : ∀ j, j ∉ st₁.ctxDeps ((x, τ) :: Γ') → InsensitiveTo ρ' j := by
      intro j hj raw tv
      have hjid : j ≠ id := by intro hEq; apply hj; simp [hctx₁, hEq]
      have hj' : j ∉ st₀.ctxDeps Γ' := by intro hmem; apply hj; simp [hctx₁, hmem]
      have hρj := hρ_deps j hj' raw tv
      exact VEnv.cons_ext (readVal_extend_ne raw j id tv τ.base hjid.symm) hρj
    have hρ'_var : EnvRespectsLookupDeps st₁ ρ' := by
      intro y σ hy j hj raw tv
      cases hy with
      | here =>
          have hlookup : st₁.lookupDeps x = ({id} : Finset Nat) := by
            simpa [st₁] using stNode.lookupDeps_addVar_eq_self_of_fresh x τ {id}
              (by intro d hd'; have := Finset.mem_singleton.mp hd'; subst d
                  exact Nat.lt_succ_self id)
              (by simpa [stNode, MAIDCompileState.addNode] using hxvars)
          have hjid : j ≠ id := by
            simpa [Finset.mem_singleton] using (show j ∉ ({id} : Finset Nat) by
              simpa [hlookup] using hj)
          simpa [ρ', VEnv.get, readVal_extend_ne, hjid] using
            (readVal_extend_ne (B := B) raw j id tv τ.base hjid.symm)
      | there hy' =>
          have hxy : y ≠ x := fun hEq => hxΓ (hEq.symm ▸ hy'.mem_map_fst)
          have hlookupVar : st₁.lookupDeps y = stNode.lookupDeps y := by
            simpa [st₁] using stNode.lookupDeps_addVar_eq_of_ne x τ {id}
              (by intro d hd'; have := Finset.mem_singleton.mp hd'; subst d
                  exact Nat.lt_succ_self id) hxy
          have hlookupNode : stNode.lookupDeps y = st₀.lookupDeps y := by
            simpa [stNode] using st₀.lookupDeps_addNode nd hndeps y
          have hj' : j ∉ st₀.lookupDeps y := by simpa [hlookupVar, hlookupNode] using hj
          simpa [ρ', VEnv.get, VEnv.cons_get_there] using hρ_var hy' j hj' raw tv
    let st := MAIDCompileState.ofProg B k hl hd.2 ρ' st₁
    have hid_lt : id < st.nextId :=
      Nat.lt_of_lt_of_le (by
        simp [st₁, stNode, id, MAIDCompileState.addVar, MAIDCompileState.addNode])
        (MAIDCompileState.ofProg_nextId_le B k hl hd.2 ρ' st₁)
    let nd0 : Fin st.nextId := ⟨id, hid_lt⟩
    have hdrop :
        (List.finRange st.nextId).drop id =
          nd0 :: (List.finRange st.nextId).drop st₁.nextId := by
      have hlen : id < (List.finRange st.nextId).length := by simpa using hid_lt
      rw [show st₁.nextId = id + 1 by
        simp [st₁, stNode, id, MAIDCompileState.addVar, MAIDCompileState.addNode]]
      rw [← List.cons_getElem_drop_succ (l := List.finRange st.nextId) (n := id) (h := hlen)]
      simp [nd0]
    have hdesc0 : st.descAt nd0 = nd := by
      have hdesc1 := MAIDCompileState.ofProg_descAt_old B k hl hd.2 ρ' st₁ id
        (by simp [st₁, stNode, id, MAIDCompileState.addVar, MAIDCompileState.addNode])
      rw [hdesc1]
      simpa [st₁, stNode] using st₀.addNode_descAt_new nd hndeps
    -- sorry'd: ρ at projCfg = ρ at rawOfTAssign (needs rawEnvOfCfg_proj_eq_select + eq_on_ctxDeps)
    have hρeq :
        ρ (st.rawEnvOfCfg (MAID.projCfg a₀ (st.toStruct.parents nd0))) =
          ρ (rawOfTAssign st a₀) := by sorry
    -- Peel off the chance node from the fold
    change PMF.map (fun a => extractOutcomeAux B (.sample x τ m D' k) ρ st₀.nextId (rawOfTAssign st a))
      (List.foldl (evalStep st.toStruct st.toSem pol) (PMF.pure a₀)
        ((List.finRange st.nextId).drop id)) =
      nativeOutcomeDistPMFV B (.sample x τ m D' k) hd
        (reflectPolicyAuxV B (.sample x τ m D' k) hl hd ρ st₀ pol) ρ
        id (rawOfTAssign st a₀)
    rw [hdrop, List.foldl_cons]
    simp only [nativeOutcomeDistPMFV, reflectPolicyAuxV]
    simp only [evalStep, PMF.pure_bind]
    rw [foldl_evalStep_bind_left, PMF.map_bind]
    have hst₁_id : st₁.nextId = id + 1 := by
      simp [st₁, stNode, id, MAIDCompileState.addVar, MAIDCompileState.addNode]
    -- Apply IH to rewrite inner fold for each v
    have hρ'_readers : ViewDeterminesRaw st₁ ((x, τ) :: Γ') ρ' := by sorry
    have hρ'_readval : EnvReadValAtDeps st₁ ((x, τ) :: Γ') ρ' := by sorry
    have hinner : ∀ v, PMF.map (fun a => extractOutcomeAux B (.sample x τ m D' k) ρ
          st₀.nextId (rawOfTAssign st a))
        (List.foldl (evalStep st.toStruct st.toSem pol)
          (PMF.pure (updateAssign a₀ nd0 v))
          ((List.finRange st.nextId).drop st₁.nextId)) =
        nativeOutcomeDistPMFV B k hd.2 (reflectPolicyAuxV B k hl hd.2 ρ' st₁ pol)
          ρ' (id + 1) (rawOfTAssign st (updateAssign a₀ nd0 v)) := by
      intro v; rw [← hst₁_id]
      exact ih hl hd.2 hfresh.2 ρ' st₁ hvars₁ hρ'_deps hρ'_var hρ'_readers
        hρ'_readval (List.nodup_cons.mpr ⟨hxΓ, hnodup⟩) pol _
    simp_rw [hinner]
    -- sorry'd: rawOfTAssign update → extend (needs rawOfTAssign_updateAssign_of_tagged)
    have hraw : ∀ v, rawOfTAssign st (updateAssign a₀ nd0 v) =
        (rawOfTAssign st a₀).extend id ⟨τ.base, castValType hdesc0 v⟩ := by sorry
    simp_rw [hraw]
    -- Unfold nodeDist and connect CPDs
    simp only [nodeDist]
    have hkind_chance : (st.descAt nd0).kind = .chance := by
      simp [hdesc0, nd, CompiledNode.kind]
    split
    · -- chance branch: the correct one
      simp only [MAIDCompileState.toSem]
      split
      · -- inner match: .chance
        rename_i hk τ₁ deps₁ cpd₁ norm₁ hdesc₁
        have hinj := hdesc₁.symm.trans hdesc0
        simp only [nd, CompiledNode.chance.injEq] at hinj
        have hτeq := hinj.1; subst hτeq
        have hcpd : cpd₁ = cpdFDist := eq_of_heq hinj.2.2; subst hcpd
        have hdeps := hinj.2.1; subst hdeps
        have hnorm : norm₁ = cpdNorm := funext fun _ => Subsingleton.elim _ _; subst hnorm
        rw [show hdesc₁ = hdesc0 from Subsingleton.elim _ _]
        simp only [_root_.id, eq_mpr_eq_cast]
        let F : CompiledNode.valType nd → PMF (Outcome Player) :=
          fun w => nativeOutcomeDistPMFV B k hd.2
            (reflectPolicyAuxV B k hl hd.2 ρ' st₁ pol) ρ'
            (id + 1) ((rawOfTAssign st a₀).extend id ⟨τ.base, w⟩)
        change PMF.bind (cast _ ((cpdFDist (st.rawEnvOfCfg
          (MAID.projCfg a₀ (st.toStruct.parents nd0)))).toPMF _))
          (fun a => F (castValType hdesc0 a)) = _
        rw [pmf_descAt_cast_bind_cancel hdesc0]
        change ((cpdFDist (st.rawEnvOfCfg
            (MAID.projCfg a₀ (st.toStruct.parents nd0)))).toPMF (cpdNorm _)).bind F =
          ((L.evalDist D' (VEnv.eraseDistEnv τ m (ρ (rawOfTAssign st a₀)))).toPMF _).bind F
        congr 1
        exact congrArg (fun env => FDist.toPMF (L.evalDist D' (VEnv.eraseDistEnv τ m env))
          (hd.1 env)) hρeq
      · rename_i hdesc₁
        rw [hdesc₁] at hkind_chance; simp [CompiledNode.kind] at hkind_chance
      · rename_i hdesc₁
        rw [hdesc₁] at hkind_chance; simp [CompiledNode.kind] at hkind_chance
    · rename_i hk
      rw [toStruct_kind] at hk; rw [hkind_chance] at hk; exact absurd hk (by simp)
    · rename_i hk
      rw [toStruct_kind] at hk; rw [hkind_chance] at hk; exact absurd hk (by simp)
  | commit x who_commit R k ih =>
    rename_i Γ' b
    intro pol a₀
    have hxΓ : Fresh x Γ' := hfresh.1
    have hxvars : x ∉ st₀.vars.map Prod.fst := fun hxmem => hxΓ (hvars x hxmem)
    let obs := st₀.viewDeps who_commit Γ'
    let acts := allValues B b
    let id := st₀.nextId
    let nd : CompiledNode Player L B := .decision b who_commit acts
      (allValues_ne_nil B b) (allValues_nodup B b) obs
    have hndeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st₀.nextId := by
      intro d hd'; have hd'' : d ∈ obs := by
        simpa [nd, CompiledNode.parents, CompiledNode.obsParents] using hd'
      exact st₀.depsOfVars_lt _ d hd''
    let stNode := (st₀.addNode nd hndeps).2
    let st₁ := stNode.addVar x (.hidden who_commit b) ({id}) (by
      intro d hd'; have := Finset.mem_singleton.mp hd'; subst d; exact Nat.lt_succ_self id)
    let ρ' : RawNodeEnv L → VEnv (Player := Player) L ((x, .hidden who_commit b) :: Γ') :=
      fun raw => VEnv.cons (τ := .hidden who_commit b)
        (MAIDCompileState.readVal (B := B) raw b id) (ρ raw)
    have hvars₁ : st₁.VarsSubCtx ((x, .hidden who_commit b) :: Γ') := by
      simpa [st₁, stNode, nd, obs, id] using
        st₀.VarsSubCtx_addNode_addVar_singleton_step hvars nd hndeps x (.hidden who_commit b) hxΓ
    have hctx₁ : st₁.ctxDeps ((x, .hidden who_commit b) :: Γ') = {id} ∪ st₀.ctxDeps Γ' := by
      simpa [st₁, stNode, nd, obs, id] using
        st₀.ctxDeps_addNode_addVar_singleton_cons_eq_of_fresh nd hndeps x (.hidden who_commit b) hxΓ hxvars
    have hρ'_deps : ∀ j, j ∉ st₁.ctxDeps ((x, .hidden who_commit b) :: Γ') → InsensitiveTo ρ' j := by
      intro j hj raw tv
      have hjid : j ≠ id := by intro hEq; apply hj; simp [hctx₁, hEq]
      have hj' : j ∉ st₀.ctxDeps Γ' := by intro hmem; apply hj; simp [hctx₁, hmem]
      exact VEnv.cons_ext (readVal_extend_ne raw j id tv b hjid.symm) (hρ_deps j hj' raw tv)
    have hρ'_var : EnvRespectsLookupDeps st₁ ρ' := by
      intro y σ hy j hj raw tv
      cases hy with
      | here =>
          have hlookup : st₁.lookupDeps x = ({id} : Finset Nat) := by
            simpa [st₁] using stNode.lookupDeps_addVar_eq_self_of_fresh x (.hidden who_commit b) {id}
              (by intro d hd'; have := Finset.mem_singleton.mp hd'; subst d; exact Nat.lt_succ_self id)
              (by simpa [stNode, MAIDCompileState.addNode] using hxvars)
          have hjid : j ≠ id := by
            simpa [Finset.mem_singleton] using (show j ∉ ({id} : Finset Nat) by simpa [hlookup] using hj)
          simpa [ρ', VEnv.get, readVal_extend_ne, hjid] using
            (readVal_extend_ne (B := B) raw j id tv b hjid.symm)
      | there hy' =>
          have hxy : y ≠ x := fun hEq => hxΓ (hEq.symm ▸ hy'.mem_map_fst)
          have hlookupVar : st₁.lookupDeps y = stNode.lookupDeps y := by
            simpa [st₁] using stNode.lookupDeps_addVar_eq_of_ne x (.hidden who_commit b) {id}
              (by intro d hd'; have := Finset.mem_singleton.mp hd'; subst d; exact Nat.lt_succ_self id) hxy
          have hlookupNode : stNode.lookupDeps y = st₀.lookupDeps y := by
            simpa [stNode] using st₀.lookupDeps_addNode nd hndeps y
          have hj' : j ∉ st₀.lookupDeps y := by simpa [hlookupVar, hlookupNode] using hj
          simpa [ρ', VEnv.get, VEnv.cons_get_there] using hρ_var hy' j hj' raw tv
    let st := MAIDCompileState.ofProg B k hl.2 hd ρ' st₁
    have hid_lt : id < st.nextId :=
      Nat.lt_of_lt_of_le (by
        simp [st₁, stNode, id, MAIDCompileState.addVar, MAIDCompileState.addNode])
        (MAIDCompileState.ofProg_nextId_le B k hl.2 hd ρ' st₁)
    let nd0 : Fin st.nextId := ⟨id, hid_lt⟩
    have hdrop :
        (List.finRange st.nextId).drop id =
          nd0 :: (List.finRange st.nextId).drop st₁.nextId := by
      have hlen : id < (List.finRange st.nextId).length := by simpa using hid_lt
      rw [show st₁.nextId = id + 1 by
        simp [st₁, stNode, id, MAIDCompileState.addVar, MAIDCompileState.addNode]]
      rw [← List.cons_getElem_drop_succ (l := List.finRange st.nextId) (n := id) (h := hlen)]
      simp [nd0]
    have hdesc0 : st.descAt nd0 = nd := by
      have hdesc1 := MAIDCompileState.ofProg_descAt_old B k hl.2 hd ρ' st₁ id
        (by simp [st₁, stNode, id, MAIDCompileState.addVar, MAIDCompileState.addNode])
      rw [hdesc1]; simpa [st₁, stNode] using st₀.addNode_descAt_new nd hndeps
    -- View equivalence (where VegasMAID obsParents = parents helps)
    have hViewEq :
        projectViewEnv (P := Player) (L := L) who_commit
          (VEnv.eraseEnv (ρ (st.rawEnvOfCfg
            (MAID.projCfg a₀ (st.toStruct.obsParents nd0))))) =
        projectViewEnv (P := Player) (L := L) who_commit
          (VEnv.eraseEnv (ρ (rawOfTAssign st a₀))) := by sorry
    -- Peel off the decision node from the fold
    change PMF.map (fun a => extractOutcomeAux B (.commit x who_commit R k) ρ st₀.nextId (rawOfTAssign st a))
      (List.foldl (evalStep st.toStruct st.toSem pol) (PMF.pure a₀)
        ((List.finRange st.nextId).drop id)) =
      nativeOutcomeDistPMFV B (.commit x who_commit R k) hd
        (reflectPolicyAuxV B (.commit x who_commit R k) hl hd ρ st₀ pol) ρ
        id (rawOfTAssign st a₀)
    rw [hdrop, List.foldl_cons]
    simp only [nativeOutcomeDistPMFV, reflectPolicyAuxV]
    simp only [evalStep, PMF.pure_bind]
    rw [foldl_evalStep_bind_left, PMF.map_bind]
    have hst₁_id : st₁.nextId = id + 1 := by
      simp [st₁, stNode, id, MAIDCompileState.addVar, MAIDCompileState.addNode]
    -- Apply IH to inner fold (sorry'd invariant propagation)
    have hρ'_readers : ViewDeterminesRaw st₁ ((x, .hidden who_commit b) :: Γ') ρ' := by sorry
    have hρ'_readval : EnvReadValAtDeps st₁ ((x, .hidden who_commit b) :: Γ') ρ' := by sorry
    have hinner : ∀ v, PMF.map (fun a => extractOutcomeAux B (.commit x who_commit R k) ρ
          st₀.nextId (rawOfTAssign st a))
        (List.foldl (evalStep st.toStruct st.toSem pol)
          (PMF.pure (updateAssign a₀ nd0 v))
          ((List.finRange st.nextId).drop st₁.nextId)) =
        nativeOutcomeDistPMFV B k hd (reflectPolicyAuxV B k hl.2 hd ρ' st₁ pol)
          ρ' (id + 1) (rawOfTAssign st (updateAssign a₀ nd0 v)) := by
      intro v; rw [← hst₁_id]
      exact ih hl.2 hd hfresh.2 ρ' st₁ hvars₁ hρ'_deps hρ'_var hρ'_readers
        hρ'_readval (List.nodup_cons.mpr ⟨hxΓ, hnodup⟩) pol _
    simp_rw [hinner]
    -- Cast rawOfTAssign update to extend (sorry'd)
    have hraw : ∀ v, rawOfTAssign st (updateAssign a₀ nd0 v) =
        (rawOfTAssign st a₀).extend id ⟨b, castValType hdesc0 v⟩ := by sorry
    simp_rw [hraw]
    -- Unfold nodeDist at decision node
    simp only [nodeDist]
    have hkind_decision : (st.descAt nd0).kind = .decision who_commit := by
      simp [hdesc0, nd, CompiledNode.kind]
    split
    · -- chance: contradiction
      rename_i hk; rw [toStruct_kind] at hk; rw [hkind_decision] at hk; exact absurd hk (by simp)
    · -- decision: the correct branch
      rename_i p hk
      have hp : p = who_commit := by
        have := (toStruct_kind st nd0).symm.trans hk
        rw [hkind_decision] at this; exact (NodeKind.decision.inj this).symm
      subst hp
      -- Match reflected kernel with MAID policy
      -- This is where VegasMAID's obsParents = parents simplifies things
      sorry
    · -- utility: contradiction
      rename_i hk; rw [toStruct_kind] at hk; rw [hkind_decision] at hk; exact absurd hk (by simp)
  | reveal y who_r x_r hx k ih =>
    rename_i Γ' b
    intro pol a₀
    have hyΓ : Fresh y Γ' := hfresh.1
    have hyvars : y ∉ st₀.vars.map Prod.fst := fun hymem => hyΓ (hvars y hymem)
    let ρ' : RawNodeEnv L → VEnv (Player := Player) L ((y, .pub b) :: Γ') :=
      fun raw =>
        let v : L.Val b := VEnv.get (L := L) (ρ raw) hx
        VEnv.cons (L := L) (x := y) (τ := .pub b) v (ρ raw)
    let st₁ := st₀.addVar y (.pub b) (st₀.lookupDeps x_r) (st₀.lookupDeps_lt x_r)
    have hvars₁ : st₁.VarsSubCtx ((y, .pub b) :: Γ') := by
      simpa [st₁] using st₀.VarsSubCtx_addVar hvars y _ _ _ hyΓ
    have hctx₁ : st₁.ctxDeps ((y, .pub b) :: Γ') = st₀.ctxDeps Γ' := by
      simpa [st₁] using st₀.ctxDeps_reveal_step y who_r x_r hx hyΓ hyvars
    have hρ'_deps : ∀ j, j ∉ st₁.ctxDeps ((y, .pub b) :: Γ') → InsensitiveTo ρ' j := by
      intro j hj raw tv
      have hj' : j ∉ st₀.ctxDeps Γ' := by simpa [hctx₁] using hj
      have hρj := hρ_deps j hj' raw tv
      simp only [ρ', hρj]
    have hρ'_var : EnvRespectsLookupDeps st₁ ρ' := by
      intro z σ hz j hj raw tv
      cases hz with
      | here =>
          have hj' : j ∉ st₀.lookupDeps x_r := by
            simpa [st₁, st₀.lookupDeps_addVar_eq_self_of_fresh y (.pub b) (st₀.lookupDeps x_r)
              (st₀.lookupDeps_lt x_r) hyvars] using hj
          simpa [ρ', VEnv.get] using hρ_var hx j hj' raw tv
      | there hz' =>
          have hzy : z ≠ y := fun hEq => hyΓ (hEq.symm ▸ hz'.mem_map_fst)
          have hj' : j ∉ st₀.lookupDeps z := by
            simpa [st₁, st₀.lookupDeps_addVar_eq_of_ne y (.pub b) (st₀.lookupDeps x_r)
              (st₀.lookupDeps_lt x_r) hzy] using hj
          simpa [ρ', VEnv.get, VEnv.cons_get_there] using hρ_var hz' j hj' raw tv
    have hρ'_readers : ViewDeterminesRaw st₁ ((y, .pub b) :: Γ') ρ' := by
      intro who raw₁ raw₂ hout hnot_vd htyped hview i hi
      have hview_old := projectViewEnv_cons_eq
        (List.nodup_cons.mpr ⟨hyΓ, hnodup⟩) hview
      have hy_not_view : y ∉ (viewVCtx who Γ').map Prod.fst :=
        fun hmem => hyΓ (viewVCtx_map_fst_sub hmem)
      have hVD : st₁.viewDeps who ((y, .pub b) :: Γ') =
          st₀.lookupDeps x_r ∪ st₀.viewDeps who Γ' := by
        unfold MAIDCompileState.viewDeps
        simp only [viewVCtx, canSee, ite_true, List.map_cons, MAIDCompileState.depsOfVars]
        rw [st₀.lookupDeps_addVar_eq_self_of_fresh y (.pub b) (st₀.lookupDeps x_r)
            (st₀.lookupDeps_lt x_r) hyvars,
          st₀.depsOfVars_addVar_eq_of_not_mem y (.pub b) _ _ _ hy_not_view]
      have hhead := projectViewEnv_cons_head_eq
        (List.nodup_cons.mpr ⟨hyΓ, hnodup⟩) (by simp [canSee]) hview
      have hraw_lookup_eq : ∀ j ∈ st₀.lookupDeps x_r, raw₁ j = raw₂ j := by
        intro j hj_mem
        rcases hρ_readval x_r who_r b hx ⟨j, hj_mem⟩ with ⟨k, hklt, hsingleton, hdescAt_type, hreadval⟩
        have hjk : j = k := Finset.mem_singleton.mp (hsingleton ▸ hj_mem); subst hjk
        rw [hreadval raw₁, hreadval raw₂] at hhead
        have hj_vd := hVD ▸ Finset.mem_union_left _ hj_mem
        have htyped_j := htyped j hj_vd (by simp only [MAIDCompileState.addVar, st₁]; exact hklt)
        simp only [RawsMatchDescAt,
          show st₁.descAt ⟨j, _⟩ = st₀.descAt ⟨j, hklt⟩ from rfl] at htyped_j
        revert htyped_j hdescAt_type; match st₀.descAt ⟨j, hklt⟩ with
        | .chance τ _ _ _ | .decision τ _ _ _ _ _ =>
          intro hτb ⟨v₁, v₂, hraw₁, hraw₂⟩
          subst hτb
          exact readVal_tagged_eq hraw₁ hraw₂ hhead
        | .utility _ _ _ =>
          intro _ ⟨h₁, h₂⟩; rw [h₁, h₂]
      rw [hVD] at hi
      rcases Finset.mem_union.mp hi with hi_lookup | hi_old
      · exact hraw_lookup_eq i hi_lookup
      · apply hρ_readers who raw₁ raw₂
        · intro j hj; exact hout j (by
            simp [st₁, MAIDCompileState.addVar] at hj ⊢; exact hj)
        · intro j hj hjlt
          by_cases hj_lookup : j ∈ st₀.lookupDeps x_r
          · exact hraw_lookup_eq j hj_lookup
          · exact hnot_vd j (fun hmem => by
              rw [hVD] at hmem
              rcases Finset.mem_union.mp hmem with h | h
              · exact hj_lookup h
              · exact hj h) (by simp [st₁, MAIDCompileState.addVar]; exact hjlt)
        · intro j hj hjlt
          exact htyped j (by rw [hVD]; exact Finset.mem_union_right _ hj)
            (by simp [st₁, MAIDCompileState.addVar]; exact hjlt)
        · exact hview_old
        · exact hi_old
    exact ih hl hd hfresh.2 ρ' st₁ hvars₁ hρ'_deps hρ'_var hρ'_readers
      (fun z who_z bz hz hne_z => by
        cases hz with
        | there hy' =>
          have hne : z ≠ y := fun h => hyΓ (h.symm ▸ hy'.mem_map_fst)
          have hld_eq : st₁.lookupDeps z = st₀.lookupDeps z := by
            simp [st₁, st₀.lookupDeps_addVar_eq_of_ne y (.pub b) _ _ hne]
          have hne_z' : (st₀.lookupDeps z).Nonempty := by rwa [← hld_eq]
          rcases hρ_readval z who_z bz hy' hne_z' with ⟨j, hjlt, hj_sing, hdesc_j, hget⟩
          exact ⟨j, hjlt, by rwa [hld_eq], hdesc_j,
            fun raw => by simpa [ρ', VEnv.get, VEnv.cons_get_there] using hget raw⟩)
      (List.nodup_cons.mpr ⟨hyΓ, hnodup⟩) pol a₀

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
