import Vegas.MAID.Defs
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

private theorem cast_PMF_pure {α β : Type} (h₁ : PMF α = PMF β) (h₂ : α = β) (x : α) :
    cast h₁ (PMF.pure x) = PMF.pure (cast h₂ x) := by
  subst h₂
  rfl

private noncomputable def fdist_transport {α β : Type} [DecidableEq α] [DecidableEq β]
    (h : α = β) (d : FDist α) : FDist β := h ▸ d

@[simp] private theorem fdist_transport_totalWeight {α β : Type}
    [DecidableEq α] [DecidableEq β] (h : α = β) (d : FDist α) :
    (fdist_transport h d).totalWeight = d.totalWeight := by
  subst h
  rfl

private theorem toPMF_fdist_transport_cast {α β : Type}
    [DecidableEq α] [DecidableEq β] (h : α = β) (d : FDist α)
    (hn : (fdist_transport h d).totalWeight = 1) :
    (fdist_transport h d).toPMF hn =
      cast (congrArg PMF h) (d.toPMF ((fdist_transport_totalWeight h d).symm ▸ hn)) := by
  subst h
  rfl

@[congr] private theorem FDist.toPMF_congr' [DecidableEq α]
    {d₁ d₂ : FDist α} {h₁ h₂} (heq : d₁ = d₂) :
    FDist.toPMF d₁ h₁ = FDist.toPMF d₂ h₂ := by
  subst heq
  rfl

private theorem taggedOfVal_castValType
    {c c' : CompiledNode Player L B} (hc : c = c') (v : CompiledNode.valType c) :
    MAIDCompileState.taggedOfVal c' (castValType hc v) =
      MAIDCompileState.taggedOfVal c v := by
  subst hc
  rfl

private theorem eq_on_ctxDeps_raw
    (st : MAIDCompileState Player L B)
    {deps : Finset Nat} {f : RawNodeEnv L → α}
    (hf : ∀ j, j ∉ deps → InsensitiveTo f j)
    (raw : RawNodeEnv L)
    (hraw_hi : ∀ j, st.nextId ≤ j → raw j = none) :
    let rawSel : RawNodeEnv L := fun i =>
      if i < st.nextId then
        if i ∈ deps then raw i else none else none
    f rawSel = f raw := by
  intro rawSel
  let ks : List Nat := (List.range st.nextId).filter (· ∉ deps)
  have hclear : rawSel = fun i => if i ∈ ks then none else raw i := by
    funext i
    by_cases hi : i < st.nextId
    · have hmem : i ∈ ks ↔ i ∉ deps := by
        unfold ks
        simp [hi]
      by_cases hdep : i ∈ deps
      · simp [rawSel, hi, hdep, hmem]
      · simp [rawSel, hi, hdep, hmem]
    · simp [rawSel, hi, ks, hraw_hi i (by omega)]
  rw [hclear]
  haveI : Nonempty (RawTaggedVal L) := by
    let ⟨v⟩ := B.toMAIDValuation.nonemptyVal L.bool
    exact ⟨⟨L.bool, v⟩⟩
  apply InsensitiveTo.eq_of_agree_off_list ks
  · intro k hk
    apply hf k
    have hk' : k ∈ (List.range st.nextId).filter (fun j => j ∉ deps) := by
      simpa [ks] using hk
    simpa using (List.mem_filter.mp hk').2
  · intro i hi
    simp [hi]

private theorem envRespectsLookupDeps_letExpr
    {Γ' : VCtx Player L}
    (st : MAIDCompileState Player L B)
    (ρ : RawNodeEnv L → VEnv (Player := Player) L Γ')
    (hρ_var : EnvRespectsLookupDeps st ρ)
    {x : VarId} {b : L.Ty} (e : L.Expr (erasePubVCtx Γ') b)
    (hxΓ : Fresh x Γ')
    (hxvars : x ∉ st.vars.map Prod.fst) :
    let ρ' : RawNodeEnv L → VEnv (Player := Player) L ((x, .pub b) :: Γ') :=
      fun raw => VEnv.cons (L := L) (x := x) (τ := .pub b)
        (L.eval e (VEnv.erasePubEnv (ρ raw))) (ρ raw)
    let st₁ := st.addVar x (.pub b) (st.pubCtxDeps Γ') (st.depsOfVars_lt _)
    EnvRespectsLookupDeps st₁ ρ' := by
  intro ρ' st₁ y τ hy j hj raw tv
  cases hy with
  | here =>
      have hj' : j ∉ st.pubCtxDeps Γ' := by
        simpa [st₁, st.lookupDeps_addVar_eq_self_of_fresh x (.pub b)
          (st.pubCtxDeps Γ') (st.depsOfVars_lt _) hxvars] using hj
      exact Vegas.eval_pubExpr_insensitive_of_pubCtxDeps st ρ hρ_var e j hj' raw tv
  | there hy' =>
      have hxy : y ≠ x := fun hEq => hxΓ (hEq.symm ▸ hy'.mem_map_fst)
      have hj' : j ∉ st.lookupDeps y := by
        simpa [st₁, st.lookupDeps_addVar_eq_of_ne x (.pub b)
          (st.pubCtxDeps Γ') (st.depsOfVars_lt _) hxy] using hj
      simpa [ρ', VEnv.get, VEnv.cons_get_there] using hρ_var hy' j hj' raw tv

private theorem envRespectsLookupDeps_sample
    {Γ' : VCtx Player L}
    (st : MAIDCompileState Player L B)
    (ρ : RawNodeEnv L → VEnv (Player := Player) L Γ')
    (hρ_var : EnvRespectsLookupDeps st ρ)
    {x : VarId} {τ : BindTy Player L} {m : SampleMode τ}
    (D' : L.DistExpr (eraseVCtx (distVCtx τ m Γ')) τ.base)
    (hd : ∀ env, FDist.totalWeight (L.evalDist D' (VEnv.eraseDistEnv τ m env)) = 1)
    (hxΓ : Fresh x Γ')
    (hxvars : x ∉ st.vars.map Prod.fst) :
    let nd : CompiledNode Player L B := .chance τ.base (st.ctxDeps Γ')
      (fun raw => L.evalDist D' (VEnv.eraseDistEnv τ m (ρ raw))) (fun raw => hd _)
    let hndeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId := by
      intro d hd'; rcases Finset.mem_union.mp hd' with h | h <;>
        simpa [CompiledNode.parents, CompiledNode.obsParents, nd] using st.depsOfVars_lt _ d h
    let stNode := (st.addNode nd hndeps).2
    let st₁ := stNode.addVar x τ ({st.nextId}) (by
      intro d hd'; have := Finset.mem_singleton.mp hd'; subst d
      exact Nat.lt_succ_self _)
    let ρ' : RawNodeEnv L → VEnv (Player := Player) L ((x, τ) :: Γ') :=
      fun raw => VEnv.cons (MAIDCompileState.readVal (B := B) raw τ.base st.nextId) (ρ raw)
    EnvRespectsLookupDeps st₁ ρ' := by
  intro nd hndeps stNode st₁ ρ' y σ hy j hj raw tv
  cases hy with
  | here =>
      have hlookup : st₁.lookupDeps x = ({st.nextId} : Finset Nat) := by
        simpa [st₁] using stNode.lookupDeps_addVar_eq_self_of_fresh x τ {st.nextId}
          (by
            intro d hd'
            have := Finset.mem_singleton.mp hd'
            subst d
            exact Nat.lt_succ_self _)
          (by simpa [stNode, MAIDCompileState.addNode] using hxvars)
      have hjid : j ≠ st.nextId := by
        simpa [Finset.mem_singleton] using
          (show j ∉ ({st.nextId} : Finset Nat) by simpa [hlookup] using hj)
      simpa [ρ', VEnv.get, readVal_extend_ne, hjid] using
        (readVal_extend_ne (B := B) raw j st.nextId tv τ.base hjid.symm)
  | there hy' =>
      have hxy : y ≠ x := fun hEq => hxΓ (hEq.symm ▸ hy'.mem_map_fst)
      have hlookupVar : st₁.lookupDeps y = stNode.lookupDeps y := by
        simpa [st₁] using stNode.lookupDeps_addVar_eq_of_ne x τ {st.nextId}
          (by
            intro d hd'
            have := Finset.mem_singleton.mp hd'
            subst d
            exact Nat.lt_succ_self _) hxy
      have hlookupNode : stNode.lookupDeps y = st.lookupDeps y := by
        simpa [stNode] using st.lookupDeps_addNode nd hndeps y
      have hj' : j ∉ st.lookupDeps y := by
        simpa [hlookupVar, hlookupNode] using hj
      simpa [ρ', VEnv.get, VEnv.cons_get_there] using hρ_var hy' j hj' raw tv

private theorem envRespectsLookupDeps_reveal
    {Γ' : VCtx Player L}
    (st : MAIDCompileState Player L B)
    (ρ : RawNodeEnv L → VEnv (Player := Player) L Γ')
    (hρ_var : EnvRespectsLookupDeps st ρ)
    {y x : VarId} {who : Player} {b : L.Ty}
    (hx : VHasVar (L := L) Γ' x (.hidden who b))
    (hyΓ : Fresh y Γ')
    (hyvars : y ∉ st.vars.map Prod.fst) :
    let ρ' : RawNodeEnv L → VEnv (Player := Player) L ((y, .pub b) :: Γ') :=
      fun raw =>
        let v : L.Val b := VEnv.get (L := L) (ρ raw) hx
        VEnv.cons (L := L) (x := y) (τ := .pub b) v (ρ raw)
    let st₁ := st.addVar y (.pub b) (st.lookupDeps x) (st.lookupDeps_lt x)
    EnvRespectsLookupDeps st₁ ρ' := by
  intro ρ' st₁ z σ hz j hj raw tv
  cases hz with
  | here =>
      have hj' : j ∉ st.lookupDeps x := by
        simpa [st₁, st.lookupDeps_addVar_eq_self_of_fresh y (.pub b) (st.lookupDeps x)
          (st.lookupDeps_lt x) hyvars] using hj
      simpa [ρ', VEnv.get] using hρ_var hx j hj' raw tv
  | there hz' =>
      have hzy : z ≠ y := fun hEq => hyΓ (hEq.symm ▸ hz'.mem_map_fst)
      have hj' : j ∉ st.lookupDeps z := by
        simpa [st₁, st.lookupDeps_addVar_eq_of_ne y (.pub b) (st.lookupDeps x)
          (st.lookupDeps_lt x) hzy] using hj
      simpa [ρ', VEnv.get, VEnv.cons_get_there] using hρ_var hz' j hj' raw tv

private theorem envRespectsLookupDeps_commit
    {Γ' : VCtx Player L}
    (st : MAIDCompileState Player L B)
    (ρ : RawNodeEnv L → VEnv (Player := Player) L Γ')
    (hρ_var : EnvRespectsLookupDeps st ρ)
    {x : VarId} {who : Player} {b : L.Ty}
    (hxΓ : Fresh x Γ')
    (hxvars : x ∉ st.vars.map Prod.fst) :
    let nd : CompiledNode Player L B :=
      .decision b who (allValues B b) (allValues_ne_nil B b)
        (allValues_nodup B b) (st.viewDeps who Γ')
    let hndeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId := by
      intro d hd'; rcases Finset.mem_union.mp hd' with h | h <;>
        simpa [CompiledNode.parents, CompiledNode.obsParents, nd] using st.depsOfVars_lt _ d h
    let stNode := (st.addNode nd hndeps).2
    let st₁ := stNode.addVar x (.hidden who b) ({st.nextId}) (by
      intro d hd'; have := Finset.mem_singleton.mp hd'; subst d
      exact Nat.lt_succ_self _)
    let ρ' : RawNodeEnv L → VEnv (Player := Player) L ((x, .hidden who b) :: Γ') :=
      fun raw => VEnv.cons (τ := .hidden who b)
        (MAIDCompileState.readVal (B := B) raw b st.nextId) (ρ raw)
    EnvRespectsLookupDeps st₁ ρ' := by
  intro nd hndeps stNode st₁ ρ' y σ hy j hj raw tv
  cases hy with
  | here =>
      have hlookup : st₁.lookupDeps x = ({st.nextId} : Finset Nat) := by
        simpa [st₁] using
          stNode.lookupDeps_addVar_eq_self_of_fresh x (.hidden who b) {st.nextId}
            (by
              intro d hd'
              have := Finset.mem_singleton.mp hd'
              subst d
              exact Nat.lt_succ_self _)
            (by simpa [stNode, MAIDCompileState.addNode] using hxvars)
      have hjid : j ≠ st.nextId := by
        simpa [Finset.mem_singleton] using
          (show j ∉ ({st.nextId} : Finset Nat) by simpa [hlookup] using hj)
      simpa [ρ', VEnv.get, readVal_extend_ne, hjid] using
        (readVal_extend_ne (B := B) raw j st.nextId tv b hjid.symm)
  | there hy' =>
      have hxy : y ≠ x := fun hEq => hxΓ (hEq.symm ▸ hy'.mem_map_fst)
      have hlookupVar : st₁.lookupDeps y = stNode.lookupDeps y := by
        simpa [st₁] using stNode.lookupDeps_addVar_eq_of_ne x (.hidden who b) {st.nextId}
          (by
            intro d hd'
            have := Finset.mem_singleton.mp hd'
            subst d
            exact Nat.lt_succ_self _) hxy
      have hlookupNode : stNode.lookupDeps y = st.lookupDeps y := by
        simpa [stNode] using st.lookupDeps_addNode nd hndeps y
      have hj' : j ∉ st.lookupDeps y := by
        simpa [hlookupVar, hlookupNode] using hj
      simpa [ρ', VEnv.get, VEnv.cons_get_there] using hρ_var hy' j hj' raw tv

private theorem rawWitness_extend_addNode_addVar
    (st : MAIDCompileState Player L B)
    (nd : CompiledNode Player L B)
    (hndeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId)
    {x : VarId} {τ : BindTy Player L}
    (raw₀ : RawNodeEnv L)
    (hraw_typed : ∀ j (hj : j < st.nextId), ∃ v,
      raw₀ j = MAIDCompileState.taggedOfVal (st.descAt ⟨j, hj⟩) v)
    (hraw_hi : ∀ j, st.nextId ≤ j → raw₀ j = none)
    (tv : RawTaggedVal L)
    (htag : ∃ v, MAIDCompileState.taggedOfVal nd v = some tv) :
    let stNode := (st.addNode nd hndeps).2
    let st₁ := stNode.addVar x τ ({st.nextId}) (by
      intro d hd'; have := Finset.mem_singleton.mp hd'; subst d
      exact Nat.lt_succ_self _)
    (∀ j (hj : j < st₁.nextId), ∃ v,
      (raw₀.extend st.nextId tv) j = MAIDCompileState.taggedOfVal (st₁.descAt ⟨j, hj⟩) v) ∧
    (∀ j, st₁.nextId ≤ j → (raw₀.extend st.nextId tv) j = none) := by
  intro stNode st₁
  constructor
  · intro j hj
    by_cases hjid : j = st.nextId
    · subst hjid
      rcases htag with ⟨v, hv⟩
      have hdesc_new : st₁.descAt ⟨st.nextId, hj⟩ = nd := by
        simp only [st₁, MAIDCompileState.addVar, stNode]
        exact st.addNode_descAt_new nd hndeps
      refine ⟨castValType hdesc_new.symm v, ?_⟩
      simp [RawNodeEnv.extend, hv, taggedOfVal_castValType]
    · have hj_old : j < st.nextId := by
        have hnext : st₁.nextId = st.nextId + 1 := by
          simp [st₁, MAIDCompileState.addVar, stNode, MAIDCompileState.addNode]
        omega
      rcases hraw_typed j hj_old with ⟨v, hv⟩
      have hdesc_old : st₁.descAt ⟨j, hj⟩ = st.descAt ⟨j, hj_old⟩ := by
        simp only [st₁, MAIDCompileState.addVar, stNode]
        exact st.addNode_descAt_old nd hndeps ⟨j, hj_old⟩
      refine ⟨castValType hdesc_old.symm v, ?_⟩
      simpa [RawNodeEnv.extend, hjid, hdesc_old, taggedOfVal_castValType] using hv
  · intro j hj
    have hjid : j ≠ st.nextId := by
      intro hEq
      subst hEq
      have hnext : st₁.nextId = st.nextId + 1 := by
        simp [st₁, MAIDCompileState.addVar, stNode, MAIDCompileState.addNode]
      omega
    have hge : st.nextId ≤ j := by
      have hnext : st₁.nextId = st.nextId + 1 := by
        simp [st₁, MAIDCompileState.addVar, stNode, MAIDCompileState.addNode]
      omega
    simpa [RawNodeEnv.extend, hjid] using hraw_hi j hge

/-! ## Pure bridge -/

private theorem compilePureProfileV_eq_pureToPolicy_aux
    (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ)
    (hl : Legal p) (hd : NormalizedDists p) (hfresh : FreshBindings p)
    (ρ : RawNodeEnv L → VEnv (Player := Player) L Γ)
    (st₀ : MAIDCompileState Player L B)
    (π : ProgramPureProfile (P := Player) (L := L) p) :
    translateStrategyV B p hl hd ρ st₀ (ProgramPureProfile.toBehavioral p π) =
      MAID.pureToPolicy (fp := B.fintypePlayer) (compilePureProfileAuxV B p hl hd ρ st₀ π) := by
  induction p generalizing st₀ with
  | ret =>
      funext player ⟨d, cfg⟩
      simp [translateStrategyV, compilePureProfileAuxV,
        MAID.pureToPolicy, MAID.pureToPlayerStrategy]
  | letExpr _ _ k ih =>
      simp only [translateStrategyV, compilePureProfileAuxV]
      exact ih hl hd hfresh.2 _ _ _
  | sample _ _ _ _ k ih =>
      exact ih hl hd.2 hfresh.2 _ _ _
  | commit x who_c R k ih =>
      funext player ⟨d, cfg⟩
      simp only [translateStrategyV, compilePureProfileAuxV,
        MAID.pureToPolicy, MAID.pureToPlayerStrategy]
      split
      · simp only [toStruct_kind, id,
          ProgramBehavioralStrategy.headKernel, ProgramPureProfile.toBehavioral,
          ↓reduceDIte, ProgramBehavioralKernel.ofPure, ProgramPureStrategy.headKernel,
          eq_mp_eq_cast, eq_mpr_eq_cast, cast_cast, cast_eq, FDist.toPMF_pure]
        exact cast_PMF_pure _ _ _
      · simpa [ProgramPureProfile.tail_toBehavioral, MAID.pureToPolicy,
          MAID.pureToPlayerStrategy] using
          congrFun (congrFun (ih hl.2 hd hfresh.2 _ _ _) player) ⟨d, cfg⟩
  | reveal _ _ _ _ k ih =>
      exact ih hl hd hfresh.2 _ _ _

private theorem compilePureProfileV_eq_pureToPolicy
    (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ)
    (env : VEnv (Player := Player) L Γ)
    (hl : Legal p) (hd : NormalizedDists p) (hfresh : FreshBindings p)
    (hpub : ∀ y who b, VHasVar (L := L) Γ y (.hidden who b) → False)
    (π : ProgramPureProfile (P := Player) (L := L) p) :
    let β := ProgramPureProfile.toBehavioral p π
    compiledPolicyV B p env hl hd hfresh hpub β =
      MAID.pureToPolicy (fp := B.fintypePlayer)
        (compilePureProfileV B p env hl hd hfresh hpub π) := by
  intro β
  exact compilePureProfileV_eq_pureToPolicy_aux B p hl hd hfresh (fun _ => env) .empty π

private theorem toBehavioralPMF_eq_toPMFProfile_toBehavioral
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ)
    (π : ProgramPureProfile (P := Player) (L := L) p) :
    ProgramPureProfile.toBehavioralPMF p π =
      ProgramBehavioralProfile.toPMFProfile p (ProgramPureProfile.toBehavioral p π) := by
  have hofPure :
      ∀ {who : Player} {Γ : VCtx Player L} {b : L.Ty}
        (κ : PureKernel (P := Player) (L := L) who Γ b),
        ProgramBehavioralKernelPMF.ofFDist
            (ProgramBehavioralKernel.ofPure (P := Player) (L := L) κ) =
          ProgramBehavioralKernelPMF.ofPure (P := Player) (L := L) κ := by
    intro who Γ b κ
    ext view
    simp [ProgramBehavioralKernelPMF.ofFDist, ProgramBehavioralKernelPMF.ofPure,
      ProgramBehavioralKernel.ofPure, FDist.toPMF_pure]
  induction p with
  | ret =>
      funext who
      simp [ProgramPureProfile.toBehavioralPMF, ProgramBehavioralProfile.toPMFProfile,
        ]
  | letExpr x e k ih =>
      funext who
      simp [ProgramPureProfile.toBehavioralPMF, ProgramBehavioralProfile.toPMFProfile,
        ProgramPureProfile.toBehavioral, ih]
  | sample x τ m D' k ih =>
      funext who
      simp [ProgramPureProfile.toBehavioralPMF, ProgramBehavioralProfile.toPMFProfile,
        ProgramPureProfile.toBehavioral, ih]
  | commit x who_commit R k ih =>
      funext who
      by_cases h : who_commit = who
      · subst h
        simp [ProgramPureProfile.toBehavioralPMF, ProgramBehavioralProfile.toPMFProfile]
        constructor
        · simpa [ProgramPureProfile.toBehavioral] using
            (hofPure (κ := (ProgramPureStrategy.headKernel (π who_commit)))).symm
        · simpa using congrFun (ih (ProgramPureProfile.tail π)) who_commit
      · simp [ProgramPureProfile.toBehavioralPMF, ProgramBehavioralProfile.toPMFProfile, h]
        simpa using congrFun (ih (ProgramPureProfile.tail π)) who
  | reveal y who x hx k ih =>
      funext who'
      simp [ProgramPureProfile.toBehavioralPMF, ProgramBehavioralProfile.toPMFProfile,
        ProgramPureProfile.toBehavioral, ih]

/-! ## Bundled Bridge Invariant -/
private structure BridgeInv
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
    (hnodup : (Γ.map Prod.fst).Nodup) : Prop where
  fold_eq :
    ∀ (hρ_readers : ViewDeterminesRaw st₀ Γ ρ)
      (hρ_readval : EnvReadValAtDeps st₀ Γ ρ)
      (pol : Policy (fp := B.fintypePlayer)
        (MAIDCompileState.ofProg B p hl hd ρ st₀).toStruct)
      (a₀ : TAssign (fp := B.fintypePlayer) (MAIDCompileState.ofProg B p hl hd ρ st₀).toStruct),
      PMF.map (fun a =>
          extractOutcomeAux B p ρ st₀.nextId
            (rawOfTAssign (MAIDCompileState.ofProg B p hl hd ρ st₀) a))
        ((List.finRange (MAIDCompileState.ofProg B p hl hd ρ st₀).nextId).drop st₀.nextId |>.foldl
          (evalStep (fp := B.fintypePlayer)
            (MAIDCompileState.ofProg B p hl hd ρ st₀).toStruct
            (MAIDCompileState.toSem (MAIDCompileState.ofProg B p hl hd ρ st₀)) pol)
          (PMF.pure a₀)) =
      nativeOutcomeDistPMFV B p hd
        (reflectPolicyAuxV B p hl hd ρ st₀ pol)
        ρ st₀.nextId
        (rawOfTAssign (MAIDCompileState.ofProg B p hl hd ρ st₀) a₀)
  behavioral_eq :
    ∀ (β : ProgramBehavioralProfile (P := Player) (L := L) p)
      (pol : Policy (fp := B.fintypePlayer)
        (MAIDCompileState.ofProg B p hl hd ρ st₀).toStruct)
      (env : VEnv (Player := Player) L Γ),
      (∀ (who : Player)
          (I : MAID.Infoset (fp := B.fintypePlayer)
            (MAIDCompileState.ofProg B p hl hd ρ st₀).toStruct who),
        I.1.1.val ≥ st₀.nextId →
        pol who I = translateStrategyV B p hl hd ρ st₀ β who I) →
      (∃ raw₀, ρ raw₀ = env ∧
        (∀ j (hj : j < st₀.nextId), ∃ v,
          raw₀ j = MAIDCompileState.taggedOfVal (st₀.descAt ⟨j, hj⟩) v) ∧
        (∀ j, st₀.nextId ≤ j → raw₀ j = none)) →
      outcomeDistBehavioralPMF p hd
        (reflectPolicyAuxV B p hl hd ρ st₀ pol) env =
      outcomeDistBehavioralPMF p hd
        (ProgramBehavioralProfile.toPMFProfile p β) env

private theorem bridgeInv_ret
    (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (u : List (Player × L.Expr (erasePubVCtx Γ) L.int))
    (hl : Legal (.ret u)) (hd : NormalizedDists (.ret u))
    (hfresh : FreshBindings (.ret u))
    (ρ : RawNodeEnv L → VEnv (Player := Player) L Γ)
    (st₀ : MAIDCompileState Player L B)
    (hvars : st₀.VarsSubCtx Γ)
    (hρ_deps : ∀ j, j ∉ (st₀.ctxDeps Γ : Finset Nat) → InsensitiveTo ρ j)
    (hρ_var : EnvRespectsLookupDeps st₀ ρ)
    (hnodup : (Γ.map Prod.fst).Nodup) :
    BridgeInv B (.ret u) hl hd hfresh ρ st₀ hvars hρ_deps hρ_var hnodup := by
  letI := B.fintypePlayer
  refine ⟨?_, ?_⟩
  · intro hρ_readers hρ_readval pol a₀
    let st := MAIDCompileState.ofProg B (.ret u) hl hd ρ st₀
    let extract := fun a => extractOutcomeAux B (.ret u) ρ st₀.nextId (rawOfTAssign st a)
    have hutility : ∀ nd ∈ (List.finRange st.nextId).drop st₀.nextId,
        ∃ who, (st.descAt nd).kind = .utility who := fun nd hnd => by
      have hge : st₀.nextId ≤ nd.val := by
        rcases List.mem_iff_getElem.mp hnd with ⟨i, hi, hget⟩
        have := congrArg Fin.val hget
        rw [List.getElem_drop] at this
        simp at this
        omega
      exact MAIDCompileState.addUtilityNodes_all_utility
        (st := st₀) (st₀.ctxDeps Γ) (hdeps := st₀.depsOfVars_lt _)
        (ufn := fun who raw => ((evalPayoffs u (ρ raw)) who : ℝ))
        (players := Finset.univ.toList) (i := nd) hge
    have hstep : ∀ (nd : Fin st.nextId)
        (hwho : ∃ who, (st.descAt nd).kind = .utility who) (acc : PMF (TAssign st.toStruct)),
        PMF.map extract (evalStep st.toStruct (MAIDCompileState.toSem st) pol acc nd) =
        PMF.map extract acc := by
      intro nd hwho acc
      simp only [evalStep, PMF.map_bind]
      congr 1
      funext a
      obtain ⟨w, hw⟩ := hwho
      have hkind : st.toStruct.kind nd = .utility w := by
        simp only [toStruct_kind]
        exact hw
      conv_lhs =>
        rw [show (fun a_1 => PMF.map extract (PMF.pure (updateAssign a nd a_1))) =
          (fun a_1 => PMF.pure (extract (updateAssign a nd a_1))) from
          funext fun v => PMF.pure_map extract (updateAssign a nd v)]
      simp only [nodeDist]
      split
      · rename_i hk
        simp only [toStruct_kind] at hk
        rw [hk] at hw
        exact absurd hw (by simp)
      · rename_i p hk
        simp only [toStruct_kind] at hk
        rw [hk] at hw
        exact absurd hw (by simp)
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
    simp [extract, extractOutcomeAux, nativeOutcomeDistPMFV]
    rfl
  · intro β pol env hpol hraw
    rfl

private theorem bridgeInv_letExpr
    (B : MAIDBackend Player L)
    {Γ' : VCtx Player L} {x : VarId} {b : L.Ty}
    (e : L.Expr (erasePubVCtx Γ') b)
    (k : VegasCore Player L ((x, .pub b) :: Γ'))
    (ih : ∀ (hl : Legal k) (hd : NormalizedDists k) (hfresh : FreshBindings k)
      (ρ : RawNodeEnv L → VEnv (Player := Player) L ((x, .pub b) :: Γ'))
      (st₀ : MAIDCompileState Player L B)
      (hvars : st₀.VarsSubCtx ((x, .pub b) :: Γ'))
      (hρ_deps : ∀ j, j ∉ (st₀.ctxDeps ((x, .pub b) :: Γ') : Finset Nat) → InsensitiveTo ρ j)
      (hρ_var : EnvRespectsLookupDeps st₀ ρ)
      (hnodup : (((x, .pub b) :: Γ').map Prod.fst).Nodup),
      BridgeInv B k hl hd hfresh ρ st₀ hvars hρ_deps hρ_var hnodup)
    (hl : Legal (.letExpr x e k)) (hd : NormalizedDists (.letExpr x e k))
    (hfresh : FreshBindings (.letExpr x e k))
    (ρ : RawNodeEnv L → VEnv (Player := Player) L Γ')
    (st₀ : MAIDCompileState Player L B)
    (hvars : st₀.VarsSubCtx Γ')
    (hρ_deps : ∀ j, j ∉ (st₀.ctxDeps Γ' : Finset Nat) → InsensitiveTo ρ j)
    (hρ_var : EnvRespectsLookupDeps st₀ ρ)
    (hnodup : (Γ'.map Prod.fst).Nodup) :
    BridgeInv B (.letExpr x e k) hl hd hfresh ρ st₀ hvars hρ_deps hρ_var hnodup := by
  letI := B.fintypePlayer
  refine ⟨?_, ?_⟩
  · intro hρ_readers hρ_readval pol a₀
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
      · intro j hj
        exact hout j (by simp only [st₁, MAIDCompileState.addVar] at hj ⊢; exact hj)
      · intro j hj hjlt
        exact hnot_vd j (fun hmem => hj (hVD ▸ hmem))
          (by simp only [st₁, MAIDCompileState.addVar]; exact hjlt)
      · intro j hj hjlt
        exact htyped j (hVD ▸ hj) (by simp only [st₁, MAIDCompileState.addVar]; exact hjlt)
      · exact hview_old
      · rwa [hVD] at hi
    exact (ih hl hd hfresh.2 ρ' st₁
      (st₀.VarsSubCtx_letExpr_step hvars x hxΓ) hρ'_deps hρ'_var
      (List.nodup_cons.mpr ⟨hxΓ, hnodup⟩)).fold_eq
      hρ'_readers
      (fun y who' bt hy hne_deps => by
        cases hy with
        | there hy' =>
          have hne : y ≠ x := fun h => hxΓ (h.symm ▸ hy'.mem_map_fst)
          have hne_deps' : (st₀.lookupDeps y).Nonempty := by
            rwa [show st₁.lookupDeps y = st₀.lookupDeps y from by
              simp [st₁, st₀.lookupDeps_addVar_eq_of_ne x (.pub b)
                (st₀.pubCtxDeps Γ') (st₀.depsOfVars_lt _) hne]] at hne_deps
          rcases hρ_readval y who' bt hy' hne_deps' with ⟨j, hjlt, hld, hdesc_j, hget⟩
          exact ⟨j, hjlt, by
              simp [st₁, st₀.lookupDeps_addVar_eq_of_ne x (.pub b)
                (st₀.pubCtxDeps Γ') (st₀.depsOfVars_lt _) hne, hld],
            hdesc_j, fun raw => by
              simpa [ρ', VEnv.get, VEnv.cons_get_there] using hget raw⟩)
      pol a₀
  · intro β pol env hpol ⟨raw₀, hraw₀, hraw_typed, hraw_hi⟩
    have hxΓ : Fresh x _ := hfresh.1
    exact (ih hl hd hfresh.2 _ _
      (st₀.VarsSubCtx_letExpr_step hvars x hxΓ)
      (fun j hj raw tv => by
        have hρj := hρ_deps j (fun h => hj (by
          simp only [MAIDCompileState.ctxDeps, MAIDCompileState.depsOfVars, List.map,
            MAIDCompileState.depsOfVars_addVar_eq_of_fresh _ _ _ _ _ _ hxΓ] at h ⊢
          exact Finset.mem_union_right _ h)) raw tv
        simp [hρj])
      (envRespectsLookupDeps_letExpr st₀ ρ hρ_var e hxΓ
        (fun hmem => hxΓ (hvars x hmem)))
      (List.nodup_cons.mpr ⟨hxΓ, hnodup⟩)).behavioral_eq
      β pol _ hpol
      ⟨raw₀, by simp [hraw₀], hraw_typed, hraw_hi⟩

private theorem bridgeInv
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
    (hnodup : (Γ.map Prod.fst).Nodup) :
    BridgeInv B p hl hd hfresh ρ st₀ hvars hρ_deps hρ_var hnodup := by
  letI := B.fintypePlayer
  induction p generalizing st₀ with
  | ret u =>
      exact bridgeInv_ret B u hl hd hfresh ρ st₀ hvars hρ_deps hρ_var hnodup
  | letExpr x e k ih =>
      exact bridgeInv_letExpr B e k ih hl hd hfresh ρ st₀ hvars hρ_deps hρ_var hnodup
  | sample x τ m D' k ih =>
      rename_i Γ'
      refine ⟨?_, ?_⟩
      · intro hρ_readers hρ_readval pol a₀
        have hxΓ : Fresh x Γ' := hfresh.1
        have hxvars : x ∉ st₀.vars.map Prod.fst := fun hxmem => hxΓ (hvars x hxmem)
        let cpdFDist : RawNodeEnv L → FDist (L.Val τ.base) := fun raw =>
          L.evalDist D' (VEnv.eraseDistEnv τ m (ρ raw))
        let cpdNorm : ∀ raw, FDist.totalWeight (cpdFDist raw) = 1 := fun raw => hd.1 _
        let nd : CompiledNode Player L B := .chance τ.base (st₀.ctxDeps Γ') cpdFDist cpdNorm
        have hndeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st₀.nextId := by
          intro d hd'
          have hd'' : d ∈ st₀.ctxDeps Γ' := by
            simpa [CompiledNode.parents, CompiledNode.obsParents] using hd'
          exact st₀.depsOfVars_lt _ d hd''
        let stNode := (st₀.addNode nd hndeps).2
        let st₁ := stNode.addVar x τ ({st₀.nextId}) (by
          intro d hd'; have := Finset.mem_singleton.mp hd'; subst d
          exact Nat.lt_succ_self st₀.nextId)
        let ρ' : RawNodeEnv L → VEnv (Player := Player) L ((x, τ) :: Γ') :=
          fun raw => VEnv.cons (MAIDCompileState.readVal (B := B) raw τ.base st₀.nextId) (ρ raw)
        have hvars₁ : st₁.VarsSubCtx ((x, τ) :: Γ') := by
          simpa [st₁, stNode, nd] using
            st₀.VarsSubCtx_addNode_addVar_singleton_step hvars nd hndeps x τ hxΓ
        have hctx₁ : st₁.ctxDeps ((x, τ) :: Γ') = {st₀.nextId} ∪ st₀.ctxDeps Γ' := by
          simpa [st₁, stNode, nd] using
            st₀.ctxDeps_addNode_addVar_singleton_cons_eq_of_fresh nd hndeps x τ hxΓ hxvars
        have hρ'_deps : ∀ j, j ∉ st₁.ctxDeps ((x, τ) :: Γ') → InsensitiveTo ρ' j := by
          intro j hj raw tv
          have hjid : j ≠ st₀.nextId := by intro hEq; apply hj; simp [hctx₁, hEq]
          have hj' : j ∉ st₀.ctxDeps Γ' := by intro hmem; apply hj; simp [hctx₁, hmem]
          have hρj := hρ_deps j hj' raw tv
          exact VEnv.cons_ext (readVal_extend_ne raw j st₀.nextId tv τ.base hjid.symm) hρj
        have hρ'_var : EnvRespectsLookupDeps st₁ ρ' := by
          intro y σ hy j hj raw tv
          cases hy with
          | here =>
              have hlookup : st₁.lookupDeps x = ({st₀.nextId} : Finset Nat) := by
                simpa [st₁] using stNode.lookupDeps_addVar_eq_self_of_fresh x τ {st₀.nextId}
                  (by intro d hd'; have := Finset.mem_singleton.mp hd'; subst d
                      exact Nat.lt_succ_self st₀.nextId)
                  (by simpa [stNode, MAIDCompileState.addNode] using hxvars)
              have hjid : j ≠ st₀.nextId := by
                simpa [Finset.mem_singleton] using (show j ∉ ({st₀.nextId} : Finset Nat) by
                  simpa [hlookup] using hj)
              simpa [ρ', VEnv.get, readVal_extend_ne, hjid] using
                (readVal_extend_ne (B := B) raw j st₀.nextId tv τ.base hjid.symm)
          | there hy' =>
              have hxy : y ≠ x := fun hEq => hxΓ (hEq.symm ▸ hy'.mem_map_fst)
              have hlookupVar : st₁.lookupDeps y = stNode.lookupDeps y := by
                simpa [st₁] using stNode.lookupDeps_addVar_eq_of_ne x τ {st₀.nextId}
                  (by intro d hd'; have := Finset.mem_singleton.mp hd'; subst d
                      exact Nat.lt_succ_self st₀.nextId) hxy
              have hlookupNode : stNode.lookupDeps y = st₀.lookupDeps y := by
                simpa [stNode] using st₀.lookupDeps_addNode nd hndeps y
              have hj' : j ∉ st₀.lookupDeps y := by simpa [hlookupVar, hlookupNode] using hj
              simpa [ρ', VEnv.get, VEnv.cons_get_there] using hρ_var hy' j hj' raw tv
        let st := MAIDCompileState.ofProg B k hl hd.2 ρ' st₁
        have hid_lt : st₀.nextId < st.nextId :=
          Nat.lt_of_lt_of_le (by
            simp [st₁, stNode, MAIDCompileState.addVar, MAIDCompileState.addNode])
            (MAIDCompileState.ofProg_nextId_le B k hl hd.2 ρ' st₁)
        let nd0 : Fin st.nextId := ⟨st₀.nextId, hid_lt⟩
        have hdrop :
            (List.finRange st.nextId).drop st₀.nextId =
              nd0 :: (List.finRange st.nextId).drop st₁.nextId := by
          have hlen : st₀.nextId < (List.finRange st.nextId).length := by simpa using hid_lt
          rw [show st₁.nextId = st₀.nextId + 1 by
            simp [st₁, stNode, MAIDCompileState.addVar, MAIDCompileState.addNode]]
          rw [← List.cons_getElem_drop_succ (l := List.finRange st.nextId)
            (n := st₀.nextId) (h := hlen)]
          simp [nd0]
        have hdesc0 : st.descAt nd0 = nd := by
          have hdesc1 := MAIDCompileState.ofProg_descAt_old B k hl hd.2 ρ' st₁ st₀.nextId
            (by simp [st₁, stNode, MAIDCompileState.addVar, MAIDCompileState.addNode])
          rw [hdesc1]
          simpa [st₁, stNode] using st₀.addNode_descAt_new nd hndeps
        have hρeq :
            ρ (st.rawEnvOfCfg (MAID.projCfg a₀ (st.toStruct.parents nd0))) =
              ρ (rawOfTAssign st a₀) := by
          have hrawP : st.rawEnvOfCfg (MAID.projCfg a₀ (st.toStruct.parents nd0)) =
              fun i => if i < st.nextId then
                if i ∈ st₀.ctxDeps Γ' then rawOfTAssign st a₀ i else none else none := by
            apply rawEnvOfCfg_proj_eq_select st a₀ (st.toStruct.parents nd0) (st₀.ctxDeps Γ')
            intro i hi
            simp only [st.mem_toStruct_parents_iff nd0 hi, hdesc0, nd, CompiledNode.parents]
          rw [hrawP]
          simpa using (eq_on_ctxDeps_rawOfTAssign st (deps := st₀.ctxDeps Γ') hρ_deps a₀)
        change PMF.map (fun a => extractOutcomeAux B (.sample x τ m D' k)
          ρ st₀.nextId (rawOfTAssign st a))
          (List.foldl (evalStep st.toStruct st.toSem pol) (PMF.pure a₀)
            ((List.finRange st.nextId).drop st₀.nextId)) =
          nativeOutcomeDistPMFV B (.sample x τ m D' k) hd
            (reflectPolicyAuxV B (.sample x τ m D' k) hl hd ρ st₀ pol) ρ
            st₀.nextId (rawOfTAssign st a₀)
        rw [hdrop, List.foldl_cons]
        simp only [nativeOutcomeDistPMFV, reflectPolicyAuxV]
        simp only [evalStep, PMF.pure_bind]
        rw [foldl_evalStep_bind_left, PMF.map_bind]
        have hst₁_id : st₁.nextId = st₀.nextId + 1 := by
          simp [st₁, stNode, MAIDCompileState.addVar, MAIDCompileState.addNode]
        have hρ'_readers : ViewDeterminesRaw st₁ ((x, τ) :: Γ') ρ' := by
          intro who raw₁ raw₂ hout hnot_vd htyped hview i hi
          have hview_old := projectViewEnv_cons_eq
            (List.nodup_cons.mpr ⟨hxΓ, hnodup⟩) hview
          have hid_lt_st₁ : st₀.nextId < st₁.nextId := by rw [hst₁_id]; omega
          have hx_not_view : x ∉ (viewVCtx who Γ').map Prod.fst :=
            fun hmem => hxΓ (viewVCtx_map_fst_sub hmem)
          have hlt_fwd (j : Nat) (hj : j < st₀.nextId) : j < st₁.nextId := by rw [hst₁_id]; omega
          have hid_not_old : st₀.nextId ∉ st₀.viewDeps who Γ' :=
            fun hmem => absurd (st₀.depsOfVars_lt _ st₀.nextId hmem) (by omega)
          by_cases hsee : canSee who τ
          · have hVD : st₁.viewDeps who ((x, τ) :: Γ') = insert st₀.nextId (st₀.viewDeps who Γ') := by
              unfold MAIDCompileState.viewDeps
              simp only [viewVCtx, hsee, ite_true, List.map_cons, MAIDCompileState.depsOfVars]
              rw [stNode.lookupDeps_addVar_eq_self_of_fresh x τ {st₀.nextId}
                  (by
                    intro d hd_
                    simp only [Finset.mem_singleton] at hd_
                    subst hd_
                    exact Nat.lt_succ_self _)
                  (by simpa [stNode, MAIDCompileState.addNode] using hxvars),
                stNode.depsOfVars_addVar_eq_of_not_mem x τ _ _ _ hx_not_view,
                Finset.singleton_union]
              congr 1
              induction (viewVCtx who Γ').map Prod.fst with
              | nil => rfl
              | cons y ys ih_vd =>
                simp [stNode, MAIDCompileState.depsOfVars, st₀.lookupDeps_addNode nd hndeps, ih_vd]
            have hraw_id_eq : raw₁ st₀.nextId = raw₂ st₀.nextId := by
              have hhead := projectViewEnv_cons_head_eq
                (List.nodup_cons.mpr ⟨hxΓ, hnodup⟩) hsee hview
              have htyped_id := htyped st₀.nextId (by
                rw [hVD]
                exact Finset.mem_insert_self _ _) hid_lt_st₁
              have hdesc_id : st₁.descAt ⟨st₀.nextId, hid_lt_st₁⟩ = nd :=
                MAIDCompileState.addNode_descAt_new st₀ nd hndeps
              simp only [RawsMatchDescAt, hdesc_id, nd] at htyped_id
              rcases htyped_id with ⟨v₁, v₂, hraw₁, hraw₂⟩
              have hr₁ : MAIDCompileState.readVal (B := B) raw₁ τ.base st₀.nextId = v₁ := by
                simp [MAIDCompileState.readVal, hraw₁]
              have hr₂ : MAIDCompileState.readVal (B := B) raw₂ τ.base st₀.nextId = v₂ := by
                simp [MAIDCompileState.readVal, hraw₂]
              rw [hr₁, hr₂] at hhead; rw [hraw₁, hraw₂, hhead]
            rw [hVD] at hi
            rcases Finset.mem_insert.mp hi with rfl | hold
            · exact hraw_id_eq
            · apply hρ_readers who raw₁ raw₂
              · intro j hj; by_cases hjid : j = st₀.nextId
                · subst hjid; exact hraw_id_eq
                · exact hout j (by rw [hst₁_id]; omega)
              · intro j hj hjlt
                exact hnot_vd j (fun hmem => hj (by
                  rw [hVD] at hmem; rcases Finset.mem_insert.mp hmem with rfl | h
                  · exact absurd hjlt (by omega)
                  · exact h)) (hlt_fwd j hjlt)
              · intro j hj hjlt
                exact RawsMatchDescAt_of_descAt_eq
                  (MAIDCompileState.addNode_descAt_old st₀ nd hndeps ⟨j, hjlt⟩)
                  (htyped j (by rw [hVD]; exact Finset.mem_insert_of_mem hj) (hlt_fwd j hjlt))
              · exact hview_old
              · exact hold
          · have hVD : st₁.viewDeps who ((x, τ) :: Γ') = st₀.viewDeps who Γ' := by
              unfold MAIDCompileState.viewDeps
              have hcf : canSee who τ = false := by
                cases h : canSee who τ
                · rfl
                · exact absurd h hsee
              simp only [viewVCtx, hcf, ite_false, Bool.false_eq_true]
              rw [stNode.depsOfVars_addVar_eq_of_not_mem x τ _ _ _ hx_not_view]
              induction (viewVCtx who Γ').map Prod.fst with
              | nil => rfl
              | cons y ys ih_vd =>
                simp [stNode, MAIDCompileState.depsOfVars, st₀.lookupDeps_addNode nd hndeps, ih_vd]
            apply hρ_readers who raw₁ raw₂
            · intro j hj; by_cases hjid : j = st₀.nextId
              · subst hjid; exact hnot_vd st₀.nextId (by rw [hVD]; exact hid_not_old) hid_lt_st₁
              · exact hout j (by rw [hst₁_id]; omega)
            · intro j hj hjlt
              exact hnot_vd j (fun hmem => hj (by rwa [hVD] at hmem)) (hlt_fwd j hjlt)
            · intro j hj hjlt
              exact RawsMatchDescAt_of_descAt_eq
                (MAIDCompileState.addNode_descAt_old st₀ nd hndeps ⟨j, hjlt⟩)
                (htyped j (by rw [hVD]; exact hj) (hlt_fwd j hjlt))
            · exact hview_old
            · rwa [hVD] at hi
        have hρ'_readval : EnvReadValAtDeps st₁ ((x, τ) :: Γ') ρ' := by
          intro z who_z bz hz hne_z
          have hlN : ∀ w, stNode.lookupDeps w = st₀.lookupDeps w :=
            fun w => by simp [stNode, MAIDCompileState.addNode, MAIDCompileState.lookupDeps]
          cases hz with
          | here =>
            exact ⟨st₀.nextId, by rw [hst₁_id]; omega,
              stNode.lookupDeps_addVar_eq_self_of_fresh x (.hidden who_z bz) {st₀.nextId}
                (by
                  intro d hd'
                  simp only [Finset.mem_singleton] at hd'
                  subst hd'
                  exact Nat.lt_succ_self _)
                (by simpa [stNode, MAIDCompileState.addNode] using hxvars),
              by have := MAIDCompileState.addNode_descAt_new st₀ nd hndeps
                 simp only [show st₁.descAt ⟨st₀.nextId, _⟩ = nd from this, nd]; rfl,
              fun _ => rfl⟩
          | there hy' =>
            have hne : z ≠ x := fun h => hxΓ (h.symm ▸ hy'.mem_map_fst)
            have hld_st₁_st₀ : st₁.lookupDeps z = st₀.lookupDeps z := by
              simp [st₁, stNode.lookupDeps_addVar_eq_of_ne x _ _ _ hne, hlN]
            have hne_z' : (st₀.lookupDeps z).Nonempty := by rwa [← hld_st₁_st₀]
            rcases hρ_readval z who_z bz hy' hne_z' with ⟨j, hjlt, hj_sing, hdesc_j, hget⟩
            have hdesc_fwd : st₁.descAt ⟨j, by rw [hst₁_id]; omega⟩ = st₀.descAt ⟨j, hjlt⟩ :=
              MAIDCompileState.addNode_descAt_old st₀ nd hndeps ⟨j, hjlt⟩
            exact ⟨j, by rw [hst₁_id]; omega, by rwa [hld_st₁_st₀],
              by simp only [hdesc_fwd]; exact hdesc_j,
              fun raw => by simpa [ρ', VEnv.get, VEnv.cons_get_there] using hget raw⟩
        have hinner : ∀ v, PMF.map (fun a => extractOutcomeAux B (.sample x τ m D' k) ρ
              st₀.nextId (rawOfTAssign st a))
            (List.foldl (evalStep st.toStruct st.toSem pol)
              (PMF.pure (updateAssign a₀ nd0 v))
              ((List.finRange st.nextId).drop st₁.nextId)) =
          nativeOutcomeDistPMFV B k hd.2 (reflectPolicyAuxV B k hl hd.2 ρ' st₁ pol)
            ρ' (st₀.nextId + 1) (rawOfTAssign st (updateAssign a₀ nd0 v)) := by
          intro v; rw [← hst₁_id]
          exact (ih hl hd.2 hfresh.2 ρ' st₁ hvars₁ hρ'_deps hρ'_var
            (List.nodup_cons.mpr ⟨hxΓ, hnodup⟩)).fold_eq
            hρ'_readers hρ'_readval pol _
        simp_rw [hinner]
        have hraw : ∀ v, rawOfTAssign st (updateAssign a₀ nd0 v) =
            (rawOfTAssign st a₀).extend st₀.nextId ⟨τ.base, castValType hdesc0 v⟩ :=
          fun v => rawOfTAssign_updateAssign_of_tagged st a₀ nd0 v _ (taggedOfVal_chance_cast hdesc0 v)
        simp_rw [hraw]
        simp only [nodeDist]
        have hkind_chance : (st.descAt nd0).kind = .chance := by
          simp [hdesc0, nd, CompiledNode.kind]
        split
        · simp only [MAIDCompileState.toSem]
          split
          · rename_i hk τ₁ deps₁ cpd₁ norm₁ hdesc₁
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
                (st₀.nextId + 1) ((rawOfTAssign st a₀).extend st₀.nextId ⟨τ.base, w⟩)
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
      · intro β pol env hpol ⟨raw₀, hraw₀, hraw_typed, hraw_hi⟩
        simp only [outcomeDistBehavioralPMF]
        have hxΓ : Fresh x _ := hfresh.1
        have hxvars : x ∉ st₀.vars.map Prod.fst := fun hmem => hxΓ (hvars x hmem)
        let nd : CompiledNode Player L B := .chance τ.base (st₀.ctxDeps Γ')
          (fun raw => L.evalDist D' (VEnv.eraseDistEnv τ m (ρ raw))) (fun raw => hd.1 _)
        have hndeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st₀.nextId := by
          intro d hd'; rcases Finset.mem_union.mp hd' with h | h <;>
            simpa [CompiledNode.parents, CompiledNode.obsParents, nd] using st₀.depsOfVars_lt _ d h
        let stNode := (st₀.addNode nd hndeps).2
        let st₁ := stNode.addVar x τ {st₀.nextId} (by
          intro d hd₁; simp only [Finset.mem_singleton] at hd₁; subst hd₁
          exact Nat.lt_succ_self _)
        congr 1
        funext v
        exact (ih hl hd.2 hfresh.2 _ _
          (st₀.VarsSubCtx_addNode_addVar_singleton_step hvars _ _ x τ hxΓ)
          (fun j hj raw tv => by
            have hne : j ≠ st₀.nextId := by
              intro heq; subst heq; apply hj
              simp only [MAIDCompileState.ctxDeps, MAIDCompileState.depsOfVars, List.map,
                MAIDCompileState.addNode, MAIDCompileState.addVar]
              apply Finset.mem_union_left
              simp only [MAIDCompileState.lookupDeps]
              rw [lookupDepsAux_append_singleton_eq_self_of_fresh _ _ _ _ hxvars]
              exact Finset.mem_singleton_self _
            exact VEnv.cons_ext
              (readVal_extend_ne raw j st₀.nextId tv τ.base (Ne.symm hne))
              (hρ_deps j (fun h => hj (by
                simp only [MAIDCompileState.ctxDeps, MAIDCompileState.depsOfVars, List.map] at h ⊢
                rw [MAIDCompileState.depsOfVars_addVar_eq_of_fresh _ _ _ _ _ _ hxΓ,
                  MAIDCompileState.depsOfVars_addNode_eq]
                exact Finset.mem_union_right _ h)) raw tv))
          (envRespectsLookupDeps_sample st₀ ρ hρ_var D' (fun env => hd.1 env) hxΓ hxvars)
          (List.nodup_cons.mpr ⟨hfresh.1, hnodup⟩)).behavioral_eq
          β pol _
          (fun who I hge => hpol who I
            (le_trans (by simp [MAIDCompileState.addVar, MAIDCompileState.addNode]) hge))
          ⟨RawNodeEnv.extend raw₀ st₀.nextId ⟨τ.base, v⟩, by
            constructor
            · change VEnv.cons (MAIDCompileState.readVal
                (RawNodeEnv.extend raw₀ st₀.nextId ⟨τ.base, v⟩) τ.base st₀.nextId)
                (ρ (RawNodeEnv.extend raw₀ st₀.nextId ⟨τ.base, v⟩)) = VEnv.cons v env
              rw [show MAIDCompileState.readVal (B := B)
                (RawNodeEnv.extend raw₀ st₀.nextId ⟨τ.base, v⟩) τ.base st₀.nextId = v from by
                simp [RawNodeEnv.extend, MAIDCompileState.readVal]]
              rw [show ρ (RawNodeEnv.extend raw₀ st₀.nextId ⟨τ.base, v⟩) = env from by
                 rw [hρ_deps st₀.nextId
                    (by intro h; exact absurd (st₀.depsOfVars_lt _ _ h) (by omega))
                    raw₀ ⟨τ.base, v⟩, hraw₀]]
            · exact ⟨(rawWitness_extend_addNode_addVar st₀ nd hndeps (x := x) (τ := τ) raw₀
                  hraw_typed hraw_hi ⟨τ.base, v⟩
                  ⟨v, by simp [nd, MAIDCompileState.taggedOfVal]⟩).1,
                (rawWitness_extend_addNode_addVar st₀ nd hndeps (x := x) (τ := τ) raw₀
                  hraw_typed hraw_hi ⟨τ.base, v⟩
                  ⟨v, by simp [nd, MAIDCompileState.taggedOfVal]⟩).2⟩⟩
  | reveal y who x hx k ih =>
      rename_i Γ' b
      refine ⟨?_, ?_⟩
      · intro hρ_readers hρ_readval pol a₀
        have hyΓ : Fresh y Γ' := hfresh.1
        have hyvars : y ∉ st₀.vars.map Prod.fst := fun hymem => hyΓ (hvars y hymem)
        let ρ' : RawNodeEnv L → VEnv (Player := Player) L ((y, .pub b) :: Γ') :=
          fun raw =>
            let v := VEnv.get (L := L) (ρ raw) hx
            VEnv.cons (L := L) (x := y) (τ := .pub b) v (ρ raw)
        let st₁ := st₀.addVar y (.pub b) (st₀.lookupDeps x) (st₀.lookupDeps_lt x)
        have hvars₁ : st₁.VarsSubCtx ((y, .pub b) :: Γ') := by
          simpa [st₁] using st₀.VarsSubCtx_addVar hvars y _ _ _ hyΓ
        have hctx₁ : st₁.ctxDeps ((y, .pub b) :: Γ') = st₀.ctxDeps Γ' := by
          simpa [st₁] using st₀.ctxDeps_reveal_step y who x hx hyΓ hyvars
        have hρ'_deps : ∀ j, j ∉ st₁.ctxDeps ((y, .pub b) :: Γ') → InsensitiveTo ρ' j := by
          intro j hj raw tv
          have hj' : j ∉ st₀.ctxDeps Γ' := by simpa [hctx₁] using hj
          have hρj := hρ_deps j hj' raw tv
          simp only [ρ', hρj]
        have hρ'_var : EnvRespectsLookupDeps st₁ ρ' := by
          intro z σ hz j hj raw tv
          cases hz with
          | here =>
              have hj' : j ∉ st₀.lookupDeps x := by
                simpa [st₁, st₀.lookupDeps_addVar_eq_self_of_fresh y (.pub b) (st₀.lookupDeps x)
                  (st₀.lookupDeps_lt x) hyvars] using hj
              simpa [ρ', VEnv.get] using hρ_var hx j hj' raw tv
          | there hz' =>
              have hzy : z ≠ y := fun hEq => hyΓ (hEq.symm ▸ hz'.mem_map_fst)
              have hj' : j ∉ st₀.lookupDeps z := by
                simpa [st₁, st₀.lookupDeps_addVar_eq_of_ne y (.pub b) (st₀.lookupDeps x)
                  (st₀.lookupDeps_lt x) hzy] using hj
              simpa [ρ', VEnv.get, VEnv.cons_get_there] using hρ_var hz' j hj' raw tv
        have hρ'_readers : ViewDeterminesRaw st₁ ((y, .pub b) :: Γ') ρ' := by
          intro who' raw₁ raw₂ hout hnot_vd htyped hview i hi
          have hview_old := projectViewEnv_cons_eq
            (List.nodup_cons.mpr ⟨hyΓ, hnodup⟩) hview
          have hy_not_view : y ∉ (viewVCtx who' Γ').map Prod.fst := fun hmem =>
            hyΓ (viewVCtx_map_fst_sub hmem)
          have hVD : st₁.viewDeps who' ((y, .pub b) :: Γ') =
              st₀.lookupDeps x ∪ st₀.viewDeps who' Γ' := by
            unfold MAIDCompileState.viewDeps
            simp only [viewVCtx, canSee, ite_true, List.map_cons, MAIDCompileState.depsOfVars]
            rw [st₀.lookupDeps_addVar_eq_self_of_fresh y (.pub b) (st₀.lookupDeps x)
                (st₀.lookupDeps_lt x) hyvars,
              st₀.depsOfVars_addVar_eq_of_not_mem y (.pub b) _ _ _ hy_not_view]
          have hhead := projectViewEnv_cons_head_eq
            (List.nodup_cons.mpr ⟨hyΓ, hnodup⟩) (by simp [canSee]) hview
          have hraw_lookup_eq : ∀ j ∈ st₀.lookupDeps x, raw₁ j = raw₂ j := by
            intro j hj_mem
            rcases hρ_readval x who _ hx ⟨j, hj_mem⟩ with
              ⟨k, hklt, hsingleton, hdescAt_type, hreadval⟩
            have hjk : j = k := Finset.mem_singleton.mp (hsingleton ▸ hj_mem)
            subst hjk
            rw [hreadval raw₁, hreadval raw₂] at hhead
            have hj_vd := hVD ▸ Finset.mem_union_left _ hj_mem
            have htyped_j := htyped j hj_vd (by simp only [MAIDCompileState.addVar, st₁]; exact hklt)
            simp only [RawsMatchDescAt,
              show st₁.descAt ⟨j, _⟩ = st₀.descAt ⟨j, hklt⟩ from rfl] at htyped_j
            revert htyped_j hdescAt_type
            match st₀.descAt ⟨j, hklt⟩ with
            | .chance τ _ _ _ | .decision τ _ _ _ _ _ =>
                intro hτb ⟨v₁, v₂, hraw₁, hraw₂⟩
                subst hτb
                exact readVal_tagged_eq hraw₁ hraw₂ hhead
            | .utility _ _ _ =>
                intro _ ⟨h₁, h₂⟩
                rw [h₁, h₂]
          rw [hVD] at hi
          rcases Finset.mem_union.mp hi with hi_lookup | hi_old
          · exact hraw_lookup_eq i hi_lookup
          · apply hρ_readers who' raw₁ raw₂
            · intro j hj
              exact hout j (by simp only [st₁, MAIDCompileState.addVar] at hj ⊢; exact hj)
            · intro j hj hjlt
              by_cases hj_lookup : j ∈ st₀.lookupDeps x
              · exact hraw_lookup_eq j hj_lookup
              · exact hnot_vd j (fun hmem => by
                  rw [hVD] at hmem
                  rcases Finset.mem_union.mp hmem with h | h
                  · exact hj_lookup h
                  · exact hj h) (by simp only [st₁, MAIDCompileState.addVar]; exact hjlt)
            · intro j hj hjlt
              exact htyped j (by rw [hVD]; exact Finset.mem_union_right _ hj)
                (by simp only [st₁, MAIDCompileState.addVar]; exact hjlt)
            · exact hview_old
            · exact hi_old
        exact (ih hl hd hfresh.2 ρ' st₁ hvars₁ hρ'_deps hρ'_var
          (List.nodup_cons.mpr ⟨hyΓ, hnodup⟩)).fold_eq
          hρ'_readers
          (fun z who_z bz hz hne_z => by
            cases hz with
            | there hy' =>
              have hne : z ≠ y := fun h => hyΓ (h.symm ▸ hy'.mem_map_fst)
              have hld_eq : st₁.lookupDeps z = st₀.lookupDeps z := by
                simp [st₁, st₀.lookupDeps_addVar_eq_of_ne y (.pub _) _ _ hne]
              have hne_z' : (st₀.lookupDeps z).Nonempty := by rwa [← hld_eq]
              rcases hρ_readval z who_z bz hy' hne_z' with ⟨j, hjlt, hj_sing, hdesc_j, hget⟩
              exact ⟨j, hjlt, by rwa [hld_eq], hdesc_j,
                fun raw => by simpa [ρ', VEnv.get, VEnv.cons_get_there] using hget raw⟩)
          pol a₀
      · intro β pol env hpol ⟨raw₀, hraw₀, hraw_typed, hraw_hi⟩
        simp only [outcomeDistBehavioralPMF, reflectPolicyAuxV,
          ProgramBehavioralProfile.toPMFProfile]
        have hyΓ : Fresh y _ := hfresh.1
        have hyvars : y ∉ st₀.vars.map Prod.fst := fun hmem => hyΓ (hvars y hmem)
        exact (ih hl hd hfresh.2 _ _
          (st₀.VarsSubCtx_addVar hvars y (.pub _) _ _ hyΓ)
          (fun j hj raw tv => by
            have hρj := hρ_deps j (fun h => hj (by
              simp only [MAIDCompileState.ctxDeps] at h ⊢
              simp only [MAIDCompileState.depsOfVars, List.map,
                MAIDCompileState.depsOfVars_addVar_eq_of_fresh _ _ _ _ _ _ hyΓ] at h ⊢
              exact Finset.mem_union_right _ h)) raw tv
            simp [hρj])
          (envRespectsLookupDeps_reveal st₀ ρ hρ_var hx hyΓ hyvars)
          (List.nodup_cons.mpr ⟨hyΓ, hnodup⟩)).behavioral_eq
          β pol _ hpol ⟨raw₀, by simp [hraw₀], hraw_typed, hraw_hi⟩
  | commit x who_commit R k ih =>
      rename_i Γ' b
      refine ⟨?_, ?_⟩
      · intro hρ_readers hρ_readval pol a₀
        have hxΓ : Fresh x Γ' := hfresh.1
        have hxvars : x ∉ st₀.vars.map Prod.fst := fun hxmem => hxΓ (hvars x hxmem)
        let nd : CompiledNode Player L B := .decision b who_commit (allValues B b)
          (allValues_ne_nil B b) (allValues_nodup B b) (st₀.viewDeps who_commit Γ')
        have hndeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st₀.nextId := by
          intro d hd'; have hd'' : d ∈ (st₀.viewDeps who_commit Γ') := by
            simpa [nd, CompiledNode.parents, CompiledNode.obsParents] using hd'
          exact st₀.depsOfVars_lt _ d hd''
        let stNode := (st₀.addNode nd hndeps).2
        let st₁ := stNode.addVar x (.hidden who_commit b) ({st₀.nextId}) (by
          intro d hd'; have := Finset.mem_singleton.mp hd'; subst d; exact Nat.lt_succ_self st₀.nextId)
        let ρ' : RawNodeEnv L → VEnv (Player := Player) L ((x, .hidden who_commit b) :: Γ') :=
          fun raw => VEnv.cons (τ := .hidden who_commit b)
            (MAIDCompileState.readVal (B := B) raw b st₀.nextId) (ρ raw)
        have hvars₁ : st₁.VarsSubCtx ((x, .hidden who_commit b) :: Γ') := by
          simpa [st₁, stNode, nd] using
            st₀.VarsSubCtx_addNode_addVar_singleton_step hvars nd hndeps x (.hidden who_commit b) hxΓ
        have hctx₁ : st₁.ctxDeps ((x, .hidden who_commit b) :: Γ') = {st₀.nextId} ∪ st₀.ctxDeps Γ' := by
          simpa [st₁, stNode, nd] using
            st₀.ctxDeps_addNode_addVar_singleton_cons_eq_of_fresh nd hndeps x
              (.hidden who_commit b) hxΓ hxvars
        have hρ'_deps : ∀ j, j ∉ st₁.ctxDeps ((x, .hidden who_commit b) :: Γ') →
            InsensitiveTo ρ' j := by
          intro j hj raw tv
          have hjid : j ≠ st₀.nextId := by intro hEq; apply hj; simp [hctx₁, hEq]
          have hj' : j ∉ st₀.ctxDeps Γ' := by intro hmem; apply hj; simp [hctx₁, hmem]
          exact VEnv.cons_ext (readVal_extend_ne raw j st₀.nextId tv b hjid.symm) (hρ_deps j hj' raw tv)
        have hρ'_var : EnvRespectsLookupDeps st₁ ρ' := by
          intro y σ hy j hj raw tv
          cases hy with
          | here =>
              have hlookup : st₁.lookupDeps x = ({st₀.nextId} : Finset Nat) := by
                simpa [st₁] using
                    stNode.lookupDeps_addVar_eq_self_of_fresh x (.hidden who_commit b) {st₀.nextId}
                  (by
                    intro d hd'
                    have := Finset.mem_singleton.mp hd'
                    subst d
                    exact Nat.lt_succ_self st₀.nextId)
                  (by simpa [stNode, MAIDCompileState.addNode] using hxvars)
              have hjid : j ≠ st₀.nextId := by
                simpa [Finset.mem_singleton]
                  using (show j ∉ ({st₀.nextId} : Finset Nat) by simpa [hlookup] using hj)
              simpa [ρ', VEnv.get, readVal_extend_ne, hjid] using
                (readVal_extend_ne (B := B) raw j st₀.nextId tv b hjid.symm)
          | there hy' =>
              have hxy : y ≠ x := fun hEq => hxΓ (hEq.symm ▸ hy'.mem_map_fst)
              have hlookupVar : st₁.lookupDeps y = stNode.lookupDeps y := by
                simpa [st₁]
                  using stNode.lookupDeps_addVar_eq_of_ne x (.hidden who_commit b) {st₀.nextId}
                    (by
                      intro d hd'
                      have := Finset.mem_singleton.mp hd'
                      subst d
                      exact Nat.lt_succ_self st₀.nextId) hxy
              have hlookupNode : stNode.lookupDeps y = st₀.lookupDeps y := by
                simpa [stNode] using st₀.lookupDeps_addNode nd hndeps y
              have hj' : j ∉ st₀.lookupDeps y := by simpa [hlookupVar, hlookupNode] using hj
              simpa [ρ', VEnv.get, VEnv.cons_get_there] using hρ_var hy' j hj' raw tv
        let st := MAIDCompileState.ofProg B k hl.2 hd ρ' st₁
        have hid_lt : st₀.nextId < st.nextId :=
          Nat.lt_of_lt_of_le (by
            simp [st₁, stNode, MAIDCompileState.addVar, MAIDCompileState.addNode])
            (MAIDCompileState.ofProg_nextId_le B k hl.2 hd ρ' st₁)
        let nd0 : Fin st.nextId := ⟨st₀.nextId, hid_lt⟩
        have hdrop :
            (List.finRange st.nextId).drop st₀.nextId =
              nd0 :: (List.finRange st.nextId).drop st₁.nextId := by
          have hlen : st₀.nextId < (List.finRange st.nextId).length := by simpa using hid_lt
          rw [show st₁.nextId = st₀.nextId + 1 by
            simp [st₁, stNode, MAIDCompileState.addVar, MAIDCompileState.addNode]]
          rw [←List.cons_getElem_drop_succ
            (l := List.finRange st.nextId) (n := st₀.nextId) (h := hlen)]
          simp [nd0]
        have hdesc0 : st.descAt nd0 = nd := by
          have hdesc1 := MAIDCompileState.ofProg_descAt_old B k hl.2 hd ρ' st₁ st₀.nextId
            (by simp [st₁, stNode, MAIDCompileState.addVar, MAIDCompileState.addNode])
          rw [hdesc1]; simpa [st₁, stNode] using st₀.addNode_descAt_new nd hndeps
        have hViewEq :
            projectViewEnv (P := Player) (L := L) who_commit
              (VEnv.eraseEnv (ρ (st.rawEnvOfCfg
                (MAID.projCfg a₀ (st.toStruct.obsParents nd0))))) =
            projectViewEnv (P := Player) (L := L) who_commit
              (VEnv.eraseEnv (ρ (rawOfTAssign st a₀))) := by
          have hrawO : st.rawEnvOfCfg (MAID.projCfg a₀ (st.toStruct.obsParents nd0)) =
              fun i => if i < st.nextId then
                if i ∈ (st₀.viewDeps who_commit Γ') then rawOfTAssign st a₀ i else none else none := by
            apply rawEnvOfCfg_proj_eq_select st a₀
              (st.toStruct.obsParents nd0) (st₀.viewDeps who_commit Γ')
            intro i hi
            simp only [st.mem_toStruct_obsParents_iff nd0 hi, hdesc0, nd, CompiledNode.obsParents]
          rw [hrawO]
          simpa using
            (eq_on_ctxDeps_rawOfTAssign st (deps := st₀.viewDeps who_commit Γ')
              (f := fun raw => projectViewEnv who_commit (VEnv.eraseEnv (ρ raw)))
              (fun j hj =>
                projectViewEnv_insensitive_of_viewDeps st₀ ρ hρ_var who_commit j
                  (by simpa using hj))
              a₀)
        change PMF.map
          (fun a => extractOutcomeAux B (.commit x who_commit R k) ρ st₀.nextId (rawOfTAssign st a))
          (List.foldl (evalStep st.toStruct st.toSem pol) (PMF.pure a₀)
            ((List.finRange st.nextId).drop st₀.nextId)) =
          nativeOutcomeDistPMFV B (.commit x who_commit R k) hd
            (reflectPolicyAuxV B (.commit x who_commit R k) hl hd ρ st₀ pol) ρ
            st₀.nextId (rawOfTAssign st a₀)
        rw [hdrop, List.foldl_cons]
        simp only [nativeOutcomeDistPMFV, reflectPolicyAuxV]
        simp only [evalStep, PMF.pure_bind]
        rw [foldl_evalStep_bind_left, PMF.map_bind]
        have hst₁_id : st₁.nextId = st₀.nextId + 1 := by
          simp [st₁, stNode, MAIDCompileState.addVar, MAIDCompileState.addNode]
        have hρ'_readers : ViewDeterminesRaw st₁ ((x, .hidden who_commit b) :: Γ') ρ' := by
          intro who' raw₁ raw₂ hout hnot_vd htyped hview i hi
          have hview_old := projectViewEnv_cons_eq
            (List.nodup_cons.mpr ⟨hxΓ, hnodup⟩) hview
          have hid_lt_st₁ : st₀.nextId < st₁.nextId := by rw [hst₁_id]; omega
          have hx_not_view : x ∉ (viewVCtx who' Γ').map Prod.fst :=
            fun hmem => hxΓ (viewVCtx_map_fst_sub hmem)
          have hlt_fwd (j : Nat) (hj : j < st₀.nextId) : j < st₁.nextId := by rw [hst₁_id]; omega
          have hid_not_old : st₀.nextId ∉ st₀.viewDeps who' Γ' :=
            fun hmem => absurd (st₀.depsOfVars_lt _ st₀.nextId hmem) (by omega)
          by_cases hsee : canSee who' (BindTy.hidden who_commit b)
          · have hVD : st₁.viewDeps who' ((x, .hidden who_commit b) :: Γ') =
                insert st₀.nextId (st₀.viewDeps who' Γ') := by
              unfold MAIDCompileState.viewDeps
              simp only [viewVCtx, hsee, ite_true, List.map_cons, MAIDCompileState.depsOfVars]
              rw [stNode.lookupDeps_addVar_eq_self_of_fresh x (.hidden who_commit b) {st₀.nextId}
                  (by
                    intro d hd_
                    simp only [Finset.mem_singleton] at hd_
                    subst hd_
                    exact Nat.lt_succ_self _)
                  (by simpa [stNode, MAIDCompileState.addNode] using hxvars),
                stNode.depsOfVars_addVar_eq_of_not_mem x (.hidden who_commit b) _ _ _ hx_not_view,
                Finset.singleton_union]
              congr 1
              induction (viewVCtx who' Γ').map Prod.fst with
              | nil => rfl
              | cons y ys ih_vd =>
                simp [stNode, MAIDCompileState.depsOfVars, st₀.lookupDeps_addNode nd hndeps, ih_vd]
            have hraw_id_eq : raw₁ st₀.nextId = raw₂ st₀.nextId := by
              have hhead := projectViewEnv_cons_head_eq
                (List.nodup_cons.mpr ⟨hxΓ, hnodup⟩) hsee hview
              have htyped_id := htyped st₀.nextId
                (by rw [hVD]; exact Finset.mem_insert_self _ _) hid_lt_st₁
              have hdesc_id : st₁.descAt ⟨st₀.nextId, hid_lt_st₁⟩ = nd :=
                MAIDCompileState.addNode_descAt_new st₀ nd hndeps
              simp only [RawsMatchDescAt, hdesc_id, nd] at htyped_id
              rcases htyped_id with ⟨v₁, v₂, hraw₁, hraw₂⟩
              have hr₁ : MAIDCompileState.readVal (B := B) raw₁ b st₀.nextId = v₁ := by
                simp [MAIDCompileState.readVal, hraw₁]
              have hr₂ : MAIDCompileState.readVal (B := B) raw₂ b st₀.nextId = v₂ := by
                simp [MAIDCompileState.readVal, hraw₂]
              rw [hr₁, hr₂] at hhead; rw [hraw₁, hraw₂, hhead]
            rw [hVD] at hi
            rcases Finset.mem_insert.mp hi with rfl | hold
            · exact hraw_id_eq
            · apply hρ_readers who' raw₁ raw₂
              · intro j hj; by_cases hjid : j = st₀.nextId
                · subst hjid; exact hraw_id_eq
                · exact hout j (by rw [hst₁_id]; omega)
              · intro j hj hjlt
                exact hnot_vd j (fun hmem => hj (by
                  rw [hVD] at hmem; rcases Finset.mem_insert.mp hmem with rfl | h
                  · exact absurd hjlt (by omega)
                  · exact h)) (hlt_fwd j hjlt)
              · intro j hj hjlt
                exact RawsMatchDescAt_of_descAt_eq
                  (MAIDCompileState.addNode_descAt_old st₀ nd hndeps ⟨j, hjlt⟩)
                  (htyped j (by rw [hVD]; exact Finset.mem_insert_of_mem hj) (hlt_fwd j hjlt))
              · exact hview_old
              · exact hold
          · have hVD : st₁.viewDeps who' ((x, .hidden who_commit b) :: Γ') = st₀.viewDeps who' Γ' := by
              unfold MAIDCompileState.viewDeps
              have hcf : canSee who' (BindTy.hidden who_commit b) = false := by
                cases h : canSee who' (BindTy.hidden who_commit b)
                · rfl
                · exact absurd h hsee
              simp only [viewVCtx, hcf, ite_false, Bool.false_eq_true]
              rw [stNode.depsOfVars_addVar_eq_of_not_mem x (.hidden who_commit b) _ _ _ hx_not_view]
              induction (viewVCtx who' Γ').map Prod.fst with
              | nil => rfl
              | cons y ys ih_vd =>
                simp [stNode, MAIDCompileState.depsOfVars, st₀.lookupDeps_addNode nd hndeps, ih_vd]
            apply hρ_readers who' raw₁ raw₂
            · intro j hj; by_cases hjid : j = st₀.nextId
              · subst hjid; exact hnot_vd st₀.nextId (by rw [hVD]; exact hid_not_old) hid_lt_st₁
              · exact hout j (by rw [hst₁_id]; omega)
            · intro j hj hjlt
              exact hnot_vd j (fun hmem => hj (by rwa [hVD] at hmem)) (hlt_fwd j hjlt)
            · intro j hj hjlt
              exact RawsMatchDescAt_of_descAt_eq
                (MAIDCompileState.addNode_descAt_old st₀ nd hndeps ⟨j, hjlt⟩)
                (htyped j (by rw [hVD]; exact hj) (hlt_fwd j hjlt))
            · exact hview_old
            · rwa [hVD] at hi
        have hρ'_readval : EnvReadValAtDeps st₁ ((x, .hidden who_commit b) :: Γ') ρ' := by
          intro z who_z bz hz hne_z
          have hlN : ∀ w, stNode.lookupDeps w = st₀.lookupDeps w :=
            fun w => by simp [stNode, MAIDCompileState.addNode, MAIDCompileState.lookupDeps]
          cases hz with
          | here =>
            exact ⟨st₀.nextId, by rw [hst₁_id]; omega,
              stNode.lookupDeps_addVar_eq_self_of_fresh x (.hidden who_commit b) {st₀.nextId}
                (by
                  intro d hd'
                  simp only [Finset.mem_singleton] at hd'
                  subst hd'
                  exact Nat.lt_succ_self _)
                (by simpa [stNode, MAIDCompileState.addNode] using hxvars),
              by have := MAIDCompileState.addNode_descAt_new st₀ nd hndeps
                 simp only [show st₁.descAt ⟨st₀.nextId, _⟩ = nd from this, nd],
              fun _ => rfl⟩
          | there hy' =>
            have hne : z ≠ x := fun h => hxΓ (h.symm ▸ hy'.mem_map_fst)
            have hld_st₁_st₀ : st₁.lookupDeps z = st₀.lookupDeps z := by
              simp [st₁, stNode.lookupDeps_addVar_eq_of_ne x _ _ _ hne, hlN]
            have hne_z' : (st₀.lookupDeps z).Nonempty := by rwa [← hld_st₁_st₀]
            rcases hρ_readval z who_z bz hy' hne_z' with ⟨j, hjlt, hj_sing, hdesc_j, hget⟩
            have hdesc_fwd : st₁.descAt ⟨j, by rw [hst₁_id]; omega⟩ = st₀.descAt ⟨j, hjlt⟩ :=
              MAIDCompileState.addNode_descAt_old st₀ nd hndeps ⟨j, hjlt⟩
            exact ⟨j, by rw [hst₁_id]; omega, by rwa [hld_st₁_st₀],
              by simp only [hdesc_fwd]; exact hdesc_j,
              fun raw => by simpa [ρ', VEnv.get, VEnv.cons_get_there] using hget raw⟩
        have hinner : ∀ v, PMF.map (fun a => extractOutcomeAux B (.commit x who_commit R k) ρ
              st₀.nextId (rawOfTAssign st a))
            (List.foldl (evalStep st.toStruct st.toSem pol)
              (PMF.pure (updateAssign a₀ nd0 v))
              ((List.finRange st.nextId).drop st₁.nextId)) =
          nativeOutcomeDistPMFV B k hd (reflectPolicyAuxV B k hl.2 hd ρ' st₁ pol)
            ρ' (st₀.nextId + 1) (rawOfTAssign st (updateAssign a₀ nd0 v)) := by
          intro v; rw [← hst₁_id]
          exact (ih hl.2 hd hfresh.2 ρ' st₁ hvars₁ hρ'_deps hρ'_var
            (List.nodup_cons.mpr ⟨hxΓ, hnodup⟩)).fold_eq
            hρ'_readers hρ'_readval pol _
        simp_rw [hinner]
        have hraw : ∀ v, rawOfTAssign st (updateAssign a₀ nd0 v) =
            (rawOfTAssign st a₀).extend st₀.nextId ⟨b, castValType hdesc0 v⟩ := by
          intro v
          exact rawOfTAssign_updateAssign_of_tagged st a₀ nd0 v _ (taggedOfVal_decision_cast hdesc0 v)
        simp_rw [hraw]
        simp only [nodeDist]
        have hkind_decision : (st.descAt nd0).kind = .decision who_commit := by
          simp [hdesc0, nd, CompiledNode.kind]
        split
        · rename_i hk
          rw [toStruct_kind] at hk; rw [hkind_decision] at hk; exact absurd hk (by simp)
        · rename_i p hk
          have hp : p = who_commit := by
            have := (toStruct_kind st nd0).symm.trans hk
            rw [hkind_decision] at this; exact (NodeKind.decision.inj this).symm
          subst hp
          have hprofile : reflectPolicyAuxV B k hl.2 hd ρ' st₁ pol =
              ProgramBehavioralProfilePMF.tail
                (reflectPolicyAuxV B (.commit x p R k) hl hd ρ st₀ pol) := by
            funext i; simp only [reflectPolicyAuxV, ProgramBehavioralProfilePMF.tail,
              ProgramBehavioralStrategyPMF.tailOwn]
            split_ifs with h <;> subst_vars <;> simp only <;> rfl
          have h_ex : ∃ cfg, projectViewEnv p (VEnv.eraseEnv (ρ (st.rawEnvOfCfg cfg))) =
              projectViewEnv p (VEnv.eraseEnv (ρ (rawOfTAssign st a₀))) :=
            ⟨projCfg a₀ (st.toStruct.obsParents nd0), hViewEq⟩
          have cfg_injective : ∀ (h : ∃ cfg, projectViewEnv p
                (VEnv.eraseEnv (ρ (st.rawEnvOfCfg cfg))) =
                projectViewEnv p (VEnv.eraseEnv (ρ (rawOfTAssign st a₀)))),
              Classical.choose h = projCfg a₀ (st.toStruct.obsParents nd0) := by
            intro h
            apply rawEnvOfCfg_injective st; funext j
            by_cases hj_lt : j < st.nextId
            · by_cases hj_mem : (⟨j, hj_lt⟩ : Fin st.nextId) ∈ st.toStruct.obsParents nd0
              · have hj_obs : j ∈ nd.obsParents := by
                  rw [st.mem_toStruct_obsParents_iff nd0 hj_lt] at hj_mem
                  simp only [hdesc0] at hj_mem; exact hj_mem
                exact hρ_readers p (st.rawEnvOfCfg (Classical.choose h))
                  (st.rawEnvOfCfg (projCfg a₀ (st.toStruct.obsParents nd0)))
                  (fun i hi => by
                    by_cases hilt : i < st.nextId
                    · exact (rawEnvOfCfg_not_mem st _ i hilt (by
                        intro hm; rw [st.mem_toStruct_obsParents_iff nd0 hilt] at hm
                        simp only [CompiledNode.obsParents, hdesc0] at hm
                        exact absurd (hndeps i (Finset.mem_union_right _ hm)) (by omega))).trans
                        (rawEnvOfCfg_not_mem st _ i hilt (by
                        intro hm; rw [st.mem_toStruct_obsParents_iff nd0 hilt] at hm
                        simp only [CompiledNode.obsParents, hdesc0] at hm
                        exact absurd (hndeps i (Finset.mem_union_right _ hm)) (by omega))).symm
                    · exact (rawEnvOfCfg_ge_nextId st _ i hilt).trans
                        (rawEnvOfCfg_ge_nextId st _ i hilt).symm)
                  (fun i hi hi_lt => by
                    have hilt : i < st.nextId := Nat.lt_of_lt_of_le
                      (Nat.lt_of_lt_of_le hi_lt (by simp [st₁, stNode,
                        MAIDCompileState.addVar, MAIDCompileState.addNode]))
                      (MAIDCompileState.ofProg_nextId_le B k hl.2 hd ρ' st₁)
                    exact (rawEnvOfCfg_not_mem st _ i hilt (by
                      intro hm; rw [st.mem_toStruct_obsParents_iff nd0 hilt] at hm
                      simp only [hdesc0, CompiledNode.obsParents] at hm; exact hi hm)).trans
                      (rawEnvOfCfg_not_mem st _ i hilt (by
                      intro hm; rw [st.mem_toStruct_obsParents_iff nd0 hilt] at hm
                      simp only [hdesc0, CompiledNode.obsParents] at hm; exact hi hm)).symm)
                  (fun i hi_vd hi_lt => by
                    have hilt : i < st.nextId := Nat.lt_of_lt_of_le
                      (Nat.lt_of_lt_of_le hi_lt (by simp [st₁, stNode,
                        MAIDCompileState.addVar, MAIDCompileState.addNode]))
                      (MAIDCompileState.ofProg_nextId_le B k hl.2 hd ρ' st₁)
                    exact rawEnvOfCfg_rawsMatchDescAt _ _ hilt hi_lt
                      (by rw [st.mem_toStruct_obsParents_iff nd0 hilt]
                          simp only [hdesc0, CompiledNode.obsParents]; exact hi_vd)
                      (by rw [MAIDCompileState.ofProg_descAt_old B k hl.2 hd ρ' st₁ i
                            (show i < st₁.nextId by simp [st₁, stNode,
                              MAIDCompileState.addVar, MAIDCompileState.addNode]; omega)]
                          exact MAIDCompileState.addNode_descAt_old st₀ nd hndeps ⟨i, hi_lt⟩))
                  ((Classical.choose_spec h).trans hViewEq.symm) j hj_obs
              · exact (rawEnvOfCfg_not_mem st _ j hj_lt hj_mem).trans
                  (rawEnvOfCfg_not_mem st _ j hj_lt hj_mem).symm
            · exact (rawEnvOfCfg_ge_nextId st _ j hj_lt).trans
                (rawEnvOfCfg_ge_nextId st _ j hj_lt).symm
          have hcfg : Classical.choose h_ex = projCfg a₀ (st.toStruct.obsParents nd0) :=
            cfg_injective h_ex
          simp only [dif_pos trivial, ProgramBehavioralStrategyPMF.headKernel_mk]
          split_ifs with h_exists
          · have hcfg_eq := cfg_injective h_exists
            rw [hcfg_eq]
            have hprofile : reflectPolicyAuxV B k hl.2 hd ρ' st₁ pol =
                ProgramBehavioralProfilePMF.tail
                  (reflectPolicyAuxV B (.commit x p R k) hl hd ρ st₀ pol) := by
              funext i; simp only [reflectPolicyAuxV, ProgramBehavioralProfilePMF.tail,
                ProgramBehavioralStrategyPMF.tailOwn]
              split_ifs with h <;> subst_vars <;> simp only <;> rfl
            rw [hprofile]
            convert pmf_descAt_cast_bind_cancel hdesc0 _
              (fun v => nativeOutcomeDistPMFV B k hd
                (reflectPolicyAuxV B (.commit x p R k) hl hd ρ st₀ pol).tail ρ'
                (st₀.nextId + 1) ((rawOfTAssign st a₀).extend st₀.nextId ⟨b, v⟩))
              (congrArg PMF (congrArg CompiledNode.valType hdesc0.symm)) using 5
            · change _ = _
              simp only [CompiledNode.valType, eqRec_eq_cast, cast_cast, cast_eq]
              rfl
            · funext i
              simp only [reflectPolicyAuxV, ProgramBehavioralProfilePMF.tail,
                ProgramBehavioralStrategyPMF.tailOwn]
              split_ifs with h <;> subst_vars <;> simp only
          · exfalso; apply h_exists; exact ⟨_, hViewEq⟩
        · rename_i hk
          rw [toStruct_kind] at hk; rw [hkind_decision] at hk; exact absurd hk (by simp)
      · intro β pol env hpol ⟨raw₀, hraw₀, hraw_typed, hraw_hi⟩
        apply Vegas.outcomeDistBehavioralPMF_commit_congr
        · simp only [reflectPolicyAuxV, ProgramBehavioralProfile.toPMFProfile, dif_pos rfl,
            dif_pos trivial, ProgramBehavioralStrategyPMF.headKernel,
            ProgramBehavioralKernelPMF.run_ofFDist]
          have hxvars : x ∉ st₀.vars.map Prod.fst := fun hmem => hfresh.1 (hvars x hmem)
          let nd : CompiledNode Player L B :=
            .decision b who_commit (allValues B b) (allValues_ne_nil B b)
              (allValues_nodup B b) (st₀.viewDeps who_commit Γ')
          have hndeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st₀.nextId := by
            intro d hd'; rcases Finset.mem_union.mp hd' with h | h <;>
              simpa [CompiledNode.parents, CompiledNode.obsParents, nd] using st₀.depsOfVars_lt _ d h
          let stNode := (st₀.addNode nd hndeps).2
          let st₁ := stNode.addVar x (.hidden who_commit b) ({st₀.nextId}) (by
            intro d hd'; have := Finset.mem_singleton.mp hd'; subst d
            exact Nat.lt_succ_self _)
          let ρ' : RawNodeEnv L → VEnv (Player := Player) L ((x, .hidden who_commit b) :: Γ') :=
            fun raw => VEnv.cons (τ := .hidden who_commit b)
              (MAIDCompileState.readVal (B := B) raw b st₀.nextId) (ρ raw)
          let st := MAIDCompileState.ofProg B k hl.2 hd ρ' st₁
          have hid_lt : st₀.nextId < st.nextId := by
            refine Nat.lt_of_lt_of_le ?_ (MAIDCompileState.ofProg_nextId_le B k hl.2 hd ρ' st₁)
            simp [st₁, stNode, MAIDCompileState.addVar, MAIDCompileState.addNode]
          let nd0 : Fin st.nextId := ⟨st₀.nextId, hid_lt⟩
          have hdesc0 : st.descAt nd0 = nd := by
            have hdesc1 := MAIDCompileState.ofProg_descAt_old B k hl.2 hd ρ' st₁ st₀.nextId
              (by simp [st₁, stNode, MAIDCompileState.addVar, MAIDCompileState.addNode])
            rw [hdesc1]
            simpa [st₁, stNode] using st₀.addNode_descAt_new nd hndeps
          have hobs_mem : ∀ i (hi : i < st.nextId),
              ((⟨i, hi⟩ : Fin st.nextId) ∈ st.toStruct.obsParents nd0 ↔
                i ∈ st₀.viewDeps who_commit Γ') := by
            intro i hi
            rw [st.mem_toStruct_obsParents_iff nd0 hi]
            simp only [hdesc0, nd, CompiledNode.obsParents]
          let cfg : MAID.Cfg (fp := B.fintypePlayer) st.toStruct (st.toStruct.obsParents nd0) := by
            intro i
            have himem : i.1.val ∈ st₀.viewDeps who_commit Γ' := (hobs_mem i.1.val i.1.isLt).mp i.2
            have hi_old : i.1.val < st₀.nextId := st₀.depsOfVars_lt _ _ himem
            have hdesc_i : st.descAt i.1 = st₀.descAt ⟨i.1.val, hi_old⟩ := by
              have hprog_old := MAIDCompileState.ofProg_descAt_old B k hl.2 hd ρ' st₁ i.1.val
                (by
                  have hnext : st₁.nextId = st₀.nextId + 1 := by
                    simp [st₁, stNode, MAIDCompileState.addVar, MAIDCompileState.addNode]
                  omega)
              rw [hprog_old]
              exact MAIDCompileState.addNode_descAt_old st₀ nd hndeps ⟨i.1.val, hi_old⟩
            exact castValType hdesc_i.symm (Classical.choose (hraw_typed i.1.val hi_old))
          have hraw_cfg : st.rawEnvOfCfg cfg =
              fun i => if i < st.nextId then
                if i ∈ st₀.viewDeps who_commit Γ' then raw₀ i else none else none := by
            funext i
            by_cases hi : i < st.nextId
            · by_cases hmem : i ∈ st₀.viewDeps who_commit Γ'
              · have hi_obs : (⟨i, hi⟩ : Fin st.nextId) ∈ st.toStruct.obsParents nd0 :=
                  (hobs_mem i hi).2 hmem
                have hi_old : i < st₀.nextId := st₀.depsOfVars_lt _ _ hmem
                have hdesc_i : st.descAt ⟨i, hi⟩ = st₀.descAt ⟨i, hi_old⟩ := by
                  have hprog_old := MAIDCompileState.ofProg_descAt_old B k hl.2 hd ρ' st₁ i
                    (by
                      have hnext : st₁.nextId = st₀.nextId + 1 := by
                        simp [st₁, stNode, MAIDCompileState.addVar, MAIDCompileState.addNode]
                      omega)
                  rw [hprog_old]
                  exact MAIDCompileState.addNode_descAt_old st₀ nd hndeps ⟨i, hi_old⟩
                have hchoose := Classical.choose_spec (hraw_typed i hi_old)
                simp only [MAIDCompileState.rawEnvOfCfg, hi, ↓reduceDIte, hi_obs, ↓reduceIte]
                simp only [hmem, reduceIte]
                change
                  MAIDCompileState.taggedOfVal (st.descAt ⟨i, hi⟩) (cfg ⟨⟨i, hi⟩, hi_obs⟩) = raw₀ i
                dsimp [cfg]
                rw [taggedOfVal_castValType hdesc_i.symm]
                exact hchoose.symm
              · have hi_obs : (⟨i, hi⟩ : Fin st.nextId) ∉ st.toStruct.obsParents nd0 := by
                  intro hm
                  exact hmem ((hobs_mem i hi).mp hm)
                simp [MAIDCompileState.rawEnvOfCfg, hi, hmem, hi_obs]
            · simp [MAIDCompileState.rawEnvOfCfg, hi]
          have hraw_cfg_old : st.rawEnvOfCfg cfg =
              (fun i => if i < st₀.nextId then
                if i ∈ st₀.viewDeps who_commit Γ' then raw₀ i else none
              else none) := by
            rw [hraw_cfg]
            funext i
            by_cases hi₀ : i < st₀.nextId
            · have hi₁ : i < st₁.nextId := by
                have hnext : st₁.nextId = st₀.nextId + 1 := by
                  simp [st₁, stNode, MAIDCompileState.addVar, MAIDCompileState.addNode]
                omega
              have hi : i < st.nextId := Nat.lt_of_lt_of_le hi₁
                (MAIDCompileState.ofProg_nextId_le B k hl.2 hd ρ' st₁)
              simp [hi, hi₀]
            · have hnot_mem : i ∉ st₀.viewDeps who_commit Γ' := by
                intro hmem
                exact hi₀ (st₀.depsOfVars_lt _ _ hmem)
              by_cases hi : i < st.nextId
              · simp [hi, hi₀, hnot_mem]
              · simp [hi, hi₀]
          have hViewEq :
              projectViewEnv (P := Player) (L := L) who_commit
                (VEnv.eraseEnv (ρ (st.rawEnvOfCfg cfg))) =
              projectViewEnv (P := Player) (L := L) who_commit
                (VEnv.eraseEnv env) := by
            rw [hraw_cfg_old, ← hraw₀]
            simpa using
              (eq_on_ctxDeps_raw st₀ (deps := st₀.viewDeps who_commit Γ')
                (f := fun raw => projectViewEnv who_commit (VEnv.eraseEnv (ρ raw)))
                (fun j hj =>
                  projectViewEnv_insensitive_of_viewDeps st₀ ρ hρ_var who_commit j
                    (by simpa using hj))
                raw₀ hraw_hi)
          have hkind0 : st.toStruct.kind nd0 = NodeKind.decision who_commit := by
            simp [toStruct_kind, hdesc0, nd, CompiledNode.kind]
          have h_exists : ∃ cfg,
              projectViewEnv (P := Player) (L := L) who_commit
                (VEnv.eraseEnv (ρ (st.rawEnvOfCfg cfg))) =
              projectViewEnv (P := Player) (L := L) who_commit
                (VEnv.eraseEnv env) := ⟨cfg, hViewEq⟩
          split_ifs with h_exists'
          · rw [hpol who_commit ⟨⟨nd0, hkind0⟩, Classical.choose h_exists'⟩ (by simp [nd0])]
            simp only [translateStrategyV]
            simp only [show (nd0 : Nat) = st₀.nextId from rfl, ↓reduceDIte, id, Eq.mpr]
            have htype_eq : st.toStruct.Val nd0 = L.Val b := by
              change CompiledNode.valType (st.descAt nd0) = L.Val b
              rw [hdesc0]
              rfl
            revert h_exists'
            generalize hT : st.toStruct.Val nd0 = T
            intro h_exists'
            subst T
            let view_choose := projectViewEnv who_commit
              (ρ (st.rawEnvOfCfg (Classical.choose h_exists'))).eraseEnv
            let view_env := projectViewEnv who_commit env.eraseEnv
            have hview' : view_choose = view_env := by
              simpa [view_choose, view_env, st] using Classical.choose_spec h_exists'
            have hkernel_eq :
                ProgramBehavioralStrategy.headKernel (β who_commit) view_choose =
                  ProgramBehavioralStrategy.headKernel (β who_commit) view_env := by
              exact congrArg (ProgramBehavioralStrategy.headKernel (β who_commit)) hview'
            have hpmf_eq :
                ((β who_commit).headKernel view_choose).toPMF
                  (ProgramBehavioralStrategy.headKernel_normalized (β who_commit) view_choose) =
                ((β who_commit).headKernel view_env).toPMF
                  (ProgramBehavioralStrategy.headKernel_normalized (β who_commit) view_env) := by
              exact FDist.toPMF_congr' hkernel_eq
            simpa [eqRec_eq_cast] using hpmf_eq
          · exfalso
            exact h_exists' h_exists
        · intro v
          let nd : CompiledNode Player L B :=
            .decision b who_commit (allValues B b) (allValues_ne_nil B b)
              (allValues_nodup B b) (st₀.viewDeps who_commit Γ')
          have hndeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st₀.nextId := by
            intro d hd'; rcases Finset.mem_union.mp hd' with h | h <;>
              simpa [CompiledNode.parents, CompiledNode.obsParents, nd] using st₀.depsOfVars_lt _ d h
          let st₁ := (st₀.addNode nd hndeps).2.addVar x (.hidden who_commit b) ({st₀.nextId}) (by
            intro d hd₁; simp only [Finset.mem_singleton] at hd₁; subst hd₁; exact Nat.lt_succ_self _)
          let ρ' : RawNodeEnv L → VEnv (Player := Player) L ((x, .hidden who_commit b) :: Γ') :=
            fun raw => VEnv.cons (τ := .hidden who_commit b)
              (MAIDCompileState.readVal (B := B) raw b st₀.nextId) (ρ raw)
          have hst₁_le : ∀ (who : Player)
              (I : MAID.Infoset (fp := B.fintypePlayer)
                (MAIDCompileState.ofProg B k hl.2 hd ρ' st₁).toStruct who),
              I.1.1.val ≥ st₁.nextId →
              pol who I = translateStrategyV B k hl.2 hd ρ' st₁
                (ProgramBehavioralProfile.tail β) who I := by
            intro who ⟨d, cfg⟩ hge
            rw [hpol who ⟨d, cfg⟩ (le_trans (by simp [st₁, MAIDCompileState.addVar,
              MAIDCompileState.addNode]) hge)]
            simp only [translateStrategyV]
            have hne : d.1.val ≠ st₀.nextId := by
              have : st₁.nextId = st₀.nextId + 1 := by
                simp [st₁, MAIDCompileState.addVar, MAIDCompileState.addNode]
              exact Ne.symm (Nat.ne_of_lt hge)
            simp only [toStruct_kind, hne, ↓reduceDIte]
            exact ((fun a ↦ a) ∘ fun a ↦ a) rfl
          have h1 : (reflectPolicyAuxV B (.commit x who_commit R k) hl hd ρ st₀ pol).tail =
              reflectPolicyAuxV B k hl.2 hd ρ' st₁ pol := by
            funext w; simp only [ProgramBehavioralProfilePMF.tail, reflectPolicyAuxV]
            by_cases hw : who_commit = w
            · subst hw; simp [ProgramBehavioralStrategyPMF.tailOwn]; rfl
            · simp [hw]; rfl
          rw [h1, ProgramBehavioralProfile.tail_toPMFProfile]
          have hxvars : x ∉ st₀.vars.map Prod.fst := fun hmem => hfresh.1 (hvars x hmem)
          let stNode := (st₀.addNode nd hndeps).2
          exact (ih hl.2 hd hfresh.2 ρ' st₁
            (st₀.VarsSubCtx_addNode_addVar_singleton_step hvars nd hndeps x _ hfresh.1)
            (fun j hj raw tv => by
              have hne : j ≠ st₀.nextId := by
                intro heq; subst heq; apply hj
                simp only [st₁, MAIDCompileState.ctxDeps, MAIDCompileState.depsOfVars, List.map,
                  MAIDCompileState.addNode, MAIDCompileState.addVar]
                apply Finset.mem_union_left
                simp only [MAIDCompileState.lookupDeps]
                rw [lookupDepsAux_append_singleton_eq_self_of_fresh _ _ _ _ hxvars]
                exact Finset.mem_singleton_self _
              change ρ' (raw.extend j tv) = ρ' raw
              simp only [ρ']
              exact VEnv.cons_ext
                (readVal_extend_ne raw j st₀.nextId tv b (Ne.symm hne))
                (hρ_deps j (fun h => hj (by
                  simp only [st₁, MAIDCompileState.ctxDeps, MAIDCompileState.depsOfVars,
                    List.map] at h ⊢
                  rw [MAIDCompileState.depsOfVars_addVar_eq_of_fresh _ _ _ _ _ _ hfresh.1,
                    MAIDCompileState.depsOfVars_addNode_eq]
                  exact Finset.mem_union_right _ h)) raw tv))
            (envRespectsLookupDeps_commit st₀ ρ hρ_var hfresh.1 hxvars)
            (List.nodup_cons.mpr ⟨hfresh.1, hnodup⟩)).behavioral_eq
            (ProgramBehavioralProfile.tail β) pol _ hst₁_le
            ⟨RawNodeEnv.extend raw₀ st₀.nextId ⟨b, v⟩, by
              constructor
              · change VEnv.cons (MAIDCompileState.readVal (B := B)
                  (RawNodeEnv.extend raw₀ st₀.nextId ⟨b, v⟩) b st₀.nextId)
                  (ρ (RawNodeEnv.extend raw₀ st₀.nextId ⟨b, v⟩)) = VEnv.cons v env
                rw [show MAIDCompileState.readVal (B := B)
                  (RawNodeEnv.extend raw₀ st₀.nextId ⟨b, v⟩) b st₀.nextId = v from by
                  simp [RawNodeEnv.extend, MAIDCompileState.readVal]]
                rw [show ρ (RawNodeEnv.extend raw₀ st₀.nextId ⟨b, v⟩) = env from by
                  rw [hρ_deps st₀.nextId
                    (by intro h; exact absurd (st₀.depsOfVars_lt _ _ h) (by omega))
                    raw₀ ⟨b, v⟩, hraw₀]]
              · exact ⟨(rawWitness_extend_addNode_addVar st₀ nd hndeps (x := x)
                    (τ := .hidden who_commit b) raw₀ hraw_typed hraw_hi ⟨b, v⟩
                    ⟨v, by simp [nd, MAIDCompileState.taggedOfVal]⟩).1,
                  (rawWitness_extend_addNode_addVar st₀ nd hndeps (x := x)
                    (τ := .hidden who_commit b) raw₀ hraw_typed hraw_hi ⟨b, v⟩
                    ⟨v, by simp [nd, MAIDCompileState.taggedOfVal]⟩).2⟩⟩

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
    let st := MAIDCompileState.ofProg B p hl hd ρ st₀
    ∀ (pol : Policy (fp := B.fintypePlayer) st.toStruct)
      (a₀ : TAssign (fp := B.fintypePlayer) st.toStruct),
      PMF.map (fun a => extractOutcomeAux B p ρ st₀.nextId (rawOfTAssign st a))
        ((List.finRange st.nextId).drop st₀.nextId |>.foldl
          (evalStep (fp := B.fintypePlayer) st.toStruct
            (MAIDCompileState.toSem st) pol) (PMF.pure a₀)) =
      nativeOutcomeDistPMFV B p hd
        (reflectPolicyAuxV B p hl hd ρ st₀ pol)
        ρ st₀.nextId (rawOfTAssign st a₀) := by
  exact (bridgeInv B p hl hd hfresh ρ st₀ hvars hρ_deps hρ_var hnodup).fold_eq
    hρ_readers hρ_readval

private theorem outcomeDistRoundtripV
    (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ)
    (hl : Legal p)
    (hd : NormalizedDists p)
    (hfresh : FreshBindings p)
    (ρ : RawNodeEnv L → VEnv L Γ)
    (st₀ : MAIDCompileState Player L B)
    (hvars : st₀.VarsSubCtx Γ)
    (β : ProgramBehavioralProfile p)
    (pol : MAID.Policy (fp := B.fintypePlayer) (MAIDCompileState.ofProg B p hl hd ρ st₀).toStruct)
    (env : VEnv L Γ) :
    (∀ (who : Player) (I : MAID.Infoset (fp := B.fintypePlayer)
      (MAIDCompileState.ofProg B p hl hd ρ st₀).toStruct who),
      I.1.1.val ≥ st₀.nextId →
      pol who I =
        translateStrategyV B p hl hd ρ st₀ β who I) →
    (∃ raw₀, ρ raw₀ = env ∧
      (∀ j (hj : j < st₀.nextId), ∃ v,
        raw₀ j = MAIDCompileState.taggedOfVal (st₀.descAt ⟨j, hj⟩) v) ∧
      (∀ j, st₀.nextId ≤ j → raw₀ j = none)) →
    (∀ j, j ∉ (st₀.ctxDeps Γ : Finset Nat) → InsensitiveTo ρ j) →
    EnvRespectsLookupDeps st₀ ρ →
    (Γ.map Prod.fst).Nodup →
    outcomeDistBehavioralPMF p hd
      (reflectPolicyAuxV B p hl hd ρ st₀ pol) env =
    outcomeDistBehavioralPMF p hd
      (ProgramBehavioralProfile.toPMFProfile p β) env := by
  intro hpol hraw hρ_deps hρ_var hnodup
  exact (bridgeInv B p hl hd hfresh ρ st₀ hvars hρ_deps hρ_var hnodup).behavioral_eq
    β pol env hpol hraw

/-! ## Reverse bridge -/

/-- **Reverse bridge**: any MAID policy can be reflected to a Vegas PMF behavioral
profile that produces the same outcome distribution via `frontierEval`. -/
theorem vegasMAID_reverse_bridge
    (B : MAIDBackend Player L) {Γ : VCtx Player L}
    (p : VegasCore Player L Γ) (env : VEnv (Player := Player) L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (hfresh : FreshBindings p)
    (hpub : ∀ y who b, VHasVar (L := L) Γ y (.hidden who b) → False)
    (hnodup : (Γ.map Prod.fst).Nodup)
    (pol : Policy (fp := B.fintypePlayer) (compiledStruct B p env hl hd hfresh hpub)) :
    let S := compiledStruct B p env hl hd hfresh hpub
    let sem := vegasMAIDSem B p env hl hd hfresh hpub
    let σ := reflectPolicyV B p env hl hd hfresh hpub pol
    PMF.map (extractOutcomeV B p env hl hd hfresh hpub)
      (frontierEval (fp := B.fintypePlayer) S sem pol) =
    outcomeDistBehavioralPMF p hd σ env := by
  intro S sem σ
  letI := B.fintypePlayer
  rw [MAID.frontierEval_eq_evalAssignDist]
  let st := compiledState B p env hl hd
  have hnat := compiled_naturalOrderV st
  rw [MAID.evalAssignDist_eq_evalFold S sem pol hnat.toTopologicalOrder]
  have hinv := bridgeInv B p hl hd hfresh (fun _ => env) .empty
    (fun _ h => by simp [MAIDCompileState.empty] at h)
    (fun j _ => by intro raw tv; rfl)
    (envRespectsLookupDeps_const (B := B) .empty env)
    hnodup
  have hbridge := hinv.fold_eq
    (fun who raw₁ raw₂ _ _ _ _ i hi => by
      simp only [MAIDCompileState.viewDeps, MAIDCompileState.empty] at hi
      exact absurd hi (by
        have := MAIDCompileState.depsOfVars_lt MAIDCompileState.empty
          ((viewVCtx who _).map Prod.fst) i hi
        simp [MAIDCompileState.empty] at this))
    (fun x who' bt hx hne => absurd hne (by
      simp [MAIDCompileState.empty, MAIDCompileState.lookupDeps,
        MAIDCompileState.lookupDepsAux, Finset.not_nonempty_empty]))
    pol (defaultAssign S)
  rw [show (MAIDCompileState.empty (B := B) (Player := Player) (L := L)).nextId = 0 from rfl,
    List.drop_zero] at hbridge
  have hnative := nativeOutcomeDistPMFV_eq B p hd
    (reflectPolicyAuxV B p hl hd (fun _ => env) .empty pol)
    (fun _ => env) 0
    (fun nid _ raw tv => rfl)
  have hfold : evalFold S sem pol hnat.toTopologicalOrder =
      (List.finRange st.nextId).foldl (evalStep S sem pol)
        (PMF.pure (defaultAssign S)) := by
    rfl
  rw [hfold]
  exact hbridge.trans (hnative _)

theorem vegasMAID_behavioral_bridge
    (B : MAIDBackend Player L) {Γ : VCtx Player L}
    (p : VegasCore Player L Γ) (env : VEnv L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (hfresh : FreshBindings p)
    (hpub : ∀ y who b, VHasVar Γ y (.hidden who b) → False)
    (hnodup : (Γ.map Prod.fst).Nodup)
    (β : ProgramBehavioralProfile p) :
    PMF.map (extractOutcomeV B p env hl hd hfresh hpub)
      (frontierEval (fp := B.fintypePlayer) (compiledStruct B p env hl hd hfresh hpub)
        (vegasMAIDSem B p env hl hd hfresh hpub)
        (compiledPolicyV B p env hl hd hfresh hpub β)) =
    outcomeDistBehavioralPMF p hd (ProgramBehavioralProfile.toPMFProfile p β) env := by
  letI := B.fintypePlayer
  have hrev := vegasMAID_reverse_bridge B p env hl hd hfresh hpub hnodup
    (compiledPolicyV B p env hl hd hfresh hpub β)
  rw [hrev]
  have hinv := bridgeInv B p hl hd hfresh (fun _ => env) .empty
    (fun _ h => by simp [MAIDCompileState.empty] at h)
    (fun j _ => fun _ _ => rfl)
    (fun _ _ _ _ _ => rfl)
    hnodup
  have hrt := hinv.behavioral_eq β
    (compiledPolicyV B p env hl hd hfresh hpub β)
    env (by intro who I _; simp [compiledPolicyV])
    ⟨fun _ => none, rfl, fun j hj => absurd hj (by simp [MAIDCompileState.empty]), fun _ _ => rfl⟩
  simpa [reflectPolicyV, compiledPolicyV] using hrt

theorem vegasMAID_pure_bridge
    (B : MAIDBackend Player L) {Γ : VCtx Player L}
    (p : VegasCore Player L Γ) (env : VEnv L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (hfresh : FreshBindings p)
    (hpub : ∀ y who b, VHasVar Γ y (.hidden who b) → False)
    (hnodup : (Γ.map Prod.fst).Nodup)
    (π : ProgramPureProfile p) :
    PMF.map (extractOutcomeV B p env hl hd hfresh hpub)
      (frontierEval (fp := B.fintypePlayer)
        (compiledStruct B p env hl hd hfresh hpub) (vegasMAIDSem B p env hl hd hfresh hpub)
        (pureToPolicy (fp := B.fintypePlayer)
          (compilePureProfileV B p env hl hd hfresh hpub π))) =
    (outcomeDistPure p π env).toPMF (outcomeDistPure_totalWeight_eq_one hd) := by
  letI := B.fintypePlayer
  let β : ProgramBehavioralProfile p :=
    ProgramPureProfile.toBehavioral p π
  have hpol :
      pureToPolicy (fp := B.fintypePlayer) (compilePureProfileV B p env hl hd hfresh hpub π) =
        compiledPolicyV B p env hl hd hfresh hpub β := by
    simpa [compiledPolicyV, β] using
      (compilePureProfileV_eq_pureToPolicy B p env hl hd hfresh hpub π).symm
  rw [hpol, vegasMAID_behavioral_bridge B p env hl hd hfresh hpub hnodup β]
  have hβpmf :
      ProgramPureProfile.toBehavioralPMF p π =
        ProgramBehavioralProfile.toPMFProfile p β := by
    simpa [β] using toBehavioralPMF_eq_toPMFProfile_toBehavioral (p := p) π
  rw [← hβpmf]
  exact outcomeDistBehavioralPMF_toBehavioralPMF_eq p π env hd

end Vegas
