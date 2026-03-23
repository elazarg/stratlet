import Vegas.StrategicPMF
import Vegas.MAID.Correctness
import Vegas.MAID.PureBridge

/-!
# MAID Policy ↔ Vegas Strategy Reflection

This file provides two constructions:

1. **`reflectPolicy`**: Convert a MAID `Policy` back to a Vegas
   `ProgramBehavioralProfilePMF`. At each commit site of the program, the
   construction looks up the corresponding MAID decision node in the compile
   state and reads the policy at that node's information set.

2. **`compilePureProfile`**: Convert a Vegas `ProgramPureProfile` to a MAID
   `PurePolicy`. This is the pure-strategy analogue of the existing
   `compiledPolicy ∘ pureProfileOperational` path, but constructed directly
   on the pure level.

Both constructions come with semantic correctness theorems connecting
them to the existing bridges.
-/

namespace Vegas

open MAID

variable {P : Type} [DecidableEq P] {L : IExpr}

/-! ## Policy reflection: MAID → Vegas PMF behavioral -/

/-- Reflect a MAID behavioral policy back to a Vegas PMF behavioral profile.

At each commit site `(x, who, Γ, b)` in program `p`:
- Look up the corresponding MAID decision node in the compile state `st`
- Read the MAID policy at that node's information set
- Convert the Vegas `ViewEnv` to the MAID infoset configuration
- Apply the policy to get the PMF over values -/
private noncomputable def reflectPolicyAux
    (B : MAIDBackend P L) :
    {Γ : VCtx P L} →
    (p : VegasCore P L Γ) →
    (hl : Legal p) → (hd : NormalizedDists p) →
    (ρ : RawNodeEnv L → VEnv (Player := P) L Γ) →
    (st₀ : MAIDCompileState P L B) →
    MAID.Policy (fp := B.fintypePlayer)
      (MAIDCompileState.ofProg B p hl hd ρ st₀).toStruct →
    ProgramBehavioralProfilePMF p
  | _, .ret _, _, _, _, _, _ => fun _ => PUnit.unit
  | _, .letExpr (b := b) x e k, hl, hd, ρ, st, pol =>
      reflectPolicyAux B k hl hd _ _ pol
  | _, .sample x τ m D' k, hl, hd, ρ, st, pol =>
      reflectPolicyAux B k hl hd.2 _ _ pol
  | Γ, .commit (b := b) x who R k, hl, hd, ρ, st, pol =>
      -- At this commit site, node id = st.nextId is a decision for `who`.
      -- The kernel reads the MAID policy at that node.
      letI := B.fintypePlayer
      let st_final := MAIDCompileState.ofProg B (.commit x who R k) hl hd ρ st
      let id := st.nextId
      let hid_lt : id < st_final.nextId :=
        Nat.lt_of_lt_of_le (by simp [MAIDCompileState.addNode, MAIDCompileState.addVar]; omega)
          (MAIDCompileState.ofProg_nextId_le B k hl.2 hd _ _)
      let kernel : ProgramBehavioralKernelPMF who Γ b :=
        { run := by
            intro view
            -- The decision node for this commit is at index st.nextId in st_final
            -- Node at id is a decision for who (from addNode_descAt_new + ofProg_descAt_old)
            -- Derive descAt for the decision node at st.nextId
            let nd : CompiledNode P L B :=
              .decision b who (allValues B b) (allValues_ne_nil B b)
                (allValues_nodup B b) (st.viewDeps who Γ)
            have hndeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId := by
              intro d hd'
              have : d ∈ st.viewDeps who Γ := by
                rcases Finset.mem_union.mp hd' with h | h <;>
                  simpa [CompiledNode.parents, CompiledNode.obsParents, nd] using h
              exact st.depsOfVars_lt _ d (by simpa [MAIDCompileState.viewDeps] using this)
            have hst1_lt : st.nextId < ((st.addNode nd hndeps).2.addVar x (.hidden who b)
                {st.nextId} (fun d hd₁ => by
                  simp only [Finset.mem_singleton] at hd₁; subst hd₁
                  exact Nat.lt_succ_self _)).nextId := by
              simp [MAIDCompileState.addVar, MAIDCompileState.addNode]
            have hdesc : st_final.descAt ⟨id, hid_lt⟩ = nd := by
              let ρ' (raw : RawNodeEnv L) : VEnv (Player := P) L ((x, .hidden who b) :: Γ) :=
                VEnv.cons (MAIDCompileState.readVal (B := B) raw b st.nextId) (ρ raw)
              let st₁ := (st.addNode nd hndeps).2.addVar x (.hidden who b) {st.nextId}
                (fun d hd₁ => by
                  simp only [Finset.mem_singleton] at hd₁
                  subst hd₁
                  exact Nat.lt_succ_self _)
              change (MAIDCompileState.ofProg B k hl.2 hd ρ' st₁).descAt ⟨st.nextId, _⟩ = nd
              rw [MAIDCompileState.ofProg_descAt_old B k hl.2 hd ρ' st₁ st.nextId hst1_lt]
              simp only [st₁, MAIDCompileState.addVar]
              exact st.addNode_descAt_new nd hndeps
            have hkind : st_final.toStruct.kind ⟨id, hid_lt⟩ =
                MAID.NodeKind.decision who := by
              simp only [toStruct_kind, hdesc, nd, CompiledNode.kind]
            have hval : st_final.toStruct.Val ⟨id, hid_lt⟩ = L.Val b := by
              change CompiledNode.valType (st_final.descAt ⟨id, hid_lt⟩) = L.Val b
              rw [hdesc]; rfl
            let obs := st_final.toStruct.obsParents ⟨id, hid_lt⟩
            let forwardMap (cfg : MAID.Cfg (fp := B.fintypePlayer) st_final.toStruct obs) :=
              projectViewEnv who (VEnv.eraseEnv (ρ (st_final.rawEnvOfCfg cfg)))
            by_cases h : ∃ cfg, forwardMap cfg = view
            · exact hval ▸ (pol who ⟨⟨⟨id, hid_lt⟩, hkind⟩, Classical.choose h⟩)
            · exact PMF.pure (MAIDValuation.defaultVal L B.toMAIDValuation b) }
      fun i => by
        by_cases h : who = i
        · subst h
          simpa [ProgramBehavioralStrategyPMF] using
            (kernel, reflectPolicyAux B k hl.2 hd _ _ pol who)
        · simpa [ProgramBehavioralStrategyPMF, h] using
            reflectPolicyAux B k hl.2 hd _ _ pol i
  | _, .reveal (b := b) y who x hx k, hl, hd, ρ, st, pol =>
      reflectPolicyAux B k hl hd _ _ pol

noncomputable def reflectPolicy
    (B : MAIDBackend P L)
    {Γ : VCtx P L}
    (p : VegasCore P L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (env : VEnv L Γ) :
    let st := MAIDCompileState.ofProg B p hl hd (fun _ => env) .empty
    MAID.Policy (fp := B.fintypePlayer) st.toStruct →
    ProgramBehavioralProfilePMF p :=
  reflectPolicyAux B p hl hd (fun _ => env) .empty

/-- Semantic correctness of `reflectPolicy`: the PMF behavioral profile
obtained by reflecting a MAID policy produces the same outcome distribution
as the MAID's `evalAssignDist` mapped through outcome extraction. -/
theorem reflectPolicy_outcomeDistBehavioralPMF_eq
    (B : MAIDBackend P L)
    {Γ : VCtx P L}
    (p : VegasCore P L Γ)
    (env : VEnv L Γ)
    (hl : Legal p)
    (hd : NormalizedDists p)
    (hwf : WF p) :
    let st := MAIDCompileState.ofProg B p hl hd (fun _ => env) .empty
    ∀ (pol : MAID.Policy (fp := B.fintypePlayer) st.toStruct),
      let extract : TAssign (fp := B.fintypePlayer) st.toStruct → Outcome P :=
        fun a => extractOutcome B p (fun _ => env) 0 (rawOfTAssign st a)
      let σ_pmf := reflectPolicy B p hl hd env pol
      PMF.map extract (evalAssignDist (fp := B.fintypePlayer) st.toStruct
        (MAIDCompileState.toSem st) pol) =
        outcomeDistBehavioralPMF p hd σ_pmf env := by
  -- This requires obs-config injectivity: at each commit site, the Classical.choose
  -- in reflectPolicyAux's kernel picks the unique cfg matching the runtime view,
  -- ensuring the reflected profile produces the same distribution as the MAID policy.
  -- The proof proceeds by structural induction on p, generalizing ρ and st₀.
  sorry

/-! ## Pure strategy compilation: Vegas → MAID -/

/-- Auxiliary for `compilePureProfile`, threading compile state.
Mirrors `translateStrategy` but extracts pure values instead of PMFs. -/
private noncomputable def compilePureProfileAux
    (B : MAIDBackend P L) :
    {Γ : VCtx P L} →
    (p : VegasCore P L Γ) →
    (hl : Legal p) → (hd : NormalizedDists p) →
    (ρ : RawNodeEnv L → VEnv (Player := P) L Γ) →
    (st₀ : MAIDCompileState P L B) →
    ProgramPureProfile p →
    MAID.PurePolicy (fp := B.fintypePlayer)
      (MAIDCompileState.ofProg B p hl hd ρ st₀).toStruct
  | _, .ret _, _, _, _, _, _ => by
      letI := B.fintypePlayer; intro _p ⟨d, _⟩
      exact default
  | _, .letExpr (b := b) x e k, hl, hd, ρ, st, π =>
      compilePureProfileAux B k hl hd
        (fun raw => VEnv.cons (τ := .pub b) (L.eval e (VEnv.erasePubEnv (ρ raw))) (ρ raw))
        (st.addVar x (.pub b) (st.ctxDeps _) (st.depsOfVars_lt _)) π
  | _, .sample x τ m D' k, hl, hd, ρ, st, π =>
      compilePureProfileAux B k hl hd.2 _ _ π
  | Γ, .commit (b := b) x who R k, hl, hd, ρ, st, π => by
      letI := B.fintypePlayer
      let id := st.nextId
      let obs := st.viewDeps who Γ
      let acts := allValues B b
      let res := st.addNode
        (.decision b who acts (allValues_ne_nil B b) (allValues_nodup B b) obs) (by
        intro d hd'
        have := Finset.mem_union.mp hd'
        rcases this with h | h <;> simpa [CompiledNode.parents, CompiledNode.obsParents] using
          st.depsOfVars_lt _ d h)
      let st' := res.2
      let ρ' : RawNodeEnv L → VEnv (Player := P) L ((x, .hidden who b) :: Γ) :=
        fun raw => VEnv.cons (τ := .hidden who b)
          (MAIDCompileState.readVal (B := B) raw b id) (ρ raw)
      let st₁ := st'.addVar x (.hidden who b) ({id}) (by
        intro d hd₁; simp only [Finset.mem_singleton] at hd₁; subst hd₁; exact Nat.lt_succ_self _)
      let pol_rest := compilePureProfileAux B k hl.2 hd ρ' st₁
        (ProgramPureProfile.tail π)
      let κ := ProgramPureStrategy.headKernel (π who)
      intro p ⟨d, cfg⟩
      let st_final := MAIDCompileState.ofProg B k hl.2 hd ρ' st₁
      by_cases hd_eq : d.1.val = id
      · have hid_lt_st₁ : id < st₁.nextId := by
          simp [st₁, st', res, id, MAIDCompileState.addVar, MAIDCompileState.addNode]
        have hid_lt : id < st_final.nextId :=
          Nat.lt_of_lt_of_le hid_lt_st₁
            (MAIDCompileState.ofProg_nextId_le B k hl.2 hd ρ' st₁)
        have hdesc : st_final.descAt d.1 =
              .decision b who acts (allValues_ne_nil B b) (allValues_nodup B b) obs := by
          have hdesc0 : st₁.descAt ⟨id, hid_lt_st₁⟩ =
              .decision b who acts (allValues_ne_nil B b) (allValues_nodup B b) obs := by
            simp only [st₁, MAIDCompileState.addVar, st', res]
            exact st.addNode_descAt_new _ _
          have h := MAIDCompileState.ofProg_descAt_old B k hl.2 hd ρ' st₁ id hid_lt_st₁
          conv_lhs => rw [show d.1 = ⟨id, hid_lt⟩ from Fin.ext hd_eq]
          exact h.trans hdesc0
        change CompiledNode.valType (st_final.descAt d.1)
        rw [hdesc]; change L.Val b
        exact κ (projectViewEnv who
          (VEnv.eraseEnv (ρ (st_final.rawEnvOfCfg cfg))))
      · exact pol_rest p ⟨d, cfg⟩
  | _, .reveal (b := b) y who x hx k, hl, hd, ρ, st, π =>
      compilePureProfileAux B k hl hd _ _ π

/-- Compile a Vegas pure profile to a MAID pure policy. -/
noncomputable def compilePureProfile
    (B : MAIDBackend P L)
    {Γ : VCtx P L}
    (p : VegasCore P L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (env : VEnv L Γ)
    (π : ProgramPureProfile p) :
    let st := MAIDCompileState.ofProg B p hl hd (fun _ => env) .empty
    MAID.PurePolicy (fp := B.fintypePlayer) st.toStruct :=
  compilePureProfileAux B p hl hd (fun _ => env) .empty π

/-- Generalized: translateStrategy of toBehavioral = pureToPolicy of compilePureProfileAux -/
private theorem compilePureProfile_eq_pureToPolicy_aux
    (B : MAIDBackend P L)
    {Γ : VCtx P L}
    (p : VegasCore P L Γ)
    (hl : Legal p) (hd : NormalizedDists p) (hfresh : FreshBindings p)
    (ρ : RawNodeEnv L → VEnv (Player := P) L Γ)
    (st₀ : MAIDCompileState P L B)
    (π : ProgramPureProfile p) :
    translateStrategy B p hl hd ρ st₀ (ProgramPureProfile.toBehavioral p π) =
      MAID.pureToPolicy (fp := B.fintypePlayer) (compilePureProfileAux B p hl hd ρ st₀ π) := by
  induction p generalizing st₀ with
  | ret => funext player ⟨d, cfg⟩
           simp [translateStrategy, compilePureProfileAux,
                 MAID.pureToPolicy, MAID.pureToPlayerStrategy]
  | letExpr _ _ k ih => exact ih hl hd hfresh.2 _ _ _
  | sample _ _ _ _ k ih => exact ih hl hd.2 hfresh.2 _ _ _
  | commit x who_c R k ih =>
    funext player ⟨d, cfg⟩
    simp only [translateStrategy, compilePureProfileAux,
      MAID.pureToPolicy, MAID.pureToPlayerStrategy]
    split
    · -- isTrue: toPMF_pure + cast commutation with PMF.pure
      simp [_root_.id, ProgramPureProfile.toBehavioral,
        ProgramBehavioralStrategy.headKernel, ProgramBehavioralKernel.ofPure,
        ProgramPureStrategy.headKernel, FDist.toPMF_pure]
      have : ∀ (α β : Type) [DecidableEq α] [DecidableEq β] (h : α = β)
          (v : α), cast (congrArg PMF h) (PMF.pure v) = PMF.pure (cast h v) := by
        intro α β _ _ h v; subst h; rfl
      exact this _ _ _ _
    · -- isFalse: IH on continuation
      simpa [ProgramPureProfile.tail_toBehavioral, MAID.pureToPolicy,
        MAID.pureToPlayerStrategy] using
        congrFun (congrFun (ih hl.2 hd hfresh.2 _ _ _) player) ⟨d, cfg⟩
  | reveal _ _ _ _ k ih => exact ih hl hd hfresh.2 _ _ _

/-- The compiled pure policy, lifted to a behavioral MAID policy via
`pureToPolicy`, agrees with the `compiledPolicy` of the operationally
lifted pure profile. -/
theorem compilePureProfile_eq_pureToPolicy
    (B : MAIDBackend P L)
    {Γ : VCtx P L}
    (p : VegasCore P L Γ)
    (env : VEnv L Γ)
    (π : ProgramPureProfile p)
    (hl : Legal p)
    (hd : NormalizedDists p)
    (hfresh : FreshBindings p) :
    let st := MAIDCompileState.ofProg B p hl hd (fun _ => env) .empty
    let β := ProgramPureProfile.toBehavioral p π
    compiledPolicy B p hl hd (fun _ => env) .empty β =
      MAID.pureToPolicy (fp := B.fintypePlayer) (compilePureProfile B p hl hd env π) := by
  intro st β
  exact compilePureProfile_eq_pureToPolicy_aux B p hl hd hfresh (fun _ => env) .empty π

end Vegas
