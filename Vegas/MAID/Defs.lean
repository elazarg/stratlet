import GameTheory.Languages.MAID.FoldEval
import Vegas.StrategicPMF
import Vegas.MAID.CompileLemmas

/-!
# Definitions for VegasMAID Bridge Proofs

Definitions for the bridge proofs: policy reflection, pure profile compilation,
view projections, and insensitivity predicates.
-/

namespace Vegas

open MAID

variable {Player : Type} [DecidableEq Player] {L : IExpr} {B : MAIDBackend Player L}

/-- Abbreviation for the compiled VegasMAID and its derived MAID structure. -/
noncomputable abbrev compiledStruct
    (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ) (env : VEnv (Player := Player) L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (hfresh : FreshBindings p)
    (hpub : ∀ y who b, VHasVar (L := L) Γ y (.hidden who b) → False) :=
  letI := B.fintypePlayer
  (compileVegasMAID B p hl hd hfresh hpub env).toStruct

/-- The underlying compile state, for definitions that need it. -/
noncomputable abbrev compiledState
    (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ) (env : VEnv (Player := Player) L Γ)
    (hl : Legal p) (hd : NormalizedDists p) :=
  MAIDCompileState.ofProg B p hl hd (fun _ => env) .empty

/-! ## Semantics -/

/-- MAID semantics for the compiled VegasMAID structure. -/
noncomputable def vegasMAIDSem
    (B : MAIDBackend Player L) {Γ : VCtx Player L}
    (p : VegasCore Player L Γ) (env : VEnv (Player := Player) L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (hfresh : FreshBindings p)
    (hpub : ∀ y who b, VHasVar (L := L) Γ y (.hidden who b) → False) :
    Sem (fp := B.fintypePlayer) (compiledStruct B p env hl hd hfresh hpub) := by
  haveI : Fintype Player := B.fintypePlayer
  exact (compiledState B p env hl hd).toSem

/-! ## Raw environment conversion -/

/-- Convert a MAID total assignment to a raw node environment (generalized). -/
noncomputable def rawOfTAssign
    (st : MAIDCompileState Player L B)
    (a : TAssign (fp := B.fintypePlayer) st.toStruct) :
    RawNodeEnv L :=
  haveI := B.fintypePlayer
  fun i =>
    if hi : i < st.nextId then
      MAIDCompileState.taggedOfVal (st.descAt ⟨i, hi⟩) (a ⟨i, hi⟩)
    else
      none

/-- Convert a MAID total assignment to a raw node environment (top-level). -/
noncomputable def rawOfTAssignV
    (B : MAIDBackend Player L) {Γ : VCtx Player L}
    (p : VegasCore Player L Γ) (env : VEnv (Player := Player) L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (hfresh : FreshBindings p)
    (hpub : ∀ y who b, VHasVar (L := L) Γ y (.hidden who b) → False)
    (a : TAssign (fp := B.fintypePlayer)
      (compiledStruct B p env hl hd hfresh hpub)) :
    RawNodeEnv L :=
  rawOfTAssign (compiledState B p env hl hd) a

/-! ## Outcome extraction -/

/-- Deterministic outcome extraction: replay the program reading node values
from a raw environment. Redefined here (independent of Correctness.lean). -/
noncomputable def extractOutcomeAux
    (B : MAIDBackend Player L) :
    {Γ : VCtx Player L} →
    VegasCore Player L Γ →
    (RawNodeEnv L → VEnv (Player := Player) L Γ) →
    Nat → (RawNodeEnv L → Outcome Player)
  | _, .ret u, ρ, _ =>
      fun raw => evalPayoffs u (ρ raw)
  | _, .letExpr _x e k, ρ, nextId =>
      extractOutcomeAux B k
        (fun raw => VEnv.cons (L.eval e (VEnv.erasePubEnv (ρ raw))) (ρ raw))
        nextId
  | _, .sample (b := b) _x _D' k, ρ, nextId =>
      extractOutcomeAux B k
        (fun raw => VEnv.cons
          (MAIDCompileState.readVal (B := B) raw b nextId) (ρ raw))
        (nextId + 1)
  | _, .commit (b := b) _x _who _R k, ρ, nextId =>
      extractOutcomeAux B k
        (fun raw => VEnv.cons
          (MAIDCompileState.readVal (B := B) raw b nextId) (ρ raw))
        (nextId + 1)
  | _, .reveal (b := b) y _who _x hx k, ρ, nextId =>
      extractOutcomeAux B k
        (fun raw =>
          let v : L.Val b := VEnv.get (L := L) (ρ raw) hx
          VEnv.cons (L := L) (x := y) (τ := .pub b) v (ρ raw))
        nextId

/-- Extract Vegas outcomes from a MAID total assignment. -/
noncomputable def extractOutcomeV
    (B : MAIDBackend Player L) {Γ : VCtx Player L}
    (p : VegasCore Player L Γ) (env : VEnv (Player := Player) L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (hfresh : FreshBindings p)
    (hpub : ∀ y who b, VHasVar (L := L) Γ y (.hidden who b) → False) :
    TAssign (fp := B.fintypePlayer)
      (compiledStruct B p env hl hd hfresh hpub) → Outcome Player :=
  fun a => extractOutcomeAux B p (fun _ => env) 0
    (rawOfTAssignV B p env hl hd hfresh hpub a)

/-! ## Policy translation -/

/-- Translate a behavioral profile into a MAID policy.
Mirrors `translateStrategy` from Correctness.lean but is self-contained
(does not import Correctness). -/
noncomputable def translateStrategyV
    (B : MAIDBackend Player L) :
    {Γ : VCtx Player L} →
      (p : VegasCore Player L Γ) →
      (hl : Legal p) → (hd : NormalizedDists p) →
      (ρ : RawNodeEnv L → VEnv L Γ) →
      (st₀ : MAIDCompileState Player L B) →
      ProgramBehavioralProfile p →
      MAID.Policy (fp := B.fintypePlayer)
        (MAIDCompileState.ofProg B p hl hd ρ st₀).toStruct
  | _Γ, .ret _payoffs, _hl, _hd, _ρ, _st, _β => by
      letI := B.fintypePlayer
      intro _p ⟨d, cfg⟩
      exact PMF.pure default
  | _Γ, .letExpr (b := b) x e k, hl, hd, ρ, st, β =>
      translateStrategyV B k hl hd
        (fun raw =>
          let env := ρ raw
          VEnv.cons (τ := .pub b) (L.eval e (VEnv.erasePubEnv env)) env)
        (st.addVar x (.pub b) (st.pubCtxDeps _Γ) (st.depsOfVars_lt _))
        β
  | _Γ, .sample (b := b) x D' k, hl, hd, ρ, st, β =>
      let deps := st.ctxDeps _Γ
      let id := st.nextId
      let cpdFDist : RawNodeEnv L → FDist (L.Val b) := fun raw =>
        let env := ρ raw
        L.evalDist D' (VEnv.eraseSampleEnv env)
      let cpdNorm : ∀ raw, FDist.totalWeight (cpdFDist raw) = 1 :=
        fun raw => hd.1 _
      let res := st.addNode (.chance b deps cpdFDist cpdNorm) (by
        intro d hd'
        have hd'' : d ∈ deps := by
          simpa [CompiledNode.parents, CompiledNode.obsParents] using hd'
        exact st.depsOfVars_lt _ d hd'')
      let st' := res.2
      translateStrategyV B k hl hd.2
        (fun raw =>
          let env := ρ raw
          let v := MAIDCompileState.readVal (B := B) raw b id
          VEnv.cons (τ := .pub b) v env)
        (st'.addVar x (.pub b) ({id}) (by
          intro d hd'
          have hdid : d = id := by simpa using hd'
          subst d; exact Nat.lt_succ_self _))
        β
  | Γ, .commit (b := b) x who R k, hl, hd, ρ, st, β => by
      letI := B.fintypePlayer
      let obs := st.viewDeps who Γ
      let acts := allValues B b
      have hacts : acts ≠ [] := allValues_ne_nil B b
      have hnodup : acts.Nodup := allValues_nodup B b
      let id := st.nextId
      let res := st.addNode
        (.decision b who acts hacts hnodup obs) (by
        intro d hd'
        have hd'' : d ∈ obs := by
          simpa [CompiledNode.parents, CompiledNode.obsParents] using hd'
        exact st.depsOfVars_lt _ d hd'')
      let st' := res.2
      let ρ' : RawNodeEnv L → VEnv L ((x, .hidden who b) :: Γ) :=
        fun raw =>
          let env := ρ raw
          let v := MAIDCompileState.readVal (B := B) raw b id
          VEnv.cons (τ := .hidden who b) v env
      let st₁ := st'.addVar x (.hidden who b) ({id}) (by
          intro d hd'
          have hdid : d = id := by simpa using hd'
          subst d; exact Nat.lt_succ_self _)
      let pol_rest := translateStrategyV B k hl.2 hd ρ' st₁
        (ProgramBehavioralProfile.tail β)
      let κ := ProgramBehavioralStrategy.headKernel (β who)
      intro p ⟨d, cfg⟩
      let st_final := MAIDCompileState.ofProg B k hl.2 hd ρ' st₁
      by_cases hd_eq : d.1.val = id
      · have hid_lt_st₁ : id < st₁.nextId := by
          simp [st₁, st', res, id, MAIDCompileState.addVar, MAIDCompileState.addNode]
        have hdesc0 : st₁.descAt ⟨id, hid_lt_st₁⟩ =
            .decision b who acts hacts hnodup obs := by
          simp only [st₁, MAIDCompileState.addVar, st', res]
          exact st.addNode_descAt_new (.decision b who acts hacts hnodup obs) _
        have hid_lt : id < st_final.nextId :=
          Nat.lt_of_lt_of_le hid_lt_st₁
            (MAIDCompileState.ofProg_nextId_le B k hl.2 hd ρ' st₁)
        have hdesc : st_final.descAt d.1 = .decision b who acts hacts hnodup obs := by
          have h := MAIDCompileState.ofProg_descAt_old B k hl.2 hd ρ' st₁ id hid_lt_st₁
          conv_lhs => rw [show d.1 = ⟨id, hid_lt⟩ from Fin.ext hd_eq]
          exact h.trans hdesc0
        change PMF (CompiledNode.valType (st_final.descAt d.1))
        rw [hdesc]; change PMF (L.Val b)
        exact FDist.toPMF
          (κ (projectViewEnv who
            (VEnv.eraseEnv (ρ (st_final.rawEnvOfCfg cfg)))))
          (ProgramBehavioralStrategy.headKernel_normalized (β who) _)
      · exact pol_rest p ⟨d, cfg⟩
  | _, .reveal (b := b) y who x hx k, hl, hd, ρ, st, β =>
      translateStrategyV B k hl hd
        (fun raw =>
          let env := ρ raw
          let v : L.Val b := VEnv.get env hx
          VEnv.cons (τ := .pub b) v env)
        (st.addVar y (.pub b) (st.lookupDeps x) (st.lookupDeps_lt x))
        β

/-- Translate a Vegas behavioral profile to a MAID policy. -/
noncomputable def compiledPolicyV
    (B : MAIDBackend Player L) {Γ : VCtx Player L}
    (p : VegasCore Player L Γ) (env : VEnv (Player := Player) L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (hfresh : FreshBindings p)
    (hpub : ∀ y who b, VHasVar (L := L) Γ y (.hidden who b) → False)
    (β : ProgramBehavioralProfile p) :
    Policy (fp := B.fintypePlayer)
      (compiledStruct B p env hl hd hfresh hpub) :=
  translateStrategyV B p hl hd (fun _ => env) .empty β

/-- Auxiliary for `reflectPolicyV`, threading compile state.
Mirrors `reflectPolicyAux` from Reflection.lean. -/
noncomputable def reflectPolicyAuxV
    (B : MAIDBackend Player L) :
    {Γ : VCtx Player L} →
    (p : VegasCore Player L Γ) →
    (hl : Legal p) → (hd : NormalizedDists p) →
    (ρ : RawNodeEnv L → VEnv (Player := Player) L Γ) →
    (st₀ : MAIDCompileState Player L B) →
    MAID.Policy (fp := B.fintypePlayer)
      (MAIDCompileState.ofProg B p hl hd ρ st₀).toStruct →
    ProgramBehavioralProfilePMF p
  | _, .ret _, _, _, _, _, _ => fun _ => .ret
  | _, .letExpr (b := b) x e k, hl, hd, ρ, st, pol =>
      fun i => .letExpr (reflectPolicyAuxV B k hl hd
        (fun raw => VEnv.cons (τ := .pub b) (L.eval e (VEnv.erasePubEnv (ρ raw))) (ρ raw))
        (st.addVar x (.pub b) (st.pubCtxDeps _) (st.depsOfVars_lt _)) pol i)
  | _, .sample x D' k, hl, hd, ρ, st, pol =>
      fun i => ProgramBehavioralStrategyPMF.sample (reflectPolicyAuxV B k hl hd.2 _ _ pol i)
  | Γ, .commit (b := b) x who R k, hl, hd, ρ, st, pol =>
      letI := B.fintypePlayer
      let st_final := MAIDCompileState.ofProg B (.commit x who R k) hl hd ρ st
      let id := st.nextId
      let obs := st.viewDeps who Γ
      let acts := allValues B b
      let nd : CompiledNode Player L B :=
        .decision b who acts (allValues_ne_nil B b) (allValues_nodup B b) obs
      have hndeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId := by
        intro d hd'
        have : d ∈ st.viewDeps who Γ := by
          rcases Finset.mem_union.mp hd' with h | h <;>
            simpa [CompiledNode.parents, CompiledNode.obsParents, nd] using h
        exact st.depsOfVars_lt _ d (by simpa [MAIDCompileState.viewDeps] using this)
      let res := st.addNode nd hndeps
      let st' := res.2
      let ρ' : RawNodeEnv L → VEnv (Player := Player) L ((x, .hidden who b) :: Γ) :=
        fun raw => VEnv.cons (τ := .hidden who b)
          (MAIDCompileState.readVal (B := B) raw b id) (ρ raw)
      let st₁ := st'.addVar x (.hidden who b) ({id}) (by
        intro d hd₁; simp only [Finset.mem_singleton] at hd₁; subst hd₁
        exact Nat.lt_succ_self _)
      let hid_lt : id < st_final.nextId :=
        Nat.lt_of_lt_of_le (by simp [MAIDCompileState.addNode, MAIDCompileState.addVar]; omega)
          (MAIDCompileState.ofProg_nextId_le B k hl.2 hd _ _)
      have hst1_lt : st.nextId < st₁.nextId := by
        simp [st₁, st', res, id, MAIDCompileState.addVar, MAIDCompileState.addNode]
      have hdesc : st_final.descAt ⟨id, hid_lt⟩ = nd := by
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
      let kernel : ProgramBehavioralKernelPMF who Γ b :=
        { run := by
            intro view
            let forwardMap (cfg : MAID.Cfg (fp := B.fintypePlayer) st_final.toStruct
                (st_final.toStruct.obsParents ⟨id, hid_lt⟩)) :=
              projectViewEnv who (VEnv.eraseEnv (ρ (st_final.rawEnvOfCfg cfg)))
            by_cases h : ∃ cfg, forwardMap cfg = view
            · exact hval ▸ (pol who ⟨⟨⟨id, hid_lt⟩, hkind⟩, Classical.choose h⟩)
            · exact PMF.pure (MAIDValuation.defaultVal L B.toMAIDValuation b) }
      fun i => by
        by_cases h : who = i
        · subst h
          exact .commitOwn kernel (reflectPolicyAuxV B k hl.2 hd _ _ pol who)
        · exact .commitOther h (reflectPolicyAuxV B k hl.2 hd _ _ pol i)
  | _, .reveal (b := b) y who x hx k, hl, hd, ρ, st, pol =>
      fun i => .reveal (reflectPolicyAuxV B k hl hd _ _ pol i)

/-- Reflect a MAID policy to a Vegas PMF behavioral profile. -/
noncomputable def reflectPolicyV
    (B : MAIDBackend Player L) {Γ : VCtx Player L}
    (p : VegasCore Player L Γ) (env : VEnv (Player := Player) L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (hfresh : FreshBindings p)
    (hpub : ∀ y who b, VHasVar (L := L) Γ y (.hidden who b) → False)
    (pol : Policy (fp := B.fintypePlayer)
      (compiledStruct B p env hl hd hfresh hpub)) :
    ProgramBehavioralProfilePMF p :=
  reflectPolicyAuxV B p hl hd (fun _ => env) .empty pol

/-- Auxiliary for `compilePureProfileV`, threading compile state.
Mirrors `compilePureProfileAux` from Reflection.lean. -/
noncomputable def compilePureProfileAuxV
    (B : MAIDBackend Player L) :
    {Γ : VCtx Player L} →
    (p : VegasCore Player L Γ) →
    (hl : Legal p) → (hd : NormalizedDists p) →
    (ρ : RawNodeEnv L → VEnv (Player := Player) L Γ) →
    (st₀ : MAIDCompileState Player L B) →
    ProgramPureProfile (P := Player) (L := L) p →
    MAID.PurePolicy (fp := B.fintypePlayer)
      (MAIDCompileState.ofProg B p hl hd ρ st₀).toStruct
  | _, .ret _, _, _, _, _, _ => by
      letI := B.fintypePlayer; intro _p ⟨d, _⟩
      exact default
  | _, .letExpr (b := b) x e k, hl, hd, ρ, st, π =>
      compilePureProfileAuxV B k hl hd
        (fun raw => VEnv.cons (τ := .pub b) (L.eval e (VEnv.erasePubEnv (ρ raw))) (ρ raw))
        (st.addVar x (.pub b) (st.pubCtxDeps _) (st.depsOfVars_lt _)) π
  | _, .sample x D' k, hl, hd, ρ, st, π =>
      compilePureProfileAuxV B k hl hd.2 _ _ π
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
      let ρ' : RawNodeEnv L → VEnv (Player := Player) L ((x, .hidden who b) :: Γ) :=
        fun raw => VEnv.cons (τ := .hidden who b)
          (MAIDCompileState.readVal (B := B) raw b id) (ρ raw)
      let st₁ := st'.addVar x (.hidden who b) ({id}) (by
        intro d hd₁; simp only [Finset.mem_singleton] at hd₁; subst hd₁
        exact Nat.lt_succ_self _)
      let pol_rest := compilePureProfileAuxV B k hl.2 hd ρ' st₁
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
      compilePureProfileAuxV B k hl hd _ _ π

theorem compilePureProfileAuxV_player_indep
    (B : MAIDBackend Player L) {Γ : VCtx Player L}
    (p : VegasCore Player L Γ) :
    ∀ (hl : Legal p) (hd : NormalizedDists p)
      (ρ : RawNodeEnv L → VEnv L Γ)
      (st₀ : MAIDCompileState Player L B)
      (π₁ π₂ : ProgramPureProfile p)
      (who : Player),
      π₁ who = π₂ who →
      compilePureProfileAuxV B p hl hd ρ st₀ π₁ who =
        compilePureProfileAuxV B p hl hd ρ st₀ π₂ who := by
  induction p with
  | ret => intros; rfl
  | letExpr x e k ih => intro hl hd ρ st π₁ π₂ who h; exact ih hl hd _ _ π₁ π₂ who h
  | sample x D' k ih => intro hl hd ρ st π₁ π₂ who h; exact ih hl hd.2 _ _ π₁ π₂ who h
  | reveal y who_r x_r hx k ih => intro hl hd ρ st π₁ π₂ who h; exact ih hl hd _ _ π₁ π₂ who h
  | commit x who_commit R k ih =>
    intro hl hd ρ st π₁ π₂ who h
    rename_i Γ' b
    letI := B.fintypePlayer
    change (compilePureProfileAuxV B (.commit x who_commit R k) hl hd ρ st π₁) who =
           (compilePureProfileAuxV B (.commit x who_commit R k) hl hd ρ st π₂) who
    simp only [compilePureProfileAuxV]
    funext ⟨d, cfg⟩; dsimp only
    split
    · -- isTrue: d.val.val = st.nextId → headKernel equality
      rename_i hd_eq; simp only [id]; congr 2
      suffices hwho : who = who_commit by subst hwho; exact h
      have hkind := d.prop; rw [toStruct_kind] at hkind
      let nd : CompiledNode Player L B :=
        .decision b who_commit (allValues B b) (allValues_ne_nil B b)
          (allValues_nodup B b) (st.viewDeps who_commit Γ')
      have hndeps : ∀ dd ∈ nd.parents ∪ nd.obsParents, dd < st.nextId := by
        intro dd hdd; rcases Finset.mem_union.mp hdd with hm | hm <;>
          simpa [CompiledNode.parents, CompiledNode.obsParents, nd] using st.depsOfVars_lt _ dd hm
      let st' := (st.addNode nd hndeps).2
      let st₁ := st'.addVar x (.hidden who_commit b) ({st.nextId}) (by
        intro dd hdd; simp only [Finset.mem_singleton] at hdd; subst dd
        exact Nat.lt_succ_self _)
      have hst1_lt : st.nextId < st₁.nextId := by
        simp [st₁, st', MAIDCompileState.addVar, MAIDCompileState.addNode]
      have hdesc0 : st₁.descAt ⟨st.nextId, hst1_lt⟩ = nd := by
        simp only [st₁, MAIDCompileState.addVar, st']; exact st.addNode_descAt_new nd hndeps
      let ρ' : RawNodeEnv L → VEnv (Player := Player) L ((x, .hidden who_commit b) :: Γ') :=
        fun raw => VEnv.cons (τ := .hidden who_commit b)
          (MAIDCompileState.readVal (B := B) raw b st.nextId) (ρ raw)
      have hid_lt : st.nextId < (MAIDCompileState.ofProg B k hl.2 hd ρ' st₁).nextId :=
        Nat.lt_of_lt_of_le hst1_lt (MAIDCompileState.ofProg_nextId_le B k hl.2 hd ρ' st₁)
      have hdesc : (MAIDCompileState.ofProg B k hl.2 hd ρ' st₁).descAt
          ⟨st.nextId, hid_lt⟩ = nd :=
        (MAIDCompileState.ofProg_descAt_old B k hl.2 hd ρ' st₁ st.nextId hst1_lt).trans hdesc0
      -- The ofProg at .commit definitionally equals ofProg at k with modified state
      have key : (MAIDCompileState.ofProg B (.commit x who_commit R k) hl hd ρ st).descAt
          (⟨st.nextId, hd_eq ▸ d.val.isLt⟩ : Fin _) = nd := hdesc
      have hkind2 : (MAIDCompileState.ofProg B (.commit x who_commit R k) hl hd ρ st).toStruct.kind
          (⟨st.nextId, hd_eq ▸ d.val.isLt⟩ : Fin _) = .decision who_commit := by
        rw [toStruct_kind, key, CompiledNode.kind]
      have hkind_who := d.prop  -- S.kind d.val = .decision who
      rw [show d.val = (⟨st.nextId, hd_eq ▸ d.val.isLt⟩ : Fin _) from Fin.ext hd_eq] at hkind_who
      exact NodeKind.decision.inj (hkind_who.symm.trans hkind2)
    · -- isFalse: delegate to continuation via IH
      rename_i hd_ne
      have htail : π₁.tail who = π₂.tail who := by
        simp only [ProgramPureProfile.tail]
        by_cases hwho : who_commit = who
        · subst hwho
          simp only
          exact congr_arg ProgramPureStrategy.tailOwn h
        · simp only [hwho, ↓reduceDIte]; exact congrArg (Eq.mp _) h
      exact congr_fun (ih hl.2 hd _ _ π₁.tail π₂.tail who htail) ⟨d, cfg⟩

/-- Compile a Vegas pure profile to a MAID pure policy. -/
noncomputable def compilePureProfileV
    (B : MAIDBackend Player L) {Γ : VCtx Player L}
    (p : VegasCore Player L Γ) (env : VEnv (Player := Player) L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (hfresh : FreshBindings p)
    (hpub : ∀ y who b, VHasVar (L := L) Γ y (.hidden who b) → False)
    (π : ProgramPureProfile (P := Player) (L := L) p) :
    PurePolicy (fp := B.fintypePlayer)
      (compiledStruct B p env hl hd hfresh hpub) :=
  compilePureProfileAuxV B p hl hd (fun _ => env) .empty π

/-- The compiled MAID pure policy at player `who` depends only on `π who`. -/
theorem compilePureProfileV_player_indep
    (B : MAIDBackend Player L) {Γ : VCtx Player L}
    (p : VegasCore Player L Γ) (env : VEnv (Player := Player) L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (hfresh : FreshBindings p)
    (hpub : ∀ y who b, VHasVar (L := L) Γ y (.hidden who b) → False)
    (π₁ π₂ : ProgramPureProfile (P := Player) (L := L) p)
    (who : Player) (h : π₁ who = π₂ who) :
    compilePureProfileV B p env hl hd hfresh hpub π₁ who =
      compilePureProfileV B p env hl hd hfresh hpub π₂ who :=
  compilePureProfileAuxV_player_indep B p hl hd _ _ π₁ π₂ who h

/-! ## Helpers for bridge proofs (copied from Correctness/Reflection, independent) -/

/-- Extend a raw node environment at a single index. -/
def RawNodeEnv.extend (raw : RawNodeEnv L) (nid : Nat) (tv : RawTaggedVal L) :
    RawNodeEnv L :=
  fun i => if i = nid then some tv else raw i

theorem readVal_extend_self (raw : RawNodeEnv L) (nid : Nat) (τ : L.Ty)
    (v : L.Val τ) :
    MAIDCompileState.readVal (B := B) (raw.extend nid ⟨τ, v⟩) τ nid = v := by
  simp [RawNodeEnv.extend, MAIDCompileState.readVal]

theorem readVal_extend_ne (raw : RawNodeEnv L) (nid nid' : Nat)
    (tv : RawTaggedVal L) (τ : L.Ty) (hne : nid' ≠ nid) :
    MAIDCompileState.readVal (B := B) (raw.extend nid tv) τ nid' =
    MAIDCompileState.readVal (B := B) raw τ nid' := by
  simp [RawNodeEnv.extend, hne, MAIDCompileState.readVal]

/-- If two raws store the same type at index `i` and readVal agrees, the raws agree. -/
theorem readVal_tagged_eq {raw₁ raw₂ : RawNodeEnv L}
    {τ : L.Ty} {v₁ v₂ : L.Val τ} {i : Nat}
    (h₁ : raw₁ i = some ⟨τ, v₁⟩) (h₂ : raw₂ i = some ⟨τ, v₂⟩)
    (heq : MAIDCompileState.readVal (B := B) raw₁ τ i =
      MAIDCompileState.readVal (B := B) raw₂ τ i) :
    raw₁ i = raw₂ i := by
  simp only [MAIDCompileState.readVal, h₁, ↓reduceDIte, h₂] at heq
  rw [h₁, h₂, heq]

/-- `ρ` is insensitive to extending the raw env at index `nid`. -/
def InsensitiveTo (f : RawNodeEnv L → α) (nid : Nat) : Prop :=
  ∀ raw (tv : RawTaggedVal L), f (raw.extend nid tv) = f raw

theorem InsensitiveTo.eq_of_eq_off [Nonempty (RawTaggedVal L)]
    {f : RawNodeEnv L → α} {k : Nat}
    (hins : InsensitiveTo f k)
    {raw₁ raw₂ : RawNodeEnv L}
    (hoff : ∀ i, i ≠ k → raw₁ i = raw₂ i) :
    f raw₁ = f raw₂ := by
  obtain ⟨tv⟩ := ‹Nonempty (RawTaggedVal L)›
  calc f raw₁ = f (raw₁.extend k tv) := (hins raw₁ tv).symm
    _ = f (raw₂.extend k tv) := by
        congr 1; funext i; simp only [RawNodeEnv.extend]
        split <;> [rfl; exact hoff i (by assumption)]
    _ = f raw₂ := hins raw₂ tv

theorem InsensitiveTo.eq_of_agree_off_list [Nonempty (RawTaggedVal L)]
    {f : RawNodeEnv L → α}
    (ks : List Nat)
    (hins : ∀ k ∈ ks, InsensitiveTo f k)
    {raw₁ raw₂ : RawNodeEnv L}
    (hagree : ∀ i, i ∉ ks → raw₁ i = raw₂ i) :
    f raw₁ = f raw₂ := by
  induction ks generalizing raw₁ with
  | nil => exact congrArg f (funext fun i => hagree i List.not_mem_nil)
  | cons k ks ih =>
    let raw_mid : RawNodeEnv L := fun i => if i = k then raw₂ i else raw₁ i
    have h1 : f raw₁ = f raw_mid :=
      InsensitiveTo.eq_of_eq_off (hins k (.head ks))
        (fun i hne => right_eq_ite_iff.mpr fun a ↦ hagree i fun a_1 ↦ hne a)
    have h2 : f raw_mid = f raw₂ :=
      @ih (fun k' hk' => hins k' (.tail k hk')) raw_mid
        (fun i hi => by
          change (if i = k then raw₂ i else raw₁ i) = raw₂ i
          split
          · rfl
          · next hne => exact hagree i (fun hmem => hi (List.mem_of_ne_of_mem hne hmem)))
    exact h1.trans h2

/-- rawOfTAssign update at a node with known tagged value = extend. -/
theorem rawOfTAssign_updateAssign_of_tagged
    (st : MAIDCompileState Player L B)
    (a : TAssign (fp := B.fintypePlayer) st.toStruct)
    (nd : Fin st.nextId)
    (v : Struct.Val (fp := B.fintypePlayer) st.toStruct nd)
    (tv : RawTaggedVal L)
    (htag : MAIDCompileState.taggedOfVal (st.descAt nd) v = some tv) :
    rawOfTAssign st (updateAssign (fp := B.fintypePlayer) a nd v) =
      (rawOfTAssign st a).extend nd.val tv := by
  funext i
  by_cases hi : i < st.nextId
  · by_cases hEq : (⟨i, hi⟩ : Fin st.nextId) = nd
    · have hival : i = nd.val := by simpa using congrArg Fin.val hEq
      subst hival; simp [rawOfTAssign, RawNodeEnv.extend, hi, updateAssign, htag]
    · have hne : i ≠ nd.val := fun hival => hEq (Fin.ext hival)
      simp [rawOfTAssign, RawNodeEnv.extend, hi, updateAssign, hEq, hne]
  · have hne : i ≠ nd.val := fun hEq => hi (hEq.symm ▸ nd.isLt)
    simp [rawOfTAssign, RawNodeEnv.extend, hi, hne]

/-- rawEnvOfCfg gives none at indices not in the support set. -/
theorem rawEnvOfCfg_not_mem
    (st : MAIDCompileState Player L B)
    {ps : Finset (Fin st.nextId)}
    (cfg : Cfg (fp := B.fintypePlayer) st.toStruct ps)
    (i : Nat) (hi : i < st.nextId)
    (hmem : (⟨i, hi⟩ : Fin st.nextId) ∉ ps) :
    st.rawEnvOfCfg cfg i = none := by
  simp [MAIDCompileState.rawEnvOfCfg, hi, hmem]

/-- rawEnvOfCfg gives none at indices ≥ nextId. -/
theorem rawEnvOfCfg_ge_nextId
    (st : MAIDCompileState Player L B)
    {ps : Finset (Fin st.nextId)}
    (cfg : Cfg (fp := B.fintypePlayer) st.toStruct ps)
    (i : Nat) (hi : ¬(i < st.nextId)) :
    st.rawEnvOfCfg cfg i = none := by
  simp [MAIDCompileState.rawEnvOfCfg, hi]

/-- rawEnvOfCfg of projCfg selects from rawOfTAssign at deps. -/
theorem rawEnvOfCfg_proj_eq_select
    (st : MAIDCompileState Player L B)
    (a : TAssign (fp := B.fintypePlayer) st.toStruct)
    (ps : Finset (Fin st.nextId))
    (deps : Finset Nat)
    (hps : ∀ i (hi : i < st.nextId), ((⟨i, hi⟩ : Fin st.nextId) ∈ ps ↔ i ∈ deps)) :
    st.rawEnvOfCfg (projCfg (fp := B.fintypePlayer) a ps) =
      fun i => if i < st.nextId then
        if i ∈ deps then rawOfTAssign st a i else none else none := by
  funext i
  by_cases hi : i < st.nextId
  · have hps' := hps i hi
    by_cases hmem : (⟨i, hi⟩ : Fin st.nextId) ∈ ps
    · simp [MAIDCompileState.rawEnvOfCfg, projCfg, rawOfTAssign, hi, hmem, (hps').mp hmem]
    · simp [MAIDCompileState.rawEnvOfCfg, projCfg, hi, hmem,
        show i ∉ deps from fun h => hmem ((hps').mpr h)]
  · simp [MAIDCompileState.rawEnvOfCfg, hi]

/-- If f is insensitive to all indices outside deps, then f applied to
the selected raw (deps only) equals f applied to the full rawOfTAssign. -/
theorem eq_on_ctxDeps_rawOfTAssign
    (st : MAIDCompileState Player L B)
    {deps : Finset Nat} {f : RawNodeEnv L → α}
    (hf : ∀ j, j ∉ deps → InsensitiveTo f j)
    (a : TAssign (fp := B.fintypePlayer) st.toStruct) :
    let rawSel : RawNodeEnv L := fun i =>
      if i < st.nextId then
        if i ∈ deps then rawOfTAssign st a i else none else none
    f rawSel = f (rawOfTAssign st a) := by
  intro rawSel
  let ks : List Nat := (List.range st.nextId).filter (· ∉ deps)
  have hclear : rawSel = fun i => if i ∈ ks then none else rawOfTAssign st a i := by
    funext i
    by_cases hi : i < st.nextId
    · have hmem : i ∈ ks ↔ i ∉ deps := by unfold ks; simp [hi]
      by_cases hdep : i ∈ deps
      · simp [rawSel, hi, hdep, hmem]
      · simp [rawSel, hi, hdep, hmem]
    · simp [rawSel, hi, ks, rawOfTAssign]
  rw [hclear]
  haveI : Nonempty (RawTaggedVal L) :=
    let ⟨v⟩ := B.toMAIDValuation.nonemptyVal L.bool; ⟨⟨L.bool, v⟩⟩
  apply InsensitiveTo.eq_of_agree_off_list ks
  · intro k hk; apply hf k
    have hk' : k ∈ (List.range st.nextId).filter (fun j => j ∉ deps) := by simpa [ks] using hk
    simpa using (List.mem_filter.mp hk').2
  · intro i hi; simp [hi]

theorem taggedOfVal_injective {c : CompiledNode Player L B}
    {v₁ v₂ : CompiledNode.valType c}
    (h : MAIDCompileState.taggedOfVal c v₁ = MAIDCompileState.taggedOfVal c v₂) :
    v₁ = v₂ := by
  cases c with
  | chance τ => simp only [MAIDCompileState.taggedOfVal, Option.some.injEq, Sigma.mk.injEq,
    heq_eq_eq, true_and] at h; exact h
  | decision τ => simp only [MAIDCompileState.taggedOfVal, Option.some.injEq, Sigma.mk.injEq,
    heq_eq_eq, true_and] at h; exact h
  | utility => exact @Subsingleton.elim PUnit instSubsingletonPUnit _ _

theorem rawEnvOfCfg_injective
    (st : MAIDCompileState Player L B)
    {ps : Finset (Fin st.nextId)}
    (cfg₁ cfg₂ : Cfg (fp := B.fintypePlayer) st.toStruct ps)
    (h : st.rawEnvOfCfg cfg₁ = st.rawEnvOfCfg cfg₂) :
    cfg₁ = cfg₂ := by
  letI := B.fintypePlayer
  funext ⟨nd, hmem⟩
  have hi := nd.isLt
  have := congr_fun h nd.val
  simp only [MAIDCompileState.rawEnvOfCfg, hi, dite_true, hmem] at this
  exact taggedOfVal_injective this

/-- Cast between CompiledNode value types along a description equality. -/
def castValType {c c' : CompiledNode Player L B}
    (hc : c = c') (v : CompiledNode.valType c) : CompiledNode.valType c' :=
  hc ▸ v

theorem taggedOfVal_chance_cast
    {c : CompiledNode Player L B}
    {τ₀ : L.Ty} {deps₀ : Finset Nat}
    {cpd₀ : RawNodeEnv L → FDist (L.Val τ₀)}
    {hn₀ : ∀ raw, FDist.totalWeight (cpd₀ raw) = 1}
    (hc : c = .chance τ₀ deps₀ cpd₀ hn₀)
    (v : CompiledNode.valType c) :
    MAIDCompileState.taggedOfVal c v = some ⟨τ₀, castValType hc v⟩ := by
  subst hc; rfl

theorem taggedOfVal_decision_cast
    {c : CompiledNode Player L B}
    {τ₀ : L.Ty} {who₀ : Player} {acts₀ : List (L.Val τ₀)}
    {hacts₀ : acts₀ ≠ []} {hnodup₀ : acts₀.Nodup}
    {obs₀ : Finset Nat}
    (hc : c = .decision τ₀ who₀ acts₀ hacts₀ hnodup₀ obs₀)
    (v : CompiledNode.valType c) :
    MAIDCompileState.taggedOfVal c v = some ⟨τ₀, castValType hc v⟩ := by
  subst hc; rfl

/-- Updating a total assignment at a utility node doesn't change `rawOfTAssign`. -/
theorem rawOfTAssign_updateAssign_utility
    (st : MAIDCompileState Player L B)
    (a : TAssign (fp := B.fintypePlayer) st.toStruct)
    (nd : Fin st.nextId) (v : Struct.Val (fp := B.fintypePlayer) st.toStruct nd)
    (hwho : ∃ who, (st.descAt nd).kind = .utility who) :
    rawOfTAssign st (updateAssign (fp := B.fintypePlayer) a nd v) = rawOfTAssign st a := by
  have taggedOfVal_utility : ∀ (c : CompiledNode Player L B)
      (_ : ∃ who, c.kind = .utility who) (v₁ v₂ : CompiledNode.valType c),
      MAIDCompileState.taggedOfVal c v₁ = MAIDCompileState.taggedOfVal c v₂ := by
    intro c ⟨who, hw⟩ v₁ v₂
    cases c <;> simp_all [MAIDCompileState.taggedOfVal, CompiledNode.kind]
  funext i; simp only [rawOfTAssign]
  split
  · next hi =>
    by_cases heq : i = nd.val
    · subst heq
      have hnd : (⟨↑nd, hi⟩ : Fin st.nextId) = nd := Fin.ext rfl
      rw [hnd]; exact taggedOfVal_utility _ hwho _ _
    · have hne : (⟨i, ‹_›⟩ : Fin st.nextId) ≠ nd := Fin.ne_of_val_ne heq
      simp [updateAssign, hne]
  · rfl

/-- The compiled structure has natural order (parents have lower indices). -/
theorem compiled_naturalOrderV (st : MAIDCompileState Player L B) :
    Struct.NaturalOrder (fp := B.fintypePlayer) st.toStruct := by
  letI : Fintype Player := B.fintypePlayer
  intro nd p hp
  rcases Finset.mem_image.mp hp with ⟨d, hd, rfl⟩
  exact st.descAt_parent_lt nd d.2

/-- `ρ` respects the compile state's lookupDeps: if `j ∉ lookupDeps x`,
then `VEnv.get (ρ raw) hx` is insensitive to extending raw at j. -/
def EnvRespectsLookupDeps
    {Γ : VCtx Player L}
    (st : MAIDCompileState Player L B)
    (ρ : RawNodeEnv L → VEnv L Γ) : Prop :=
  ∀ {x : VarId} {τ : BindTy Player L}
    (hx : VHasVar (L := L) Γ x τ) (j : Nat),
      j ∉ st.lookupDeps x →
      InsensitiveTo (fun raw => VEnv.get (L := L) (ρ raw) hx) j

theorem envRespectsLookupDeps_const
    (st : MAIDCompileState Player L B)
    {Γ : VCtx Player L}
    (env : VEnv L Γ) :
    EnvRespectsLookupDeps st (fun _ => env) :=
  fun _ _ _ _ _ => rfl

def HasVar.toVHasVarPub
    {Γ : VCtx Player L} {x : VarId} {τ : L.Ty} :
    HasVar (erasePubVCtx Γ) x τ → VHasVar (pubVCtx Γ) x (.pub τ) := by
  induction Γ with
  | nil => intro h; exact nomatch h
  | cons hd tl ih =>
    obtain ⟨y, σ⟩ := hd
    cases σ with
    | pub υ =>
      simp only [erasePubVCtx, pubVCtx]; intro h
      cases h with
      | here => exact .here
      | there h' => exact .there (ih h')
    | hidden p υ =>
      simp only [erasePubVCtx, pubVCtx]; intro h; exact ih h

omit [DecidableEq Player] in
@[simp] theorem VEnv.erasePubEnv_get
    {Γ : VCtx Player L}
    (env : VEnv (Player := Player) L Γ)
    {x : VarId} {τ : L.Ty}
    (hx : HasVar (erasePubVCtx Γ) x τ) :
    VEnv.erasePubEnv env x τ hx =
      env x (.pub τ) (VHasVar.ofPubVCtx (HasVar.toVHasVarPub hx)) := by
  induction Γ generalizing x τ with
  | nil => exact nomatch hx
  | cons hd tl ih =>
    obtain ⟨y, σ⟩ := hd
    cases σ with
    | pub υ =>
      cases hx with
      | here => rfl
      | there hx' =>
        simpa [VEnv.erasePubEnv, HasVar.toVHasVarPub] using
          (ih (env := fun a b h => env a b (VHasVar.there h)) hx')
    | hidden p υ =>
      simpa [VEnv.erasePubEnv, HasVar.toVHasVarPub] using
        (ih (env := fun a b h => env a b (VHasVar.there h)) hx)

/-- If `j ∉ pubCtxDeps`, evaluating a public expression via `ρ` is insensitive to `j`. -/
theorem eval_pubExpr_insensitive_of_pubCtxDeps
    (st : MAIDCompileState Player L B)
    {Γ : VCtx Player L}
    (ρ : RawNodeEnv L → VEnv (Player := Player) L Γ)
    (hρ_var : EnvRespectsLookupDeps st ρ)
    {τ : L.Ty}
    (e : L.Expr (erasePubVCtx Γ) τ)
    (j : Nat)
    (hj : j ∉ st.pubCtxDeps Γ) :
    InsensitiveTo (fun raw => L.eval e (VEnv.erasePubEnv (ρ raw))) j := by
  intro raw tv; apply L.expr_deps_sound; intro x τ' hx _
  simp only [VEnv.erasePubEnv_get]
  exact hρ_var (VHasVar.ofPubVCtx (HasVar.toVHasVarPub hx)) j
    (fun hjx => hj (st.lookupDeps_subset_depsOfVars_of_mem hx.mem_map_fst hjx)) raw tv

omit [DecidableEq Player] in
@[simp] theorem VEnv.eraseEnv_get_of_erased
    {Γ : VCtx Player L}
    (env : VEnv (Player := Player) L Γ)
    {x : VarId} {τ : BindTy Player L}
    (hx : VHasVar (L := L) Γ x τ) :
    VEnv.eraseEnv env x τ.base hx.toErased = env x τ hx := by
  induction hx with
  | here => rfl
  | there hx ih =>
    simpa [VEnv.eraseEnv] using (ih (env := fun a b h => env a b (VHasVar.there h)))

omit [DecidableEq Player] in
theorem VEnv.eraseEnv_toErased_eq :
    {Γ : VCtx Player L} →
    (env : VEnv (Player := Player) L Γ) →
    {x : VarId} → {b : L.Ty} →
    (hx : HasVar (eraseVCtx Γ) x b) →
    HEq (env.eraseEnv x
        (hx.toVHasVar (Player := Player) (L := L)).1.base
        (hx.toVHasVar (Player := Player) (L := L)).2.1.toErased)
      (env.eraseEnv x b hx)
  | _ :: _, _, _, _, .here => HEq.rfl
  | _ :: _, env, _, _, .there hx =>
      eraseEnv_toErased_eq (fun a b h => env a b (.there h)) hx

/-- If `j ∉ viewDeps who`, the projected view through `ρ` is insensitive to `j`. -/
theorem projectViewEnv_insensitive_of_viewDeps
    (st : MAIDCompileState Player L B)
    {Γ : VCtx Player L}
    (ρ : RawNodeEnv L → VEnv (Player := Player) L Γ)
    (hρ_var : EnvRespectsLookupDeps st ρ)
    (who : Player)
    (j : Nat)
    (hj : j ∉ st.viewDeps who Γ) :
    InsensitiveTo (fun raw => projectViewEnv who (VEnv.eraseEnv (ρ raw))) j := by
  intro raw tv
  apply projectViewEnv_eq_of_obsEq
  intro x τ hx hvis
  let tv' := hx.toVHasVar (Player := Player) (L := L) (Γ := Γ)
  let σ := tv'.1; let hv := tv'.2.1
  have hj' : j ∉ st.lookupDeps x := by
    intro hjx
    exact hj (st.lookupDeps_subset_depsOfVars_of_mem
      (xs := (viewVCtx who Γ).map Prod.fst)
      (mem_viewVCtx_map_fst_of_visible hvis) hjx)
  have h1 := VEnv.eraseEnv_toErased_eq (ρ (raw.extend j tv)) hx
  have h2 := VEnv.eraseEnv_toErased_eq (ρ raw) hx
  have step1 : (ρ (raw.extend j tv)).eraseEnv _ _ hv.toErased =
      (ρ (raw.extend j tv)) _ σ hv := VEnv.eraseEnv_get_of_erased _ hv
  have step3 : (ρ raw) _ σ hv = (ρ raw).eraseEnv _ _ hv.toErased :=
    (VEnv.eraseEnv_get_of_erased _ hv).symm
  have hmid := hρ_var hv j hj' raw tv
  exact eq_of_heq (h1.symm.trans (heq_of_eq (step1.trans (hmid.trans step3))) |>.trans h2)

/-- What it means for two raw envs to match a compiled node at index `i`. -/
def RawsMatchDescAt (st : MAIDCompileState Player L B)
    (raw₁ raw₂ : RawNodeEnv L) (i : Nat) (hi : i < st.nextId) : Prop :=
  match st.descAt ⟨i, hi⟩ with
  | .chance τ _ _ _ | .decision τ _ _ _ _ _ =>
    ∃ (v₁ v₂ : L.Val τ), raw₁ i = some ⟨τ, v₁⟩ ∧ raw₂ i = some ⟨τ, v₂⟩
  | .utility _ _ _ => raw₁ i = none ∧ raw₂ i = none

theorem RawsMatchDescAt_of_descAt_eq
    {st₁ st₀ : MAIDCompileState Player L B}
    {raw₁ raw₂ : RawNodeEnv L} {i : Nat}
    {hi₁ : i < st₁.nextId} {hi₀ : i < st₀.nextId}
    (hdesc : st₁.descAt ⟨i, hi₁⟩ = st₀.descAt ⟨i, hi₀⟩)
    (h : RawsMatchDescAt st₁ raw₁ raw₂ i hi₁) :
    RawsMatchDescAt st₀ raw₁ raw₂ i hi₀ := by
  simp only [RawsMatchDescAt, ← hdesc]; exact h

/-- Raw-level view determinacy: if two raws agree outside viewDeps and their
views through ρ agree, they agree on viewDeps. With VegasMAID (`obsParents =
parents`), this is trivially satisfied. -/
def ViewDeterminesRaw (st : MAIDCompileState Player L B)
    (Γ : VCtx Player L) (ρ : RawNodeEnv L → VEnv (Player := Player) L Γ) : Prop :=
  ∀ (who : Player) (raw₁ raw₂ : RawNodeEnv L),
    (∀ i, st.nextId ≤ i → raw₁ i = raw₂ i) →
    (∀ i, i ∉ st.viewDeps who Γ → i < st.nextId → raw₁ i = raw₂ i) →
    (∀ i, i ∈ st.viewDeps who Γ → (hi : i < st.nextId) →
      RawsMatchDescAt st raw₁ raw₂ i hi) →
    projectViewEnv (P := Player) (L := L) who
      (VEnv.eraseEnv (ρ raw₁)) =
    projectViewEnv (P := Player) (L := L) who
      (VEnv.eraseEnv (ρ raw₂)) →
    ∀ i, i ∈ st.viewDeps who Γ → raw₁ i = raw₂ i

/-- Hidden vars have singleton lookupDeps and ρ reads them via readVal. -/
def EnvReadValAtDeps (st : MAIDCompileState Player L B)
    (Γ : VCtx Player L) (ρ : RawNodeEnv L → VEnv (Player := Player) L Γ) : Prop :=
  ∀ (x : VarId) (who' : Player) (bt : L.Ty) (hx : VHasVar Γ x (.hidden who' bt)),
    (st.lookupDeps x).Nonempty →
    ∃ j, ∃ hj : j < st.nextId, st.lookupDeps x = {j} ∧
      (match st.descAt ⟨j, hj⟩ with
       | .chance τ _ _ _ | .decision τ _ _ _ _ _ => τ = bt
       | .utility _ _ _ => True) ∧
      ∀ raw, VEnv.get (ρ raw) hx = MAIDCompileState.readVal (B := B) raw bt j

/-- A raw environment that realizes a visible env for `ρ` and is well-typed
below `st.nextId` and empty above it. -/
abbrev RealizedRawEnv
    (st : MAIDCompileState Player L B)
    (ρ : RawNodeEnv L → VEnv (Player := Player) L Γ)
    (env : VEnv (Player := Player) L Γ) : Prop :=
  ∃ raw : RawNodeEnv L, ρ raw = env ∧
    (∀ j (hj : j < st.nextId), ∃ v,
      raw j = MAIDCompileState.taggedOfVal (st.descAt ⟨j, hj⟩) v) ∧
    (∀ j, st.nextId ≤ j → raw j = none)

theorem taggedOfVal_castValType
    {c c' : CompiledNode Player L B} (hc : c = c') (v : CompiledNode.valType c) :
    MAIDCompileState.taggedOfVal c' (castValType hc v) =
      MAIDCompileState.taggedOfVal c v := by
  subst hc
  rfl

theorem envRespectsLookupDeps_letExpr
    {Γ' : VCtx Player L}
    (st : MAIDCompileState Player L B)
    (ρ : RawNodeEnv L → VEnv (Player := Player) L Γ')
    (hρ_var : EnvRespectsLookupDeps st ρ)
    {x : VarId} {b : L.Ty} (e : L.Expr (erasePubVCtx Γ') b)
    (hxΓ : Fresh x Γ')
    (hxvars : x ∉ st.vars.map Prod.fst) :
    let ρ' : RawNodeEnv L → VEnv (Player := Player) L ((x, .pub b) :: Γ') :=
      fun raw => VEnv.cons (x := x) (τ := .pub b)
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

theorem envRespectsLookupDeps_sample
    {Γ' : VCtx Player L}
    (st : MAIDCompileState Player L B)
    (ρ : RawNodeEnv L → VEnv (Player := Player) L Γ')
    (hρ_var : EnvRespectsLookupDeps st ρ)
    {x : VarId} {b : L.Ty}
    (D' : L.DistExpr (erasePubVCtx Γ') b)
    (hd : ∀ env, FDist.totalWeight (L.evalDist D' (VEnv.eraseSampleEnv env)) = 1)
    (hxΓ : Fresh x Γ')
    (hxvars : x ∉ st.vars.map Prod.fst) :
    let nd : CompiledNode Player L B := .chance b (st.ctxDeps Γ')
      (fun raw => L.evalDist D' (VEnv.eraseSampleEnv (ρ raw))) (fun raw => hd _)
    let hndeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId := by
      intro d hd'; rcases Finset.mem_union.mp hd' with h | h <;>
        simpa [CompiledNode.parents, CompiledNode.obsParents, nd] using st.depsOfVars_lt _ d h
    let stNode := (st.addNode nd hndeps).2
    let st₁ := stNode.addVar x (.pub b) ({st.nextId}) (by
      intro d hd'; have := Finset.mem_singleton.mp hd'; subst d
      exact Nat.lt_succ_self _)
    let ρ' : RawNodeEnv L → VEnv (Player := Player) L ((x, .pub b) :: Γ') :=
      fun raw => VEnv.cons (τ := .pub b)
        (MAIDCompileState.readVal (B := B) raw b st.nextId) (ρ raw)
    EnvRespectsLookupDeps st₁ ρ' := by
  intro nd hndeps stNode st₁ ρ' y σ hy j hj raw tv
  cases hy with
  | here =>
      have hlookup : st₁.lookupDeps x = ({st.nextId} : Finset Nat) := by
        simpa [st₁] using stNode.lookupDeps_addVar_eq_self_of_fresh x (.pub b) {st.nextId}
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
        simpa [st₁] using stNode.lookupDeps_addVar_eq_of_ne x (.pub b) {st.nextId}
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

theorem envRespectsLookupDeps_reveal
    {Γ' : VCtx Player L}
    (st : MAIDCompileState Player L B)
    (ρ : RawNodeEnv L → VEnv (Player := Player) L Γ')
    (hρ_var : EnvRespectsLookupDeps st ρ)
    {y x : VarId} {who : Player} {b : L.Ty}
    (hx : VHasVar Γ' x (.hidden who b))
    (hyΓ : Fresh y Γ')
    (hyvars : y ∉ st.vars.map Prod.fst) :
    let ρ' : RawNodeEnv L → VEnv (Player := Player) L ((y, .pub b) :: Γ') :=
      fun raw =>
        let v : L.Val b := VEnv.get (ρ raw) hx
        VEnv.cons (x := y) (τ := .pub b) v (ρ raw)
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

theorem envRespectsLookupDeps_commit
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

theorem rawWitness_extend_addNode_addVar
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

theorem realizedRawEnv_extend_addNode_addVar
    (st : MAIDCompileState Player L B)
    {Γ : VCtx Player L}
    (ρ : RawNodeEnv L → VEnv (Player := Player) L Γ)
    (env : VEnv (Player := Player) L Γ)
    (hreal : RealizedRawEnv st ρ env)
    (hρ_deps : ∀ j, j ∉ (st.ctxDeps Γ : Finset Nat) → InsensitiveTo ρ j)
    (nd : CompiledNode Player L B)
    (hndeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId)
    {x : VarId} {τ : BindTy Player L}
    (v : L.Val τ.base)
    (htag : ∃ w, MAIDCompileState.taggedOfVal nd w = some ⟨τ.base, v⟩) :
    let stNode := (st.addNode nd hndeps).2
    let st₁ := stNode.addVar x τ ({st.nextId}) (by
      intro d hd'; have := Finset.mem_singleton.mp hd'; subst d
      exact Nat.lt_succ_self _)
    let ρ' : RawNodeEnv L → VEnv (Player := Player) L ((x, τ) :: Γ) :=
      fun raw => VEnv.cons (τ := τ)
        (MAIDCompileState.readVal (B := B) raw τ.base st.nextId) (ρ raw)
    RealizedRawEnv st₁ ρ' (VEnv.cons (τ := τ) v env) := by
  intro stNode st₁ ρ'
  rcases hreal with ⟨raw₀, hraw₀, hraw_typed, hraw_hi⟩
  refine ⟨RawNodeEnv.extend raw₀ st.nextId ⟨τ.base, v⟩, ?_, ?_, ?_⟩
  · apply VEnv.cons_ext
    · simp [RawNodeEnv.extend, MAIDCompileState.readVal]
    · rw [show ρ (RawNodeEnv.extend raw₀ st.nextId ⟨τ.base, v⟩) = env from by
        rw [hρ_deps st.nextId
          (by
            intro h
            exact absurd (st.depsOfVars_lt _ _ h) (by omega))
          raw₀ ⟨τ.base, v⟩, hraw₀]]
  · exact (rawWitness_extend_addNode_addVar st nd hndeps (x := x) (τ := τ) raw₀
      hraw_typed hraw_hi ⟨τ.base, v⟩ htag).1
  · exact (rawWitness_extend_addNode_addVar st nd hndeps (x := x) (τ := τ) raw₀
      hraw_typed hraw_hi ⟨τ.base, v⟩ htag).2

open MAID in
theorem rawEnvOfCfg_rawsMatchDescAt
    {st st₀ : MAIDCompileState Player L B}
    {ps : Finset (Fin st.nextId)}
    (cfg₁ cfg₂ : Cfg (fp := B.fintypePlayer) st.toStruct ps)
    {i : Nat} (hilt : i < st.nextId) (hi₀ : i < st₀.nextId)
    (hmem : (⟨i, hilt⟩ : Fin st.nextId) ∈ ps)
    (hdesc : st.descAt ⟨i, hilt⟩ = st₀.descAt ⟨i, hi₀⟩) :
    RawsMatchDescAt st₀ (st.rawEnvOfCfg cfg₁) (st.rawEnvOfCfg cfg₂) i hi₀ := by
  letI := B.fintypePlayer
  suffices ∀ (nd : CompiledNode Player L B) (v₁ v₂ : CompiledNode.valType nd)
      (hraw₁ : st.rawEnvOfCfg cfg₁ i = MAIDCompileState.taggedOfVal nd v₁)
      (hraw₂ : st.rawEnvOfCfg cfg₂ i = MAIDCompileState.taggedOfVal nd v₂)
      (hnd : nd = st₀.descAt ⟨i, hi₀⟩),
      RawsMatchDescAt st₀ (st.rawEnvOfCfg cfg₁) (st.rawEnvOfCfg cfg₂) i hi₀ by
    exact this (st.descAt ⟨i, hilt⟩) (cfg₁ ⟨⟨i, hilt⟩, hmem⟩) (cfg₂ ⟨⟨i, hilt⟩, hmem⟩)
      (by unfold MAIDCompileState.rawEnvOfCfg; simp [hilt, hmem])
      (by unfold MAIDCompileState.rawEnvOfCfg; simp [hilt, hmem])
      hdesc
  intro nd v₁ v₂ hraw₁ hraw₂ hnd; subst hnd
  unfold RawsMatchDescAt; rw [hraw₁, hraw₂]
  match st₀.descAt ⟨i, hi₀⟩, v₁, v₂ with
  | .chance τ _ _ _, v₁, v₂ => exact ⟨v₁, v₂, rfl, rfl⟩
  | .decision τ _ _ _ _ _, v₁, v₂ => exact ⟨v₁, v₂, rfl, rfl⟩
  | .utility _ _ _, _, _ => exact ⟨rfl, rfl⟩

/-- Cast cancellation for nodeDist: casting a PMF via descAt equality and
binding with castValType gives the same as binding directly. -/
theorem pmf_descAt_cast_bind_cancel
    {st : MAIDCompileState Player L B} {nd : Fin st.nextId}
    {c : CompiledNode Player L B} (hdesc : st.descAt nd = c)
    (d : PMF (CompiledNode.valType c))
    {γ : Type} (f : CompiledNode.valType c → PMF γ)
    (hcast : PMF (CompiledNode.valType c) =
      PMF (CompiledNode.valType (st.descAt nd))) :
    (cast hcast d).bind (fun v => f (castValType hdesc v)) = d.bind f := by
  subst hdesc; rfl

/-- Variant of `pmf_descAt_cast_bind_cancel` starting from a PMF over the struct
Val type rather than requiring an explicit `cast`. -/
theorem pmf_bind_castValType
    {st : MAIDCompileState Player L B} {nd : Fin st.nextId}
    {c : CompiledNode Player L B} (hdesc : st.descAt nd = c)
    (d : PMF (CompiledNode.valType (st.descAt nd)))
    {γ : Type} (f : CompiledNode.valType c → PMF γ) :
    d.bind (fun v => f (castValType hdesc v)) = (hdesc ▸ d).bind f := by
  subst hdesc; rfl

/-- evalStep bind distributes over left bind. -/
theorem foldl_evalStep_bind_left [Fintype Player] {n : Nat}
    {S : MAID.Struct Player n} (sem : MAID.Sem S) (pol : MAID.Policy S)
    (nodes : List (Fin n)) {β : Type} (μ : PMF β)
    (g : β → PMF (MAID.TAssign S)) :
    List.foldl (MAID.evalStep S sem pol) (μ.bind g) nodes =
      μ.bind (fun v => List.foldl (MAID.evalStep S sem pol) (g v) nodes) := by
  induction nodes generalizing g with
  | nil => simp
  | cons nd rest ih =>
    simp only [List.foldl_cons, MAID.evalStep]
    rw [show (μ.bind g).bind (fun a =>
          (MAID.nodeDist S sem pol nd a).bind (fun v =>
            PMF.pure (MAID.updateAssign a nd v))) =
        μ.bind (fun v => (g v).bind (fun a =>
          (MAID.nodeDist S sem pol nd a).bind (fun v' =>
            PMF.pure (MAID.updateAssign a nd v')))) from PMF.bind_bind _ _ _]
    exact ih _

/-! ## PMF native outcome distribution -/

/-- PMF-level native outcome distribution: like `outcomeDistBehavioralPMF` but
threads `(nextId, rawNodeEnv)` through the program. At sample/commit sites,
the raw env is extended with the new node's value. -/
noncomputable def nativeOutcomeDistPMFV
    (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ)
    (hd : NormalizedDists p)
    (σ : ProgramBehavioralProfilePMF p) :
    (ρ : RawNodeEnv L → VEnv (Player := Player) L Γ) →
    (nextId : Nat) →
    RawNodeEnv L → PMF (Outcome Player) :=
  match p, hd, σ with
  | .ret u, _, _ => fun ρ _ raw =>
      PMF.pure (evalPayoffs u (ρ raw))
  | .letExpr (b := b) x e k, hd, σ => fun ρ nextId raw =>
      nativeOutcomeDistPMFV B k hd (fun w => match σ w with | .letExpr tail => tail)
        (fun raw => VEnv.cons (L := L) (x := x) (τ := .pub b)
          (L.eval e (VEnv.erasePubEnv (ρ raw))) (ρ raw))
        nextId raw
  | .sample (b := b) x D' k, hd, σ => fun ρ nextId raw =>
      ((L.evalDist D' (VEnv.eraseSampleEnv (ρ raw))).toPMF (hd.1 _)).bind
        (fun v =>
          nativeOutcomeDistPMFV B k hd.2 (fun w => match σ w with | .sample tail => tail)
            (fun raw => VEnv.cons (L := L) (x := x) (τ := .pub b)
              (MAIDCompileState.readVal (B := B) raw b nextId) (ρ raw))
            (nextId + 1) (raw.extend nextId ⟨b, v⟩))
  | .commit (b := b) x who _ k, hd, σ => fun ρ nextId raw =>
      let κ := ProgramBehavioralStrategyPMF.headKernel (P := Player) (L := L) (σ who)
      (κ (projectViewEnv who (VEnv.eraseEnv (ρ raw)))).bind
        (fun v =>
          nativeOutcomeDistPMFV B k hd
            (ProgramBehavioralProfilePMF.tail (P := Player) (L := L) σ)
            (fun raw => VEnv.cons (L := L) (x := x) (τ := .hidden who b)
              (MAIDCompileState.readVal (B := B) raw b nextId) (ρ raw))
            (nextId + 1) (raw.extend nextId ⟨b, v⟩))
  | .reveal (b := b) y _who _x hx k, hd, σ => fun ρ nextId raw =>
      nativeOutcomeDistPMFV B k hd (fun w => match σ w with | .reveal tail => tail)
        (fun raw =>
          let v : L.Val b := VEnv.get (L := L) (ρ raw) hx
          VEnv.cons (L := L) (x := y) (τ := .pub b) v (ρ raw))
        nextId raw

/-- `nativeOutcomeDistPMFV` equals `outcomeDistBehavioralPMF` when `ρ` is
insensitive to all node IDs ≥ `nextId`. -/
theorem nativeOutcomeDistPMFV_eq
    (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ)
    (hd : NormalizedDists p)
    (σ : ProgramBehavioralProfilePMF p)
    (ρ : RawNodeEnv L → VEnv (Player := Player) L Γ)
    (nextId : Nat)
    (hρ : ∀ nid, nextId ≤ nid → InsensitiveTo ρ nid) :
    ∀ raw : RawNodeEnv L,
    nativeOutcomeDistPMFV B p hd σ ρ nextId raw =
      outcomeDistBehavioralPMF p hd σ (ρ raw) := by
  induction p generalizing nextId with
  | ret u =>
    intro raw; simp only [nativeOutcomeDistPMFV, outcomeDistBehavioralPMF]
  | letExpr x e k ih =>
    intro raw; simp only [nativeOutcomeDistPMFV, outcomeDistBehavioralPMF]
    exact ih hd (fun w => match σ w with | .letExpr tail => tail) _ nextId
      (fun nid hn raw tv => VEnv.cons_ext
        (congrArg (L.eval e) (congrArg VEnv.erasePubEnv (hρ nid hn raw tv)))
        (hρ nid hn raw tv))
      raw
  | sample x D' k ih =>
    rename_i Γ b
    intro raw; simp only [nativeOutcomeDistPMFV, outcomeDistBehavioralPMF]
    congr 1; funext v
    have hρ' : ∀ nid', nextId + 1 ≤ nid' → InsensitiveTo
        (fun raw => VEnv.cons (L := L) (x := x) (τ := .pub b)
          (MAIDCompileState.readVal (B := B) raw b nextId) (ρ raw)) nid' := by
      intro nid' hn' raw tv
      exact VEnv.cons_ext
        (readVal_extend_ne raw nid' nextId tv b (by omega))
        (hρ nid' (by omega) raw tv)
    rw [ih hd.2 (fun w => match σ w with | .sample tail => tail) _ (nextId + 1) hρ']
    congr 1
    exact VEnv.cons_ext (readVal_extend_self (B := B) raw nextId b v)
      (hρ nextId (le_refl _) raw ⟨b, v⟩)
  | @commit _ x who b R k ih =>
    intro raw; simp only [nativeOutcomeDistPMFV, outcomeDistBehavioralPMF]
    congr 1; funext v
    have hρ' : ∀ nid', nextId + 1 ≤ nid' → InsensitiveTo
        (fun raw => VEnv.cons (L := L) (x := x) (τ := .hidden who b)
          (MAIDCompileState.readVal (B := B) raw b nextId) (ρ raw)) nid' := by
      intro nid' hn' raw tv
      exact VEnv.cons_ext
        (readVal_extend_ne raw nid' nextId tv b (by omega))
        (hρ nid' (by omega) raw tv)
    rw [ih hd (ProgramBehavioralProfilePMF.tail (P := Player) (L := L) σ) _ (nextId + 1) hρ']
    congr 1
    exact VEnv.cons_ext (readVal_extend_self (B := B) raw nextId b v)
      (hρ nextId (le_refl _) raw ⟨b, v⟩)
  | reveal y who x hx k ih =>
    intro raw; simp only [nativeOutcomeDistPMFV, outcomeDistBehavioralPMF]
    exact ih hd (fun w => match σ w with | .reveal tail => tail) _ nextId
      (fun nid hn raw tv =>
        VEnv.cons_ext (τ := .pub _)
          (congrArg (VEnv.get (L := L) · hx) (hρ nid hn raw tv))
          (hρ nid hn raw tv))
      raw

end Vegas
