import Vegas.MAID.CompileV
import Vegas.StrategicPMF
import GameTheory.Languages.MAID.FoldEval

/-!
# Definitions for VegasMAID Bridge Proofs

**Status: top-down development — interfaces first, proofs later.**

Import policy: only CompileV.lean + Compile.lean + GameTheory MAID.
Do NOT reference theorems from Correctness.lean or Reflection.lean.
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
  | _, .sample _x τ _m _D' k, ρ, nextId =>
      extractOutcomeAux B k
        (fun raw => VEnv.cons
          (MAIDCompileState.readVal (B := B) raw τ.base nextId) (ρ raw))
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
private noncomputable def translateStrategyV
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
  | _Γ, .sample x τ m D' k, hl, hd, ρ, st, β =>
      let deps := st.ctxDeps _Γ
      let id := st.nextId
      let cpdFDist : RawNodeEnv L → FDist (L.Val τ.base) := fun raw =>
        let env := ρ raw
        L.evalDist D' (VEnv.eraseDistEnv τ m env)
      let cpdNorm : ∀ raw, FDist.totalWeight (cpdFDist raw) = 1 :=
        fun raw => hd.1 _
      let res := st.addNode (.chance τ.base deps cpdFDist cpdNorm) (by
        intro d hd'
        have hd'' : d ∈ deps := by
          simpa [CompiledNode.parents, CompiledNode.obsParents] using hd'
        exact st.depsOfVars_lt _ d hd'')
      let st' := res.2
      translateStrategyV B k hl hd.2
        (fun raw =>
          let env := ρ raw
          let v := MAIDCompileState.readVal (B := B) raw τ.base id
          VEnv.cons v env)
        (st'.addVar x τ ({id}) (by
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
  | _, .ret _, _, _, _, _, _ => fun _ => PUnit.unit
  | _, .letExpr (b := b) x e k, hl, hd, ρ, st, pol =>
      reflectPolicyAuxV B k hl hd
        (fun raw => VEnv.cons (τ := .pub b) (L.eval e (VEnv.erasePubEnv (ρ raw))) (ρ raw))
        (st.addVar x (.pub b) (st.pubCtxDeps _) (st.depsOfVars_lt _)) pol
  | _, .sample x τ m D' k, hl, hd, ρ, st, pol =>
      reflectPolicyAuxV B k hl hd.2 _ _ pol
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
          simpa [ProgramBehavioralStrategyPMF] using
            (kernel, reflectPolicyAuxV B k hl.2 hd _ _ pol who)
        · simpa [ProgramBehavioralStrategyPMF, h] using
            reflectPolicyAuxV B k hl.2 hd _ _ pol i
  | _, .reveal (b := b) y who x hx k, hl, hd, ρ, st, pol =>
      reflectPolicyAuxV B k hl hd _ _ pol

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
private noncomputable def compilePureProfileAuxV
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
  | _, .sample x τ m D' k, hl, hd, ρ, st, π =>
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

private theorem compilePureProfileAuxV_player_indep
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
  | sample x τ m D' k ih => intro hl hd ρ st π₁ π₂ who h; exact ih hl hd.2 _ _ π₁ π₂ who h
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

/-- `ρ` is insensitive to extending the raw env at index `nid`. -/
def InsensitiveTo (f : RawNodeEnv L → α) (nid : Nat) : Prop :=
  ∀ raw (tv : RawTaggedVal L), f (raw.extend nid tv) = f raw

/-- Cast between CompiledNode value types along a description equality. -/
def castValType {c c' : CompiledNode Player L B}
    (hc : c = c') (v : CompiledNode.valType c) : CompiledNode.valType c' :=
  hc ▸ v

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
      nativeOutcomeDistPMFV B k hd σ
        (fun raw => VEnv.cons (L := L) (x := x) (τ := .pub b)
          (L.eval e (VEnv.erasePubEnv (ρ raw))) (ρ raw))
        nextId raw
  | .sample x τ _m D' k, hd, σ => fun ρ nextId raw =>
      ((L.evalDist D' (VEnv.eraseDistEnv τ _ (ρ raw))).toPMF (hd.1 _)).bind
        (fun v =>
          nativeOutcomeDistPMFV B k hd.2 σ
            (fun raw => VEnv.cons (L := L) (x := x) (τ := τ)
              (MAIDCompileState.readVal (B := B) raw τ.base nextId) (ρ raw))
            (nextId + 1) (raw.extend nextId ⟨τ.base, v⟩))
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
      nativeOutcomeDistPMFV B k hd σ
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
    exact ih hd σ _ nextId
      (fun nid hn raw tv => VEnv.cons_ext
        (congrArg (L.eval e) (congrArg VEnv.erasePubEnv (hρ nid hn raw tv)))
        (hρ nid hn raw tv))
      raw
  | sample x τ m D' k ih =>
    intro raw; simp only [nativeOutcomeDistPMFV, outcomeDistBehavioralPMF]
    congr 1; funext v
    have hρ' : ∀ nid', nextId + 1 ≤ nid' → InsensitiveTo
        (fun raw => VEnv.cons (L := L) (x := x) (τ := τ)
          (MAIDCompileState.readVal (B := B) raw τ.base nextId) (ρ raw)) nid' := by
      intro nid' hn' raw tv
      exact VEnv.cons_ext
        (readVal_extend_ne raw nid' nextId tv τ.base (by omega))
        (hρ nid' (by omega) raw tv)
    rw [ih hd.2 σ _ (nextId + 1) hρ']
    congr 1
    exact VEnv.cons_ext (readVal_extend_self (B := B) raw nextId τ.base v)
      (hρ nextId (le_refl _) raw ⟨τ.base, v⟩)
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
    exact ih hd σ _ nextId
      (fun nid hn raw tv =>
        VEnv.cons_ext (τ := .pub _)
          (congrArg (VEnv.get (L := L) · hx) (hρ nid hn raw tv))
          (hρ nid hn raw tv))
      raw

end Vegas
