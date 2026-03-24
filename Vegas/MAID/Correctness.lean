import GameTheory.Languages.MAID.Prefix
import Vegas.Strategic
import Vegas.MAID.CompileStructural
import Vegas.MAID.Fold

namespace Vegas

open MAID

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {B : MAIDBackend Player L}

-- RawNodeEnv helpers


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

def InsensitiveTo (f : RawNodeEnv L → α) (nid : Nat) : Prop :=
  ∀ raw (tv : RawTaggedVal L), f (raw.extend nid tv) = f raw

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
    EnvRespectsLookupDeps st (fun _ => env) := by
  intro x τ hx j hj raw tv
  rfl

/-- If `f` is insensitive at position `k`, then any two raw environments that
agree on all positions except `k` give the same result under `f`. -/
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

-- nativeOutcomeDist: direct FDist (Outcome Player) by induction on VegasSimple


/-- Direct computation of `FDist (Outcome Player)` by recursion on `VegasSimple`,
threading a plain `RawNodeEnv L` argument. No `FDist (RawNodeEnv L)` appears.

Each `sample`/`commit` does `FDist.bind μ (fun v => recurse with extended raw)`.
The `FDist.bind` is over `FDist (L.Val τ)` → `FDist (Outcome Player)`, both of which
have computable `DecidableEq`. -/
noncomputable def nativeOutcomeDist
    (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ)
    (β : ProgramBehavioralProfile p) :
    (ρ : RawNodeEnv L → VEnv L Γ) →
    (nextId : Nat) →
    RawNodeEnv L → FDist (Outcome Player) :=
  match p, β with
  | .ret u, _ => fun ρ _ raw =>
      FDist.pure (evalPayoffs u (ρ raw))
  | .letExpr (b := b) x e k, β => fun ρ nextId raw =>
      nativeOutcomeDist B k β
        (fun raw => VEnv.cons (L := L) (x := x) (τ := .pub b)
          (L.eval e (VEnv.erasePubEnv (ρ raw))) (ρ raw))
        nextId raw
  | .sample x τ _m D' k, β => fun ρ nextId raw =>
      FDist.bind
        (L.evalDist D' (VEnv.eraseDistEnv τ _ (ρ raw)))
        (fun v =>
          nativeOutcomeDist B k β
            (fun raw => VEnv.cons (L := L) (x := x) (τ := τ)
              (MAIDCompileState.readVal (B := B) raw τ.base nextId) (ρ raw))
            (nextId + 1) (raw.extend nextId ⟨τ.base, v⟩))
  | .commit (b := b) x who _ k, β => fun ρ nextId raw =>
      let κ := ProgramBehavioralStrategy.headKernel (β who)
      FDist.bind
        (κ (projectViewEnv who (VEnv.eraseEnv (ρ raw))))
        (fun v =>
          nativeOutcomeDist B k (ProgramBehavioralProfile.tail β)
            (fun raw => VEnv.cons (L := L) (x := x) (τ := .hidden who b)
              (MAIDCompileState.readVal (B := B) raw b nextId) (ρ raw))
            (nextId + 1) (raw.extend nextId ⟨b, v⟩))
  | .reveal (b := b) y _who _x hx k, β => fun ρ nextId raw =>
      nativeOutcomeDist B k β
        (fun raw =>
          let v : L.Val b := VEnv.get (L := L) (ρ raw) hx
          VEnv.cons (L := L) (x := y) (τ := .pub b) v (ρ raw))
        nextId raw

-- nativeOutcomeDist = outcomeDistBehavioral


/-- **Core theorem.** `nativeOutcomeDist` equals `outcomeDistBehavioral` when ρ is
insensitive to all node ids ≥ nextId.

The proof is by structural induction on `VegasSimple`. Each case uses
`readVal_extend_self` + `InsensitiveTo` for the ρ roundtrip. -/
theorem nativeOutcomeDist_eq_outcomeDistBehavioral
    (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ)
    (β : ProgramBehavioralProfile p)
    (ρ : RawNodeEnv L → VEnv L Γ)
    (nextId : Nat)
    (hρ : ∀ nid, nextId ≤ nid → InsensitiveTo ρ nid) :
    ∀ raw : RawNodeEnv L,
    nativeOutcomeDist B p β ρ nextId raw = outcomeDistBehavioral p β (ρ raw) := by
  induction p generalizing nextId with
  | ret u =>
    intro raw
    simp only [nativeOutcomeDist, outcomeDistBehavioral]
  | letExpr x e k ih =>
    intro raw
    simp only [nativeOutcomeDist, outcomeDistBehavioral]
    exact ih β _ nextId
      (fun nid hn raw tv => VEnv.cons_ext (by rw [hρ nid hn raw tv]) (hρ nid hn raw tv))
      raw
  | sample x τ m D' k ih =>
    intro raw
    simp only [nativeOutcomeDist, outcomeDistBehavioral]
    congr 1; funext v
    have hρ' : ∀ nid', nextId + 1 ≤ nid' → InsensitiveTo
        (fun raw => VEnv.cons (L := L) (x := x) (τ := τ)
          (MAIDCompileState.readVal (B := B) raw τ.base nextId) (ρ raw)) nid' := by
      intro nid' hn' raw tv
      exact VEnv.cons_ext
        (readVal_extend_ne raw nid' nextId tv τ.base (by omega))
        (hρ nid' (by omega) raw tv)
    rw [ih β _ (nextId + 1) hρ']
    congr 1
    exact VEnv.cons_ext (readVal_extend_self (B := B) raw nextId τ.base v)
      (hρ nextId (le_refl _) raw ⟨τ.base, v⟩)
  | @commit _ x who b R k ih =>
    intro raw
    simp only [nativeOutcomeDist, outcomeDistBehavioral]
    congr 1; funext v
    have hρ' : ∀ nid', nextId + 1 ≤ nid' → InsensitiveTo
        (fun raw => VEnv.cons (L := L) (x := x) (τ := .hidden who b)
          (MAIDCompileState.readVal (B := B) raw b nextId) (ρ raw)) nid' := by
      intro nid' hn' raw tv
      exact VEnv.cons_ext
        (readVal_extend_ne raw nid' nextId tv b (by omega))
        (hρ nid' (by omega) raw tv)
    rw [ih (ProgramBehavioralProfile.tail β) _ (nextId + 1) hρ']
    congr 1
    exact VEnv.cons_ext (readVal_extend_self (B := B) raw nextId b v)
      (hρ nextId (le_refl _) raw ⟨b, v⟩)
  | reveal y who x hx k ih =>
    intro raw
    simp only [nativeOutcomeDist, outcomeDistBehavioral]
    exact ih β _ nextId
      (fun nid hn raw tv => VEnv.cons_ext (by rw [hρ nid hn raw tv]) (hρ nid hn raw tv))
      raw

/-- Corollary: for the initial state (constant ρ), `nativeOutcomeDist` = `outcomeDistBehavioral`. -/
theorem nativeOutcomeDist_eq_outcomeDistBehavioral_init
    (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ)
    (β : ProgramBehavioralProfile p)
    (env : VEnv L Γ)
    (raw₀ : RawNodeEnv L) :
    nativeOutcomeDist B p β (fun _ => env) 0 raw₀ = outcomeDistBehavioral p β env := by
  exact nativeOutcomeDist_eq_outcomeDistBehavioral B p β (fun _ => env) 0
    (fun _ _ _ _ => rfl) raw₀

-- Compiled state has natural order


theorem compiled_naturalOrder (st : MAIDCompileState Player L B) :
    Struct.NaturalOrder (fp := B.fintypePlayer) st.toStruct := by
  let _ : Fintype Player := B.fintypePlayer
  intro nd p hp
  rcases Finset.mem_image.mp hp with ⟨d, hd, rfl⟩
  exact st.descAt_parent_lt nd d.2

-- Bridge constructions


/-- Deterministic outcome extraction: given a `RawNodeEnv`, replay the VegasSimple
to reconstruct the final environment and evaluate the utility. -/
noncomputable def extractOutcome
    (B : MAIDBackend Player L) :
    {Γ : VCtx Player L} →
    VegasCore Player L Γ →
    (RawNodeEnv L → VEnv L Γ) →
    Nat → (RawNodeEnv L → Outcome Player)
  | _, .ret u, ρ, _ => fun raw => evalPayoffs u (ρ raw)
  | _, .letExpr (b := b) x e k, ρ, nextId =>
      extractOutcome B k
        (fun raw => VEnv.cons (L := L) (x := x) (τ := .pub b)
          (L.eval e (VEnv.erasePubEnv (ρ raw))) (ρ raw))
        nextId
  | _, .sample x τ _m _D' k, ρ, nextId =>
      extractOutcome B k
        (fun raw => VEnv.cons (L := L) (x := x) (τ := τ)
          (MAIDCompileState.readVal (B := B) raw τ.base nextId) (ρ raw))
        (nextId + 1)
  | _, .commit (b := b) x who _R k, ρ, nextId =>
      extractOutcome B k
        (fun raw => VEnv.cons (L := L) (x := x) (τ := .hidden who b)
          (MAIDCompileState.readVal (B := B) raw b nextId) (ρ raw))
        (nextId + 1)
  | _, .reveal (b := b) y _who _x hx k, ρ, nextId =>
      extractOutcome B k
        (fun raw =>
          let v : L.Val b := VEnv.get (L := L) (ρ raw) hx
          VEnv.cons (L := L) (x := y) (τ := .pub b) v (ρ raw))
        nextId

noncomputable def rawOfTAssign (st : MAIDCompileState Player L B)
    (a : TAssign (fp := B.fintypePlayer) st.toStruct) : RawNodeEnv L :=
  let _ : Fintype Player := B.fintypePlayer
  fun i =>
  if hi : i < st.nextId then
    MAIDCompileState.taggedOfVal (st.descAt ⟨i, hi⟩) (a ⟨i, hi⟩)
  else
    none

-- addNode_descAt_new and addNode_descAt_old moved to Compile.lean

-- addUtilityNodes_nextId, ofProg_nextId_le moved to CompileStructural.lean

/-- `nativeOutcomeDist` has total weight 1 when distributions and profile
are normalized. -/
theorem nativeOutcomeDist_totalWeight
    (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ)
    (β : ProgramBehavioralProfile p)
    (hd : NormalizedDists p)
    (ρ : RawNodeEnv L → VEnv L Γ)
    (nextId : Nat)
    (hρ : ∀ nid, nextId ≤ nid → InsensitiveTo ρ nid)
    (raw : RawNodeEnv L) :
    FDist.totalWeight (nativeOutcomeDist B p β ρ nextId raw) = 1 := by
  rw [nativeOutcomeDist_eq_outcomeDistBehavioral B p β ρ nextId hρ raw]
  exact outcomeDistBehavioral_totalWeight_eq_one hd

-- Compile-state structural lemmas


-- addUtilityNodes_descAt_old, addUtilityNodes_all_utility,
-- ofProg_descAt_old moved to CompileStructural.lean

-- translateStrategy: translate behavioral profile into MAID policy

/-- Translate a behavioral profile into a MAID policy.

At each commit site, constructs the FDist kernel from the behavioral profile
and converts to PMF. The recursive structure mirrors `ofProg`. -/
noncomputable def translateStrategy
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
      -- All new nodes are utility; any decision nodes are from the initial state.
      -- Their PMF doesn't matter (the commit case overrides via pol_rest).
      exact PMF.pure default
  | _Γ, .letExpr (b := b) x e k, hl, hd, ρ, st, β =>
      translateStrategy B k hl hd
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
      translateStrategy B k hl hd.2
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
      let pol_rest := translateStrategy B k hl.2 hd ρ' st₁
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
      translateStrategy B k hl hd
        (fun raw =>
          let env := ρ raw
          let v : L.Val b := VEnv.get env hx
          VEnv.cons (τ := .pub b) v env)
        (st.addVar y (.pub b) (st.lookupDeps x) (st.lookupDeps_lt x))
        β


/-- Compile a MAID `Policy` from a behavioral profile by translating
    the strategy through the compilation. -/
noncomputable def compiledPolicy
    (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (ρ : RawNodeEnv L → VEnv L Γ)
    (st₀ : MAIDCompileState Player L B)
    (β : ProgramBehavioralProfile p) :
    let st := MAIDCompileState.ofProg B p hl hd ρ st₀
    MAID.Policy (fp := B.fintypePlayer) st.toStruct :=
  translateStrategy B p hl hd ρ st₀ β

-- Structural lemmas (lookupDeps, depsOfVars, ctxDeps, etc.) moved to CompileStructural.lean

-- FDist compiled data
-- The compiler naturally produces FDist-valued node distributions. These are
-- assembled into `FDistNodeData` (from MAIDFDistFold) and shown compatible with
-- the PMF-based MAID semantics. `compiledFDistData_compatible` is used by the
-- bridge proof via `evalFoldFDist_toPMF_eq_evalFold`.

noncomputable instance (nd : CompiledNode Player L B) :
    DecidableEq (CompiledNode.valType (B := B) nd) := by
  cases nd with
  | chance τ _ _ _ => exact L.decEqVal
  | decision τ _ _ _ _ _ => exact L.decEqVal
  | utility _ _ _ => exact instDecidableEqPUnit

-- Extensional bridge infrastructure (kernel-independent):
-- Restored from git, adapted for 6-field decision nodes.
-- Extensional bridge: FDist-level lemmas

open MAID in
/-- `rawOfTAssign` is invariant under `updateAssign` at utility nodes,
because `taggedOfVal (.utility ..) _ = none` regardless of the value. -/
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
  funext i
  simp only [rawOfTAssign]
  split
  · next hi =>
    by_cases heq : i = nd.val
    · subst heq
      have hnd : (⟨↑nd, hi⟩ : Fin st.nextId) = nd := Fin.ext rfl
      rw [hnd]
      exact taggedOfVal_utility _ hwho _ _
    · have hne : (⟨i, ‹_›⟩ : Fin st.nextId) ≠ nd := Fin.ne_of_val_ne heq
      simp [updateAssign, hne]
  · rfl

/-- Multi-position insensitivity: if `f` is insensitive at every position
in a list, and two raw environments agree off that list, then `f` agrees. -/
theorem InsensitiveTo.eq_of_agree_off_list [Nonempty (RawTaggedVal L)]
    {f : RawNodeEnv L → α}
    (ks : List Nat)
    (hins : ∀ k ∈ ks, InsensitiveTo f k)
    {raw₁ raw₂ : RawNodeEnv L}
    (hagree : ∀ i, i ∉ ks → raw₁ i = raw₂ i) :
    f raw₁ = f raw₂ := by
  induction ks generalizing raw₁ with
  | nil =>
    exact congrArg f (funext fun i => hagree i List.not_mem_nil)
  | cons k ks ih =>
    let raw_mid : RawNodeEnv L :=
      fun i => if i = k then raw₂ i else raw₁ i
    have h1 : f raw₁ = f raw_mid :=
      InsensitiveTo.eq_of_eq_off (hins k (.head ks))
        (fun i hne => right_eq_ite_iff.mpr fun a ↦ hagree i fun a_1 ↦ hne a)
    have h2 : f raw_mid = f raw₂ :=
      @ih (fun k' hk' => hins k' (.tail k hk')) raw_mid
        (fun i hi => by
          change (if i = k then raw₂ i else raw₁ i) = raw₂ i
          split
          · rfl
          · next hne => exact hagree i (fun hmem =>
              hi (List.mem_of_ne_of_mem hne hmem)))
    exact h1.trans h2

theorem InsensitiveTo.eq_of_agree_on_finset [Nonempty (RawTaggedVal L)]
    (st : MAIDCompileState Player L B)
    {deps : Finset Nat} {f : RawNodeEnv L → α}
    (hf : ∀ j, j ∉ deps → InsensitiveTo f j)
    {raw₁ raw₂ : RawNodeEnv L}
    (hagree : ∀ i, i ∈ deps → raw₁ i = raw₂ i)
    (houtside : ∀ i, st.nextId ≤ i → raw₁ i = raw₂ i) :
    f raw₁ = f raw₂ := by
  let ks : List Nat := (List.range st.nextId).filter (· ∉ deps)
  apply InsensitiveTo.eq_of_agree_off_list ks
  · intro k hk
    apply hf k
    have hk' : k ∈ (List.range st.nextId).filter (fun j => j ∉ deps) := by
      simpa [ks] using hk
    simpa using (List.mem_filter.mp hk').2
  · intro i hi
    by_cases hlt : i < st.nextId
    · have hik : i ∈ ks ↔ i ∉ deps := by
        unfold ks
        simp [hlt]
      have hideps : i ∈ deps := by
        by_contra hnot
        exact hi ((hik).2 hnot)
      exact hagree i hideps
    · exact houtside i (Nat.le_of_not_gt hlt)

-- `mem_toStruct_parents_iff` and `mem_toStruct_obsParents_iff` moved to CompileStructural.lean

/-- Per-node FDist dispatch: given a `CompiledNode` and a decision kernel
(provided externally), produce the FDist over its value type.

Chance nodes use their stored CPD; decision nodes use the provided kernel;
utility nodes return `FDist.pure ()`. -/
noncomputable def compiledNodeFDist
    (_st : MAIDCompileState Player L B)
    (rawP : RawNodeEnv L) (rawO : RawNodeEnv L) :
    (c : CompiledNode Player L B) →
    (decisionKernel : RawNodeEnv L → FDist (CompiledNode.valType c)) →
    FDist (CompiledNode.valType c)
  | .chance _τ _ cpd _, _ => cpd rawP
  | .decision _τ _ _ _ _ _, dk => dk rawO
  | .utility _ _ _, _ => FDist.pure ()

private noncomputable def fdist_transport {α β : Type} [DecidableEq α] [DecidableEq β]
    (h : α = β) (d : FDist α) : FDist β := h ▸ d

@[simp] private theorem fdist_transport_totalWeight {α β : Type}
    [DecidableEq α] [DecidableEq β] (h : α = β) (d : FDist α) :
    (fdist_transport h d).totalWeight = d.totalWeight := by subst h; rfl

@[simp] private theorem toPMF_fdist_transport {α β : Type}
    [DecidableEq α] [DecidableEq β] (h : α = β) (d : FDist α)
    (hn : (fdist_transport h d).totalWeight = 1) :
    (fdist_transport h d).toPMF hn =
      h ▸ (d.toPMF ((fdist_transport_totalWeight h d).symm ▸ hn)) := by
  subst h; rfl

private theorem toPMF_fdist_transport_cast {α β : Type}
    [DecidableEq α] [DecidableEq β] (h : α = β) (d : FDist α)
    (hn : (fdist_transport h d).totalWeight = 1) :
    (fdist_transport h d).toPMF hn =
      cast (congrArg PMF h) (d.toPMF ((fdist_transport_totalWeight h d).symm ▸ hn)) := by
  subst h; rfl

private theorem fdist_transport_congr {α β : Type}
    [DecidableEq α] [DecidableEq β]
    {h₁ h₂ : α = β} (d : FDist α) :
    fdist_transport h₁ d = fdist_transport h₂ d := by
  cases h₁
  cases h₂
  rfl

private theorem fdist_transport_bind_cancel {α β γ : Type}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (h : α = β) (d : FDist α) (f : α → FDist γ) :
    (fdist_transport h d).bind (fun v => f (h.symm ▸ v)) = d.bind f := by
  subst h; rfl

instance (nd : CompiledNode Player L B) :
    Nonempty (CompiledNode.valType (B := B) nd) := by
  cases nd with
  | chance τ _ _ _ => exact ⟨(allValues B τ).head (allValues_ne_nil B τ)⟩
  | decision τ _ _ _ _ _ => exact ⟨(allValues B τ).head (allValues_ne_nil B τ)⟩
  | utility _ _ _ => exact ⟨()⟩

/-- Decision kernel provider: for each decision node, provides the FDist kernel
derived from the behavioral profile. Mirrors `ofProg`/`translateStrategy`. -/
noncomputable def compiledDecisionKernel
    (B : MAIDBackend Player L) :
    {Γ : VCtx Player L} →
      (p : VegasCore Player L Γ) →
      (hl : Legal p) → (hd : NormalizedDists p) →
      (ρ : RawNodeEnv L → VEnv L Γ) →
      (st₀ : MAIDCompileState Player L B) →
      ProgramBehavioralProfile p →
      (nd : Fin (MAIDCompileState.ofProg B p hl hd ρ st₀).nextId) →
      RawNodeEnv L →
      FDist (CompiledNode.valType
        ((MAIDCompileState.ofProg B p hl hd ρ st₀).descAt nd))
  | _, .ret _, _, _, _, _, _, nd, _ => by
      letI := B.fintypePlayer
      change FDist ((MAIDCompileState.ofProg B (.ret _) _ _ _ _).toStruct.Val nd)
      exact FDist.pure default
  | _Γ, .letExpr (b := b) x e k, hl, hd, ρ, st₀, β, nd, raw =>
      compiledDecisionKernel B k hl hd
        (fun raw => VEnv.cons (τ := .pub b)
          (L.eval e (VEnv.erasePubEnv (ρ raw))) (ρ raw))
        (st₀.addVar x (.pub b) (st₀.pubCtxDeps _Γ) (st₀.depsOfVars_lt _))
        β nd raw
  | _Γ, .sample x τ m D' k, hl, hd, ρ, st₀, β, nd, raw =>
      let deps := st₀.ctxDeps _Γ
      let cpdFDist := fun raw => L.evalDist D' (VEnv.eraseDistEnv τ m (ρ raw))
      let cpdNorm : ∀ raw, (cpdFDist raw).totalWeight = 1 := fun raw => hd.1 _
      let nd_data : CompiledNode Player L B :=
        .chance τ.base deps cpdFDist cpdNorm
      let hndeps : ∀ d ∈ nd_data.parents ∪ nd_data.obsParents,
          d < st₀.nextId :=
        fun d hd' => st₀.depsOfVars_lt _ d (by
          simpa [CompiledNode.parents, CompiledNode.obsParents] using hd')
      let st' := (st₀.addNode nd_data hndeps).2
      let st₁ := st'.addVar x τ ({st₀.nextId}) (by
        intro d hd'; have := Finset.mem_singleton.mp hd'
        subst d; exact Nat.lt_succ_self _)
      compiledDecisionKernel B k hl hd.2
        (fun raw => VEnv.cons
          (MAIDCompileState.readVal (B := B) raw τ.base st₀.nextId) (ρ raw))
        st₁ β nd raw
  | Γ, .commit (b := b) x who R k, hl, hd, ρ, st₀, β, nd, raw => by
      let obs := st₀.viewDeps who Γ
      let acts := allValues B b
      have hacts : acts ≠ [] := allValues_ne_nil B b
      have hnodup : acts.Nodup := allValues_nodup B b
      let id := st₀.nextId
      let res := st₀.addNode
        (.decision b who acts hacts hnodup obs) (by
        intro d hd'
        have hd'' : d ∈ obs := by
          simpa [CompiledNode.parents, CompiledNode.obsParents] using hd'
        exact st₀.depsOfVars_lt _ d hd'')
      let st' := res.2
      let ρ' : RawNodeEnv L → VEnv L
          ((x, .hidden who b) :: Γ) :=
        fun raw => VEnv.cons (τ := .hidden who b)
          (MAIDCompileState.readVal (B := B) raw b id) (ρ raw)
      let st₁ := st'.addVar x (.hidden who b) ({id}) (by
        intro d hd'; have := Finset.mem_singleton.mp hd'
        subst d; exact Nat.lt_succ_self _)
      let dk_rest := compiledDecisionKernel B k hl.2 hd ρ' st₁
        (ProgramBehavioralProfile.tail β)
      let κ := ProgramBehavioralStrategy.headKernel (P := Player)
        (L := L) (β who)
      let st_final := MAIDCompileState.ofProg B k hl.2 hd ρ' st₁
      by_cases hnd : nd.val = id
      · have hid_lt_st₁ : id < st₁.nextId := by
          simp [st₁, st', res, id,
            MAIDCompileState.addVar, MAIDCompileState.addNode]
        have hdesc : st_final.descAt nd =
            .decision b who acts hacts hnodup obs := by
          have h1 := MAIDCompileState.ofProg_descAt_old B k hl.2 hd
            ρ' st₁ id hid_lt_st₁
          have h2 : st₁.descAt ⟨id, hid_lt_st₁⟩ =
              .decision b who acts hacts hnodup obs := by
            simp only [st₁, MAIDCompileState.addVar, st', res]
            exact st₀.addNode_descAt_new _ _
          rw [show nd = ⟨id, _⟩ from Fin.ext hnd]
          exact h1.trans h2
        exact fdist_transport
          (show L.Val b = CompiledNode.valType (st_final.descAt nd)
            by rw [hdesc]; rfl)
          (κ (projectViewEnv who
            (VEnv.eraseEnv (ρ raw))))
      · exact dk_rest nd raw
  | _, .reveal (b := b) y _who x hx k, hl, hd, ρ, st₀, β, nd, raw =>
      compiledDecisionKernel B k hl hd
        (fun raw => VEnv.cons (τ := .pub b)
          (VEnv.get (ρ raw) hx : L.Val b) (ρ raw))
        (st₀.addVar y (.pub b) (st₀.lookupDeps x) (st₀.lookupDeps_lt x))
        β nd raw

theorem compiledDecisionKernel_normalized
    (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (ρ : RawNodeEnv L → VEnv L Γ)
    (st₀ : MAIDCompileState Player L B)
    (β : ProgramBehavioralProfile p) :
    let st := MAIDCompileState.ofProg B p hl hd ρ st₀
    ∀ (nd : Fin st.nextId) (raw : RawNodeEnv L),
      (∃ who, (st.descAt nd).kind = .decision who) →
      (compiledDecisionKernel B p hl hd ρ st₀ β nd raw).totalWeight = 1 := by
  intro _
  induction p generalizing st₀ with
  | ret _ =>
      intro nd raw _
      simp only [compiledDecisionKernel]
      exact FDist.totalWeight_pure _
  | letExpr x e k ih => exact ih hl hd _ _ β
  | sample x τ m D' k ih => exact ih _ _ _ _ _
  | commit x who R k ih =>
      intro nd raw ⟨w, hw⟩
      simp only [compiledDecisionKernel]
      split
      · -- headKernel wrapped in fdist_transport
        exact (fdist_transport_totalWeight _ _).trans
          (ProgramBehavioralStrategy.headKernel_normalized (β who) _)
      · exact ih _ _ _ _ _ nd raw ⟨w, hw⟩
  | reveal y _who x hx k ih => exact ih _ _ _ _ _

/-- FDist node data: non-recursive dispatch on `descAt`. Decision nodes use
`compiledDecisionKernel`. -/
noncomputable def compiledFDistData
    (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (ρ : RawNodeEnv L → VEnv L Γ)
    (st₀ : MAIDCompileState Player L B)
    (β : ProgramBehavioralProfile p) :
    let st := MAIDCompileState.ofProg B p hl hd ρ st₀
    FDistNodeData (fp := B.fintypePlayer) st.toStruct := by
  letI := B.fintypePlayer
  let st := MAIDCompileState.ofProg B p hl hd ρ st₀
  let dk := compiledDecisionKernel B p hl hd ρ st₀ β
  exact {
    dist := fun nd a =>
      let rawP := st.rawEnvOfCfg (projCfg a (st.toStruct.parents nd))
      let rawO := st.rawEnvOfCfg (projCfg a (st.toStruct.obsParents nd))
      match hdesc : st.descAt nd with
      | .chance _τ _deps cpd _cpdNorm =>
          fdist_transport (by
            change _ = CompiledNode.valType (st.descAt nd); rw [hdesc]; rfl)
            (cpd rawP)
      | .decision _τ _who _acts _hacts _hnodup _obs =>
          dk nd rawO
      | .utility _who _deps _ufn =>
          fdist_transport (by
            change _ = CompiledNode.valType (st.descAt nd); rw [hdesc]; rfl)
            (FDist.pure ())
    normalized := fun nd a => by
      dsimp only []
      split
      · next _τ _deps cpd cpdNorm hdesc =>
          exact (fdist_transport_totalWeight _ _).trans (cpdNorm _)
      · next _τ _who _acts _hacts _hnodup _obs hdesc =>
          exact compiledDecisionKernel_normalized B p hl hd ρ st₀ β
            nd _ ⟨_who, by rw [hdesc]; rfl⟩
      · next _who _deps _ufn hdesc =>
          exact (fdist_transport_totalWeight _ _).trans
            (FDist.totalWeight_pure _)
  }

private noncomputable def compiledFDistData'
    (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (ρ : RawNodeEnv L → VEnv L Γ)
    (st₀ : MAIDCompileState Player L B)
    (β : ProgramBehavioralProfile p) :
    FDistNodeData (fp := B.fintypePlayer)
      (MAIDCompileState.ofProg B p hl hd ρ st₀).toStruct := by
  letI := B.fintypePlayer
  exact compiledFDistData B p hl hd ρ st₀ β

open MAID in
private theorem compiledFDistData_dist_chance
    (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (ρ : RawNodeEnv L → VEnv L Γ)
    (st₀ : MAIDCompileState Player L B)
    (β : ProgramBehavioralProfile p)
    (nd : Fin (MAIDCompileState.ofProg B p hl hd ρ st₀).nextId)
    (a : TAssign (fp := B.fintypePlayer)
      (MAIDCompileState.ofProg B p hl hd ρ st₀).toStruct)
    {τ : L.Ty} {deps : Finset Nat}
    {cpd : RawNodeEnv L → FDist (L.Val τ)}
    {cpdNorm : ∀ raw, FDist.totalWeight (cpd raw) = 1}
    (hdesc :
      (MAIDCompileState.ofProg B p hl hd ρ st₀).descAt nd =
        .chance τ deps cpd cpdNorm) :
    letI := B.fintypePlayer
    (compiledFDistData' B p hl hd ρ st₀ β).dist nd a =
      fdist_transport
        (by
          change L.Val τ =
            CompiledNode.valType ((MAIDCompileState.ofProg B p hl hd ρ st₀).descAt nd)
          rw [hdesc]
          rfl)
        (cpd ((MAIDCompileState.ofProg B p hl hd ρ st₀).rawEnvOfCfg
          (projCfg a ((MAIDCompileState.ofProg B p hl hd ρ st₀).toStruct.parents nd)))) := by
  letI := B.fintypePlayer
  simp only [compiledFDistData', compiledFDistData]
  split
  · next _ _ cpd₁ _ hdesc₁ =>
      have heq := hdesc₁.symm.trans hdesc
      change CompiledNode.chance _ _ cpd₁ _ = CompiledNode.chance τ deps cpd cpdNorm at heq
      injection heq with h1 _ h3; subst h1; cases h3; rfl
  · next _ _ _ _ _ _ hdesc₁ =>
      exact absurd (hdesc₁.symm.trans hdesc :
        CompiledNode.decision _ _ _ _ _ _ = .chance τ deps cpd cpdNorm) nofun
  · next _ _ _ hdesc₁ =>
      exact absurd (hdesc₁.symm.trans hdesc :
        CompiledNode.utility _ _ _ = .chance τ deps cpd cpdNorm) nofun

open MAID in
private theorem compiledFDistData_dist_decision
    (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (ρ : RawNodeEnv L → VEnv L Γ)
    (st₀ : MAIDCompileState Player L B)
    (β : ProgramBehavioralProfile p)
    (nd : Fin (MAIDCompileState.ofProg B p hl hd ρ st₀).nextId)
    (a : TAssign (fp := B.fintypePlayer)
      (MAIDCompileState.ofProg B p hl hd ρ st₀).toStruct)
    {τ : L.Ty} {who : Player} {acts : List (L.Val τ)}
    {hacts : acts ≠ []} {hnodup : acts.Nodup} {obs : Finset Nat}
    (hdesc :
      (MAIDCompileState.ofProg B p hl hd ρ st₀).descAt nd =
        .decision τ who acts hacts hnodup obs) :
    letI := B.fintypePlayer
    (compiledFDistData' B p hl hd ρ st₀ β).dist nd a =
      compiledDecisionKernel B p hl hd ρ st₀ β nd
        ((MAIDCompileState.ofProg B p hl hd ρ st₀).rawEnvOfCfg
          (projCfg a ((MAIDCompileState.ofProg B p hl hd ρ st₀).toStruct.obsParents nd))) := by
  letI := B.fintypePlayer
  simp only [compiledFDistData', compiledFDistData]
  split
  · next _ _ _ _ hdesc₁ =>
      exact absurd (hdesc₁.symm.trans hdesc :
        CompiledNode.chance _ _ _ _ = .decision τ who acts hacts hnodup obs) nofun
  · next _ _ _ _ _ _ hdesc₁ => rfl
  · next _ _ _ hdesc₁ =>
      exact absurd (hdesc₁.symm.trans hdesc :
        CompiledNode.utility _ _ _ = .decision τ who acts hacts hnodup obs) nofun

open MAID in
private theorem compiledFDistData_dist_utility
    (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (ρ : RawNodeEnv L → VEnv L Γ)
    (st₀ : MAIDCompileState Player L B)
    (β : ProgramBehavioralProfile p)
    (nd : Fin (MAIDCompileState.ofProg B p hl hd ρ st₀).nextId)
    (a : TAssign (fp := B.fintypePlayer)
      (MAIDCompileState.ofProg B p hl hd ρ st₀).toStruct)
    {who : Player} {deps : Finset Nat} {ufn : RawNodeEnv L → ℝ}
    (hdesc :
      (MAIDCompileState.ofProg B p hl hd ρ st₀).descAt nd =
        .utility who deps ufn) :
    letI := B.fintypePlayer
    (compiledFDistData' B p hl hd ρ st₀ β).dist nd a =
      fdist_transport
        (by
          change Unit =
            CompiledNode.valType ((MAIDCompileState.ofProg B p hl hd ρ st₀).descAt nd)
          rw [hdesc]
          rfl)
        (FDist.pure ()) := by
  letI := B.fintypePlayer
  simp only [compiledFDistData', compiledFDistData]
  split
  · next _ _ _ _ hdesc₁ =>
      exact absurd (hdesc₁.symm.trans hdesc :
        CompiledNode.chance _ _ _ _ = .utility who deps ufn) nofun
  · next _ _ _ _ _ _ hdesc₁ =>
      exact absurd (hdesc₁.symm.trans hdesc :
        CompiledNode.decision _ _ _ _ _ _ = .utility who deps ufn) nofun
  · next _ _ _ hdesc₁ =>
      have heq := hdesc₁.symm.trans hdesc
      change CompiledNode.utility _ _ _ = CompiledNode.utility who deps ufn at heq
      rfl

@[congr] theorem FDist.toPMF_congr [DecidableEq α]
    {d₁ d₂ : FDist α} {h₁ h₂} (heq : d₁ = d₂) :
    FDist.toPMF d₁ h₁ = FDist.toPMF d₂ h₂ := by subst heq; rfl

-- `toStruct_kind` moved to CompileStructural.lean

@[simp] theorem toStruct_Val (st : MAIDCompileState Player L B) (nd : Fin st.nextId) :
    st.toStruct.Val (fp := B.fintypePlayer) nd = CompiledNode.valType (st.descAt nd) := rfl

-- Extensional bridge infrastructure (kernel-independent):
-- Restored from git, adapted for 6-field decision nodes.
-- Extensional bridge: FDist-level lemmas

open MAID in
/-- `rawOfTAssign` is invariant under `updateAssign` at utility nodes,
because `taggedOfVal (.utility ..) _ = none` regardless of the value. -/
theorem foldl_evalStepFDist_cons [Fintype Player]
    {S : MAID.Struct Player n}
    (data : FDistNodeData S) (nd : Fin n) (rest : List (Fin n))
    (acc : FDist (TAssign S)) :
    (nd :: rest).foldl (evalStepFDist data) acc =
      rest.foldl (evalStepFDist data) (evalStepFDist data acc nd) := by
  rfl

private theorem fdist_eq_pure_of_unique {α : Type} [DecidableEq α] [Unique α]
    (d : FDist α) (hnorm : FDist.totalWeight d = 1) (x : α) :
    d = FDist.pure x := by
  apply Finsupp.ext
  intro a
  have hsum : d.sum (fun _ w => w) = d default := by
    exact Finsupp.sum_unique (f := d) (g := fun _ w => w) (by simp)
  rw [FDist.totalWeight] at hnorm
  rw [hsum] at hnorm
  have ha : a = default := Subsingleton.elim _ _
  rw [ha]
  have hx : x = default := Subsingleton.elim _ _
  rw [hx]
  simpa [FDist.pure] using hnorm

theorem evalStepFDist_utility_pure
    (st : MAIDCompileState Player L B)
    (data : FDistNodeData (fp := B.fintypePlayer) st.toStruct)
    (nd : Fin st.nextId)
    (hutility : ∃ who, (st.descAt nd).kind = .utility who)
    (a : TAssign (fp := B.fintypePlayer) st.toStruct) :
    evalStepFDist (fp := B.fintypePlayer) data (FDist.pure a) nd =
      FDist.pure (updateAssign (fp := B.fintypePlayer) a nd default) := by
  letI := B.fintypePlayer
  rcases hutility with ⟨who, hwho⟩
  have hkind : st.toStruct.kind nd = .utility who := by
    simpa using hwho
  letI : Unique (st.toStruct.Val nd) := st.toStruct.utility_unique nd who hkind
  have hdist : data.dist nd a = FDist.pure default := by
    have hnorm := data.normalized nd a
    exact fdist_eq_pure_of_unique _ hnorm default
  rw [evalStepFDist, FDist.pure_bind, hdist, FDist.pure_bind]

theorem evalStepFDist_utility_map_eq
    (st : MAIDCompileState Player L B)
    (data : FDistNodeData (fp := B.fintypePlayer) st.toStruct)
    (nd : Fin st.nextId)
    (hutility : ∃ who, (st.descAt nd).kind = .utility who)
    (f : TAssign (fp := B.fintypePlayer) st.toStruct → α)
    [DecidableEq α]
    (hf : ∀ a v, f (updateAssign (fp := B.fintypePlayer) a nd v) = f a)
    (acc : FDist (TAssign (fp := B.fintypePlayer) st.toStruct)) :
    FDist.map f (evalStepFDist (fp := B.fintypePlayer) data acc nd) = FDist.map f acc := by
  letI := B.fintypePlayer
  have hinner : ∀ a,
      FDist.bind (data.dist nd a) (fun v => FDist.pure (updateAssign a nd v)) =
        FDist.pure (updateAssign a nd default) := by
    intro a
    simpa [evalStepFDist, FDist.pure_bind] using
      (evalStepFDist_utility_pure st data nd hutility a)
  have hstep :
      evalStepFDist data acc nd =
        FDist.bind acc (fun a => FDist.pure (updateAssign a nd default)) := by
    unfold evalStepFDist
    congr 1
    funext a
    exact hinner a
  rw [hstep, FDist.bind_map]
  rw [show
    (fun a => FDist.map f (FDist.pure (updateAssign a nd default))) =
      (fun a => FDist.pure (f a)) by
        funext a
        rw [← FDist.bind_pure_comp (FDist.pure (updateAssign a nd default)) f, FDist.pure_bind]
        simp [hf a default]]
  rw [FDist.bind_pure_comp]

/-- Folding `evalStepFDist` over utility-only nodes, then mapping through
`f`, equals mapping `f` over the initial accumulator — because utility
nodes draw `default` and `rawOfTAssign` is invariant at utility positions. -/
theorem foldl_utility_map_eq
    (st : MAIDCompileState Player L B)
    (data : FDistNodeData (fp := B.fintypePlayer) st.toStruct)
    (nodes : List (Fin st.nextId))
    (hutility : ∀ nd ∈ nodes,
      ∃ who, (st.descAt nd).kind = .utility who)
    (f : TAssign (fp := B.fintypePlayer) st.toStruct → α)
    [DecidableEq α]
    (hf : ∀ a nd v,
      f (updateAssign (fp := B.fintypePlayer) a nd v) = f a)
    (acc : FDist (TAssign (fp := B.fintypePlayer) st.toStruct)) :
    FDist.map f (nodes.foldl (evalStepFDist (fp := B.fintypePlayer) data) acc) =
      FDist.map f acc := by
  letI := B.fintypePlayer
  induction nodes generalizing acc with
  | nil => rfl
  | cons nd rest ih =>
      simp only [List.foldl_cons]
      calc
        FDist.map f (rest.foldl (evalStepFDist data) (evalStepFDist data acc nd)) =
            FDist.map f (evalStepFDist data acc nd) := by
              exact ih (fun nd' hnd' => hutility nd' (by simp [hnd'])) _
        _ = FDist.map f acc := by
              apply evalStepFDist_utility_map_eq st data nd (hutility nd (by simp))
              intro a v
              exact hf a nd v

theorem MAIDCompileState.rawEnvOfCfg_proj_eq_select
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

private def HasVar.toVHasVarPub
    {Γ : VCtx Player L} {x : VarId} {τ : L.Ty} :
    HasVar (erasePubVCtx Γ) x τ →
      VHasVar (pubVCtx Γ) x (.pub τ) := by
  induction Γ with
  | nil =>
      intro h
      exact nomatch h
  | cons hd tl ih =>
      obtain ⟨y, σ⟩ := hd
      cases σ with
      | pub υ =>
          simp only [erasePubVCtx, pubVCtx]
          intro h
          cases h with
          | here => exact .here
          | there h' => exact .there (ih h')
      | hidden p υ =>
          simp only [erasePubVCtx, pubVCtx]
          intro h
          exact ih h

omit [DecidableEq Player] in
/-- The round-trip `toVHasVar hx |>.2.1 |>.toErased` gives back `hx` (up to
the base-equality cast). We prove this on `Env` values directly, avoiding
the need to state `HasVar` equality. -/
private theorem VEnv.eraseEnv_toErased_eq :
    {Γ : VCtx Player L} →
    (env : VEnv L Γ) →
    {x : VarId} → {b : L.Ty} →
    (hx : HasVar (eraseVCtx Γ) x b) →
    HEq (env.eraseEnv x
        (hx.toVHasVar (Player := Player) (L := L)).1.base
        (hx.toVHasVar (Player := Player) (L := L)).2.1.toErased)
      (env.eraseEnv x b hx)
  | (_, _) :: _, _, _, _, .here => HEq.rfl
  | _ :: _, env, _, _, .there hx =>
      eraseEnv_toErased_eq (fun a b h => env a b (.there h)) hx

omit [DecidableEq Player] in
@[simp] private theorem VEnv.erasePubEnv_get
    {Γ : VCtx Player L}
    (env : VEnv L Γ)
    {x : VarId} {τ : L.Ty}
    (hx : HasVar (erasePubVCtx Γ) x τ) :
    VEnv.erasePubEnv env x τ hx =
      env x (.pub τ) (VHasVar.ofPubVCtx (HasVar.toVHasVarPub hx)) := by
  induction Γ generalizing x τ with
  | nil =>
      exact nomatch hx
  | cons hd tl ih =>
      obtain ⟨y, σ⟩ := hd
      cases σ with
      | pub υ =>
          cases hx with
          | here =>
              rfl
          | there hx' =>
              simpa [VEnv.erasePubEnv, HasVar.toVHasVarPub] using
                (ih (env := fun a b h => env a b (VHasVar.there h)) hx')
      | hidden p υ =>
          simpa [VEnv.erasePubEnv, HasVar.toVHasVarPub] using
            (ih (env := fun a b h => env a b (VHasVar.there h)) hx)

omit [DecidableEq Player] in
@[simp] private theorem VEnv.eraseEnv_get_of_erased
    {Γ : VCtx Player L}
    (env : VEnv L Γ)
    {x : VarId} {τ : BindTy Player L}
    (hx : VHasVar (L := L) Γ x τ) :
    VEnv.eraseEnv env x τ.base hx.toErased = env x τ hx := by
  induction hx with
  | here =>
      rfl
  | there hx ih =>
      simpa [VEnv.eraseEnv] using
        (ih (env := fun a b h => env a b (VHasVar.there h)))

theorem mem_viewVCtx_map_fst_of_visible
    {Γ : VCtx Player L} {who : Player} {x : VarId}
    (hx : x ∈ visibleVars (L := L) who Γ) :
    x ∈ (viewVCtx who Γ).map Prod.fst := by
  induction Γ with
  | nil => simp [visibleVars] at hx
  | cons hd tl ih =>
      obtain ⟨y, σ⟩ := hd
      cases σ with
      | pub υ =>
          simp only [visibleVars] at hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · simp [viewVCtx, canSee]
          · have := ih hx; simp [viewVCtx, canSee, this]
      | hidden owner υ =>
          by_cases hown : who = owner
          · subst hown
            simp only [visibleVars, ite_true] at hx
            simp only [viewVCtx, canSee]
            rcases Finset.mem_insert.mp hx with rfl | hx
            · exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ (ih hx)
          · simp only [visibleVars, hown, ite_false] at hx
            simp only [viewVCtx, canSee, hown]
            exact ih hx

private theorem eval_pubExpr_insensitive_of_ctxDeps
    (st : MAIDCompileState Player L B)
    {Γ : VCtx Player L}
    (ρ : RawNodeEnv L → VEnv L Γ)
    (hρ_var : EnvRespectsLookupDeps st ρ)
    {τ : L.Ty}
    (e : L.Expr (erasePubVCtx Γ) τ)
    (j : Nat)
    (hj : j ∉ st.ctxDeps Γ) :
    InsensitiveTo (fun raw => L.eval e (VEnv.erasePubEnv (ρ raw))) j := by
  intro raw tv
  apply L.expr_deps_sound
  intro x τ' hx hmem
  let hxPub : VHasVar (L := L) (pubVCtx Γ) x (.pub τ') := HasVar.toVHasVarPub hx
  let hxΓ : VHasVar (L := L) Γ x (.pub τ') := VHasVar.ofPubVCtx hxPub
  have hj' : j ∉ st.lookupDeps x := by
    intro hjx
    exact hj (st.lookupDeps_subset_ctxDeps_of_hasVar hxΓ hjx)
  simpa [VEnv.erasePubEnv_get, hxPub, hxΓ] using
    (hρ_var hxΓ j hj' raw tv)

theorem eval_pubExpr_insensitive_of_pubCtxDeps
    (st : MAIDCompileState Player L B)
    {Γ : VCtx Player L}
    (ρ : RawNodeEnv L → VEnv L Γ)
    (hρ_var : EnvRespectsLookupDeps st ρ)
    {τ : L.Ty}
    (e : L.Expr (erasePubVCtx Γ) τ)
    (j : Nat)
    (hj : j ∉ st.pubCtxDeps Γ) :
    InsensitiveTo (fun raw => L.eval e (VEnv.erasePubEnv (ρ raw))) j := by
  intro raw tv
  apply L.expr_deps_sound
  intro x τ' hx _hmem
  let hxPub : VHasVar (L := L) (pubVCtx Γ) x (.pub τ') := HasVar.toVHasVarPub hx
  let hxΓ : VHasVar (L := L) Γ x (.pub τ') := VHasVar.ofPubVCtx hxPub
  have hxMem : x ∈ (erasePubVCtx Γ).map Prod.fst := hx.mem_map_fst
  have hj' : j ∉ st.lookupDeps x := by
    intro hjx
    exact hj (st.lookupDeps_subset_depsOfVars_of_mem hxMem hjx)
  simpa [VEnv.erasePubEnv_get, hxPub, hxΓ] using
    (hρ_var hxΓ j hj' raw tv)

theorem projectViewEnv_insensitive_of_viewDeps
    (st : MAIDCompileState Player L B)
    {Γ : VCtx Player L}
    (ρ : RawNodeEnv L → VEnv L Γ)
    (hρ_var : EnvRespectsLookupDeps st ρ)
    (who : Player)
    (j : Nat)
    (hj : j ∉ st.viewDeps who Γ) :
    InsensitiveTo (fun raw => projectViewEnv who (VEnv.eraseEnv (ρ raw))) j := by
  intro raw tv
  apply projectViewEnv_eq_of_obsEq
  intro x τ hx hvis
  let tv' := hx.toVHasVar (Player := Player) (L := L) (Γ := Γ)
  let σ := tv'.1; let hv := tv'.2.1; let hτ := tv'.2.2.down
  have hj' : j ∉ st.lookupDeps x := by
    intro hjx
    exact hj (st.lookupDeps_subset_depsOfVars_of_mem
      (xs := (viewVCtx who Γ).map Prod.fst)
      (mem_viewVCtx_map_fst_of_visible hvis) hjx)
  have h1 := VEnv.eraseEnv_toErased_eq (ρ (raw.extend j tv)) hx
  have h2 := VEnv.eraseEnv_toErased_eq (ρ raw) hx
  -- h1, h2 : HEq (eraseEnv ... hv.toErased) (eraseEnv ... hx)
  have step1 : (ρ (raw.extend j tv)).eraseEnv _ _ hv.toErased =
      (ρ (raw.extend j tv)) _ σ hv := VEnv.eraseEnv_get_of_erased _ hv
  have step3 : (ρ raw) _ σ hv = (ρ raw).eraseEnv _ _ hv.toErased :=
    (VEnv.eraseEnv_get_of_erased _ hv).symm
  have hmid := hρ_var hv j hj' raw tv
  exact eq_of_heq (h1.symm.trans (heq_of_eq (step1.trans (hmid.trans step3))) |>.trans h2)

theorem projectViewEnv_eq_of_lookupDeps
    (st : MAIDCompileState Player L B)
    {Γ : VCtx Player L}
    (ρ : RawNodeEnv L → VEnv L Γ)
    (hρ_var : EnvRespectsLookupDeps st ρ)
    (who : Player)
    {raw₁ raw₂ : RawNodeEnv L}
    (hagrees : ∀ i, i ∈ st.viewDeps who Γ → raw₁ i = raw₂ i)
    (houtside : ∀ i, st.nextId ≤ i → raw₁ i = raw₂ i) :
    projectViewEnv who (VEnv.eraseEnv (ρ raw₁)) =
      projectViewEnv who (VEnv.eraseEnv (ρ raw₂)) := by
  apply projectViewEnv_eq_of_obsEq
  intro x τ hx hvis
  -- Use the toVHasVar projection approach (no rcases, preserves definitional links)
  let σ := (hx.toVHasVar (Player := Player) (L := L) (Γ := Γ)).1
  let hv := (hx.toVHasVar (Player := Player) (L := L) (Γ := Γ)).2.1
  have hdeps : st.lookupDeps x ⊆ st.viewDeps who Γ := by
    simpa [MAIDCompileState.viewDeps] using
      (st.lookupDeps_subset_depsOfVars_of_mem
        (xs := (viewVCtx who Γ).map Prod.fst)
        (mem_viewVCtx_map_fst_of_visible hvis))
  haveI : Nonempty (RawTaggedVal L) := by
    let ⟨v⟩ := B.toMAIDValuation.nonemptyVal L.bool
    exact ⟨⟨L.bool, v⟩⟩
  refine InsensitiveTo.eq_of_agree_on_finset st
    (f := fun raw => (ρ raw).eraseEnv x τ hx)
    (hf := fun j hj raw tv => by
      have h1 := VEnv.eraseEnv_toErased_eq (ρ (raw.extend j tv)) hx
      have h2 := VEnv.eraseEnv_toErased_eq (ρ raw) hx
      exact eq_of_heq (h1.symm.trans (heq_of_eq
        ((VEnv.eraseEnv_get_of_erased _ hv).trans
          ((hρ_var hv j hj raw tv).trans
            (VEnv.eraseEnv_get_of_erased _ hv).symm))) |>.trans h2))
    (houtside := houtside) ?_
  intro i hi
  exact hagrees i (hdeps hi)

open MAID in
theorem MAIDCompileState.rawOfTAssign_updateAssign_of_tagged
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


open MAID in
/-- at a chance node equals the stored CPD on parent data. -/
theorem compiledNodeFDist_chance_eq
    (st : MAIDCompileState Player L B)
    (rawP rawO : RawNodeEnv L)
    {τ₀ : L.Ty} {deps₀ : Finset Nat}
    {cpd₀ : RawNodeEnv L → FDist (L.Val τ₀)}
    {cpdNorm₀ : ∀ raw, FDist.totalWeight (cpd₀ raw) = 1}
    (dk : RawNodeEnv L → FDist (L.Val τ₀)) :
    compiledNodeFDist st rawP rawO (.chance τ₀ deps₀ cpd₀ cpdNorm₀) dk =
      cpd₀ rawP := rfl

open MAID in
/-- at a decision node equals the external kernel on obs data. -/
theorem compiledNodeFDist_decision_eq
    (st : MAIDCompileState Player L B)
    (rawP rawO : RawNodeEnv L)
    {τ₀ : L.Ty} {who₀ : Player} {acts₀ : List (L.Val τ₀)}
    {hacts₀ : acts₀ ≠ []} {hnodup₀ : acts₀.Nodup}
    {obs₀ : Finset Nat}
    (dk : RawNodeEnv L → FDist (L.Val τ₀)) :
    compiledNodeFDist st rawP rawO (.decision τ₀ who₀ acts₀ hacts₀ hnodup₀ obs₀) dk =
      dk rawO := rfl

-- Extensional bridge: type casts and bind lemmas

open MAID in
/-- Cast from `CompiledNode.valType c` to `CompiledNode.valType c'` along `c = c'`. -/
def castValType {c c' : CompiledNode Player L B}
    (hc : c = c') (v : CompiledNode.valType c) : CompiledNode.valType c' :=
  hc ▸ v

open MAID in
theorem taggedOfVal_chance_cast
    {c : CompiledNode Player L B}
    {τ₀ : L.Ty} {deps₀ : Finset Nat}
    {cpd₀ : RawNodeEnv L → FDist (L.Val τ₀)}
    {hn₀ : ∀ raw, FDist.totalWeight (cpd₀ raw) = 1}
    (hc : c = .chance τ₀ deps₀ cpd₀ hn₀)
    (v : CompiledNode.valType c) :
    MAIDCompileState.taggedOfVal c v = some ⟨τ₀, castValType hc v⟩ := by
  subst hc; rfl

open MAID in
/-- rawEnvOfCfg gives none at indices not in the support set. -/
theorem MAIDCompileState.rawEnvOfCfg_not_mem
    (st : MAIDCompileState Player L B)
    {ps : Finset (Fin st.nextId)}
    (cfg : Cfg (fp := B.fintypePlayer) st.toStruct ps)
    (i : Nat) (hi : i < st.nextId)
    (hmem : (⟨i, hi⟩ : Fin st.nextId) ∉ ps) :
    st.rawEnvOfCfg cfg i = none := by
  simp [rawEnvOfCfg, hi, hmem]

open MAID in
/-- rawEnvOfCfg gives none at indices ≥ nextId. -/
theorem MAIDCompileState.rawEnvOfCfg_ge_nextId
    (st : MAIDCompileState Player L B)
    {ps : Finset (Fin st.nextId)}
    (cfg : Cfg (fp := B.fintypePlayer) st.toStruct ps)
    (i : Nat) (hi : ¬(i < st.nextId)) :
    st.rawEnvOfCfg cfg i = none := by
  simp [rawEnvOfCfg, hi]

theorem taggedOfVal_type_consistent (nd : CompiledNode Player L B)
    (v₁ v₂ : CompiledNode.valType nd) :
    (∃ (τ : L.Ty) (w₁ w₂ : L.Val τ),
      MAIDCompileState.taggedOfVal nd v₁ = some ⟨τ, w₁⟩ ∧
      MAIDCompileState.taggedOfVal nd v₂ = some ⟨τ, w₂⟩) ∨
    (MAIDCompileState.taggedOfVal nd v₁ = none ∧
     MAIDCompileState.taggedOfVal nd v₂ = none) := by
  match nd, v₁, v₂ with
  | .chance τ _ _ _, v₁, v₂ => left; exact ⟨τ, v₁, v₂, rfl, rfl⟩
  | .decision τ _ _ _ _ _, v₁, v₂ => left; exact ⟨τ, v₁, v₂, rfl, rfl⟩
  | .utility _ _ _, _, _ => right; exact ⟨rfl, rfl⟩

open MAID in
/-- Two rawEnvOfCfg calls on the same state at the same member index produce
values with consistent type tags (same type or both none). -/
theorem MAIDCompileState.rawEnvOfCfg_type_consistent
    (st : MAIDCompileState Player L B)
    {ps₁ ps₂ : Finset (Fin st.nextId)}
    (cfg₁ : Cfg (fp := B.fintypePlayer) st.toStruct ps₁)
    (cfg₂ : Cfg (fp := B.fintypePlayer) st.toStruct ps₂)
    (i : Nat) (hi : i < st.nextId)
    (hmem₁ : (⟨i, hi⟩ : Fin st.nextId) ∈ ps₁)
    (hmem₂ : (⟨i, hi⟩ : Fin st.nextId) ∈ ps₂) :
    (∃ (τ : L.Ty) (v₁ v₂ : L.Val τ),
      st.rawEnvOfCfg cfg₁ i = some ⟨τ, v₁⟩ ∧
      st.rawEnvOfCfg cfg₂ i = some ⟨τ, v₂⟩) ∨
    (st.rawEnvOfCfg cfg₁ i = none ∧ st.rawEnvOfCfg cfg₂ i = none) := by
  simp only [rawEnvOfCfg, hi, dif_pos, hmem₁, hmem₂]
  exact taggedOfVal_type_consistent (st.descAt ⟨i, hi⟩) _ _

open MAID in
/-- If two raw envs have the same type tag at index `i` and `readVal` agrees,
then the full raw values agree. -/
theorem readVal_tagged_eq {raw₁ raw₂ : RawNodeEnv L}
    {τ : L.Ty} {v₁ v₂ : L.Val τ} {i : Nat}
    (h₁ : raw₁ i = some ⟨τ, v₁⟩) (h₂ : raw₂ i = some ⟨τ, v₂⟩)
    (heq : MAIDCompileState.readVal (B := B) raw₁ τ i =
      MAIDCompileState.readVal (B := B) raw₂ τ i) :
    raw₁ i = raw₂ i := by
  simp only [MAIDCompileState.readVal, h₁, ↓reduceDIte, h₂] at heq
  rw [h₁, h₂, heq]

open MAID in
theorem taggedOfVal_decision_cast
    {c : CompiledNode Player L B}
    {τ₀ : L.Ty} {who₀ : Player} {acts₀ : List (L.Val τ₀)}
    {hacts₀ : acts₀ ≠ []} {hnodup₀ : acts₀.Nodup}
    {obs₀ : Finset Nat}
    (hc : c = .decision τ₀ who₀ acts₀ hacts₀ hnodup₀ obs₀)
    (v : CompiledNode.valType c) :
    MAIDCompileState.taggedOfVal c v = some ⟨τ₀, castValType hc v⟩ := by
  subst hc; rfl

open MAID in
/-- `taggedOfVal` is injective for non-utility nodes: if two values produce the
same tagged value, the values are equal. -/
theorem taggedOfVal_injective {c : CompiledNode Player L B}
    {v₁ v₂ : CompiledNode.valType c}
    (h : MAIDCompileState.taggedOfVal c v₁ = MAIDCompileState.taggedOfVal c v₂) :
    v₁ = v₂ := by
  cases c with
  | chance τ => simp only [MAIDCompileState.taggedOfVal, Option.some.injEq, Sigma.mk.injEq,
    heq_eq_eq, true_and] at h; exact h
  | decision τ => simp only [MAIDCompileState.taggedOfVal, Option.some.injEq, Sigma.mk.injEq,
    heq_eq_eq, true_and] at h; exact h
  | utility => cases v₁; cases v₂; rfl

open MAID in
/-- `rawEnvOfCfg` is injective: two configurations that produce the same raw
environment on their support set must be equal. -/
theorem MAIDCompileState.rawEnvOfCfg_injective
    (st : MAIDCompileState Player L B)
    {ps : Finset (Fin st.nextId)}
    (cfg₁ cfg₂ : Cfg (fp := B.fintypePlayer) st.toStruct ps)
    (h : st.rawEnvOfCfg cfg₁ = st.rawEnvOfCfg cfg₂) :
    cfg₁ = cfg₂ := by
  letI := B.fintypePlayer
  funext ⟨nd, hmem⟩
  have hi := nd.isLt
  have := congr_fun h nd.val
  simp only [rawEnvOfCfg, hi, dite_true, hmem] at this
  exact taggedOfVal_injective this

open MAID in
open MAID in
private theorem compiledNodeFDist_chance_bind_eq
    {β : Type} [DecidableEq β]
    (st : MAIDCompileState Player L B)
    (rawP rawO : RawNodeEnv L)
    {c : CompiledNode Player L B}
    {τ₀ : L.Ty} {deps₀ : Finset Nat}
    {cpd₀ : RawNodeEnv L → FDist (L.Val τ₀)}
    {hn₀ : ∀ raw, FDist.totalWeight (cpd₀ raw) = 1}
    (hc : c = .chance τ₀ deps₀ cpd₀ hn₀)
    (dk : RawNodeEnv L → FDist (CompiledNode.valType c))
    (G : CompiledNode.valType c → FDist β)
    (H : L.Val τ₀ → FDist β)
    (hGH : ∀ v, G v = H (castValType hc v)) :
    FDist.bind (compiledNodeFDist st rawP rawO c dk) G =
      FDist.bind (cpd₀ rawP) H := by
  subst hc
  simp only [compiledNodeFDist]
  congr 1
  funext v
  exact hGH v

open MAID in
private theorem compiledNodeFDist_decision_bind_eq
    {β : Type} [DecidableEq β]
    (st : MAIDCompileState Player L B)
    (rawP rawO : RawNodeEnv L)
    {c : CompiledNode Player L B}
    {τ₀ : L.Ty} {who₀ : Player} {acts₀ : List (L.Val τ₀)}
    {hacts₀ : acts₀ ≠ []} {hnodup₀ : acts₀.Nodup}
    {obs₀ : Finset Nat}
    (hc : c = .decision τ₀ who₀ acts₀ hacts₀ hnodup₀ obs₀)
    (dk : RawNodeEnv L → FDist (CompiledNode.valType c))
    (G : CompiledNode.valType c → FDist β) :
    FDist.bind (compiledNodeFDist st rawP rawO c dk) G =
      FDist.bind (dk rawO) G := by
  subst hc
  rfl

open MAID in
/-- Transport + castValType cancel in a bind. -/
private theorem fdist_transport_bind_castValType
    {st : MAIDCompileState Player L B} {nd : Fin st.nextId}
    {c : CompiledNode Player L B}
    (h : CompiledNode.valType c = CompiledNode.valType (st.descAt nd))
    (hdesc : st.descAt nd = c)
    (d : FDist (CompiledNode.valType c))
    {γ : Type} [DecidableEq γ]
    (f : CompiledNode.valType c → FDist γ) :
    (fdist_transport h d).bind (fun v => f (castValType hdesc v)) = d.bind f := by
  subst hdesc; rfl

open MAID in
/-- On non-head nodes, the commit-program decision kernel agrees with the tail
kernel started from the post-commit state. -/
private theorem compiledDecisionKernel_commit_old_eq
    {Γ : VCtx Player L}
    {x : VarId} {who : Player} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore Player L ((x, .hidden who b) :: Γ)}
    (B : MAIDBackend Player L)
    (hl : Legal (.commit (b := b) x who R k))
    (hd : NormalizedDists (.commit (b := b) x who R k))
    (ρ : RawNodeEnv L → VEnv (Player := Player) L Γ)
    (st₀ : MAIDCompileState Player L B)
    (β : ProgramBehavioralProfile (P := Player) (L := L)
      (.commit (b := b) x who R k))
    (nd : Fin (MAIDCompileState.ofProg B (.commit (b := b) x who R k) hl hd ρ st₀).nextId)
    (raw : RawNodeEnv L)
    (hneq : nd.val ≠ st₀.nextId) :
    let id := st₀.nextId
    let obs := st₀.viewDeps who Γ
    let acts := allValues B b
    let hacts : acts ≠ [] := allValues_ne_nil B b
    let hnodup : acts.Nodup := allValues_nodup B b
    let ndHead : CompiledNode Player L B := .decision b who acts hacts hnodup obs
    let stNode := (st₀.addNode ndHead (by
      intro d hd'
      have hd'' : d ∈ obs := by
        simpa [ndHead, CompiledNode.parents, CompiledNode.obsParents] using hd'
      exact st₀.depsOfVars_lt _ d hd'')).2
    let st₁ := stNode.addVar x (.hidden who b) ({id}) (by
      intro d hd'; have := Finset.mem_singleton.mp hd'; subst d
      exact Nat.lt_succ_self _)
    let ρ' : RawNodeEnv L → VEnv (Player := Player) L ((x, .hidden who b) :: Γ) :=
      fun raw => VEnv.cons (τ := .hidden who b)
        (MAIDCompileState.readVal (B := B) raw b id) (ρ raw)
    compiledDecisionKernel B (.commit (b := b) x who R k)
      hl hd ρ st₀ β nd raw =
    compiledDecisionKernel B k hl.2 hd ρ' st₁
      (ProgramBehavioralProfile.tail β) nd raw := by
  intro id obs acts hacts hnodup ndHead stNode st₁ ρ'
  simp only [compiledDecisionKernel]
  split
  · next heq =>
      exact absurd heq hneq
  · rfl

open MAID in
/-- For old nodes, the commit-program kernel reduces to the tail kernel. -/
theorem compiledDecisionKernel_commit_bind_cancel
    {Γ : VCtx Player L}
    {x : VarId} {who : Player} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore Player L ((x, .hidden who b) :: Γ)}
    (B : MAIDBackend Player L)
    (hl : Legal (.commit (b := b) x who R k))
    (hd : NormalizedDists (.commit (b := b) x who R k))
    (ρ : RawNodeEnv L → VEnv (Player := Player) L Γ)
    (st₀ : MAIDCompileState Player L B)
    (β : ProgramBehavioralProfile (P := Player) (L := L)
      (.commit (b := b) x who R k))
    (nd0 : Fin (MAIDCompileState.ofProg B
      (.commit (b := b) x who R k) hl hd ρ st₀).nextId)
    (hnd0 : nd0.val = st₀.nextId)
    (hdesc0 :
      (MAIDCompileState.ofProg B
        (.commit (b := b) x who R k) hl hd ρ st₀).descAt nd0 =
          .decision b who (allValues B b)
            (allValues_ne_nil B b) (allValues_nodup B b)
            (st₀.viewDeps who Γ))
    (raw : RawNodeEnv L)
    {γ : Type} [DecidableEq γ] (f : L.Val b → FDist γ) :
    (compiledDecisionKernel B (.commit (b := b) x who R k)
      hl hd ρ st₀ β nd0 raw).bind
      (fun v => f (castValType hdesc0 v)) =
    (ProgramBehavioralStrategy.headKernel (P := Player) (L := L)
      (β who)
      (projectViewEnv who (VEnv.eraseEnv (ρ raw)))).bind f := by
  simp only [compiledDecisionKernel]
  split
  · rw [fdist_transport_bind_castValType (hdesc := hdesc0)]
  · next hne => exact absurd hnd0 hne

-- The toPMF of compiledDecisionKernel equals translateStrategy at decision nodes.
open MAID in
private theorem dk_toPMF_eq_ts
    (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (ρ : RawNodeEnv L → VEnv L Γ)
    (st₀ : MAIDCompileState Player L B)
    (β : ProgramBehavioralProfile p)
    (who : Player)
    (nd : Fin (MAIDCompileState.ofProg B p hl hd ρ st₀).nextId)
    (hk : (MAIDCompileState.ofProg B p hl hd ρ st₀).toStruct.kind (fp := B.fintypePlayer) nd =
      .decision who)
    (cfg) :
    (compiledDecisionKernel B p hl hd ρ st₀ β nd
      ((MAIDCompileState.ofProg B p hl hd ρ st₀).rawEnvOfCfg cfg)).toPMF
      (compiledDecisionKernel_normalized B p hl hd ρ st₀ β nd _ ⟨who, by
        simp only [toStruct_kind] at hk; exact hk⟩) =
      (translateStrategy B p hl hd ρ st₀ β) who ⟨⟨nd, hk⟩, cfg⟩ := by
  induction p generalizing st₀ with
  | ret =>
      simp only [compiledDecisionKernel, translateStrategy, id]
      exact (FDist.toPMF_congr rfl).trans (FDist.toPMF_pure _)
  | letExpr x e k ih => exact ih hl hd _ _ β nd hk cfg
  | sample x τ m D' k ih => exact @ih _ _ _ _ β nd hk cfg
  | @commit _ x who' b R k ih =>
      -- Both compiledDecisionKernel and translateStrategy for commit use
      -- by_cases on nd.val = st₀.nextId.
      -- Case nd = id: both produce the behavioral kernel κ
      -- Case nd ≠ id: both recurse → use ih
      simp only [compiledDecisionKernel, translateStrategy]
      split
      · -- nd.val = st₀.nextId: both produce the behavioral kernel
        -- Convert LHS to cast form, then match RHS cast form
        rw [toPMF_fdist_transport_cast]
        simp only [id, eq_mpr_eq_cast]
        congr 1
      · -- nd.val ≠ st₀.nextId: both recurse
        exact @ih _ _ _ _ _ nd hk cfg
  | reveal y who' x hx k ih => exact @ih _ _ _ _ β nd hk cfg

-- Compatibility of compiled FDist data with sem and pol

open MAID in
/-- The FDist data is compatible with the semantics and policy. -/
theorem compiledFDistData_compatible
    (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (ρ : RawNodeEnv L → VEnv L Γ)
    (st₀ : MAIDCompileState Player L B)
    (β : ProgramBehavioralProfile p) :
    FDistNodeDataCompatible (fp := B.fintypePlayer)
      (compiledFDistData B p hl hd ρ st₀ β)
      (MAIDCompileState.toSem (MAIDCompileState.ofProg B p hl hd ρ st₀))
      (compiledPolicy B p hl hd ρ st₀ β) := by
  letI := B.fintypePlayer
  intro nd a
  let st := MAIDCompileState.ofProg B p hl hd ρ st₀
  cases hdesc : st.descAt nd with
  | chance τ deps cpd cpdNorm =>
      have hdist := compiledFDistData_dist_chance B p hl hd ρ st₀ β nd a hdesc
      have hdesc' : (MAIDCompileState.ofProg B p hl hd ρ st₀).descAt nd =
          .chance τ deps cpd cpdNorm := hdesc
      -- Use conv to rewrite the FDist inside toPMF
      conv_lhs =>
        arg 1
        rw [show (compiledFDistData B p hl hd ρ st₀ β).dist nd a =
              (compiledFDistData' B p hl hd ρ st₀ β).dist nd a from rfl, hdist]
      -- Now LHS: (fdist_transport _ (cpd rawP)).toPMF _
      -- Unfold nodeDist on RHS and resolve
      unfold nodeDist
      split
      next hk =>
        -- Goal: (fdist_transport _ (cpd rawP)).toPMF _ = toSem.chanceCPD ⟨nd, _⟩ cfg
        -- Both sides are casts of (cpd rawP).toPMF via the same type equality
        simp only [MAIDCompileState.toSem]
        simp_all only [toStruct_Val, toPMF_fdist_transport, eq_mpr_eq_cast, id_eq, ne_eq]
        split
        next τ_1 _parents cpdFDist cpdNorm_1
          heq =>
          simp_all only [CompiledNode.chance.injEq]
          obtain ⟨left, right⟩ := hdesc'
          obtain ⟨left_1, right⟩ := right
          subst left left_1
          simp_all only [heq_eq_eq]
          subst right
          grind
        next τ_1 who acts hacts hnodup obs heq => simp_all only [reduceCtorEq]
        next who parents ufn heq => simp_all only [reduceCtorEq]
      next _ hk =>
        simp only [toStruct_kind, CompiledNode.kind, hdesc'] at hk; exact (nomatch hk)
      next _ hk =>
        simp only [toStruct_kind, CompiledNode.kind, hdesc'] at hk; exact (nomatch hk)
  | decision τ who acts hacts hnodup obs =>
      have hdist := compiledFDistData_dist_decision B p hl hd ρ st₀ β nd a hdesc
      have hdesc' : (MAIDCompileState.ofProg B p hl hd ρ st₀).descAt nd =
          .decision τ who acts hacts hnodup obs := hdesc
      conv_lhs =>
        arg 1
        rw [show (compiledFDistData B p hl hd ρ st₀ β).dist nd a =
              (compiledFDistData' B p hl hd ρ st₀ β).dist nd a from rfl, hdist]
      unfold nodeDist
      split
      next hk =>
        simp only [toStruct_kind, CompiledNode.kind, hdesc'] at hk; exact (nomatch hk)
      next p₁ hk =>
        simp only [compiledPolicy]
        exact (FDist.toPMF_congr rfl).trans
          (dk_toPMF_eq_ts B p hl hd ρ st₀ β p₁ nd hk _)
      next _ hk =>
        simp only [toStruct_kind, CompiledNode.kind, hdesc'] at hk; exact (nomatch hk)
  | utility who deps ufn =>
      have : Subsingleton (PMF (st.toStruct.Val nd)) := by
        rw [toStruct_Val, hdesc]
        dsimp [CompiledNode.valType]
        exact ⟨fun a b => PMF.ext fun ⟨⟩ => by
          change a () = b ()
          have ha := a.2.tsum_eq
          have hb := b.2.tsum_eq
          rw [tsum_eq_single () (fun x hx => absurd (Subsingleton.elim x ()) hx)] at ha hb
          exact ha.trans hb.symm⟩
      exact Subsingleton.elim _ _

-- Algebraic lemmas for the core bridge induction

open MAID in
/-- Bind distributes over foldl of evalStepFDist under map. -/
theorem foldl_evalStepFDist_bind_map_comm
    [Fintype Player]
    {n : Nat} {S : MAID.Struct Player n}
    (data : FDistNodeData S)
    {α : Type} [DecidableEq α]
    (f : TAssign S → α)
    {nd0 : Fin n}
    (μ : FDist (S.Val nd0))
    (nodes : List (Fin n))
    (g : S.Val nd0 → FDist (TAssign S)) :
    FDist.map f (nodes.foldl (evalStepFDist data) (μ.bind g)) =
      μ.bind (fun v => FDist.map f (nodes.foldl (evalStepFDist data) (g v))) := by
  induction nodes generalizing μ g with
  | nil => exact FDist.bind_map ..
  | cons nd' rest ih =>
      simp only [List.foldl_cons]
      rw [show evalStepFDist data (μ.bind g) nd' =
        μ.bind (fun v => evalStepFDist data (g v) nd') from by
          simp [evalStepFDist, FDist.bind_assoc]]
      exact ih _ _

open MAID in
/-- One step of evalStepFDist depends only on `data.dist nd`. -/
private theorem evalStepFDist_congr_dist
    [Fintype Player]
    {n : Nat} {S : MAID.Struct Player n}
    (data₁ data₂ : FDistNodeData S)
    (nd : Fin n)
    (heq : ∀ a, data₁.dist nd a = data₂.dist nd a)
    (acc : FDist (TAssign S)) :
    evalStepFDist data₁ acc nd = evalStepFDist data₂ acc nd := by
  unfold evalStepFDist
  congr 1; funext a; congr 1; exact heq a

open MAID in
/-- If two FDistNodeData agree on every node in a list, foldl of evalStepFDist gives the
same result for any accumulator. -/
theorem foldl_evalStepFDist_congr
    [Fintype Player]
    {n : Nat} {S : MAID.Struct Player n}
    (data₁ data₂ : FDistNodeData S)
    (nodes : List (Fin n))
    (hnodes : ∀ nd ∈ nodes, ∀ a, data₁.dist nd a = data₂.dist nd a)
    (acc : FDist (TAssign S)) :
    nodes.foldl (evalStepFDist data₁) acc =
      nodes.foldl (evalStepFDist data₂) acc := by
  induction nodes generalizing acc with
  | nil => exact Eq.refl acc
  | cons nd' rest ih =>
      simp only [List.foldl_cons]
      conv_lhs => rw [evalStepFDist_congr_dist data₁ data₂ nd'
        (hnodes nd' (.head _)) acc]
      exact ih (fun nd'' hmem a => hnodes nd'' (.tail _ hmem) a) _

-- Core FDist bridge induction

-- VarsSubCtx and related lemmas moved to CompileStructural.lean

open MAID in
private def foldFDist_bridge_goal
    (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ)
    (β : ProgramBehavioralProfile p)
    (hl : Legal p)
    (hd : NormalizedDists p)
    (ρ : RawNodeEnv L → VEnv L Γ)
    (st₀ : MAIDCompileState Player L B) : Prop :=
  let st := MAIDCompileState.ofProg B p hl hd ρ st₀
  ∀ (a₀ : TAssign (fp := B.fintypePlayer) st.toStruct),
    FDist.map (fun a => extractOutcome B p ρ st₀.nextId (rawOfTAssign st a))
      ((List.finRange st.nextId).drop st₀.nextId |>.foldl
        (evalStepFDist (fp := B.fintypePlayer) (compiledFDistData B p hl hd ρ st₀ β))
          (FDist.pure a₀))
      = nativeOutcomeDist B p β ρ st₀.nextId (rawOfTAssign st a₀)

/-- **Core FDist bridge.** -/
theorem foldFDist_map_extract_eq_nativeOutcomeDist
    (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ)
    (β : ProgramBehavioralProfile p)
    (hl : Legal p)
    (hd : NormalizedDists p)
    (hfresh : FreshBindings p)
    (ρ : RawNodeEnv L → VEnv L Γ)
    (st₀ : MAIDCompileState Player L B)
    (hvars : st₀.VarsSubCtx Γ)
    (hρ_deps : ∀ j, j ∉ (st₀.ctxDeps Γ : Finset Nat) → InsensitiveTo ρ j)
    (hρ_var : EnvRespectsLookupDeps st₀ ρ) :
    foldFDist_bridge_goal B p β hl hd ρ st₀ := by
  letI := B.fintypePlayer
  dsimp [foldFDist_bridge_goal]
  induction p generalizing st₀ with
  | ret u =>
      rename_i Γ'
      intro a₀
      let st : MAIDCompileState Player L B :=
        MAIDCompileState.ofProg B (VegasCore.ret u) hl hd ρ st₀
      let data := compiledFDistData B (VegasCore.ret u) hl hd ρ st₀ β
      have hutility :
          ∀ nd ∈ (List.finRange st.nextId).drop st₀.nextId,
            ∃ who, (st.descAt nd).kind = .utility who := by
        intro nd hnd
        have hge : st₀.nextId ≤ nd.val := by
          rcases List.mem_iff_getElem.mp hnd with ⟨i, hi, hget⟩
          have hget' := congrArg Fin.val hget
          rw [List.getElem_drop] at hget'
          simp at hget'
          omega
        exact MAIDCompileState.addUtilityNodes_all_utility
          (st := st₀) (deps := st₀.ctxDeps Γ')
          (hdeps := st₀.depsOfVars_lt (Γ'.map Prod.fst))
          (ufn := fun who raw => ((evalPayoffs u (ρ raw)) who : ℝ))
          (players := Finset.univ.toList) (i := nd) hge
      have hfold :
          ∀ (nodes : List (Fin st.nextId))
            (hnodes : ∀ nd ∈ nodes, ∃ who, (st.descAt nd).kind = .utility who)
            (acc : FDist (TAssign st.toStruct)),
          FDist.map (fun a => extractOutcome B (VegasCore.ret u) ρ st₀.nextId (rawOfTAssign st a))
            (List.foldl (evalStepFDist data) acc nodes) =
          FDist.map (fun a => extractOutcome B (VegasCore.ret u) ρ st₀.nextId (rawOfTAssign st a))
            acc := by
        intro nodes hnodes acc
        induction nodes generalizing acc with
        | nil => rfl
        | cons nd rest ih =>
          simp only [List.foldl_cons]
          rw [ih (fun nd' hnd' => hnodes nd' (by simp [hnd']))
            (evalStepFDist data acc nd)]
          have hnd := hnodes nd (by simp)
          apply evalStepFDist_utility_map_eq st data nd hnd
          intro a v; congr 1
          exact rawOfTAssign_updateAssign_utility st a nd v hnd
      rw [hfold _ hutility, FDist.map_pure]
      simp [extractOutcome, nativeOutcomeDist]; rfl
  | letExpr x e k ih =>
      rename_i Γ' b
      intro a₀
      have hxΓ : Fresh x Γ' := hfresh.1
      have hxvars : x ∉ st₀.vars.map Prod.fst := fun hxmem => hxΓ (hvars x hxmem)
      let ρ' : RawNodeEnv L → VEnv L ((x, .pub b) :: Γ') :=
        fun raw => VEnv.cons (τ := .pub b) (L.eval e (VEnv.erasePubEnv (ρ raw))) (ρ raw)
      let st₁ := st₀.addVar x (.pub b) (st₀.pubCtxDeps Γ') (st₀.depsOfVars_lt _)
      have hvars₁ : st₁.VarsSubCtx ((x, .pub b) :: Γ') := by
        simpa [st₁] using st₀.VarsSubCtx_letExpr_step hvars x hxΓ
      have hρ'_deps : ∀ j, j ∉ st₁.ctxDeps ((x, .pub b) :: Γ') → InsensitiveTo ρ' j := by
        intro j hj raw tv
        have hj' : j ∉ st₀.ctxDeps Γ' := by
          simpa [st₁, st₀.ctxDeps_letExpr_step x hxΓ hxvars] using hj
        have hρj := hρ_deps j hj' raw tv
        exact VEnv.cons_ext (by simp [hρj]) hρj
      have hρ'_var : EnvRespectsLookupDeps st₁ ρ' := by
        intro y τ hy j hj raw tv
        cases hy with
        | here =>
            have hj' : j ∉ st₀.pubCtxDeps Γ' := by
              simpa [st₁, st₀.lookupDeps_addVar_eq_self_of_fresh x (.pub b) (st₀.pubCtxDeps Γ')
                (st₀.depsOfVars_lt _) hxvars] using hj
            simpa [ρ', VEnv.get] using
              (eval_pubExpr_insensitive_of_pubCtxDeps st₀ ρ hρ_var e j hj' raw tv)
        | there hy' =>
            have hxy : y ≠ x := by
              intro hEq
              exact hxΓ (hEq.symm ▸ hy'.mem_map_fst)
            have hj' : j ∉ st₀.lookupDeps y := by
              simpa [st₁, st₀.lookupDeps_addVar_eq_of_ne x (.pub b) (st₀.pubCtxDeps Γ')
                (st₀.depsOfVars_lt _) hxy] using hj
            simpa [ρ', VEnv.get, VEnv.cons_get_there] using hρ_var hy' j hj' raw tv
      exact ih β hl hd hfresh.2 ρ' st₁ hvars₁ hρ'_deps hρ'_var a₀
  | sample x τ m D' k ih =>
      rename_i Γ'
      intro a₀
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
      let ρ' : RawNodeEnv L → VEnv L ((x, τ) :: Γ') :=
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
                (by
                  intro d hd'
                  have := Finset.mem_singleton.mp hd'
                  subst d
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
                (by
                  intro d hd'
                  have := Finset.mem_singleton.mp hd'
                  subst d
                  exact Nat.lt_succ_self id)
                hxy
            have hlookupNode : stNode.lookupDeps y = st₀.lookupDeps y := by
              simpa [stNode] using st₀.lookupDeps_addNode nd hndeps y
            have hj' : j ∉ st₀.lookupDeps y := by simpa [hlookupVar, hlookupNode] using hj
            simpa [ρ', VEnv.get, VEnv.cons_get_there] using hρ_var hy' j hj' raw tv
      let st : MAIDCompileState Player L B := MAIDCompileState.ofProg B k hl hd.2 ρ' st₁
      let data := compiledFDistData B k hl hd.2 ρ' st₁ β
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
      have hρeq :
          ρ (st.rawEnvOfCfg (projCfg a₀ (st.toStruct.parents nd0))) =
            ρ (rawOfTAssign st a₀) := by
        have hrawP : st.rawEnvOfCfg (projCfg a₀ (st.toStruct.parents nd0)) =
            fun i => if i < st.nextId then
              if i ∈ deps then rawOfTAssign st a₀ i else none else none := by
          apply st.rawEnvOfCfg_proj_eq_select a₀ (st.toStruct.parents nd0) deps
          intro i hi
          simp only [st.mem_toStruct_parents_iff nd0 hi, hdesc0, nd, CompiledNode.parents]
        rw [hrawP]
        simpa [deps] using (eq_on_ctxDeps_rawOfTAssign (st := st) (deps := deps) hρ_deps a₀)
      let μ : FDist (st.toStruct.Val nd0) := data.dist nd0 a₀
      let f : TAssign st.toStruct → Outcome Player :=
        fun a => extractOutcome B (VegasCore.sample x τ m D' k) ρ st₀.nextId (rawOfTAssign st a)
      have hih := ih β hl hd.2 hfresh.2 ρ' st₁ hvars₁ hρ'_deps hρ'_var
      -- Use compiledFDistData_dist_chance instead of inline hμ proof
      have hμ := compiledFDistData_dist_chance B k hl hd.2 ρ' st₁ β nd0 a₀ hdesc0
      -- Main step: peel off nd0, use bind-map comm, apply IH, cancel transport
      have hmain :
          FDist.map f
              ((List.finRange st.nextId).drop id |>.foldl (evalStepFDist data) (FDist.pure a₀)) =
            nativeOutcomeDist B (VegasCore.sample x τ m D' k) β ρ
              st₀.nextId (rawOfTAssign st a₀) := by
        rw [hdrop]
        simp only [List.foldl_cons, evalStepFDist, FDist.pure_bind]
        -- Use foldl_evalStepFDist_bind_map_comm instead of inline hbindmap_aux
        rw [foldl_evalStepFDist_bind_map_comm data f μ
          ((List.finRange st.nextId).drop st₁.nextId)
          (fun v => FDist.pure (updateAssign a₀ nd0 v))]
        let H : L.Val τ.base → FDist (Outcome Player) :=
          fun w => nativeOutcomeDist B k β ρ' (id + 1)
            ((rawOfTAssign st a₀).extend id ⟨τ.base, w⟩)
        have hGH : ∀ v, (fun v => FDist.map f (List.foldl (evalStepFDist data)
            (FDist.pure (updateAssign a₀ nd0 v))
            (List.drop st₁.nextId (List.finRange st.nextId)))) v =
            H (castValType hdesc0 v) := by
          intro v
          have h1 : st₁.nextId = id + 1 := by
            simp [st₁, stNode, id, MAIDCompileState.addVar, MAIDCompileState.addNode]
          have h2 : rawOfTAssign st (updateAssign a₀ nd0 v) =
              (rawOfTAssign st a₀).extend id ⟨τ.base, castValType hdesc0 v⟩ :=
            MAIDCompileState.rawOfTAssign_updateAssign_of_tagged st a₀ nd0
              v ⟨τ.base, castValType hdesc0 v⟩ (taggedOfVal_chance_cast hdesc0 v)
          exact (hih (updateAssign a₀ nd0 v)).trans (by rw [h1, h2])
        conv_lhs => rw [show (fun v => FDist.map f (List.foldl (evalStepFDist data)
            (FDist.pure (updateAssign a₀ nd0 v))
            (List.drop st₁.nextId (List.finRange st.nextId)))) =
          (fun v => H (castValType hdesc0 v)) from funext hGH]
        -- Use compiledFDistData_dist_chance for μ
        rw [show μ = _ from hμ]
        rw [fdist_transport_bind_castValType (hdesc := hdesc0)]
        -- Now: (cpdFDist rawP).bind H = (cpdFDist rawTAssign).bind H
        -- These differ only in the environment argument to ρ
        congr 1
        exact congrArg (fun env => L.evalDist D' (VEnv.eraseDistEnv τ m env)) hρeq
      exact hmain
  | @commit _ x who b R k ih =>
      rename_i Γ'
      intro a₀
      have hxΓ : Fresh x Γ' := hfresh.1
      have hxvars : x ∉ st₀.vars.map Prod.fst := by
        intro hxmem; exact hxΓ (hvars x hxmem)
      let obs := st₀.viewDeps who Γ'
      let acts := allValues B b
      have hacts : acts ≠ [] := allValues_ne_nil B b
      have hnodup : acts.Nodup := allValues_nodup B b
      let id := st₀.nextId
      let nd : CompiledNode Player L B := .decision b who acts hacts hnodup obs
      have hndeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st₀.nextId := by
        intro d hd'; have hd'' : d ∈ obs := by
          simpa [nd, CompiledNode.parents, CompiledNode.obsParents] using hd'
        exact st₀.depsOfVars_lt _ d hd''
      let stNode := (st₀.addNode nd hndeps).2
      let st₁ := stNode.addVar x (.hidden who b) ({id}) (by
        intro d hd'; have := Finset.mem_singleton.mp hd'; subst d
        exact Nat.lt_succ_self _)
      let ρ' : RawNodeEnv L → VEnv (Player := Player) L ((x, .hidden who b) :: Γ') :=
        fun raw => VEnv.cons (τ := .hidden who b)
          (MAIDCompileState.readVal (B := B) raw b id) (ρ raw)
      have hvars₁ : st₁.VarsSubCtx ((x, .hidden who b) :: Γ') := by
        simpa [st₁, stNode, nd, obs, id] using
          st₀.VarsSubCtx_addNode_addVar_singleton_step hvars nd hndeps x (.hidden who b) hxΓ
      have hctx₁ : st₁.ctxDeps ((x, .hidden who b) :: Γ') = {id} ∪ st₀.ctxDeps Γ' := by
        simpa [st₁, stNode, nd, obs, id] using
          st₀.ctxDeps_addNode_addVar_singleton_cons_eq_of_fresh
            nd hndeps x (.hidden who b) hxΓ hxvars
      have hρ'_deps : ∀ j, j ∉ st₁.ctxDeps ((x, .hidden who b) :: Γ') → InsensitiveTo ρ' j := by
        intro j hj raw tv
        have hjid : j ≠ id := by intro hEq; apply hj; simp [hctx₁, hEq]
        have hj' : j ∉ st₀.ctxDeps Γ' := by intro hmem; apply hj; simp [hctx₁, hmem]
        have hρj := hρ_deps j hj' raw tv
        exact VEnv.cons_ext (readVal_extend_ne (B := B) raw j id tv b hjid.symm) hρj
      have hρ'_var : EnvRespectsLookupDeps st₁ ρ' := by
        intro y σ hy j hj raw tv
        cases hy with
        | here =>
            have hlookup : st₁.lookupDeps x = ({id} : Finset Nat) := by
              simpa [st₁] using
                stNode.lookupDeps_addVar_eq_self_of_fresh x (BindTy.hidden who b) {id}
                  (by
                    intro d hd'
                    have := Finset.mem_singleton.mp hd'
                    subst d
                    exact Nat.lt_succ_self id)
                  (by
                    simpa [stNode, MAIDCompileState.addNode] using hxvars)
            have hjSet : j ∉ ({id} : Finset Nat) := by
              simpa [hlookup] using hj
            have hjid : j ≠ id := by
              simpa [Finset.mem_singleton] using hjSet
            simpa [ρ', VEnv.get, readVal_extend_ne, hjid] using
              (readVal_extend_ne (B := B) raw j id tv b hjid.symm)
        | there hy' =>
            have hxy : y ≠ x := by
              intro hEq
              exact hxΓ (hEq.symm ▸ hy'.mem_map_fst)
            have hlookupVar : st₁.lookupDeps y = stNode.lookupDeps y := by
              simpa [st₁] using
                stNode.lookupDeps_addVar_eq_of_ne x (BindTy.hidden who b) {id}
                  (by
                    intro d hd'
                    have := Finset.mem_singleton.mp hd'
                    subst d
                    exact Nat.lt_succ_self id)
                  hxy
            have hlookupNode : stNode.lookupDeps y = st₀.lookupDeps y := by
              simpa [stNode] using st₀.lookupDeps_addNode nd hndeps y
            have hj' : j ∉ st₀.lookupDeps y := by
              simpa [hlookupVar, hlookupNode] using hj
            simpa [ρ', VEnv.get, VEnv.cons_get_there] using hρ_var hy' j hj' raw tv
      let st : MAIDCompileState Player L B := MAIDCompileState.ofProg B k hl.2 hd ρ' st₁
      let dataCommit := compiledFDistData B (VegasCore.commit x who R k) hl hd ρ st₀ β
      let dataTail := compiledFDistData B k hl.2 hd ρ' st₁
        (ProgramBehavioralProfile.tail β)
      have hst :
          MAIDCompileState.ofProg B (VegasCore.commit x who R k) hl hd ρ st₀ = st := by
        rfl
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
      have hrawO :
          st.rawEnvOfCfg (projCfg a₀ (st.toStruct.obsParents nd0)) =
            fun i => if i < st.nextId then
              if i ∈ obs then rawOfTAssign st a₀ i else none else none := by
        apply st.rawEnvOfCfg_proj_eq_select a₀ (st.toStruct.obsParents nd0) obs
        intro i hi
        simp only [st.mem_toStruct_obsParents_iff nd0 hi, hdesc0, nd, CompiledNode.obsParents]
      -- The kernel output only depends on viewDeps (obs), not all ctxDeps
      have hViewEq :
          projectViewEnv (P := Player) (L := L) who
            (VEnv.eraseEnv (ρ (st.rawEnvOfCfg
              (projCfg a₀ (st.toStruct.obsParents nd0))))) =
          projectViewEnv (P := Player) (L := L) who
            (VEnv.eraseEnv (ρ (rawOfTAssign st a₀))) := by
        rw [hrawO]
        simpa [obs] using
          (eq_on_ctxDeps_rawOfTAssign (st := st) (deps := obs)
            (f := fun raw => projectViewEnv who (VEnv.eraseEnv (ρ raw)))
            (fun j hj =>
              projectViewEnv_insensitive_of_viewDeps st₀ ρ hρ_var who j
                (by simpa [obs] using hj))
            a₀)
      have hdist_rest :
          ∀ nd' ∈ (List.finRange st.nextId).drop st₁.nextId,
            ∀ a, dataCommit.dist nd' a = dataTail.dist nd' a := by
        intro nd' hmem a
        have hge : st₁.nextId ≤ nd'.val := by
          rcases List.mem_iff_getElem.mp hmem with ⟨i, hi, hget⟩
          have hget' := congrArg Fin.val hget
          rw [List.getElem_drop] at hget'
          simp at hget'
          omega
        have hneq : nd'.val ≠ id := by
          rw [show st₁.nextId = id + 1 by
            simp [st₁, stNode, id, MAIDCompileState.addVar, MAIDCompileState.addNode]] at hge
          omega
        let rawP' := st.rawEnvOfCfg (projCfg a (st.toStruct.parents nd'))
        let rawO' := st.rawEnvOfCfg (projCfg a (st.toStruct.obsParents nd'))
        cases hdescTail : st.descAt nd' with
        | chance τ deps cpd cpdNorm =>
            have hdescCommit :
                (MAIDCompileState.ofProg B (VegasCore.commit x who R k) hl hd ρ st₀).descAt nd' =
                  .chance τ deps cpd cpdNorm := by
              simpa [hst, st] using hdescTail
            have hcommitChance :
                dataCommit.dist nd' a =
                  fdist_transport
                    (by change L.Val τ = CompiledNode.valType (st.descAt nd')
                        rw [hdescTail]
                        rfl)
                    (cpd rawP') := by
              simpa [dataCommit, hst, st, rawP'] using
                (compiledFDistData_dist_chance B (VegasCore.commit x who R k) hl hd ρ st₀ β
                  nd' a hdescCommit)
            have htailChance :
                dataTail.dist nd' a =
                  fdist_transport
                    (by change L.Val τ = CompiledNode.valType (st.descAt nd')
                        rw [hdescTail]
                        rfl)
                    (cpd rawP') := by
              simpa [dataTail, st, rawP'] using
                (compiledFDistData_dist_chance B k hl.2 hd ρ' st₁
                  (ProgramBehavioralProfile.tail β) nd' a hdescTail)
            exact hcommitChance.trans htailChance.symm
        | decision τ who' acts' hacts' hnodup' obs' =>
            have hdescCommit :
                (MAIDCompileState.ofProg B (VegasCore.commit x who R k) hl hd ρ st₀).descAt nd' =
                  .decision τ who' acts' hacts' hnodup' obs' := by
              simpa [hst, st] using hdescTail
            have hcommitDecision :
                dataCommit.dist nd' a =
                  compiledDecisionKernel B (VegasCore.commit x who R k)
                    hl hd ρ st₀ β nd' rawO' := by
              simpa [dataCommit, hst, st, rawO'] using
                (compiledFDistData_dist_decision B (VegasCore.commit x who R k) hl hd ρ st₀ β
                  nd' a hdescCommit)
            have htailDecision :
                dataTail.dist nd' a =
                  compiledDecisionKernel B k hl.2 hd ρ' st₁
                    (ProgramBehavioralProfile.tail β) nd' rawO' := by
              simpa [dataTail, st, rawO'] using
                (compiledFDistData_dist_decision B k hl.2 hd ρ' st₁
                  (ProgramBehavioralProfile.tail β) nd' a hdescTail)
            have hdec :
                compiledDecisionKernel B (VegasCore.commit x who R k) hl hd ρ st₀ β nd' rawO' =
                  compiledDecisionKernel B k hl.2 hd ρ' st₁
                    (ProgramBehavioralProfile.tail β) nd' rawO' := by
              simpa [rawO', hst, st] using
                (compiledDecisionKernel_commit_old_eq B hl hd ρ st₀ β nd' rawO' hneq)
            exact hcommitDecision.trans (hdec.trans htailDecision.symm)
        | utility who' deps' ufn =>
            have hdescCommit :
                (MAIDCompileState.ofProg B (VegasCore.commit x who R k) hl hd ρ st₀).descAt nd' =
                  .utility who' deps' ufn := by
              simpa [hst, st] using hdescTail
            have hcommitUtility :
                dataCommit.dist nd' a =
                  fdist_transport
                    (by change Unit = CompiledNode.valType (st.descAt nd')
                        rw [hdescTail]
                        rfl)
                    (FDist.pure ()) := by
              simpa [dataCommit, hst, st] using
                (compiledFDistData_dist_utility B (VegasCore.commit x who R k) hl hd ρ st₀ β
                  nd' a hdescCommit)
            have htailUtility :
                dataTail.dist nd' a =
                  fdist_transport
                    (by change Unit = CompiledNode.valType (st.descAt nd')
                        rw [hdescTail]
                        rfl)
                    (FDist.pure ()) := by
              simpa [dataTail, st] using
                (compiledFDistData_dist_utility B k hl.2 hd ρ' st₁
                  (ProgramBehavioralProfile.tail β) nd' a hdescTail)
            exact hcommitUtility.trans htailUtility.symm
      let μ : FDist (st.toStruct.Val nd0) := dataCommit.dist nd0 a₀
      let f : TAssign st.toStruct → Outcome Player :=
        fun a => extractOutcome B (VegasCore.commit x who R k) ρ st₀.nextId (rawOfTAssign st a)
      have hih := ih (ProgramBehavioralProfile.tail β) hl.2 hd
        hfresh.2 ρ' st₁ hvars₁ hρ'_deps hρ'_var
      have hmain :
          FDist.map f ((List.finRange st.nextId).drop id |>.foldl
            (evalStepFDist dataCommit) (FDist.pure a₀)) =
          nativeOutcomeDist B (VegasCore.commit x who R k) β ρ
            st₀.nextId (rawOfTAssign st a₀) := by
        rw [hdrop]
        simp only [List.foldl_cons, evalStepFDist, FDist.pure_bind]
        rw [foldl_evalStepFDist_congr dataCommit dataTail _ hdist_rest]
        rw [foldl_evalStepFDist_bind_map_comm dataTail f μ
          ((List.finRange st.nextId).drop st₁.nextId)
          (fun v => FDist.pure (updateAssign a₀ nd0 v))]
        let H : L.Val b → FDist (Outcome Player) :=
          fun w => nativeOutcomeDist B k (ProgramBehavioralProfile.tail β) ρ' (id + 1)
            ((rawOfTAssign st a₀).extend id ⟨b, w⟩)
        conv_lhs => rw [show (fun v => FDist.map f (List.foldl (evalStepFDist dataTail)
            (FDist.pure (updateAssign a₀ nd0 v))
            (List.drop st₁.nextId (List.finRange st.nextId)))) =
          (fun v => H (castValType hdesc0 v)) from funext fun v =>
            (hih (updateAssign a₀ nd0 v)).trans (by
              rw [show st₁.nextId = id + 1 by
                simp [st₁, stNode, id, MAIDCompileState.addVar, MAIDCompileState.addNode],
                MAIDCompileState.rawOfTAssign_updateAssign_of_tagged st a₀ nd0
                  v ⟨b, castValType hdesc0 v⟩ (taggedOfVal_decision_cast hdesc0 v)])]
        let rawO := st.rawEnvOfCfg (projCfg a₀ (st.toStruct.obsParents nd0))
        have hμ := compiledFDistData_dist_decision B
          (VegasCore.commit x who R k) hl hd ρ st₀ β nd0 a₀
          (by simpa [hst, st] using hdesc0)
        rw [show μ = _ from hμ]
        exact (compiledDecisionKernel_commit_bind_cancel B hl hd
          ρ st₀ β nd0 rfl hdesc0 rawO H).trans (by
          simp only [nativeOutcomeDist]
          congr 1
          exact congrArg (ProgramBehavioralStrategy.headKernel (β who)) hViewEq)
      exact hmain
  | reveal y who x hx k ih =>
      rename_i Γ' b
      intro a₀
      have hyΓ : Fresh y Γ' := hfresh.1
      have hyvars : y ∉ st₀.vars.map Prod.fst := by
        intro hymem; exact hyΓ (hvars y hymem)
      let ρ' : RawNodeEnv L → VEnv L ((y, .pub b) :: Γ') :=
        fun raw =>
          let v : L.Val b := VEnv.get (ρ raw) hx
          VEnv.cons (τ := .pub b) v (ρ raw)
      let st₁ := st₀.addVar y (.pub b) (st₀.lookupDeps x) (st₀.lookupDeps_lt x)
      have hvars₁ : st₁.VarsSubCtx ((y, .pub b) :: Γ') := by
        simpa [st₁] using st₀.VarsSubCtx_addVar hvars y _ _ _ hyΓ
      have hctx₁ : st₁.ctxDeps ((y, .pub b) :: Γ') = st₀.ctxDeps Γ' := by
        simpa [st₁] using st₀.ctxDeps_reveal_step y who x hx hyΓ hyvars
      have hρ'_deps : ∀ j, j ∉ st₁.ctxDeps ((y, .pub b) :: Γ') → InsensitiveTo ρ' j := by
        intro j hj raw tv
        have hj' : j ∉ st₀.ctxDeps Γ' := by simpa [hctx₁] using hj
        have hρj := hρ_deps j hj' raw tv
        exact VEnv.cons_ext (by simp [hρj]) hρj
      have hρ'_var : EnvRespectsLookupDeps st₁ ρ' := by
        intro z σ hz j hj raw tv
        cases hz with
        | here =>
            have hj' : j ∉ st₀.lookupDeps x := by
              simpa [st₁, st₀.lookupDeps_addVar_eq_self_of_fresh y (.pub b) (st₀.lookupDeps x)
                (st₀.lookupDeps_lt x) hyvars] using hj
            simpa [ρ', VEnv.get] using hρ_var hx j hj' raw tv
        | there hz' =>
            have hzy : z ≠ y := by
              intro hEq
              exact hyΓ (hEq.symm ▸ hz'.mem_map_fst)
            have hj' : j ∉ st₀.lookupDeps z := by
              simpa [st₁, st₀.lookupDeps_addVar_eq_of_ne y (.pub b) (st₀.lookupDeps x)
                (st₀.lookupDeps_lt x) hzy] using hj
            simpa [ρ', VEnv.get, VEnv.cons_get_there] using hρ_var hz' j hj' raw tv
      have hih := ih β hl hd hfresh.2 ρ' st₁ hvars₁ hρ'_deps hρ'_var
      exact hih a₀

-- Key bridge theorems

open MAID in
/-- **Bridge lemma.** -/
theorem maid_map_extract_eq_outcomeDistBehavioral
    (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ)
    (env : VEnv L Γ)
    (β : ProgramBehavioralProfile p)
    (hl : Legal p)
    (hd : NormalizedDists p)
    (hfresh : FreshBindings p) :
    let st := MAIDCompileState.ofProg B p hl hd (fun _ => env) .empty
    let S := st.toStruct
    let sem := MAIDCompileState.toSem st
    let pol := compiledPolicy B p hl hd (fun _ => env) .empty β
    let extract : TAssign (fp := B.fintypePlayer) S → Outcome Player :=
      fun a => extractOutcome B p (fun _ => env) 0 (rawOfTAssign st a)
    PMF.map extract (evalAssignDist (fp := B.fintypePlayer) S sem pol) =
      (outcomeDistBehavioral p β env).toPMF
        (outcomeDistBehavioral_totalWeight_eq_one hd) := by
  intro st S sem pol extract
  letI := B.fintypePlayer
  let hnat := compiled_naturalOrder st
  let σ_topo := hnat.toTopologicalOrder
  rw [evalAssignDist_eq_evalFold S sem pol σ_topo]
  let data := compiledFDistData B p hl hd (fun _ => env) .empty β
  let hcompat := compiledFDistData_compatible B p hl hd (fun _ => env) .empty β
  rw [← evalFoldFDist_toPMF_eq_evalFold data sem pol hcompat σ_topo]
  have hfold_norm := evalFoldFDist_normalized data σ_topo
  have hmap_norm : (FDist.map extract (evalFoldFDist data σ_topo)).totalWeight = 1 := by
    rw [FDist.totalWeight_map]; exact hfold_norm
  rw [← FDist.toPMF_map (evalFoldFDist data σ_topo) extract hfold_norm hmap_norm]
  apply FDist.toPMF_congr
  have key := foldFDist_map_extract_eq_nativeOutcomeDist B p β hl hd
    hfresh (fun _ => env) .empty
    (by intro x hx; simp [MAIDCompileState.empty] at hx)
    (fun _ _ _ _ => rfl)
    (envRespectsLookupDeps_const (B := B) (st := .empty) env)
    (defaultAssign st.toStruct)
  have : (MAIDCompileState.empty (B := B) (Player := Player)
    (L := L)).nextId = 0 := rfl
  rw [this, List.drop_zero] at key
  exact key.trans (nativeOutcomeDist_eq_outcomeDistBehavioral_init B p β env _)

open MAID in
/-- **B2: Vegas to MAID distribution equality (behavioral).** -/
theorem vegas_maid_dist_eq
    (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ)
    (env : VEnv L Γ)
    (β : ProgramBehavioralProfile p)
    (hl : Legal p)
    (hd : NormalizedDists p)
    (hfresh : FreshBindings p) :
    let st := MAIDCompileState.ofProg B p hl hd (fun _ => env) .empty
    let S := st.toStruct
    let sem := MAIDCompileState.toSem st
    ∃ (pol : Policy (fp := B.fintypePlayer) S)
      (extract : TAssign (fp := B.fintypePlayer) S → Outcome Player),
      PMF.map extract (evalAssignDist (fp := B.fintypePlayer) S sem pol) =
        (outcomeDistBehavioral p β env).toPMF
          (outcomeDistBehavioral_totalWeight_eq_one hd) := by
  intro st S sem
  let pol := compiledPolicy B p hl hd (fun _ => env) .empty β
  let extract : TAssign (fp := B.fintypePlayer) st.toStruct → Outcome Player :=
    fun a => extractOutcome B p (fun _ => env) 0 (rawOfTAssign st a)
  exact ⟨pol, extract,
    maid_map_extract_eq_outcomeDistBehavioral B p env β hl hd hfresh⟩

open MAID in
/-- Reverse direction. -/
theorem maid_behavioral_bridge
    (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ)
    (env : VEnv L Γ)
    (hl : Legal p)
    (hd : NormalizedDists p) (hfresh : FreshBindings p) :
    ∀ (β : ProgramBehavioralProfile p),
    let st := MAIDCompileState.ofProg B p hl hd (fun _ => env) .empty
    let S := st.toStruct
    let sem := MAIDCompileState.toSem st
    let extract : TAssign (fp := B.fintypePlayer) S → Outcome Player :=
      fun a => extractOutcome B p (fun _ => env) 0 (rawOfTAssign st a)
    ∀ (pol : Policy (fp := B.fintypePlayer) S),
    ∃ (β' : ProgramBehavioralProfile p),
      PMF.map extract (evalAssignDist (fp := B.fintypePlayer) S sem pol) =
        (outcomeDistBehavioral p β' env).toPMF
          (outcomeDistBehavioral_totalWeight_eq_one hd) := by
  sorry

end Vegas
