import GameTheory.Languages.MAID.Prefix
import Vegas.Strategic
import Vegas.MAID.Compile
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
    @Struct.NaturalOrder Player _ B.fintypePlayer st.nextId st.toStruct := by
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
    (a : @TAssign Player _ B.fintypePlayer st.nextId st.toStruct) : RawNodeEnv L :=
  let _ : Fintype Player := B.fintypePlayer
  fun i =>
  if hi : i < st.nextId then
    MAIDCompileState.taggedOfVal (st.descAt ⟨i, hi⟩) (a ⟨i, hi⟩)
  else
    none

/-- `descAt` for the new node added by `addNode`. -/
theorem MAIDCompileState.addNode_descAt_new
    (st : MAIDCompileState Player L B)
    (nd : CompiledNode Player L B)
    (hdeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId) :
    (st.addNode nd hdeps).2.descAt ⟨st.nextId, Nat.lt_succ_self _⟩ = nd := by
  simp only [descAt, addNode]
  change ((st.nodes ++ [(st.nextId, nd)])[st.nextId]'(by
    simp [st.nodes_length_eq_nextId])).2 = nd
  rw [List.getElem_append_right (by simp [st.nodes_length_eq_nextId])]
  simp [st.nodes_length_eq_nextId]

/-- `descAt` for old nodes is unchanged by `addNode`. -/
theorem MAIDCompileState.addNode_descAt_old
    (st : MAIDCompileState Player L B)
    (nd : CompiledNode Player L B)
    (hdeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId)
    (i : Fin st.nextId) :
    (st.addNode nd hdeps).2.descAt ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ = st.descAt i := by
  simp only [descAt, addNode]
  change ((st.nodes ++ [(st.nextId, nd)])[i.val]'(by
    simp [st.nodes_length_eq_nextId])).2 =
    (st.nodes[i.val]'(st.index_lt_nodes i)).2
  congr 1
  rw [List.getElem_append_left]

-- Compile-state monotonicity


/-- `addUtilityNodes` increases `nextId` by the number of players. -/
theorem MAIDCompileState.addUtilityNodes_nextId
    (st : MAIDCompileState Player L B) (deps hdeps ufn)
    (players : List Player) :
    (st.addUtilityNodes deps hdeps ufn players).nextId =
      st.nextId + players.length := by
  induction players generalizing st with
  | nil => simp [addUtilityNodes]
  | cons who rest ih =>
    simp only [addUtilityNodes, List.length_cons]
    rw [ih]; simp [addNode]; omega

/-- `ofProg` only increases `nextId`. -/
theorem MAIDCompileState.ofProg_nextId_le
    (B : MAIDBackend Player L) {Γ : VCtx Player L}
    (p : VegasCore Player L Γ) (hl ha hd)
    (ρ : RawNodeEnv L → VEnv L Γ)
    (st₀ : MAIDCompileState Player L B) :
    st₀.nextId ≤ (MAIDCompileState.ofProg B p hl ha hd ρ st₀).nextId := by
  induction p generalizing st₀ with
  | ret u =>
    letI := B.fintypePlayer; simp only [MAIDCompileState.ofProg]
    rw [MAIDCompileState.addUtilityNodes_nextId]; omega
  | letExpr x e k ih =>
    exact ih hl ha hd
      (fun raw => VEnv.cons (L.eval e (VEnv.erasePubEnv (ρ raw))) (ρ raw))
      (st₀.addVar _ _ _ _)
  | sample x τ m D' k ih =>
    refine le_trans (Nat.le_succ _) ?_
    exact ih hl ha hd.2
      (fun raw => VEnv.cons (MAIDCompileState.readVal (B := B) raw τ.base st₀.nextId) (ρ raw))
      ((st₀.addNode _ _).2.addVar _ _ _ _)
  | commit x who R k ih =>
    rename_i Γ' b
    refine le_trans (Nat.le_succ _) ?_
    exact ih hl.2 ha hd
      (fun raw => VEnv.cons (MAIDCompileState.readVal (B := B) raw b st₀.nextId) (ρ raw))
      ((st₀.addNode _ _).2.addVar _ _ _ _)
  | reveal y who x hx k ih =>
    exact ih hl ha hd
      (fun raw =>
        let env := ρ raw
        let v : L.Val _ := VEnv.get env hx
        VEnv.cons (τ := .pub _) v env)
      (st₀.addVar _ _ _ _)

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


/-- `addUtilityNodes` preserves `descAt` for old nodes. -/
theorem MAIDCompileState.addUtilityNodes_descAt_old
    (st : MAIDCompileState Player L B)
    (deps : Finset Nat) (hdeps : ∀ d ∈ deps, d < st.nextId)
    (ufn : Player → RawNodeEnv L → ℝ) (players : List Player)
    (j : Nat) (hj : j < st.nextId) :
    let stf := st.addUtilityNodes deps hdeps ufn players
    (stf.descAt ⟨j, Nat.lt_of_lt_of_le hj (by
      rw [addUtilityNodes_nextId]; omega)⟩) =
    st.descAt ⟨j, hj⟩ := by
  induction players generalizing st with
  | nil => rfl
  | cons who rest ih =>
    simp only [addUtilityNodes]
    rw [ih]; exact addNode_descAt_old st _ _ ⟨j, hj⟩

/-- All nodes added by `addUtilityNodes` are utility nodes in the struct. -/
theorem MAIDCompileState.addUtilityNodes_all_utility
    (st : MAIDCompileState Player L B)
    (deps : Finset Nat) (hdeps : ∀ d ∈ deps, d < st.nextId)
    (ufn : Player → RawNodeEnv L → ℝ) (players : List Player)
    (i : Fin (st.addUtilityNodes deps hdeps ufn players).nextId)
    (hi : st.nextId ≤ i.val) :
    let _ := B.fintypePlayer
    ∃ who, (st.addUtilityNodes deps hdeps ufn players).toStruct.kind i =
      NodeKind.utility who := by
  letI := B.fintypePlayer
  -- Suffices to show the descAt is a utility node (since toStruct.kind = descAt.kind)
  suffices h : ∃ who, ((st.addUtilityNodes deps hdeps ufn players).descAt i).kind =
      NodeKind.utility who by exact h
  induction players generalizing st with
  | nil =>
    simp only [MAIDCompileState.addUtilityNodes] at i ⊢
    exact absurd i.isLt (by omega)
  | cons who rest ih =>
    simp only [MAIDCompileState.addUtilityNodes] at i ⊢
    by_cases heq : i.val = st.nextId
    · -- i is the node just added by this step
      have hutdeps : ∀ d ∈ (CompiledNode.utility (B := B) who deps (ufn who)).parents ∪
          (CompiledNode.utility (B := B) who deps (ufn who)).obsParents, d < st.nextId := by
        intro d hd'; rcases Finset.mem_union.mp hd' with h | h <;>
          simpa [CompiledNode.parents, CompiledNode.obsParents] using hdeps d h
      have hj_lt : i.val < (st.addNode (.utility who deps (ufn who)) hutdeps).2.nextId := by
        simp [MAIDCompileState.addNode]; omega
      have hdesc : ((st.addNode (.utility who deps (ufn who)) hutdeps).2.addUtilityNodes deps
          _ ufn rest).descAt ⟨i.val, i.isLt⟩ = .utility who deps (ufn who) := by
        rw [MAIDCompileState.addUtilityNodes_descAt_old _ _ _ _ rest i.val hj_lt]
        rw [show (⟨i.val, hj_lt⟩ : Fin _) = ⟨st.nextId, Nat.lt_succ_self _⟩ from Fin.ext heq]
        exact st.addNode_descAt_new _ _
      exact ⟨who, by
        rw [show i = ⟨i.val, i.isLt⟩ from Fin.ext rfl]; simp only [hdesc]; rfl⟩
    · -- i is beyond st.nextId, use IH
      have hutdeps : ∀ d ∈ (CompiledNode.utility (B := B) who deps (ufn who)).parents ∪
          (CompiledNode.utility (B := B) who deps (ufn who)).obsParents, d < st.nextId := by
        intro d hd'; rcases Finset.mem_union.mp hd' with h | h <;>
          simpa [CompiledNode.parents, CompiledNode.obsParents] using hdeps d h
      exact ih (st.addNode (.utility who deps (ufn who)) hutdeps).2 _
        ⟨i.val, i.isLt⟩ (by simp [MAIDCompileState.addNode]; omega)

-- ofProg preserves descAt for old nodes


/-- `ofProg` preserves `descAt` for nodes below the initial `nextId`. -/
theorem MAIDCompileState.ofProg_descAt_old
    (B : MAIDBackend Player L) {Γ : VCtx Player L}
    (p : VegasCore Player L Γ) (hl ha hd)
    (ρ : RawNodeEnv L → VEnv L Γ)
    (st₀ : MAIDCompileState Player L B)
    (j : Nat) (hj : j < st₀.nextId) :
    let st := MAIDCompileState.ofProg B p hl ha hd ρ st₀
    (st.descAt ⟨j, Nat.lt_of_lt_of_le hj (ofProg_nextId_le B p hl ha hd ρ st₀)⟩) =
    st₀.descAt ⟨j, hj⟩ := by
  induction p generalizing st₀ with
  | ret u =>
    simp only [MAIDCompileState.ofProg]
    exact MAIDCompileState.addUtilityNodes_descAt_old st₀ _ _ _ _ j hj
  | letExpr x e k ih =>
    simp only [MAIDCompileState.ofProg]
    exact ih hl ha hd _ (st₀.addVar _ _ _ _) hj
  | sample x τ m D' k ih =>
    change (MAIDCompileState.ofProg B k hl ha hd.2 _ _).descAt ⟨j, _⟩ = _
    rw [ih hl ha hd.2 _ _ (Nat.lt_succ_of_lt hj)]
    simp only [MAIDCompileState.descAt, MAIDCompileState.addVar, MAIDCompileState.addNode]
    congr 1
    rw [List.getElem_append_left (by rw [st₀.nodes_length_eq_nextId]; exact hj)]
  | commit x who R k ih =>
    change (MAIDCompileState.ofProg B k hl.2 ha hd _ _).descAt ⟨j, _⟩ = _
    rw [ih hl.2 ha hd _ _ (Nat.lt_succ_of_lt hj)]
    simp only [MAIDCompileState.descAt, MAIDCompileState.addVar, MAIDCompileState.addNode]
    congr 1
    rw [List.getElem_append_left (by rw [st₀.nodes_length_eq_nextId]; exact hj)]
  | reveal y who x hx k ih =>
    simp only [MAIDCompileState.ofProg]
    exact ih hl ha hd _ (st₀.addVar _ _ _ _) hj

-- translateStrategy: translate behavioral profile into MAID policy

/-- Translate a behavioral profile into a MAID policy.

At each commit site, constructs the FDist kernel from the behavioral profile
and converts to PMF. The recursive structure mirrors `ofProg`. -/
noncomputable def translateStrategy
    (B : MAIDBackend Player L) :
    {Γ : VCtx Player L} →
      (p : VegasCore Player L Γ) →
      (hl : Legal p) → (ha : DistinctActs p) → (hd : NormalizedDists p) →
      (ρ : RawNodeEnv L → VEnv L Γ) →
      (st₀ : MAIDCompileState Player L B) →
      ProgramBehavioralProfile p →
      @MAID.Policy Player _ B.fintypePlayer
        (MAIDCompileState.ofProg B p hl ha hd ρ st₀).nextId
        (MAIDCompileState.ofProg B p hl ha hd ρ st₀).toStruct
  | _Γ, .ret _payoffs, _hl, _ha, _hd, _ρ, _st, _β => by
      letI := B.fintypePlayer
      intro _p ⟨d, cfg⟩
      -- All new nodes are utility; any decision nodes are from the initial state.
      -- Their PMF doesn't matter (the commit case overrides via pol_rest).
      exact PMF.pure default
  | _Γ, .letExpr (b := b) x e k, hl, ha, hd, ρ, st, β =>
      translateStrategy B k hl ha hd
        (fun raw =>
          let env := ρ raw
          VEnv.cons (τ := .pub b) (L.eval e (VEnv.erasePubEnv env)) env)
        (st.addVar x (.pub b) (st.ctxDeps _Γ) (st.depsOfVars_lt _))
        β
  | _Γ, .sample x τ m D' k, hl, ha, hd, ρ, st, β =>
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
      translateStrategy B k hl ha hd.2
        (fun raw =>
          let env := ρ raw
          let v := MAIDCompileState.readVal (B := B) raw τ.base id
          VEnv.cons v env)
        (st'.addVar x τ ({id}) (by
          intro d hd'
          have hdid : d = id := by simpa using hd'
          subst d; exact Nat.lt_succ_self _))
        β
  | Γ, .commit (b := b) x who R k, hl, ha, hd, ρ, st, β => by
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
      let pol_rest := translateStrategy B k hl.2 ha hd ρ' st₁
        (ProgramBehavioralProfile.tail β)
      let κ := ProgramBehavioralStrategy.headKernel (β who)
      intro p ⟨d, cfg⟩
      let st_final := MAIDCompileState.ofProg B k hl.2 ha hd ρ' st₁
      by_cases hd_eq : d.1.val = id
      · have hid_lt_st₁ : id < st₁.nextId := by
          simp [st₁, st', res, id, MAIDCompileState.addVar, MAIDCompileState.addNode]
        have hdesc0 : st₁.descAt ⟨id, hid_lt_st₁⟩ =
            .decision b who acts hacts hnodup obs := by
          simp only [st₁, MAIDCompileState.addVar, st', res]
          exact st.addNode_descAt_new (.decision b who acts hacts hnodup obs) _
        have hid_lt : id < st_final.nextId :=
          Nat.lt_of_lt_of_le hid_lt_st₁
            (MAIDCompileState.ofProg_nextId_le B k hl.2 ha hd ρ' st₁)
        have hdesc : st_final.descAt d.1 = .decision b who acts hacts hnodup obs := by
          have h := MAIDCompileState.ofProg_descAt_old B k hl.2 ha hd ρ' st₁ id hid_lt_st₁
          conv_lhs => rw [show d.1 = ⟨id, hid_lt⟩ from Fin.ext hd_eq]
          exact h.trans hdesc0
        change PMF (CompiledNode.valType (st_final.descAt d.1))
        rw [hdesc]; change PMF (L.Val b)
        exact FDist.toPMF
          (κ (projectViewEnv who
            (VEnv.eraseEnv (ρ (st_final.rawEnvOfCfg cfg)))))
          (ProgramBehavioralStrategy.headKernel_normalized (β who) _)
      · exact pol_rest p ⟨d, cfg⟩
  | _, .reveal (b := b) y who x hx k, hl, ha, hd, ρ, st, β =>
      translateStrategy B k hl ha hd
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
    (hl : Legal p) (ha : DistinctActs p) (hd : NormalizedDists p)
    (ρ : RawNodeEnv L → VEnv L Γ)
    (st₀ : MAIDCompileState Player L B)
    (β : ProgramBehavioralProfile p) :
    let st := MAIDCompileState.ofProg B p hl ha hd ρ st₀
    @MAID.Policy Player _ B.fintypePlayer st.nextId st.toStruct :=
  translateStrategy B p hl ha hd ρ st₀ β

-- ctxDeps tracking lemmas

section
omit [DecidableEq Player]

theorem lookupDepsAux_append_singleton_eq_of_ne
    (vars : List (MAIDVarEntry Player L))
    (x y : VarId) (τ : BindTy Player L) (deps : Finset Nat)
    (hxy : y ≠ x) :
    MAIDCompileState.lookupDepsAux (vars ++ [(x, τ, deps)]) y =
      MAIDCompileState.lookupDepsAux vars y := by
  induction vars with
  | nil =>
    simp [MAIDCompileState.lookupDepsAux, hxy]
  | cons e rest ih =>
    rcases e with ⟨z, σ, deps'⟩
    by_cases hyz : y = z
    · subst hyz
      simp [MAIDCompileState.lookupDepsAux]
    · simp [MAIDCompileState.lookupDepsAux, hyz, ih]

theorem lookupDepsAux_append_singleton_eq_self_of_fresh
    (vars : List (MAIDVarEntry Player L))
    (x : VarId) (τ : BindTy Player L) (deps : Finset Nat)
    (hfresh : x ∉ vars.map Prod.fst) :
    MAIDCompileState.lookupDepsAux (vars ++ [(x, τ, deps)]) x = deps := by
  induction vars with
  | nil =>
    simp [MAIDCompileState.lookupDepsAux]
  | cons e rest ih =>
    rcases e with ⟨y, σ, deps'⟩
    have hxy : x ≠ y := by
      intro h
      apply hfresh
      simp [h]
    have hfresh' : x ∉ rest.map Prod.fst := by
      intro h
      apply hfresh
      simp [h]
    simp [MAIDCompileState.lookupDepsAux, hxy, ih, hfresh']

end

theorem MAIDCompileState.lookupDeps_addVar_eq_of_ne
    (st : MAIDCompileState Player L B)
    (x : VarId) (τ : BindTy Player L) (deps : Finset Nat)
    (hdeps : ∀ d ∈ deps, d < st.nextId)
    {y : VarId} (hxy : y ≠ x) :
    (st.addVar x τ deps hdeps).lookupDeps y = st.lookupDeps y := by
  unfold MAIDCompileState.lookupDeps
  simpa [MAIDCompileState.addVar] using
    lookupDepsAux_append_singleton_eq_of_ne st.vars x y τ deps hxy

theorem MAIDCompileState.lookupDeps_addVar_eq_self_of_fresh
    (st : MAIDCompileState Player L B)
    (x : VarId) (τ : BindTy Player L) (deps : Finset Nat)
    (hdeps : ∀ d ∈ deps, d < st.nextId)
    (hfresh : x ∉ st.vars.map Prod.fst) :
    (st.addVar x τ deps hdeps).lookupDeps x = deps := by
  unfold MAIDCompileState.lookupDeps
  simpa [MAIDCompileState.addVar] using
    lookupDepsAux_append_singleton_eq_self_of_fresh st.vars x τ deps hfresh

theorem MAIDCompileState.lookupDeps_addNode
    (st : MAIDCompileState Player L B)
    (nd : CompiledNode Player L B)
    (hdeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId)
    (x : VarId) :
    (st.addNode nd hdeps).2.lookupDeps x = st.lookupDeps x := by
  simp [MAIDCompileState.lookupDeps, MAIDCompileState.addNode]

theorem MAIDCompileState.depsOfVars_addVar_eq_of_fresh
    (st : MAIDCompileState Player L B)
    (x : VarId) (τ : BindTy Player L) (deps : Finset Nat)
    (hdeps : ∀ d ∈ deps, d < st.nextId)
    (xs : List VarId) (hfresh : x ∉ xs) :
    (st.addVar x τ deps hdeps).depsOfVars xs = st.depsOfVars xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    have hyx : y ≠ x := by intro h; apply hfresh; simp [h]
    have hfresh' : x ∉ ys := by intro h; apply hfresh; simp [h]
    simp [MAIDCompileState.depsOfVars,
      st.lookupDeps_addVar_eq_of_ne x τ deps hdeps hyx, ih hfresh']

theorem MAIDCompileState.ctxDeps_addVar_cons_eq_of_fresh
    (st : MAIDCompileState Player L B)
    (x : VarId) (τ : BindTy Player L) (deps : Finset Nat)
    (hdeps : ∀ d ∈ deps, d < st.nextId)
    {Γ : VCtx Player L}
    (hfreshΓ : Fresh x Γ)
    (hfreshVars : x ∉ st.vars.map Prod.fst) :
    (st.addVar x τ deps hdeps).ctxDeps ((x, τ) :: Γ) = deps ∪ st.ctxDeps Γ := by
  unfold MAIDCompileState.ctxDeps
  rw [List.map_cons, MAIDCompileState.depsOfVars,
    st.lookupDeps_addVar_eq_self_of_fresh x τ deps hdeps hfreshVars,
    st.depsOfVars_addVar_eq_of_fresh x τ deps hdeps (Γ.map Prod.fst) hfreshΓ]

theorem MAIDCompileState.lookupDeps_subset_depsOfVars_of_mem
    (st : MAIDCompileState Player L B)
    {xs : List VarId} {x : VarId}
    (hx : x ∈ xs) :
    st.lookupDeps x ⊆ st.depsOfVars xs := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
    intro d hd
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp [MAIDCompileState.depsOfVars, hd]
    · have hd' : d ∈ st.depsOfVars ys := ih hx hd
      simp [MAIDCompileState.depsOfVars, hd']

theorem MAIDCompileState.lookupDeps_subset_ctxDeps_of_mem
    (st : MAIDCompileState Player L B)
    {Γ : VCtx Player L} {x : VarId}
    (hx : x ∈ Γ.map Prod.fst) :
    st.lookupDeps x ⊆ st.ctxDeps Γ := by
  simpa [MAIDCompileState.ctxDeps] using
    st.lookupDeps_subset_depsOfVars_of_mem hx

theorem MAIDCompileState.lookupDeps_subset_ctxDeps_of_hasVar
    (st : MAIDCompileState Player L B)
    {Γ : VCtx Player L} {x : VarId} {τ : BindTy Player L}
    (hx : VHasVar (L := L) Γ x τ) :
    st.lookupDeps x ⊆ st.ctxDeps Γ :=
  st.lookupDeps_subset_ctxDeps_of_mem hx.mem_map_fst

theorem MAIDCompileState.ctxDeps_addNode_eq
    (st : MAIDCompileState Player L B)
    (nd : CompiledNode Player L B)
    (hdeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId)
    (Γ : VCtx Player L) :
    (st.addNode nd hdeps).2.ctxDeps Γ = st.ctxDeps Γ := by
  unfold MAIDCompileState.ctxDeps
  have haux : ∀ xs : List VarId,
      (st.addNode nd hdeps).2.depsOfVars xs = st.depsOfVars xs := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih =>
        simp [MAIDCompileState.depsOfVars, MAIDCompileState.lookupDeps_addNode, ih]
  exact haux (Γ.map Prod.fst)

theorem MAIDCompileState.ctxDeps_letExpr_step
    (st : MAIDCompileState Player L B)
    {Γ : VCtx Player L} (x : VarId) {b : L.Ty}
    (hfreshΓ : Fresh x Γ)
    (hfreshVars : x ∉ st.vars.map Prod.fst) :
    (st.addVar x (.pub b) (st.ctxDeps Γ) (st.depsOfVars_lt _)).ctxDeps
      ((x, .pub b) :: Γ) = st.ctxDeps Γ := by
  rw [st.ctxDeps_addVar_cons_eq_of_fresh x (.pub b) (st.ctxDeps Γ)
    (st.depsOfVars_lt _) hfreshΓ hfreshVars]
  simp

theorem MAIDCompileState.ctxDeps_addNode_addVar_singleton_cons_eq_of_fresh
    (st : MAIDCompileState Player L B)
    (nd : CompiledNode Player L B)
    (hndeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId)
    {Γ : VCtx Player L}
    (x : VarId) (τ : BindTy Player L)
    (hfreshΓ : Fresh x Γ)
    (hfreshVars : x ∉ st.vars.map Prod.fst) :
    (((st.addNode nd hndeps).2).addVar x τ {st.nextId}
      (by
        intro d hd
        simp_all only [List.mem_map, Prod.exists, exists_and_right, exists_eq_right, not_exists,
          Finset.mem_singleton]
        exact Nat.lt_add_one st.nextId)).ctxDeps ((x, τ) :: Γ) =
      {st.nextId} ∪ st.ctxDeps Γ := by
  have hfreshVars' : x ∉ ((st.addNode nd hndeps).2).vars.map Prod.fst := by
    simpa [MAIDCompileState.addNode] using hfreshVars
  rw [((st.addNode nd hndeps).2).ctxDeps_addVar_cons_eq_of_fresh x τ {st.nextId}
    (by
      intro d hd
      simp_all only [List.mem_map, Prod.exists, exists_and_right, exists_eq_right, not_exists,
        Finset.mem_singleton]
      exact Nat.lt_add_one st.nextId) hfreshΓ hfreshVars']
  rw [MAIDCompileState.ctxDeps_addNode_eq]

theorem MAIDCompileState.ctxDeps_reveal_step
    (st : MAIDCompileState Player L B)
    {Γ : VCtx Player L}
    (y : VarId) (who : Player) (x : VarId) {b : L.Ty}
    (hx : VHasVar (L := L) Γ x (.hidden who b))
    (hfreshΓ : Fresh y Γ)
    (hfreshVars : y ∉ st.vars.map Prod.fst) :
    (st.addVar y (.pub b) (st.lookupDeps x) (st.lookupDeps_lt x)).ctxDeps
      ((y, .pub b) :: Γ) = st.ctxDeps Γ := by
  rw [st.ctxDeps_addVar_cons_eq_of_fresh y (.pub b) (st.lookupDeps x)
    (st.lookupDeps_lt x) hfreshΓ hfreshVars]
  apply Finset.union_eq_right.mpr
  exact st.lookupDeps_subset_ctxDeps_of_hasVar hx

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
    (a : @TAssign Player _ B.fintypePlayer st.nextId st.toStruct)
    (nd : Fin st.nextId) (v : @Struct.Val Player _ B.fintypePlayer st.nextId st.toStruct nd)
    (hwho : ∃ who, (st.descAt nd).kind = .utility who) :
    let _ := B.fintypePlayer
    rawOfTAssign st (updateAssign a nd v) = rawOfTAssign st a := by
  intro _inst
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

theorem MAIDCompileState.mem_toStruct_parents_iff
    (st : MAIDCompileState Player L B)
    (nd : Fin st.nextId)
    {i : Nat} (hi : i < st.nextId) :
    let _ : Fintype Player := B.fintypePlayer
    (⟨i, hi⟩ : Fin st.nextId) ∈ st.toStruct.parents nd ↔ i ∈ (st.descAt nd).parents := by
  letI := B.fintypePlayer
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨d, hd, hEq⟩
    have hval : d.1 = i := by
      simpa using congrArg Fin.val hEq
    simpa [hval] using d.2
  · intro h
    refine Finset.mem_image.mpr ?_
    refine ⟨⟨i, h⟩, by simp, ?_⟩
    exact Fin.ext rfl

theorem MAIDCompileState.mem_toStruct_obsParents_iff
    (st : MAIDCompileState Player L B)
    (nd : Fin st.nextId)
    {i : Nat} (hi : i < st.nextId) :
    let _ : Fintype Player := B.fintypePlayer
    (⟨i, hi⟩ : Fin st.nextId) ∈ st.toStruct.obsParents nd ↔ i ∈ (st.descAt nd).obsParents := by
  letI := B.fintypePlayer
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨d, hd, hEq⟩
    have hval : d.1 = i := by simpa using congrArg Fin.val hEq
    simpa [hval] using d.2
  · intro h
    refine Finset.mem_image.mpr ?_
    refine ⟨⟨i, h⟩, by simp, ?_⟩
    exact Fin.ext rfl

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
      (hl : Legal p) → (ha : DistinctActs p) → (hd : NormalizedDists p) →
      (ρ : RawNodeEnv L → VEnv L Γ) →
      (st₀ : MAIDCompileState Player L B) →
      ProgramBehavioralProfile p →
      (nd : Fin (MAIDCompileState.ofProg B p hl ha hd ρ st₀).nextId) →
      RawNodeEnv L →
      FDist (CompiledNode.valType
        ((MAIDCompileState.ofProg B p hl ha hd ρ st₀).descAt nd))
  | _, .ret _, _, _, _, _, _, _, _, _ => by
      letI := B.fintypePlayer; exact FDist.pure (Classical.choice inferInstance)
  | _Γ, .letExpr (b := b) x e k, hl, ha, hd, ρ, st₀, β, nd, raw =>
      compiledDecisionKernel B k hl ha hd
        (fun raw => VEnv.cons (τ := .pub b)
          (L.eval e (VEnv.erasePubEnv (ρ raw))) (ρ raw))
        (st₀.addVar x (.pub b) (st₀.ctxDeps _Γ) (st₀.depsOfVars_lt _))
        β nd raw
  | _Γ, .sample x τ m D' k, hl, ha, hd, ρ, st₀, β, nd, raw =>
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
      compiledDecisionKernel B k hl ha hd.2
        (fun raw => VEnv.cons
          (MAIDCompileState.readVal (B := B) raw τ.base st₀.nextId) (ρ raw))
        st₁ β nd raw
  | Γ, .commit (b := b) x who R k, hl, ha, hd, ρ, st₀, β, nd, raw => by
      letI := B.fintypePlayer
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
      let dk_rest := compiledDecisionKernel B k hl.2 ha hd ρ' st₁
        (ProgramBehavioralProfile.tail β)
      let κ := ProgramBehavioralStrategy.headKernel (P := Player)
        (L := L) (β who)
      let st_final := MAIDCompileState.ofProg B k hl.2 ha hd ρ' st₁
      by_cases hnd : nd.val = id
      · have hid_lt_st₁ : id < st₁.nextId := by
          simp [st₁, st', res, id,
            MAIDCompileState.addVar, MAIDCompileState.addNode]
        have hdesc : st_final.descAt nd =
            .decision b who acts hacts hnodup obs := by
          have h1 := MAIDCompileState.ofProg_descAt_old B k hl.2 ha hd
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
  | _, .reveal (b := b) y _who x hx k, hl, ha, hd, ρ, st₀, β, nd, raw =>
      compiledDecisionKernel B k hl ha hd
        (fun raw => VEnv.cons (τ := .pub b)
          (VEnv.get (ρ raw) hx : L.Val b) (ρ raw))
        (st₀.addVar y (.pub b) (st₀.lookupDeps x) (st₀.lookupDeps_lt x))
        β nd raw

theorem compiledDecisionKernel_normalized
    (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ)
    (hl : Legal p) (ha : DistinctActs p) (hd : NormalizedDists p)
    (ρ : RawNodeEnv L → VEnv L Γ)
    (st₀ : MAIDCompileState Player L B)
    (β : ProgramBehavioralProfile p) :
    let st := MAIDCompileState.ofProg B p hl ha hd ρ st₀
    ∀ (nd : Fin st.nextId) (raw : RawNodeEnv L),
      (∃ who, (st.descAt nd).kind = .decision who) →
      (compiledDecisionKernel B p hl ha hd ρ st₀ β nd raw).totalWeight = 1 := by
  intro _
  induction p generalizing st₀ with
  | ret _ =>
      intro nd raw _
      simp only [compiledDecisionKernel]
      exact FDist.totalWeight_pure _
  | letExpr x e k ih => exact ih _ _ _ _ _ _
  | sample x τ m D' k ih => exact ih _ _ _ _ _ _
  | commit x who R k ih =>
      letI := B.fintypePlayer
      intro nd raw ⟨w, hw⟩
      simp only [compiledDecisionKernel]
      split
      · -- headKernel wrapped in fdist_transport
        exact (fdist_transport_totalWeight _ _).trans
          (ProgramBehavioralStrategy.headKernel_normalized (β who) _)
      · exact ih _ _ _ _ _ _ nd raw ⟨w, hw⟩
  | reveal y _who x hx k ih => exact ih _ _ _ _ _ _

/-- FDist node data: non-recursive dispatch on `descAt`. Decision nodes use
`compiledDecisionKernel`. -/
noncomputable def compiledFDistData
    (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ)
    (hl : Legal p) (ha : DistinctActs p) (hd : NormalizedDists p)
    (ρ : RawNodeEnv L → VEnv L Γ)
    (st₀ : MAIDCompileState Player L B)
    (β : ProgramBehavioralProfile p) :
    let st := MAIDCompileState.ofProg B p hl ha hd ρ st₀
    @FDistNodeData Player _ B.fintypePlayer _ st.toStruct := by
  letI := B.fintypePlayer
  let st := MAIDCompileState.ofProg B p hl ha hd ρ st₀
  let dk := compiledDecisionKernel B p hl ha hd ρ st₀ β
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
          exact compiledDecisionKernel_normalized B p hl ha hd ρ st₀ β
            nd _ ⟨_who, by rw [hdesc]; rfl⟩
      · next _who _deps _ufn hdesc =>
          exact (fdist_transport_totalWeight _ _).trans
            (FDist.totalWeight_pure _)
  }

@[congr] theorem FDist.toPMF_congr [DecidableEq α]
    {d₁ d₂ : FDist α} {h₁ h₂} (heq : d₁ = d₂) :
    FDist.toPMF d₁ h₁ = FDist.toPMF d₂ h₂ := by subst heq; rfl

@[simp] theorem toStruct_kind (st : MAIDCompileState Player L B) (nd : Fin st.nextId) :
    letI := B.fintypePlayer; st.toStruct.kind nd = (st.descAt nd).kind := rfl

@[simp] theorem toStruct_Val (st : MAIDCompileState Player L B) (nd : Fin st.nextId) :
    letI := B.fintypePlayer; st.toStruct.Val nd = CompiledNode.valType (st.descAt nd) := rfl

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
    (data : @FDistNodeData Player _ B.fintypePlayer _ st.toStruct)
    (nd : Fin st.nextId)
    (hutility : ∃ who, (st.descAt nd).kind = .utility who)
    (a : @TAssign Player _ B.fintypePlayer st.nextId st.toStruct) :
    letI := B.fintypePlayer
    evalStepFDist data (FDist.pure a) nd =
      FDist.pure (updateAssign a nd default) := by
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
    (data : @FDistNodeData Player _ B.fintypePlayer _ st.toStruct)
    (nd : Fin st.nextId)
    (hutility : ∃ who, (st.descAt nd).kind = .utility who)
    (f : @TAssign Player _ B.fintypePlayer st.nextId st.toStruct → α)
    [DecidableEq α]
    (hf : ∀ a v, f (@updateAssign Player _ B.fintypePlayer st.nextId st.toStruct a nd v) = f a)
    (acc : FDist (@TAssign Player _ B.fintypePlayer st.nextId st.toStruct)) :
    letI := B.fintypePlayer
    FDist.map f (evalStepFDist data acc nd) = FDist.map f acc := by
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
    (data : @FDistNodeData Player _ B.fintypePlayer _ st.toStruct)
    (nodes : List (Fin st.nextId))
    (hutility : ∀ nd ∈ nodes,
      ∃ who, (st.descAt nd).kind = .utility who)
    (f : @TAssign Player _ B.fintypePlayer st.nextId st.toStruct → α)
    [DecidableEq α]
    (hf : ∀ a nd v,
      f (@updateAssign Player _ B.fintypePlayer st.nextId st.toStruct a nd v) = f a)
    (acc : FDist (@TAssign Player _ B.fintypePlayer st.nextId st.toStruct)) :
    letI := B.fintypePlayer
    FDist.map f (nodes.foldl (evalStepFDist data) acc) =
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
    (a : @TAssign Player _ B.fintypePlayer st.nextId st.toStruct)
    (ps : Finset (Fin st.nextId))
    (deps : Finset Nat)
    (hps : ∀ i (hi : i < st.nextId), ((⟨i, hi⟩ : Fin st.nextId) ∈ ps ↔ i ∈ deps)) :
    let _ : Fintype Player := B.fintypePlayer
    st.rawEnvOfCfg (projCfg a ps) =
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
    (a : @TAssign Player _ B.fintypePlayer st.nextId st.toStruct) :
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

open MAID in
theorem MAIDCompileState.rawOfTAssign_updateAssign_of_tagged
    (st : MAIDCompileState Player L B)
    (a : @TAssign Player _ B.fintypePlayer st.nextId st.toStruct)
    (nd : Fin st.nextId)
    (v : @Struct.Val Player _ B.fintypePlayer st.nextId st.toStruct nd)
    (tv : RawTaggedVal L)
    (htag : MAIDCompileState.taggedOfVal (st.descAt nd) v = some tv) :
    let _ : Fintype Player := B.fintypePlayer
    rawOfTAssign st (updateAssign a nd v) =
      (rawOfTAssign st a).extend nd.val tv := by
  letI := B.fintypePlayer
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
private def castValType {c c' : CompiledNode Player L B}
    (hc : c = c') (v : CompiledNode.valType c) : CompiledNode.valType c' :=
  hc ▸ v

open MAID in
private theorem taggedOfVal_chance_cast
    {c : CompiledNode Player L B}
    {τ₀ : L.Ty} {deps₀ : Finset Nat}
    {cpd₀ : RawNodeEnv L → FDist (L.Val τ₀)}
    {hn₀ : ∀ raw, FDist.totalWeight (cpd₀ raw) = 1}
    (hc : c = .chance τ₀ deps₀ cpd₀ hn₀)
    (v : CompiledNode.valType c) :
    MAIDCompileState.taggedOfVal c v = some ⟨τ₀, castValType hc v⟩ := by
  subst hc; rfl

open MAID in
private theorem taggedOfVal_decision_cast
    {c : CompiledNode Player L B}
    {τ₀ : L.Ty} {who₀ : Player} {acts₀ : List (L.Val τ₀)}
    {hacts₀ : acts₀ ≠ []} {hnodup₀ : acts₀.Nodup}
    {obs₀ : Finset Nat}
    (hc : c = .decision τ₀ who₀ acts₀ hacts₀ hnodup₀ obs₀)
    (v : CompiledNode.valType c) :
    MAIDCompileState.taggedOfVal c v = some ⟨τ₀, castValType hc v⟩ := by
  subst hc; rfl

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
/-- At the commit's new decision node, `compiledDecisionKernel` returns
`fdist_transport ... (headKernel (β who) view)`. Binding with `f ∘ castValType`
cancels the transport + cast, leaving `(headKernel (β who) view).bind f`. -/
theorem compiledDecisionKernel_commit_bind_cancel
    {Γ : VCtx Player L}
    {x : VarId} {who : Player} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore Player L ((x, .hidden who b) :: Γ)}
    (B : MAIDBackend Player L)
    (hl : Legal (.commit (b := b) x who R k))
    (ha : DistinctActs (.commit (b := b) x who R k))
    (hd : NormalizedDists (.commit (b := b) x who R k))
    (ρ : RawNodeEnv L → VEnv (Player := Player) L Γ)
    (st₀ : MAIDCompileState Player L B)
    (β : ProgramBehavioralProfile (P := Player) (L := L)
      (.commit (b := b) x who R k))
    (raw : RawNodeEnv L)
    {γ : Type} [DecidableEq γ] (f : L.Val b → FDist γ) :
    let _ := B.fintypePlayer
    let st := MAIDCompileState.ofProg B
      (.commit (b := b) x who R k) hl ha hd ρ st₀
    let nd0 : Fin st.nextId := ⟨st₀.nextId,
      Nat.lt_of_lt_of_le
        (by simp [MAIDCompileState.addVar, MAIDCompileState.addNode])
        (MAIDCompileState.ofProg_nextId_le B k hl.2 ha hd _ _)⟩
    let hdesc0 : st.descAt nd0 = .decision b who (allValues B b)
        (allValues_ne_nil B b) (allValues_nodup B b)
        (st₀.viewDeps who Γ) := by
      sorry
    (compiledDecisionKernel B (.commit (b := b) x who R k)
      hl ha hd ρ st₀ β nd0 raw).bind
      (fun v => f (castValType hdesc0 v)) =
    (ProgramBehavioralStrategy.headKernel (P := Player) (L := L)
      (β who)
      (projectViewEnv who (VEnv.eraseEnv (ρ raw)))).bind f := by
  intro _ st nd0 hdesc0
  -- compiledDecisionKernel at commit with nd0.val = st₀.nextId
  -- returns fdist_transport ... (headKernel (β who) view)
  simp only [compiledDecisionKernel]
  split
  · -- New node case: transport + castValType cancel
    rw [fdist_transport_bind_castValType (hdesc := hdesc0)]
  · next hne => exact absurd rfl hne

-- Compatibility of compiled FDist data with sem and pol

open MAID in
/-- The FDist data is compatible with the semantics and policy. -/
theorem compiledFDistData_compatible
    (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ)
    (hl : Legal p) (ha : DistinctActs p) (hd : NormalizedDists p)
    (ρ : RawNodeEnv L → VEnv L Γ)
    (st₀ : MAIDCompileState Player L B)
    (β : ProgramBehavioralProfile p) :
    let _ := B.fintypePlayer
    let st := MAIDCompileState.ofProg B p hl ha hd ρ st₀
    FDistNodeDataCompatible
      (compiledFDistData B p hl ha hd ρ st₀ β)
      (MAIDCompileState.toSem st)
      (compiledPolicy B p hl ha hd ρ st₀ β) := by
  sorry

-- Core FDist bridge induction

def MAIDCompileState.VarsSubCtx
    (st : MAIDCompileState Player L B) (Γ : VCtx Player L) : Prop :=
  ∀ x, x ∈ st.vars.map Prod.fst → x ∈ Γ.map Prod.fst

theorem MAIDCompileState.VarsSubCtx_addNode
    (st : MAIDCompileState Player L B) {Γ : VCtx Player L}
    (hvars : st.VarsSubCtx Γ) (nd : CompiledNode Player L B)
    (hdeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId) :
    (st.addNode nd hdeps).2.VarsSubCtx Γ := by
  intro x; simpa [VarsSubCtx, addNode] using hvars x

theorem MAIDCompileState.VarsSubCtx_addVar
    (st : MAIDCompileState Player L B) {Γ : VCtx Player L}
    (hvars : st.VarsSubCtx Γ) (x : VarId) (τ : BindTy Player L)
    (deps : Finset Nat) (hdeps : ∀ d ∈ deps, d < st.nextId)
    (hfresh : Fresh x Γ) :
    (st.addVar x τ deps hdeps).VarsSubCtx ((x, τ) :: Γ) := by
  intro y hy
  have hy' : y ∈ st.vars.map Prod.fst ∨ y = x := by
    simpa [addVar, List.map_append] using hy
  simp only [List.map_cons, List.mem_cons, List.mem_map, Prod.exists,
    exists_and_right, exists_eq_right]
  rcases hy' with hy' | rfl
  · exact Or.inr (by simpa [List.mem_map] using hvars y hy')
  · exact Or.inl rfl

theorem MAIDCompileState.VarsSubCtx_letExpr_step
    (st : MAIDCompileState Player L B) {Γ : VCtx Player L}
    (hvars : st.VarsSubCtx Γ) (x : VarId) {b : L.Ty}
    (hfreshΓ : Fresh x Γ) :
    (st.addVar x (.pub b) (st.ctxDeps Γ) (st.depsOfVars_lt _)).VarsSubCtx
      ((x, .pub b) :: Γ) :=
  st.VarsSubCtx_addVar hvars x _ _ _ hfreshΓ

theorem MAIDCompileState.VarsSubCtx_addNode_addVar_singleton_step
    (st : MAIDCompileState Player L B) {Γ : VCtx Player L}
    (hvars : st.VarsSubCtx Γ) (nd : CompiledNode Player L B)
    (hndeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId)
    (x : VarId) (τ : BindTy Player L) (hfreshΓ : Fresh x Γ) :
    (((st.addNode nd hndeps).2).addVar x τ {st.nextId} (by
      intro d hd; simp_all only [Finset.mem_singleton]
      exact Nat.lt_add_one st.nextId)).VarsSubCtx ((x, τ) :: Γ) :=
  ((st.addNode nd hndeps).2).VarsSubCtx_addVar
    (st.VarsSubCtx_addNode hvars nd hndeps) x τ _ _ hfreshΓ

open MAID in
/-- **Core FDist bridge.** -/
theorem foldFDist_map_extract_eq_nativeOutcomeDist
    (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ)
    (β : ProgramBehavioralProfile p)
    (hl : Legal p) (ha : DistinctActs p)
    (hd : NormalizedDists p)
    (hfresh : FreshBindings p)
    (ρ : RawNodeEnv L → VEnv L Γ)
    (st₀ : MAIDCompileState Player L B)
    (hvars : st₀.VarsSubCtx Γ)
    (hρ_deps : ∀ j, j ∉ (st₀.ctxDeps Γ : Finset Nat) → InsensitiveTo ρ j) :
    let _ := B.fintypePlayer
    let st := MAIDCompileState.ofProg B p hl ha hd ρ st₀
    ∀ (a₀ : TAssign st.toStruct),
    FDist.map (fun a => extractOutcome B p ρ st₀.nextId (rawOfTAssign st a))
      ((List.finRange st.nextId).drop st₀.nextId |>.foldl
        (evalStepFDist (compiledFDistData B p hl ha hd ρ st₀ β)) (FDist.pure a₀))
    = nativeOutcomeDist B p β ρ st₀.nextId (rawOfTAssign st a₀) := by
  letI := B.fintypePlayer
  induction p generalizing st₀ with
  | ret u =>
      rename_i Γ'
      dsimp
      intro a₀
      let st : MAIDCompileState Player L B :=
        MAIDCompileState.ofProg B (VegasCore.ret u) hl ha hd ρ st₀
      let data := compiledFDistData B (VegasCore.ret u) hl ha hd ρ st₀ β
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
      dsimp
      intro a₀
      have hxΓ : Fresh x Γ' := hfresh.1
      have hxvars : x ∉ st₀.vars.map Prod.fst := fun hxmem => hxΓ (hvars x hxmem)
      let ρ' : RawNodeEnv L → VEnv L ((x, .pub b) :: Γ') :=
        fun raw => VEnv.cons (τ := .pub b) (L.eval e (VEnv.erasePubEnv (ρ raw))) (ρ raw)
      let st₁ := st₀.addVar x (.pub b) (st₀.ctxDeps Γ') (st₀.depsOfVars_lt _)
      have hvars₁ : st₁.VarsSubCtx ((x, .pub b) :: Γ') := by
        simpa [st₁] using st₀.VarsSubCtx_letExpr_step hvars x hxΓ
      have hρ'_deps : ∀ j, j ∉ st₁.ctxDeps ((x, .pub b) :: Γ') → InsensitiveTo ρ' j := by
        intro j hj raw tv
        have hj' : j ∉ st₀.ctxDeps Γ' := by
          simpa [st₁, st₀.ctxDeps_letExpr_step x hxΓ hxvars] using hj
        have hρj := hρ_deps j hj' raw tv
        exact VEnv.cons_ext (by simp [hρj]) hρj
      exact ih β hl ha hd hfresh.2 ρ' st₁ hvars₁ hρ'_deps a₀
  | sample x τ m D' k ih =>
      rename_i Γ'
      dsimp
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
        intro d hd'
        have := Finset.mem_singleton.mp hd'
        subst d
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
      let st : MAIDCompileState Player L B := MAIDCompileState.ofProg B k hl ha hd.2 ρ' st₁
      let data := compiledFDistData B k hl ha hd.2 ρ' st₁ β
      have hid_lt : id < st.nextId :=
        Nat.lt_of_lt_of_le (by
          simp [st₁, stNode, id, MAIDCompileState.addVar, MAIDCompileState.addNode])
          (MAIDCompileState.ofProg_nextId_le B k hl ha hd.2 ρ' st₁)
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
        have hdesc1 := MAIDCompileState.ofProg_descAt_old B k hl ha hd.2 ρ' st₁ id
          (by simp [st₁, stNode, id, MAIDCompileState.addVar, MAIDCompileState.addNode])
        rw [hdesc1]
        simpa [st₁, stNode] using st₀.addNode_descAt_new nd hndeps
      have hrawP :
          st.rawEnvOfCfg (projCfg a₀ (st.toStruct.parents nd0)) =
            fun i => if i < st.nextId then
              if i ∈ deps then rawOfTAssign st a₀ i else none else none := by
        apply st.rawEnvOfCfg_proj_eq_select a₀ (st.toStruct.parents nd0) deps
        intro i hi
        simp only [st.mem_toStruct_parents_iff nd0 hi, hdesc0, nd, CompiledNode.parents]
      have hρeq :
          ρ (st.rawEnvOfCfg (projCfg a₀ (st.toStruct.parents nd0))) =
            ρ (rawOfTAssign st a₀) := by
        rw [hrawP]
        simpa [deps] using (eq_on_ctxDeps_rawOfTAssign (st := st) (deps := deps) hρ_deps a₀)
      let μ : FDist (st.toStruct.Val nd0) := data.dist nd0 a₀
      let f : TAssign st.toStruct → Outcome Player :=
        fun a => extractOutcome B (VegasCore.sample x τ m D' k) ρ st₀.nextId (rawOfTAssign st a)
      have hbindmap_aux :
          ∀ (nodes : List (Fin st.nextId))
            (g : st.toStruct.Val nd0 → FDist (TAssign st.toStruct)),
            FDist.map f (nodes.foldl (evalStepFDist data) (FDist.bind μ g)) =
              FDist.bind μ (fun v => FDist.map f (nodes.foldl (evalStepFDist data) (g v))) := by
        intro nodes g
        induction nodes generalizing g with
        | nil => simp [f, FDist.bind_map]
        | cons nd' rest ih' =>
            simpa [List.foldl_cons, evalStepFDist, FDist.bind_assoc, f] using
              (ih' (fun v => FDist.bind (g v) (fun a =>
                FDist.bind (data.dist nd' a) (fun w => FDist.pure (updateAssign a nd' w)))))
      have hih := ih β hl ha hd.2 hfresh.2 ρ' st₁ hvars₁ hρ'_deps
      have hmain :
          FDist.map f
              ((List.finRange st.nextId).drop id |>.foldl (evalStepFDist data) (FDist.pure a₀)) =
            nativeOutcomeDist B (VegasCore.sample x τ m D' k) β ρ
              st₀.nextId (rawOfTAssign st a₀) := by
        rw [hdrop]
        simp only [List.foldl_cons, evalStepFDist, FDist.pure_bind]
        change FDist.map f
              (((List.finRange st.nextId).drop st₁.nextId).foldl (evalStepFDist data)
                (FDist.bind μ (fun v => FDist.pure (updateAssign a₀ nd0 v)))) = _
        rw [hbindmap_aux _ _]
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
        -- μ dispatches on descAt nd0 = .chance via hdesc0.
        -- Transport + castValType cancel; cpdFDist rawP = cpdFDist (rawOfTAssign st a₀).
        let rawP := st.rawEnvOfCfg (projCfg a₀ (st.toStruct.parents nd0))
        have hμ : μ = fdist_transport (by
            change _ = CompiledNode.valType (st.descAt nd0); rw [hdesc0]; rfl)
            (cpdFDist rawP) := by
          change (compiledFDistData B k hl ha hd.2 ρ' st₁ β).dist nd0 a₀ = _
          unfold compiledFDistData
          dsimp only []
          split
          · next _ _ cpd₁ _ hdesc₁ =>
              have heq := hdesc₁.symm.trans hdesc0
              change CompiledNode.chance _ _ cpd₁ _ =
                CompiledNode.chance τ.base deps cpdFDist cpdNorm at heq
              injection heq with h1 _ h3; subst h1; cases h3; rfl
          · next _ _ _ _ _ _ hdesc => exact absurd (hdesc.symm.trans hdesc0 :
              CompiledNode.decision _ _ _ _ _ _ = .chance τ.base deps cpdFDist cpdNorm) nofun
          · next _ _ _ hdesc => exact absurd (hdesc.symm.trans hdesc0 :
              CompiledNode.utility _ _ _ = .chance τ.base deps cpdFDist cpdNorm) nofun
        rw [hμ]
        rw [fdist_transport_bind_castValType (hdesc := hdesc0)]
        change (cpdFDist rawP).bind H =
          FDist.bind (L.evalDist D' (VEnv.eraseDistEnv τ m (ρ (rawOfTAssign st a₀))))
            (fun v => nativeOutcomeDist B k β ρ' (id + 1)
              ((rawOfTAssign st a₀).extend id ⟨τ.base, v⟩))
        congr 1
        exact congrArg (fun env => L.evalDist D' (VEnv.eraseDistEnv τ m env)) hρeq
      exact hmain
  | @commit _ x who b R k ih =>
      rename_i Γ'
      dsimp; intro a₀
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
          st₀.ctxDeps_addNode_addVar_singleton_cons_eq_of_fresh nd hndeps x (.hidden who b) hxΓ hxvars
      have hρ'_deps : ∀ j, j ∉ st₁.ctxDeps ((x, .hidden who b) :: Γ') → InsensitiveTo ρ' j := by
        intro j hj raw tv
        have hjid : j ≠ id := by intro hEq; apply hj; simp [hctx₁, hEq]
        have hj' : j ∉ st₀.ctxDeps Γ' := by intro hmem; apply hj; simp [hctx₁, hmem]
        have hρj := hρ_deps j hj' raw tv
        exact VEnv.cons_ext (readVal_extend_ne (B := B) raw j id tv b hjid.symm) hρj
      let st : MAIDCompileState Player L B := MAIDCompileState.ofProg B k hl.2 ha hd ρ' st₁
      let data := compiledFDistData B k hl.2 ha hd ρ' st₁
        (ProgramBehavioralProfile.tail β)
      have hid_lt : id < st.nextId :=
        Nat.lt_of_lt_of_le (by
          simp [st₁, stNode, id, MAIDCompileState.addVar, MAIDCompileState.addNode])
          (MAIDCompileState.ofProg_nextId_le B k hl.2 ha hd ρ' st₁)
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
        have hdesc1 := MAIDCompileState.ofProg_descAt_old B k hl.2 ha hd ρ' st₁ id
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
        -- rawSel and rawOfTAssign agree on obs positions;
        -- projectViewEnv only accesses view variables whose deps ⊆ obs
        sorry
      let μ : FDist (st.toStruct.Val nd0) := data.dist nd0 a₀
      let f : TAssign st.toStruct → Outcome Player :=
        fun a => extractOutcome B (VegasCore.commit x who R k) ρ st₀.nextId (rawOfTAssign st a)
      have hbindmap_aux :
          ∀ (nodes : List (Fin st.nextId))
            (g : st.toStruct.Val nd0 → FDist (TAssign st.toStruct)),
            FDist.map f (nodes.foldl (evalStepFDist data) (FDist.bind μ g)) =
              FDist.bind μ (fun v => FDist.map f (nodes.foldl (evalStepFDist data) (g v))) := by
        intro nodes g
        induction nodes generalizing g with
        | nil => simp [f, FDist.bind_map]
        | cons nd' rest ih' =>
            simpa [List.foldl_cons, evalStepFDist, FDist.bind_assoc, f] using
              (ih' (fun v => FDist.bind (g v) (fun a =>
                FDist.bind (data.dist nd' a) (fun w => FDist.pure (updateAssign a nd' w)))))
      have hih := ih (ProgramBehavioralProfile.tail β) hl.2 ha hd hfresh.2 ρ' st₁ hvars₁ hρ'_deps
      have hmain :
          FDist.map f
              ((List.finRange st.nextId).drop id |>.foldl (evalStepFDist data) (FDist.pure a₀)) =
            nativeOutcomeDist B (VegasCore.commit x who R k) β ρ
              st₀.nextId (rawOfTAssign st a₀) := by
        rw [hdrop]; simp only [List.foldl_cons, evalStepFDist, FDist.pure_bind]
        change FDist.map f
              (((List.finRange st.nextId).drop st₁.nextId).foldl (evalStepFDist data)
                (FDist.bind μ (fun v => FDist.pure (updateAssign a₀ nd0 v)))) = _
        rw [hbindmap_aux _ _]
        let H : L.Val b → FDist (Outcome Player) :=
          fun w => nativeOutcomeDist B k (ProgramBehavioralProfile.tail β) ρ' (id + 1)
            ((rawOfTAssign st a₀).extend id ⟨b, w⟩)
        have hGH : ∀ v, (fun v => FDist.map f (List.foldl (evalStepFDist data)
            (FDist.pure (updateAssign a₀ nd0 v))
            (List.drop st₁.nextId (List.finRange st.nextId)))) v =
            H (castValType hdesc0 v) := by
          intro v
          have h1 : st₁.nextId = id + 1 := by
            simp [st₁, stNode, id, MAIDCompileState.addVar, MAIDCompileState.addNode]
          have h2 : rawOfTAssign st (updateAssign a₀ nd0 v) =
              (rawOfTAssign st a₀).extend id ⟨b, castValType hdesc0 v⟩ :=
            MAIDCompileState.rawOfTAssign_updateAssign_of_tagged st a₀ nd0
              v ⟨b, castValType hdesc0 v⟩ (taggedOfVal_decision_cast hdesc0 v)
          exact (hih (updateAssign a₀ nd0 v)).trans (by rw [h1, h2])
        conv_lhs => rw [show (fun v => FDist.map f (List.foldl (evalStepFDist data)
            (FDist.pure (updateAssign a₀ nd0 v))
            (List.drop st₁.nextId (List.finRange st.nextId)))) =
          (fun v => H (castValType hdesc0 v)) from funext hGH]
        -- μ dispatches on descAt nd0 = .decision via hdesc0.
        -- μ = dk nd0 rawO (via compiledFDistData decision branch).
        let rawO := st.rawEnvOfCfg (projCfg a₀ (st.toStruct.obsParents nd0))
        -- μ = dk nd0 rawO (decision branch has no transport)
        have hμ : μ = compiledDecisionKernel B k hl.2 ha hd ρ' st₁
            (ProgramBehavioralProfile.tail β) nd0 rawO := by
          change (compiledFDistData B k hl.2 ha hd ρ' st₁
            (ProgramBehavioralProfile.tail β)).dist nd0 a₀ = _
          unfold compiledFDistData; dsimp only []
          split
          · next _ _ _ _ hdesc₁ => exact absurd (hdesc₁.symm.trans hdesc0 :
              CompiledNode.chance _ _ _ _ = .decision b who acts hacts hnodup obs) nofun
          · next _ _ _ _ _ _ hdesc₁ => rfl
          · next _ _ _ hdesc₁ => exact absurd (hdesc₁.symm.trans hdesc0 :
              CompiledNode.utility _ _ _ = .decision b who acts hacts hnodup obs) nofun
        -- hμ gives μ = dk nd0 rawO. Through compiledDecisionKernel_commit_bind_cancel,
        -- the bind with H ∘ castValType cancels, leaving (headKernel (β who) view₁).bind H.
        -- hViewEq gives view₁ = view₂. Together this closes the goal.
        -- Blocked by: rw [hμ] times out (proof term too large).
        sorry
      sorry -- exact hmain (times out)
  | reveal y who x hx k ih =>
      rename_i Γ' b
      dsimp
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
      exact ih β hl ha hd hfresh.2 ρ' st₁ hvars₁ hρ'_deps a₀

-- Key bridge theorems

open MAID in
/-- **Bridge lemma.** -/
theorem maid_map_extract_eq_outcomeDistBehavioral
    (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ)
    (env : VEnv L Γ)
    (β : ProgramBehavioralProfile p)
    (hl : Legal p) (ha : DistinctActs p)
    (hd : NormalizedDists p)
    (hfresh : FreshBindings p) :
    let _ : Fintype Player := B.fintypePlayer
    let st := MAIDCompileState.ofProg B p hl ha hd (fun _ => env) .empty
    let S := st.toStruct
    let sem := MAIDCompileState.toSem st
    let pol := compiledPolicy B p hl ha hd (fun _ => env) .empty β
    let extract : TAssign S → Outcome Player :=
      fun a => extractOutcome B p (fun _ => env) 0 (rawOfTAssign st a)
    PMF.map extract (evalAssignDist S sem pol) =
      (outcomeDistBehavioral p β env).toPMF
        (outcomeDistBehavioral_totalWeight_eq_one hd) := by
  intro _inst st S sem pol extract
  let hnat := compiled_naturalOrder st
  let σ_topo := hnat.toTopologicalOrder
  rw [evalAssignDist_eq_evalFold S sem pol σ_topo]
  let data := compiledFDistData B p hl ha hd (fun _ => env) .empty β
  let hcompat := compiledFDistData_compatible B p hl ha hd (fun _ => env) .empty β
  rw [← evalFoldFDist_toPMF_eq_evalFold data sem pol hcompat σ_topo]
  have hfold_norm := evalFoldFDist_normalized data σ_topo
  have hmap_norm : (FDist.map extract (evalFoldFDist data σ_topo)).totalWeight = 1 := by
    rw [FDist.totalWeight_map]; exact hfold_norm
  rw [← FDist.toPMF_map (evalFoldFDist data σ_topo) extract hfold_norm hmap_norm]
  apply FDist.toPMF_congr
  have key := foldFDist_map_extract_eq_nativeOutcomeDist B p β hl ha hd
    hfresh (fun _ => env) .empty
    (by intro x hx; simp [MAIDCompileState.empty] at hx)
    (fun _ _ _ _ => rfl) (defaultAssign st.toStruct)
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
    (hl : Legal p) (ha : DistinctActs p)
    (hd : NormalizedDists p)
    (hfresh : FreshBindings p) :
    let _ : Fintype Player := B.fintypePlayer
    let st := MAIDCompileState.ofProg B p hl ha hd (fun _ => env) .empty
    let S := st.toStruct
    let sem := MAIDCompileState.toSem st
    ∃ (pol : @Policy Player _ B.fintypePlayer st.nextId S)
      (extract : @TAssign Player _ B.fintypePlayer st.nextId S → Outcome Player),
      PMF.map extract (evalAssignDist S sem pol) =
        (outcomeDistBehavioral p β env).toPMF
          (outcomeDistBehavioral_totalWeight_eq_one hd) := by
  intro _inst st S sem
  let pol := compiledPolicy B p hl ha hd (fun _ => env) .empty β
  let extract : @TAssign Player _ B.fintypePlayer st.nextId st.toStruct → Outcome Player :=
    fun a => extractOutcome B p (fun _ => env) 0 (rawOfTAssign st a)
  exact ⟨pol, extract,
    maid_map_extract_eq_outcomeDistBehavioral B p env β hl ha hd hfresh⟩

open MAID in
/-- Reverse direction. -/
theorem maid_behavioral_bridge
    (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ)
    (env : VEnv L Γ)
    (hl : Legal p) (ha : DistinctActs p)
    (hd : NormalizedDists p) (hfresh : FreshBindings p) :
    let _ : Fintype Player := B.fintypePlayer
    ∀ (β : ProgramBehavioralProfile p),
    let st := MAIDCompileState.ofProg B p hl ha hd (fun _ => env) .empty
    let S := st.toStruct
    let sem := MAIDCompileState.toSem st
    let extract : @TAssign Player _ B.fintypePlayer st.nextId S → Outcome Player :=
      fun a => extractOutcome B p (fun _ => env) 0 (rawOfTAssign st a)
    ∀ (pol : @Policy Player _ B.fintypePlayer st.nextId S),
    ∃ (β' : ProgramBehavioralProfile p),
      PMF.map extract (evalAssignDist S sem pol) =
        (outcomeDistBehavioral p β' env).toPMF
          (outcomeDistBehavioral_totalWeight_eq_one hd) := by
  sorry

end Vegas
