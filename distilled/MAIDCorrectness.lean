import GameTheory.Languages.MAID.Prefix
import distilled.MAIDCompile
import distilled.OutcomeKernelBridge
import distilled.MAIDFDistFold

namespace Distilled

open MAID

variable {Player : Type} [DecidableEq Player] {L : ExprLanguage}
variable [E : VisExprKit Player L] [D : VisDistKit Player L] [U : VisPayoffKit Player L]
variable {B : MAIDBackend Player L}

-- RawNodeEnv helpers


def RawNodeEnv.extend (raw : RawNodeEnv L) (nid : Nat) (tv : TaggedVal L) :
    RawNodeEnv L :=
  fun i => if i = nid then some tv else raw i

omit E D U in
theorem readVal_extend_self (raw : RawNodeEnv L) (nid : Nat) (τ : L.Ty)
    (v : L.Val τ) :
    MAIDCompileState.readVal (B := B) (raw.extend nid ⟨τ, v⟩) τ nid = v := by
  simp [RawNodeEnv.extend, MAIDCompileState.readVal]

omit E D U in
theorem readVal_extend_ne (raw : RawNodeEnv L) (nid nid' : Nat)
    (tv : TaggedVal L) (τ : L.Ty) (hne : nid' ≠ nid) :
    MAIDCompileState.readVal (B := B) (raw.extend nid tv) τ nid' =
    MAIDCompileState.readVal (B := B) raw τ nid' := by
  simp [RawNodeEnv.extend, hne, MAIDCompileState.readVal]

def InsensitiveTo (f : RawNodeEnv L → α) (nid : Nat) : Prop :=
  ∀ raw (tv : TaggedVal L), f (raw.extend nid tv) = f raw

/-- If `f` is insensitive at position `k`, then any two raw environments that
agree on all positions except `k` give the same result under `f`. -/
theorem InsensitiveTo.eq_of_eq_off [Nonempty (TaggedVal L)]
    {f : RawNodeEnv L → α} {k : Nat}
    (hins : InsensitiveTo f k)
    {raw₁ raw₂ : RawNodeEnv L}
    (hoff : ∀ i, i ≠ k → raw₁ i = raw₂ i) :
    f raw₁ = f raw₂ := by
  obtain ⟨tv⟩ := ‹Nonempty (TaggedVal L)›
  calc f raw₁ = f (raw₁.extend k tv) := (hins raw₁ tv).symm
    _ = f (raw₂.extend k tv) := by
        congr 1; funext i; simp only [RawNodeEnv.extend]
        split <;> [rfl; exact hoff i (by assumption)]
    _ = f raw₂ := hins raw₂ tv

-- nativeOutcomeDist: direct FDist U.Outcome by induction on Prog


/-- Direct computation of `FDist U.Outcome` by recursion on `Prog`,
threading a plain `RawNodeEnv L` argument. No `FDist (RawNodeEnv L)` appears.

Each `sample`/`commit` does `FDist.bind μ (fun v => recurse with extended raw)`.
The `FDist.bind` is over `FDist (L.Val τ)` → `FDist U.Outcome`, both of which
have computable `DecidableEq`. -/
noncomputable def nativeOutcomeDist
    (B : MAIDBackend Player L)
    (σ : Profile (Player := Player) (L := L)) :
    {Γ : VisCtx Player L} →
    (p : Prog Player L Γ) →
    (ρ : RawNodeEnv L → VisEnv (Player := Player) L Γ) →
    (nextId : Nat) →
    RawNodeEnv L → FDist U.Outcome
  | _, .ret u, ρ, _, raw =>
      FDist.pure (U.eval u (ρ raw))
  | _, .letExpr (b := b) x e k, ρ, nextId, raw =>
      nativeOutcomeDist B σ k
        (fun raw => VisEnv.cons (Player := Player) (L := L) (x := x) (τ := .pub b)
          (E.eval e (ρ raw)) (ρ raw))
        nextId raw
  | _, .sample x τ _m D' k, ρ, nextId, raw =>
      FDist.bind
        (D.eval D' (VisEnv.projectDist (Player := Player) (L := L) τ _ (ρ raw)))
        (fun v =>
          nativeOutcomeDist B σ k
            (fun raw => VisEnv.cons (Player := Player) (L := L) (x := x) (τ := τ)
              (MAIDCompileState.readVal (B := B) raw τ.base nextId) (ρ raw))
            (nextId + 1) (raw.extend nextId ⟨τ.base, v⟩))
  | _, .commit (b := b) x who acts R k, ρ, nextId, raw =>
      FDist.bind
        (σ.commit who x acts R (VisEnv.toView (Player := Player) (L := L) who (ρ raw)))
        (fun v =>
          nativeOutcomeDist B σ k
            (fun raw => VisEnv.cons (Player := Player) (L := L) (x := x) (τ := .hidden who b)
              (MAIDCompileState.readVal (B := B) raw b nextId) (ρ raw))
            (nextId + 1) (raw.extend nextId ⟨b, v⟩))
  | _, .reveal (b := b) y _who _x hx k, ρ, nextId, raw =>
      nativeOutcomeDist B σ k
        (fun raw =>
          let v : L.Val b := VisEnv.get (Player := Player) (L := L) (ρ raw) hx
          VisEnv.cons (Player := Player) (L := L) (x := y) (τ := .pub b) v (ρ raw))
        nextId raw

-- nativeOutcomeDist = outcomeDist


/-- **Core theorem.** `nativeOutcomeDist` equals `outcomeDist` when ρ is
insensitive to all node ids ≥ nextId.

The proof is by structural induction on `Prog`. Each case uses
`readVal_extend_self` + `InsensitiveTo` for the ρ roundtrip. -/
theorem nativeOutcomeDist_eq_outcomeDist
    (B : MAIDBackend Player L)
    {Γ : VisCtx Player L}
    (p : Prog Player L Γ)
    (σ : Profile (Player := Player) (L := L))
    (ρ : RawNodeEnv L → VisEnv (Player := Player) L Γ)
    (nextId : Nat)
    (hρ : ∀ nid, nextId ≤ nid → InsensitiveTo ρ nid) :
    ∀ raw : RawNodeEnv L,
    nativeOutcomeDist B σ p ρ nextId raw = outcomeDist σ p (ρ raw) := by
  induction p generalizing nextId with
  | ret u =>
    intro raw
    simp only [nativeOutcomeDist, outcomeDist]
  | letExpr x e k ih =>
    intro raw
    simp only [nativeOutcomeDist, outcomeDist]
    exact ih _ nextId
      (fun nid hn raw tv => VisEnv.cons_ext (by rw [hρ nid hn raw tv]) (hρ nid hn raw tv))
      raw
  | sample x τ m D' k ih =>
    intro raw
    simp only [nativeOutcomeDist, outcomeDist]
    congr 1; funext v
    have hρ' : ∀ nid', nextId + 1 ≤ nid' → InsensitiveTo
        (fun raw => VisEnv.cons (Player := Player) (L := L) (x := x) (τ := τ)
          (MAIDCompileState.readVal (B := B) raw τ.base nextId) (ρ raw)) nid' := by
      intro nid' hn' raw tv
      exact VisEnv.cons_ext
        (readVal_extend_ne raw nid' nextId tv τ.base (by omega))
        (hρ nid' (by omega) raw tv)
    rw [ih _ (nextId + 1) hρ']
    congr 1
    exact VisEnv.cons_ext (readVal_extend_self (B := B) raw nextId τ.base v)
      (hρ nextId (le_refl _) raw ⟨τ.base, v⟩)
  | @commit _ x who b acts R k ih =>
    intro raw
    simp only [nativeOutcomeDist, outcomeDist]
    congr 1; funext v
    have hρ' : ∀ nid', nextId + 1 ≤ nid' → InsensitiveTo
        (fun raw => VisEnv.cons (Player := Player) (L := L) (x := x) (τ := .hidden who b)
          (MAIDCompileState.readVal (B := B) raw b nextId) (ρ raw)) nid' := by
      intro nid' hn' raw tv
      exact VisEnv.cons_ext
        (readVal_extend_ne raw nid' nextId tv b (by omega))
        (hρ nid' (by omega) raw tv)
    rw [ih _ (nextId + 1) hρ']
    congr 1
    exact VisEnv.cons_ext (readVal_extend_self (B := B) raw nextId b v)
      (hρ nextId (le_refl _) raw ⟨b, v⟩)
  | reveal y who x hx k ih =>
    intro raw
    simp only [nativeOutcomeDist, outcomeDist]
    exact ih _ nextId
      (fun nid hn raw tv => VisEnv.cons_ext (by rw [hρ nid hn raw tv]) (hρ nid hn raw tv))
      raw

/-- Corollary: for the initial state (constant ρ), `nativeOutcomeDist` = `outcomeDist`. -/
theorem nativeOutcomeDist_eq_outcomeDist_init
    (B : MAIDBackend Player L)
    {Γ : VisCtx Player L}
    (p : Prog Player L Γ)
    (σ : Profile (Player := Player) (L := L))
    (env : VisEnv (Player := Player) L Γ)
    (raw₀ : RawNodeEnv L) :
    nativeOutcomeDist B σ p (fun _ => env) 0 raw₀ = outcomeDist σ p env := by
  exact nativeOutcomeDist_eq_outcomeDist B p σ (fun _ => env) 0
    (fun _ _ _ _ => rfl) raw₀

-- Compiled state has natural order


theorem compiled_naturalOrder (st : MAIDCompileState Player L B) :
    @Struct.NaturalOrder Player _ B.fintypePlayer st.nextId st.toStruct := by
  let _ : Fintype Player := B.fintypePlayer
  intro nd p hp
  rcases Finset.mem_image.mp hp with ⟨d, hd, rfl⟩
  exact st.descAt_parent_lt nd d.2

-- Bridge constructions


/-- Deterministic outcome extraction: given a `RawNodeEnv`, replay the Prog
to reconstruct the final environment and evaluate the utility. -/
noncomputable def extractOutcome
    (B : MAIDBackend Player L) :
    {Γ : VisCtx Player L} →
    Prog Player L Γ →
    (RawNodeEnv L → VisEnv (Player := Player) L Γ) →
    Nat → (RawNodeEnv L → U.Outcome)
  | _, .ret u, ρ, _ => fun raw => U.eval u (ρ raw)
  | _, .letExpr (b := b) x e k, ρ, nextId =>
      extractOutcome B k
        (fun raw => VisEnv.cons (Player := Player) (L := L) (x := x) (τ := .pub b)
          (E.eval e (ρ raw)) (ρ raw))
        nextId
  | _, .sample x τ _m _D' k, ρ, nextId =>
      extractOutcome B k
        (fun raw => VisEnv.cons (Player := Player) (L := L) (x := x) (τ := τ)
          (MAIDCompileState.readVal (B := B) raw τ.base nextId) (ρ raw))
        (nextId + 1)
  | _, .commit (b := b) x who _acts _R k, ρ, nextId =>
      extractOutcome B k
        (fun raw => VisEnv.cons (Player := Player) (L := L) (x := x) (τ := .hidden who b)
          (MAIDCompileState.readVal (B := B) raw b nextId) (ρ raw))
        (nextId + 1)
  | _, .reveal (b := b) y _who _x hx k, ρ, nextId =>
      extractOutcome B k
        (fun raw =>
          let v : L.Val b := VisEnv.get (Player := Player) (L := L) (ρ raw) hx
          VisEnv.cons (Player := Player) (L := L) (x := y) (τ := .pub b) v (ρ raw))
        nextId

/-- Convert a total MAID assignment to a `RawNodeEnv`. -/
noncomputable def rawOfTAssign (st : MAIDCompileState Player L B)
    (a : @TAssign Player _ B.fintypePlayer st.nextId st.toStruct) : RawNodeEnv L :=
  let _ : Fintype Player := B.fintypePlayer
  fun i =>
  if hi : i < st.nextId then
    MAIDCompileState.taggedOfVal (st.descAt ⟨i, hi⟩) (a ⟨i, hi⟩)
  else
    none

-- Compiled policy


/-- Kernel normalization: every decision node in `st`, when its kernel is
applied to `σ`, produces a normalized FDist. -/
def MAIDCompileState.KernelNormalized (st : MAIDCompileState Player L B)
    (σ : Profile (Player := Player) (L := L)) : Prop :=
  ∀ (nd : Fin st.nextId) (raw : RawNodeEnv L)
    (τ : L.Ty) (who : Player) (acts : List (L.Val τ))
    (hacts : acts ≠ []) (hnodup : acts.Nodup) (obs : Finset Nat)
    (kernel : Profile (Player := Player) (L := L) → RawNodeEnv L → FDist (L.Val τ)),
    st.descAt nd = .decision τ who acts hacts hnodup obs kernel →
    FDist.totalWeight (kernel σ raw) = 1

/-- Compile a Vegas `Profile` into a MAID `Policy`. Each decision node's
kernel is evaluated and converted via `toPMF`. -/
noncomputable def compiledPolicy (st : MAIDCompileState Player L B)
    (σ : Profile (Player := Player) (L := L))
    (hkn : st.KernelNormalized σ) :
    @MAID.Policy Player _ B.fintypePlayer st.nextId st.toStruct := by
  let _ : Fintype Player := B.fintypePlayer
  intro p ⟨d, cfg⟩
  change PMF (CompiledNode.valType (st.descAt d.1))
  exact match hdesc : st.descAt d.1 with
  | .decision τ _who acts hacts hnodup obs kernel =>
      @FDist.toPMF (L.Val τ) L.decEqVal (kernel σ (st.rawEnvOfCfg cfg))
        (hkn d.1 (st.rawEnvOfCfg cfg) τ _ acts hacts hnodup obs kernel hdesc)
  | .chance τ ps cpd hn =>
      absurd d.2 (by simp [MAIDCompileState.toStruct, CompiledNode.kind, hdesc])
  | .utility who ps ufn =>
      absurd d.2 (by simp [MAIDCompileState.toStruct, CompiledNode.kind, hdesc])


-- Kernel normalization preservation


/-- The empty compile state trivially satisfies kernel normalization
(it has no nodes). -/
theorem MAIDCompileState.empty_kernelNormalized
    (σ : Profile (Player := Player) (L := L)) :
    (MAIDCompileState.empty (B := B)).KernelNormalized σ :=
  fun nd => nd.elim0

/-- `addVar` does not change nodes, so kernel normalization is preserved. -/
theorem MAIDCompileState.addVar_kernelNormalized
    (st : MAIDCompileState Player L B)
    (σ : Profile (Player := Player) (L := L))
    (x : VarId) (τ : VisBindTy Player L) (deps : Finset Nat)
    (hdeps : ∀ d ∈ deps, d < st.nextId)
    (hst : st.KernelNormalized σ) :
    (st.addVar x τ deps hdeps).KernelNormalized σ :=
  hst  -- addVar preserves nodes and nextId

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

/-- `addNode` with a chance node preserves kernel normalization. -/
theorem MAIDCompileState.addNode_chance_kernelNormalized
    (st : MAIDCompileState Player L B)
    (σ : Profile (Player := Player) (L := L))
    (τ : L.Ty) (deps : Finset Nat)
    (cpd : RawNodeEnv L → FDist (L.Val τ))
    (hn : ∀ raw, FDist.totalWeight (cpd raw) = 1)
    (hdeps : ∀ d ∈ (CompiledNode.chance τ deps cpd hn).parents ∪
      (CompiledNode.chance τ deps cpd hn).obsParents, d < st.nextId)
    (hst : st.KernelNormalized σ) :
    (st.addNode (.chance τ deps cpd hn) hdeps).2.KernelNormalized σ := by
  intro nd raw τ' who acts hacts hnodup obs kernel hdesc
  by_cases h : nd.val < st.nextId
  · -- Old node
    have heq := st.addNode_descAt_old (.chance τ deps cpd hn) hdeps ⟨nd.val, h⟩
    simp only [Fin.eta] at heq
    rw [heq] at hdesc
    exact hst ⟨nd.val, h⟩ raw τ' who acts hacts hnodup obs kernel hdesc
  · -- New node at st.nextId
    have hlen : (st.addNode (.chance τ deps cpd hn) hdeps).2.nextId = st.nextId + 1 := rfl
    have hnd : nd.val = st.nextId := by omega
    have heq := st.addNode_descAt_new (.chance τ deps cpd hn) hdeps
    have hnd' : nd = ⟨st.nextId, Nat.lt_succ_self _⟩ := Fin.ext hnd
    rw [hnd'] at hdesc
    rw [heq] at hdesc
    -- hdesc says .chance = .decision, contradiction
    cases hdesc

/-- `addNode` with a decision node preserves kernel normalization when the
kernel is normalized. -/
theorem MAIDCompileState.addNode_decision_kernelNormalized
    (st : MAIDCompileState Player L B)
    (σ : Profile (Player := Player) (L := L))
    (τ : L.Ty) (who : Player) (acts : List (L.Val τ))
    (hacts : acts ≠ []) (hnodup : acts.Nodup) (obs : Finset Nat)
    (kernel : Profile (Player := Player) (L := L) → RawNodeEnv L → FDist (L.Val τ))
    (hdeps : ∀ d ∈ (CompiledNode.decision τ who acts hacts hnodup obs kernel).parents ∪
      (CompiledNode.decision τ who acts hacts hnodup obs kernel).obsParents, d < st.nextId)
    (hst : st.KernelNormalized σ)
    (hkernel : ∀ raw, FDist.totalWeight (kernel σ raw) = 1) :
    (st.addNode (.decision τ who acts hacts hnodup obs kernel) hdeps).2.KernelNormalized σ := by
  intro nd raw τ' who' acts' hacts' hnodup' obs' kernel' hdesc
  by_cases h : nd.val < st.nextId
  · have heq := st.addNode_descAt_old
        (.decision τ who acts hacts hnodup obs kernel) hdeps ⟨nd.val, h⟩
    simp only [Fin.eta] at heq
    rw [heq] at hdesc
    exact hst ⟨nd.val, h⟩ raw τ' who' acts' hacts' hnodup' obs' kernel' hdesc
  · have hlen : (st.addNode (.decision τ who acts hacts hnodup obs kernel) hdeps).2.nextId =
        st.nextId + 1 := rfl
    have hnd : nd.val = st.nextId := by omega
    have heq := st.addNode_descAt_new (.decision τ who acts hacts hnodup obs kernel) hdeps
    have hnd' : nd = ⟨st.nextId, Nat.lt_succ_self _⟩ := Fin.ext hnd
    rw [hnd'] at hdesc; rw [heq] at hdesc
    cases hdesc
    exact hkernel raw

/-- Utility nodes preserve kernel normalization. -/
theorem MAIDCompileState.addUtilityNodes_kernelNormalized
    (st : MAIDCompileState Player L B)
    (σ : Profile (Player := Player) (L := L))
    (deps : Finset Nat) (hdeps : ∀ d ∈ deps, d < st.nextId)
    (ufn : Player → RawNodeEnv L → ℝ) (players : List Player)
    (hst : st.KernelNormalized σ) :
    (st.addUtilityNodes deps hdeps ufn players).KernelNormalized σ := by
  induction players generalizing st with
  | nil => exact hst
  | cons who rest ih =>
    apply ih
    have hutdeps : ∀ d ∈ (CompiledNode.utility (B := B) who deps
        (ufn who)).parents ∪
        (CompiledNode.utility (B := B) who deps (ufn who)).obsParents,
        d < st.nextId := by
      intro d hd'; have := Finset.mem_union.mp hd'
      rcases this with h | h <;>
        simpa [CompiledNode.parents, CompiledNode.obsParents]
          using hdeps d h
    intro nd raw τ who' acts hacts hnodup obs kernel hdesc
    by_cases h : nd.val < st.nextId
    · have heq := st.addNode_descAt_old
        (.utility who deps (ufn who)) hutdeps ⟨nd.val, h⟩
      simp only [Fin.eta] at heq; rw [heq] at hdesc
      exact hst ⟨nd.val, h⟩ raw τ who' acts hacts hnodup
        obs kernel hdesc
    · have hlen : (st.addNode (.utility who deps (ufn who))
          hutdeps).2.nextId = st.nextId + 1 := rfl
      have hnd : nd.val = st.nextId := by omega
      have heq := st.addNode_descAt_new
        (.utility who deps (ufn who)) hutdeps
      have hnd' : nd = ⟨st.nextId, Nat.lt_succ_self _⟩ :=
        Fin.ext hnd
      rw [hnd'] at hdesc; rw [heq] at hdesc
      cases hdesc

/-- `ofProg` preserves kernel normalization: if `st₀` satisfies kernel
normalization and `σ` is normalized on `p`, then so does `ofProg B p ... st₀`. -/
theorem ofProg_kernelNormalized
    (B : MAIDBackend Player L)
    {Γ : VisCtx Player L}
    (p : Prog Player L Γ)
    (σ : Profile (Player := Player) (L := L))
    (hl : Legal p) (ha : DistinctActs p)
    (hd : _root_.NormalizedDists p)
    (hσ_norm : σ.NormalizedOn p)
    (ρ : RawNodeEnv L → VisEnv (Player := Player) L Γ)
    (st₀ : MAIDCompileState Player L B)
    (hst₀ : st₀.KernelNormalized σ) :
    (MAIDCompileState.ofProg B p hl ha hd ρ st₀).KernelNormalized σ := by
  induction p generalizing st₀ with
  | ret u =>
    exact st₀.addUtilityNodes_kernelNormalized σ _ _ _ _ hst₀
  | letExpr x e k ih =>
    exact ih hl ha hd hσ_norm _ _ (st₀.addVar_kernelNormalized σ _ _ _ _ hst₀)
  | sample x τ m D' k ih =>
    exact ih hl ha hd.2 hσ_norm _ _
      ((st₀.addNode _ _).2.addVar_kernelNormalized σ _ _ _ _
        (st₀.addNode_chance_kernelNormalized σ τ.base _ _ _ _ hst₀))
  | @commit Γ x who b acts R k ih =>
    exact ih hl.2 ha.2 hd hσ_norm.2 _ _
      ((st₀.addNode _ _).2.addVar_kernelNormalized σ _ _ _ _
        (st₀.addNode_decision_kernelNormalized σ b who acts _ ha.1 _ _ _ hst₀
          (fun raw => hσ_norm.1 _)))
  | reveal y who x hx k ih =>
    exact ih hl ha hd hσ_norm _ _ (st₀.addVar_kernelNormalized σ _ _ _ _ hst₀)

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
    (B : MAIDBackend Player L) {Γ : VisCtx Player L}
    (p : Prog Player L Γ) (hl ha hd)
    (ρ : RawNodeEnv L → VisEnv (Player := Player) L Γ)
    (st₀ : MAIDCompileState Player L B) :
    st₀.nextId ≤ (MAIDCompileState.ofProg B p hl ha hd ρ st₀).nextId := by
  induction p generalizing st₀ with
  | ret u =>
    letI := B.fintypePlayer; simp only [MAIDCompileState.ofProg]
    rw [MAIDCompileState.addUtilityNodes_nextId]; omega
  | letExpr x e k ih =>
    (expose_names;
      exact
        le_of_le_of_eq''
          (ih hl ha hd
            (fun raw ↦
              have env := ρ raw;
              VisEnv.cons (VisExprKit.eval e env) env)
            (st₀.addVar x (VisBindTy.pub b) (st₀.ctxDeps Γ_1) (ofProg._proof_1 B Γ_1 st₀)))
          rfl)
  | sample x τ m D' k ih =>
    change st₀.nextId ≤ (MAIDCompileState.ofProg B k hl ha hd.2 _ _).nextId
    refine le_trans (Nat.le_succ _) ?_
    (expose_names;
      exact
        le_of_le_of_eq''
          (ih hl ha hd.right
            (fun raw ↦
              have env := ρ raw;
              have v := readVal raw τ.base st₀.nextId;
              VisEnv.cons v env)
            ((st₀.addNode
                    (CompiledNode.chance τ.base (st₀.ctxDeps Γ_1)
                      (fun raw ↦
                        have env := ρ raw;
                        VisDistKit.eval D' (VisEnv.projectDist τ m env))
                      (ofProg._proof_2 Γ_1 x τ m D' k hd ρ))
                    (ofProg._proof_3 B Γ_1 x τ m D' k hd ρ st₀)).2.addVar
              x τ {st₀.nextId} (ofProg._proof_5 B Γ_1 x τ m D' k hd ρ st₀)))
          rfl)
  | commit x who acts R k ih =>
    change st₀.nextId ≤ (MAIDCompileState.ofProg B k hl.2 ha.2 hd _ _).nextId
    refine le_trans (Nat.le_succ _) ?_
    (expose_names;
      exact
        le_of_le_of_eq''
          (ih hl.right ha.right hd
            (fun raw ↦
              have env := ρ raw;
              have v := readVal raw _ st₀.nextId;
              VisEnv.cons v env)
            ((st₀.addNode
                    (CompiledNode.decision _ who acts _ _ (st₀.ctxDeps Γ_1) fun σ raw ↦
                      σ.commit who x acts R (VisEnv.toView who (ρ raw)))
                    _).2.addVar
              x _ {st₀.nextId} _))
          rfl)
  | reveal y who x hx k ih =>
    (expose_names;
      exact
        le_of_le_of_eq''
          (ih hl ha hd
            (fun raw ↦
              have env := ρ raw;
              have v := env.get hx;
              VisEnv.cons v env)
            (st₀.addVar y (VisBindTy.pub b) (st₀.lookupDeps x) (lookupDeps_lt st₀ x)))
          rfl)

/-- `nativeOutcomeDist` has total weight 1 when distributions and profile
are normalized. -/
theorem nativeOutcomeDist_totalWeight
    (B : MAIDBackend Player L)
    {Γ : VisCtx Player L}
    (p : Prog Player L Γ)
    (σ : Profile (Player := Player) (L := L))
    (hd : NormalizedDists p)
    (hσ_norm : σ.NormalizedOn p)
    (ρ : RawNodeEnv L → VisEnv (Player := Player) L Γ)
    (nextId : Nat)
    (hρ : ∀ nid, nextId ≤ nid → InsensitiveTo ρ nid)
    (raw : RawNodeEnv L) :
    FDist.totalWeight (nativeOutcomeDist B σ p ρ nextId raw) = 1 := by
  rw [nativeOutcomeDist_eq_outcomeDist B p σ ρ nextId hρ raw]
  exact outcomeDist_totalWeight_eq_one hd hσ_norm

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
    (B : MAIDBackend Player L) {Γ : VisCtx Player L}
    (p : Prog Player L Γ) (hl ha hd)
    (ρ : RawNodeEnv L → VisEnv (Player := Player) L Γ)
    (st₀ : MAIDCompileState Player L B) (j : Nat) (hj : j < st₀.nextId) :
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
    -- addVar preserves descAt; use addNode_descAt_old
    simp only [MAIDCompileState.descAt, MAIDCompileState.addVar, MAIDCompileState.addNode]
    congr 1
    rw [List.getElem_append_left (by rw [st₀.nodes_length_eq_nextId]; exact hj)]
  | commit x who acts R k ih =>
    change (MAIDCompileState.ofProg B k hl.2 ha.2 hd _ _).descAt ⟨j, _⟩ = _
    rw [ih hl.2 ha.2 hd _ _ (Nat.lt_succ_of_lt hj)]
    simp only [MAIDCompileState.descAt, MAIDCompileState.addVar, MAIDCompileState.addNode]
    congr 1
    rw [List.getElem_append_left (by rw [st₀.nodes_length_eq_nextId]; exact hj)]
  | reveal y who x hx k ih =>
    simp only [MAIDCompileState.ofProg]
    exact ih hl ha hd _ (st₀.addVar _ _ _ _) hj

-- ctxDeps tracking lemmas

section
omit [DecidableEq Player] E D U

theorem VisHasVar.mem_map_fst
    {Γ : VisCtx Player L} {x : VarId} {τ : VisBindTy Player L}
    (h : VisHasVar (L := L) Γ x τ) :
    x ∈ Γ.map Prod.fst := by
  induction h with
  | here => simp
  | there h ih => exact List.mem_cons_of_mem _ ih

theorem lookupDepsAux_append_singleton_eq_of_ne
    (vars : List (MAIDVarEntry Player L))
    (x y : VarId) (τ : VisBindTy Player L) (deps : Finset Nat)
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
    (x : VarId) (τ : VisBindTy Player L) (deps : Finset Nat)
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
    (x : VarId) (τ : VisBindTy Player L) (deps : Finset Nat)
    (hdeps : ∀ d ∈ deps, d < st.nextId)
    {y : VarId} (hxy : y ≠ x) :
    (st.addVar x τ deps hdeps).lookupDeps y = st.lookupDeps y := by
  unfold MAIDCompileState.lookupDeps
  simpa [MAIDCompileState.addVar] using
    lookupDepsAux_append_singleton_eq_of_ne st.vars x y τ deps hxy

theorem MAIDCompileState.lookupDeps_addVar_eq_self_of_fresh
    (st : MAIDCompileState Player L B)
    (x : VarId) (τ : VisBindTy Player L) (deps : Finset Nat)
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
    (x : VarId) (τ : VisBindTy Player L) (deps : Finset Nat)
    (hdeps : ∀ d ∈ deps, d < st.nextId)
    (xs : List VarId) (hfresh : x ∉ xs) :
    (st.addVar x τ deps hdeps).depsOfVars xs = st.depsOfVars xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    have hyx : y ≠ x := by
      intro h
      apply hfresh
      simp [h]
    have hfresh' : x ∉ ys := by
      intro h
      apply hfresh
      simp [h]
    simp [MAIDCompileState.depsOfVars,
      st.lookupDeps_addVar_eq_of_ne x τ deps hdeps hyx, ih hfresh']

theorem MAIDCompileState.ctxDeps_addVar_eq_of_fresh
    (st : MAIDCompileState Player L B)
    (x : VarId) (τ : VisBindTy Player L) (deps : Finset Nat)
    (hdeps : ∀ d ∈ deps, d < st.nextId)
    {Γ : VisCtx Player L}
    (hfresh : Fresh x Γ) :
    (st.addVar x τ deps hdeps).ctxDeps Γ = st.ctxDeps Γ := by
  simpa [MAIDCompileState.ctxDeps] using
    st.depsOfVars_addVar_eq_of_fresh x τ deps hdeps (Γ.map Prod.fst) hfresh

theorem MAIDCompileState.ctxDeps_addVar_cons_eq_of_fresh
    (st : MAIDCompileState Player L B)
    (x : VarId) (τ : VisBindTy Player L) (deps : Finset Nat)
    (hdeps : ∀ d ∈ deps, d < st.nextId)
    {Γ : VisCtx Player L}
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
  | nil =>
    cases hx
  | cons y ys ih =>
    intro d hd
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp [MAIDCompileState.depsOfVars, hd]
    · have hd' : d ∈ st.depsOfVars ys := ih hx hd
      simp [MAIDCompileState.depsOfVars, hd']

theorem MAIDCompileState.lookupDeps_subset_ctxDeps_of_mem
    (st : MAIDCompileState Player L B)
    {Γ : VisCtx Player L} {x : VarId}
    (hx : x ∈ Γ.map Prod.fst) :
    st.lookupDeps x ⊆ st.ctxDeps Γ := by
  simpa [MAIDCompileState.ctxDeps] using
    st.lookupDeps_subset_depsOfVars_of_mem hx

theorem MAIDCompileState.lookupDeps_subset_ctxDeps_of_hasVar
    (st : MAIDCompileState Player L B)
    {Γ : VisCtx Player L} {x : VarId} {τ : VisBindTy Player L}
    (hx : VisHasVar (L := L) Γ x τ) :
    st.lookupDeps x ⊆ st.ctxDeps Γ :=
  st.lookupDeps_subset_ctxDeps_of_mem hx.mem_map_fst

theorem MAIDCompileState.ctxDeps_addNode_eq
    (st : MAIDCompileState Player L B)
    (nd : CompiledNode Player L B)
    (hdeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId)
    (Γ : VisCtx Player L) :
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
    {Γ : VisCtx Player L} (x : VarId) {b : L.Ty}
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
    {Γ : VisCtx Player L}
    (x : VarId) (τ : VisBindTy Player L)
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
    {Γ : VisCtx Player L}
    (y : VarId) (who : Player) (x : VarId) {b : L.Ty}
    (hx : VisHasVar (L := L) Γ x (.hidden who b))
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
  | decision τ _ _ _ _ _ _ => exact L.decEqVal
  | utility _ _ _ => exact instDecidableEqPUnit

/-- Per-node FDist dispatch: given a `CompiledNode`, produce the FDist over
its value type. -/
noncomputable def compiledNodeFDist
    (_st : MAIDCompileState Player L B)
    (σ : Profile (Player := Player) (L := L))
    (rawP : RawNodeEnv L) (rawO : RawNodeEnv L) :
    (c : CompiledNode Player L B) → FDist (CompiledNode.valType c)
  | .chance _τ _ cpd _ => cpd rawP
  | .decision _τ _ _ _ _ _ kernel => kernel σ rawO
  | .utility _ _ _ => FDist.pure ()

/-- FDist node data produced by the compiler. -/
noncomputable def compiledFDistData
    (st : MAIDCompileState Player L B)
    (σ : Profile (Player := Player) (L := L))
    (hkn : st.KernelNormalized σ) :
    @FDistNodeData Player _ B.fintypePlayer _ st.toStruct :=
  letI := B.fintypePlayer
  { dist := fun nd a =>
      compiledNodeFDist st σ
        (st.rawEnvOfCfg (projCfg a (st.toStruct.parents nd)))
        (st.rawEnvOfCfg (projCfg a (st.toStruct.obsParents nd)))
        (st.descAt nd)
    normalized := by
      intro nd a
      change FDist.totalWeight (compiledNodeFDist st σ _ _ (st.descAt nd)) = 1
      match hdesc : st.descAt nd with
      | .chance _ _ _ hn => simp only [compiledNodeFDist]; exact hn _
      | .decision _ _ _ _ _ _ _ =>
          simp only [compiledNodeFDist]; exact hkn nd _ _ _ _ _ _ _ _ hdesc
      | .utility _ _ _ => simp [compiledNodeFDist, FDist.totalWeight_pure] }

@[congr] theorem FDist.toPMF_congr [DecidableEq α]
    {d₁ d₂ : FDist α} {h₁ h₂} (heq : d₁ = d₂) :
    FDist.toPMF d₁ h₁ = FDist.toPMF d₂ h₂ := by subst heq; rfl

@[simp] theorem toStruct_kind (st : MAIDCompileState Player L B) (nd : Fin st.nextId) :
    letI := B.fintypePlayer; st.toStruct.kind nd = (st.descAt nd).kind := rfl

@[simp] theorem toStruct_Val (st : MAIDCompileState Player L B) (nd : Fin st.nextId) :
    letI := B.fintypePlayer; st.toStruct.Val nd = CompiledNode.valType (st.descAt nd) := rfl

theorem compiledFDistData_dist_eq
    (st : MAIDCompileState Player L B)
    (σ : Profile (Player := Player) (L := L))
    (hkn : st.KernelNormalized σ)
    (nd : Fin st.nextId)
    (a : @TAssign Player _ B.fintypePlayer st.nextId st.toStruct) :
    letI := B.fintypePlayer
    (compiledFDistData st σ hkn).dist nd a =
    compiledNodeFDist st σ
      (st.rawEnvOfCfg (projCfg a (st.toStruct.parents nd)))
      (st.rawEnvOfCfg (projCfg a (st.toStruct.obsParents nd)))
      (st.descAt nd) := rfl

theorem compiledFDistData_compatible
    (st : MAIDCompileState Player L B)
    (σ : Profile (Player := Player) (L := L))
    (hkn : st.KernelNormalized σ) :
    @FDistNodeDataCompatible _ _ B.fintypePlayer _ _ (compiledFDistData st σ hkn)
      (MAIDCompileState.toSem st) (compiledPolicy st σ hkn) := by
  letI := B.fintypePlayer
  intro nd a
  let rawP := st.rawEnvOfCfg (projCfg a (st.toStruct.parents nd))
  let rawO := st.rawEnvOfCfg (projCfg a (st.toStruct.obsParents nd))
  have hnorm : FDist.totalWeight (compiledNodeFDist st σ rawP rawO (st.descAt nd)) = 1 :=
    (compiledFDistData st σ hkn).normalized nd a
  suffices ∀ (c : CompiledNode Player L B)
      (hn : FDist.totalWeight (compiledNodeFDist st σ rawP rawO c) = 1)
      (hc : st.descAt nd = c),
      FDist.toPMF (compiledNodeFDist st σ rawP rawO c) hn =
        (hc ▸ nodeDist st.toStruct st.toSem (compiledPolicy st σ hkn) nd a) by
    exact this (st.descAt nd) hnorm rfl
  intro c hn hc
  cases c with
  | chance τ ps cpd hcn =>
      simp_all only [compiledNodeFDist, nodeDist, toStruct_kind, CompiledNode.kind,
         MAIDCompileState.toSem, eq_mpr_eq_cast, id_eq]
      grind only
  | decision τ who acts ha hnd obs k =>
      simp_all only [compiledNodeFDist, nodeDist, toStruct_kind, CompiledNode.kind,
        id_eq, compiledPolicy]
      grind only
  | utility who ps ufn =>
      have hsub : Subsingleton (PMF Unit) := ⟨fun a b => PMF.ext fun ⟨⟩ => by
        have ha := a.2.tsum_eq
        rw [tsum_eq_single ()
          (fun x hx => absurd (Subsingleton.elim x ()) hx)] at ha
        have hb := b.2.tsum_eq
        rw [tsum_eq_single ()
          (fun x hx => absurd (Subsingleton.elim x ()) hx)] at hb
        exact ha.trans hb.symm⟩
      exact hsub.elim _ _

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
theorem InsensitiveTo.eq_of_agree_off_list [Nonempty (TaggedVal L)]
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
    have hval : d.1 = i := by
      simpa using congrArg Fin.val hEq
    simpa [hval] using d.2
  · intro h
    refine Finset.mem_image.mpr ?_
    refine ⟨⟨i, h⟩, by simp, ?_⟩
    exact Fin.ext rfl

theorem MAIDCompileState.rawEnvOfCfg_proj_eq_select
    (st : MAIDCompileState Player L B)
    (a : @TAssign Player _ B.fintypePlayer st.nextId st.toStruct)
    (ps : Finset (Fin st.nextId))
    (deps : Finset Nat)
    (hps : ∀ i (hi : i < st.nextId), ((⟨i, hi⟩ : Fin st.nextId) ∈ ps ↔ i ∈ deps)) :
    let _ : Fintype Player := B.fintypePlayer
    st.rawEnvOfCfg (projCfg a ps) =
      fun i =>
        if i < st.nextId then
          if i ∈ deps then rawOfTAssign st a i else none
        else
          none := by
  funext i
  by_cases hi : i < st.nextId
  · have hps' := hps i hi
    by_cases hmem : (⟨i, hi⟩ : Fin st.nextId) ∈ ps
    · have hdep : i ∈ deps := (hps').mp hmem
      simp [MAIDCompileState.rawEnvOfCfg, projCfg, rawOfTAssign, hi, hmem, hdep]
    · have hdep : i ∉ deps := by
        intro hdep
        exact hmem ((hps').mpr hdep)
      simp [MAIDCompileState.rawEnvOfCfg, projCfg, hi, hmem, hdep]
  · simp [MAIDCompileState.rawEnvOfCfg, hi]

theorem eq_on_ctxDeps_rawOfTAssign
    (st : MAIDCompileState Player L B)
    {deps : Finset Nat}
    {f : RawNodeEnv L → α}
    (hf : ∀ j, j ∉ deps → InsensitiveTo f j)
    (a : @TAssign Player _ B.fintypePlayer st.nextId st.toStruct) :
    let rawSel : RawNodeEnv L := fun i =>
      if i < st.nextId then
        if i ∈ deps then rawOfTAssign st a i else none
      else
        none
    f rawSel = f (rawOfTAssign st a) := by
  intro rawSel
  let ks : List Nat := (List.range st.nextId).filter (· ∉ deps)
  have hclear :
      rawSel = fun i => if i ∈ ks then none else rawOfTAssign st a i := by
    funext i
    by_cases hi : i < st.nextId
    · have hmem : i ∈ ks ↔ i ∉ deps := by
        unfold ks
        simp [hi]
      by_cases hdep : i ∈ deps
      · simp [rawSel, hi, hdep, hmem]
      · simp [rawSel, hi, hdep, hmem]
    · simp [rawSel, hi, ks, rawOfTAssign]
  rw [hclear]
  haveI : Nonempty (TaggedVal L) :=
    let ⟨v⟩ := B.toMAIDValuation.nonemptyVal L.bool; ⟨⟨L.bool, v⟩⟩
  apply InsensitiveTo.eq_of_agree_off_list ks
  · intro k hk
    apply hf k
    have hk' : k ∈ (List.range st.nextId).filter (fun j => j ∉ deps) := by
      simpa [ks] using hk
    simpa using (List.mem_filter.mp hk').2
  · intro i hi
    simp [hi]

theorem MAIDCompileState.rawOfTAssign_updateAssign_of_tagged
    (st : MAIDCompileState Player L B)
    (a : @TAssign Player _ B.fintypePlayer st.nextId st.toStruct)
    (nd : Fin st.nextId)
    (v : @Struct.Val Player _ B.fintypePlayer st.nextId st.toStruct nd)
    (tv : TaggedVal L)
    (htag : MAIDCompileState.taggedOfVal (st.descAt nd) v = some tv) :
    let _ : Fintype Player := B.fintypePlayer
    rawOfTAssign st (updateAssign a nd v) =
      (rawOfTAssign st a).extend nd.val tv := by
  letI := B.fintypePlayer
  funext i
  by_cases hi : i < st.nextId
  · by_cases hEq : (⟨i, hi⟩ : Fin st.nextId) = nd
    · have hival : i = nd.val := by simpa using congrArg Fin.val hEq
      subst hival
      simp [rawOfTAssign, RawNodeEnv.extend, hi, updateAssign, htag]
    · have hne : i ≠ nd.val := by
        intro hival
        apply hEq
        exact Fin.ext hival
      simp [rawOfTAssign, RawNodeEnv.extend, hi, updateAssign, hEq, hne]
  · have hne : i ≠ nd.val := by
      intro hEq
      exact hi (hEq.symm ▸ nd.isLt)
    simp [rawOfTAssign, RawNodeEnv.extend, hi, hne]

theorem foldl_evalStepFDist_bind [Fintype Player]
    {S : MAID.Struct Player n}
    (data : FDistNodeData S) (L : List (Fin n))
    (acc : FDist (TAssign S)) (g : TAssign S → FDist (TAssign S)) :
    L.foldl (evalStepFDist data) (FDist.bind acc g) =
      FDist.bind acc (fun a => L.foldl (evalStepFDist data) (g a)) := by
  induction L generalizing acc g with
  | nil => rfl
  | cons nd rest ih =>
      simp only [List.foldl_cons, evalStepFDist]
      rw [FDist.bind_assoc]
      simpa using ih acc (fun a =>
        FDist.bind (g a) (fun a =>
          FDist.bind (data.dist nd a) (fun v =>
            FDist.pure (updateAssign a nd v))))

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
    (σ : Profile (Player := Player) (L := L))
    (hkn : st.KernelNormalized σ)
    (data : @FDistNodeData Player _ B.fintypePlayer _ st.toStruct)
    (hdata : data = compiledFDistData st σ hkn)
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
    subst hdata
    exact fdist_eq_pure_of_unique _ hnorm default
  rw [evalStepFDist, FDist.pure_bind, hdist, FDist.pure_bind]

theorem evalStepFDist_utility_map_eq
    (st : MAIDCompileState Player L B)
    (σ : Profile (Player := Player) (L := L))
    (hkn : st.KernelNormalized σ)
    (data : @FDistNodeData Player _ B.fintypePlayer _ st.toStruct)
    (hdata : data = compiledFDistData st σ hkn)
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
      (evalStepFDist_utility_pure st σ hkn data hdata nd hutility a)
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
    (σ : Profile (Player := Player) (L := L))
    (hkn : st.KernelNormalized σ)
    (data : @FDistNodeData Player _ B.fintypePlayer _ st.toStruct)
    (hdata : data = compiledFDistData st σ hkn)
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
              apply evalStepFDist_utility_map_eq st σ hkn data hdata nd (hutility nd (by simp))
              intro a v
              exact hf a nd v

def MAIDCompileState.VarsSubCtx
    (st : MAIDCompileState Player L B) (Γ : VisCtx Player L) : Prop :=
  ∀ x, x ∈ st.vars.map Prod.fst → x ∈ Γ.map Prod.fst

theorem MAIDCompileState.VarsSubCtx_addNode
    (st : MAIDCompileState Player L B)
    {Γ : VisCtx Player L}
    (hvars : st.VarsSubCtx Γ)
    (nd : CompiledNode Player L B)
    (hdeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId) :
    (st.addNode nd hdeps).2.VarsSubCtx Γ := by
  intro x
  simpa [MAIDCompileState.VarsSubCtx, MAIDCompileState.addNode] using hvars x

theorem MAIDCompileState.VarsSubCtx_addVar
    (st : MAIDCompileState Player L B)
    {Γ : VisCtx Player L}
    (hvars : st.VarsSubCtx Γ)
    (x : VarId) (τ : VisBindTy Player L) (deps : Finset Nat)
    (hdeps : ∀ d ∈ deps, d < st.nextId)
    (hfresh : Fresh x Γ) :
    (st.addVar x τ deps hdeps).VarsSubCtx ((x, τ) :: Γ) := by
  intro y hy
  have hy' : y ∈ st.vars.map Prod.fst ∨ y = x := by
    simpa [MAIDCompileState.addVar, List.map_append] using hy
  simp only [List.map_cons, List.mem_cons, List.mem_map, Prod.exists, exists_and_right,
    exists_eq_right]
  rcases hy' with hy' | rfl
  · exact Or.inr (by simpa [List.mem_map] using hvars y hy')
  · exact Or.inl rfl

theorem MAIDCompileState.VarsSubCtx_letExpr_step
    (st : MAIDCompileState Player L B)
    {Γ : VisCtx Player L}
    (hvars : st.VarsSubCtx Γ)
    (x : VarId) {b : L.Ty}
    (hfreshΓ : Fresh x Γ) :
    (st.addVar x (.pub b) (st.ctxDeps Γ) (st.depsOfVars_lt _)).VarsSubCtx
      ((x, .pub b) :: Γ) := by
  exact st.VarsSubCtx_addVar hvars x (.pub b) (st.ctxDeps Γ)
    (st.depsOfVars_lt _) hfreshΓ

theorem MAIDCompileState.VarsSubCtx_addNode_addVar_singleton_step
    (st : MAIDCompileState Player L B)
    {Γ : VisCtx Player L}
    (hvars : st.VarsSubCtx Γ)
    (nd : CompiledNode Player L B)
    (hndeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId)
    (x : VarId) (τ : VisBindTy Player L)
    (hfreshΓ : Fresh x Γ) :
    (((st.addNode nd hndeps).2).addVar x τ {st.nextId}
      (by
        intro d hd
        simp_all only [Finset.mem_singleton]
        exact Nat.lt_add_one st.nextId)).VarsSubCtx ((x, τ) :: Γ) := by
  exact ((st.addNode nd hndeps).2).VarsSubCtx_addVar
    (st.VarsSubCtx_addNode hvars nd hndeps) x τ {st.nextId}
    (by
      intro d hd
      simp_all only [Finset.mem_singleton]
      exact Nat.lt_add_one st.nextId)
    hfreshΓ

theorem MAIDCompileState.VarsSubCtx_sample_step
    (st : MAIDCompileState Player L B)
    {Γ : VisCtx Player L}
    (hvars : st.VarsSubCtx Γ)
    (nd : CompiledNode Player L B)
    (hndeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId)
    (x : VarId) (τ : VisBindTy Player L)
    (hfreshΓ : Fresh x Γ) :
    (((st.addNode nd hndeps).2).addVar x τ {st.nextId}
      (by
        intro d hd
        simp_all only [Finset.mem_singleton]
        exact Nat.lt_add_one st.nextId)).VarsSubCtx ((x, τ) :: Γ) := by
  exact st.VarsSubCtx_addNode_addVar_singleton_step hvars nd hndeps x τ hfreshΓ

theorem MAIDCompileState.VarsSubCtx_commit_step
    (st : MAIDCompileState Player L B)
    {Γ : VisCtx Player L}
    (hvars : st.VarsSubCtx Γ)
    (nd : CompiledNode Player L B)
    (hndeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId)
    (x : VarId) (τ : VisBindTy Player L)
    (hfreshΓ : Fresh x Γ) :
    (((st.addNode nd hndeps).2).addVar x τ {st.nextId}
      (by
        intro d hd
        simp_all only [Finset.mem_singleton]
        exact Nat.lt_add_one st.nextId)).VarsSubCtx ((x, τ) :: Γ) := by
  exact st.VarsSubCtx_addNode_addVar_singleton_step hvars nd hndeps x τ hfreshΓ

theorem MAIDCompileState.VarsSubCtx_reveal_step
    (st : MAIDCompileState Player L B)
    {Γ : VisCtx Player L}
    (hvars : st.VarsSubCtx Γ)
    (y : VarId) (x : VarId) {b : L.Ty}
    (hfreshΓ : Fresh y Γ) :
    (st.addVar y (.pub b) (st.lookupDeps x) (st.lookupDeps_lt x)).VarsSubCtx
      ((y, .pub b) :: Γ) := by
  exact st.VarsSubCtx_addVar hvars y (.pub b) (st.lookupDeps x)
    (st.lookupDeps_lt x) hfreshΓ

open MAID in
/-- **Core FDist bridge.** The partial FDist fold from `st₀.nextId`, mapped
through `extractOutcome ∘ rawOfTAssign`, equals `nativeOutcomeDist`.

The hypothesis `hρ_deps` captures that `ρ` only reads from positions in
`ctxDeps Γ` — trivially true for constant `ρ`, and maintained through the
Prog recursion since each sample/commit adds exactly its node ID to `ctxDeps`. -/
theorem foldFDist_map_extract_eq_nativeOutcomeDist
    (B : MAIDBackend Player L)
    {Γ : VisCtx Player L}
    (p : Prog Player L Γ)
    (σ : Profile (Player := Player) (L := L))
    (hl : Legal p) (ha : DistinctActs p)
    (hd : _root_.NormalizedDists p)
    (hwf : WF p)
    (hσ_norm : σ.NormalizedOn p)
    (ρ : RawNodeEnv L → VisEnv (Player := Player) L Γ)
    (st₀ : MAIDCompileState Player L B)
    (hst₀ : st₀.KernelNormalized σ)
    (hvars : st₀.VarsSubCtx Γ)
    (hρ_deps : ∀ j, j ∉ (st₀.ctxDeps Γ : Finset Nat) → InsensitiveTo ρ j) :
    let _ := B.fintypePlayer
    let st := MAIDCompileState.ofProg B p hl ha hd ρ st₀
    let data := compiledFDistData st σ
      (ofProg_kernelNormalized B p σ hl ha hd hσ_norm ρ st₀ hst₀)
    ∀ (a₀ : @TAssign Player _ B.fintypePlayer st.nextId st.toStruct),
    FDist.map (fun a => extractOutcome B p ρ st₀.nextId (rawOfTAssign st a))
      ((List.finRange st.nextId).drop st₀.nextId |>.foldl
        (evalStepFDist data) (FDist.pure a₀))
    = nativeOutcomeDist B σ p ρ st₀.nextId (rawOfTAssign st a₀) := by
  letI := B.fintypePlayer
  induction p generalizing st₀ with
  | ret u =>
      rename_i Γ'
      dsimp
      set st : MAIDCompileState Player L B := MAIDCompileState.ofProg B (Prog.ret u) hl ha hd ρ st₀
      intro a₀
      let data :=
        compiledFDistData st σ
          (ofProg_kernelNormalized B (Prog.ret u) σ hl ha hd hσ_norm ρ st₀ hst₀)
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
        have haux :
            ∃ who,
              ((st₀.addUtilityNodes (st₀.ctxDeps Γ')
                (st₀.depsOfVars_lt (Γ'.map Prod.fst))
                (fun who raw => (U.payoff (U.eval u (ρ raw)) who : ℝ))
                Finset.univ.toList).descAt nd).kind = NodeKind.utility who := by
          exact MAIDCompileState.addUtilityNodes_all_utility
            (st := st₀)
            (deps := st₀.ctxDeps Γ')
            (hdeps := st₀.depsOfVars_lt (Γ'.map Prod.fst))
            (ufn := fun who raw => (U.payoff (U.eval u (ρ raw)) who : ℝ))
            (players := Finset.univ.toList)
            (i := nd)
            hge
        simpa [st, MAIDCompileState.ofProg] using haux
      have hfold_aux :
          ∀ (nodes : List (Fin st.nextId))
            (hnodes : ∀ nd ∈ nodes, ∃ who, (st.descAt nd).kind = NodeKind.utility who)
            (acc : FDist (@TAssign Player _ B.fintypePlayer st.nextId st.toStruct)),
          FDist.map (fun a => extractOutcome B (Prog.ret u) ρ st₀.nextId (rawOfTAssign st a))
            (List.foldl (evalStepFDist data) acc nodes) =
          FDist.map (fun a => extractOutcome B (Prog.ret u) ρ st₀.nextId (rawOfTAssign st a))
            acc := by
        intro nodes hnodes acc
        induction nodes generalizing acc with
        | nil => rfl
        | cons nd rest ih =>
            simp only [List.foldl_cons]
            calc
              FDist.map (fun a => extractOutcome B (Prog.ret u) ρ st₀.nextId (rawOfTAssign st a))
                  (rest.foldl (evalStepFDist data) (evalStepFDist data acc nd)) =
                FDist.map (fun a => extractOutcome B (Prog.ret u) ρ st₀.nextId (rawOfTAssign st a))
                  (evalStepFDist data acc nd) := by
                    exact ih (fun nd' hnd' => hnodes nd' (by simp [hnd'])) _
              _ =
                FDist.map (fun a => extractOutcome B (Prog.ret u) ρ st₀.nextId (rawOfTAssign st a))
                  acc := by
                    apply evalStepFDist_utility_map_eq st σ
                      (ofProg_kernelNormalized B (Prog.ret u) σ hl ha hd hσ_norm ρ st₀ hst₀)
                      data rfl nd (hnodes nd (by simp))
                    intro a v
                    rw [rawOfTAssign_updateAssign_utility st a nd v (hnodes nd (by simp))]
      have hfold :
          FDist.map (fun a => extractOutcome B (Prog.ret u) ρ st₀.nextId (rawOfTAssign st a))
            (List.foldl (evalStepFDist data) (FDist.pure a₀)
              ((List.finRange st.nextId).drop st₀.nextId)) =
          FDist.map (fun a => extractOutcome B (Prog.ret u) ρ st₀.nextId (rawOfTAssign st a))
            (FDist.pure a₀) := by
        exact hfold_aux ((List.finRange st.nextId).drop st₀.nextId) hutility (FDist.pure a₀)
      have hmain :
        FDist.map (fun a => extractOutcome B (Prog.ret u) ρ st₀.nextId (rawOfTAssign st a))
            (List.foldl (evalStepFDist data) (FDist.pure a₀)
              ((List.finRange st.nextId).drop st₀.nextId)) =
          FDist.map (fun a => extractOutcome B (Prog.ret u) ρ st₀.nextId (rawOfTAssign st a))
            (FDist.pure a₀) := hfold
      have hmain' :
          FDist.map (fun a => extractOutcome B (Prog.ret u) ρ st₀.nextId (rawOfTAssign st a))
              (List.foldl (evalStepFDist data) (FDist.pure a₀)
                ((List.finRange st.nextId).drop st₀.nextId)) =
            nativeOutcomeDist B σ (Prog.ret u) ρ st₀.nextId (rawOfTAssign st a₀) := by
        calc
          FDist.map (fun a => extractOutcome B (Prog.ret u) ρ st₀.nextId (rawOfTAssign st a))
              (List.foldl (evalStepFDist data) (FDist.pure a₀)
                ((List.finRange st.nextId).drop st₀.nextId)) =
            FDist.map (fun a => extractOutcome B (Prog.ret u) ρ st₀.nextId (rawOfTAssign st a))
              (FDist.pure a₀) := hfold
          _ = nativeOutcomeDist B σ (Prog.ret u) ρ st₀.nextId (rawOfTAssign st a₀) := by
            rw [FDist.map_pure]
            simp [extractOutcome, nativeOutcomeDist]
      simpa [st, data] using hmain'
  | letExpr x e k ih =>
      rename_i Γ' b
      dsimp
      intro a₀
      have hxΓ : Fresh x Γ' := hwf.1
      have hxvars : x ∉ st₀.vars.map Prod.fst := by
        intro hxmem
        exact hxΓ (hvars x hxmem)
      let ρ' : RawNodeEnv L → VisEnv (Player := Player) L ((x, .pub b) :: Γ') :=
        fun raw =>
          let env := ρ raw
          VisEnv.cons (τ := .pub b) (E.eval e env) env
      let st₁ := st₀.addVar x (.pub b) (st₀.ctxDeps Γ') (st₀.depsOfVars_lt _)
      have hvars₁ : st₁.VarsSubCtx ((x, .pub b) :: Γ') := by
        simpa [st₁] using st₀.VarsSubCtx_letExpr_step hvars x hxΓ
      have hρ'_deps : ∀ j, j ∉ st₁.ctxDeps ((x, .pub b) :: Γ') → InsensitiveTo ρ' j := by
        intro j hj raw tv
        have hj' : j ∉ st₀.ctxDeps Γ' := by
          simpa [st₁, st₀.ctxDeps_letExpr_step x hxΓ hxvars] using hj
        have hρj := hρ_deps j hj' raw tv
        exact VisEnv.cons_ext (by simp [hρj]) hρj
      simpa [ρ', st₁, extractOutcome, nativeOutcomeDist] using
        (ih hl ha hd hwf.2 hσ_norm ρ' st₁
          (st₀.addVar_kernelNormalized σ x (.pub b) (st₀.ctxDeps Γ') (st₀.depsOfVars_lt _) hst₀)
          hvars₁ hρ'_deps a₀)
  | sample x τ m D' k ih =>
      dsimp
      intro a₀
      -- Player : Type
      -- inst✝ : DecidableEq Player
      -- L : ExprLanguage
      -- E : VisExprKit Player L
      -- D : VisDistKit Player L
      -- U : VisPayoffKit Player L
      -- B : MAIDBackend Player L
      -- Γ : VisCtx Player L
      -- σ : Profile Player L
      -- this : Fintype Player := B.fintypePlayer
      -- Γ✝ : VisCtx Player L
      -- x : VarId
      -- τ : VisBindTy Player L
      -- m : SampleMode τ
      -- D' : VisDistKit.DistExpr (distCtx τ m Γ✝) τ.base
      -- k : Prog Player L ((x, τ) :: Γ✝)
      -- ih : ∀ (hl : Legal k) (ha : DistinctActs k) (hd : NormalizedDists k),
      --   WF k →
      --     ∀ (hσ_norm : σ.NormalizedOn k) (ρ : RawNodeEnv L → VisEnv L ((x, τ) :: Γ✝)) (st₀ : MAIDCompileState Player L B)
      --       (hst₀ : st₀.KernelNormalized σ),
      --       st₀.VarsSubCtx ((x, τ) :: Γ✝) →
      --         (∀ j ∉ st₀.ctxDeps ((x, τ) :: Γ✝), InsensitiveTo ρ j) →
      --           let x_1 := B.fintypePlayer;
      --           let st := MAIDCompileState.ofProg B k hl ha hd ρ st₀;
      --           let data := compiledFDistData st σ ⋯;
      --           ∀ (a₀ : TAssign st.toStruct),
      --             FDist.map (fun a ↦ extractOutcome B k ρ st₀.nextId (rawOfTAssign st a))
      --                 (List.foldl (evalStepFDist data) (FDist.pure a₀) (List.drop st₀.nextId (List.finRange st.nextId))) =
      --               nativeOutcomeDist B σ k ρ st₀.nextId (rawOfTAssign st a₀)
      -- hl✝ : Legal (Prog.sample x τ m D' k)
      -- ha✝ : DistinctActs (Prog.sample x τ m D' k)
      -- hd✝ : NormalizedDists (Prog.sample x τ m D' k)
      -- hwf✝ : WF (Prog.sample x τ m D' k)
      -- hσ_norm : σ.NormalizedOn (Prog.sample x τ m D' k)
      -- ρ : RawNodeEnv L → VisEnv L Γ✝
      -- st₀ : MAIDCompileState Player L B
      -- hst₀ : st₀.KernelNormalized σ
      -- hvars : st₀.VarsSubCtx Γ✝
      -- hρ_deps : ∀ j ∉ st₀.ctxDeps Γ✝, InsensitiveTo ρ j
      -- hl : Fintype Player := B.fintypePlayer
      -- ha : MAIDCompileState Player L B := MAIDCompileState.ofProg B (Prog.sample x τ m D' k) hl✝ ha✝ hd✝ ρ st₀
      -- hd : FDistNodeData ha.toStruct := compiledFDistData ha σ ⋯
      -- hwf : TAssign ha.toStruct
      -- ⊢ FDist.map (fun a ↦ extractOutcome B (Prog.sample x τ m D' k) ρ st₀.nextId (rawOfTAssign ha a))
      --     (List.foldl (evalStepFDist hd) (FDist.pure hwf) (List.drop st₀.nextId (List.finRange ha.nextId))) =
      --   nativeOutcomeDist B σ (Prog.sample x τ m D' k) ρ st₀.nextId (rawOfTAssign ha hwf)
      sorry
  | commit x who acts R k ih =>
      dsimp
      intro a₀
      -- Player : Type
      -- inst✝ : DecidableEq Player
      -- L : ExprLanguage
      -- E : VisExprKit Player L
      -- D : VisDistKit Player L
      -- U : VisPayoffKit Player L
      -- B : MAIDBackend Player L
      -- Γ : VisCtx Player L
      -- σ : Profile Player L
      -- this : Fintype Player := B.fintypePlayer
      -- Γ✝ : VisCtx Player L
      -- x : VarId
      -- who : Player
      -- b✝ : L.Ty
      -- acts : List (L.Val b✝)
      -- R : VisExprKit.Expr ((x, VisBindTy.pub b✝) :: flattenCtx (viewCtx who Γ✝)) L.bool
      -- k : Prog Player L ((x, VisBindTy.hidden who b✝) :: Γ✝)
      -- ih : ∀ (hl : Legal k) (ha : DistinctActs k) (hd : NormalizedDists k),
      --   WF k →
      --     ∀ (hσ_norm : σ.NormalizedOn k) (ρ : RawNodeEnv L → VisEnv L ((x, VisBindTy.hidden who b✝) :: Γ✝))
      --       (st₀ : MAIDCompileState Player L B) (hst₀ : st₀.KernelNormalized σ),
      --       st₀.VarsSubCtx ((x, VisBindTy.hidden who b✝) :: Γ✝) →
      --         (∀ j ∉ st₀.ctxDeps ((x, VisBindTy.hidden who b✝) :: Γ✝), InsensitiveTo ρ j) →
      --           let x_1 := B.fintypePlayer;
      --           let st := MAIDCompileState.ofProg B k hl ha hd ρ st₀;
      --           let data := compiledFDistData st σ ⋯;
      --           ∀ (a₀ : TAssign st.toStruct),
      --             FDist.map (fun a ↦ extractOutcome B k ρ st₀.nextId (rawOfTAssign st a))
      --                 (List.foldl (evalStepFDist data) (FDist.pure a₀) (List.drop st₀.nextId (List.finRange st.nextId))) =
      --               nativeOutcomeDist B σ k ρ st₀.nextId (rawOfTAssign st a₀)
      -- hl✝ : Legal (Prog.commit x who acts R k)
      -- ha✝ : DistinctActs (Prog.commit x who acts R k)
      -- hd✝ : NormalizedDists (Prog.commit x who acts R k)
      -- hwf✝ : WF (Prog.commit x who acts R k)
      -- hσ_norm : σ.NormalizedOn (Prog.commit x who acts R k)
      -- ρ : RawNodeEnv L → VisEnv L Γ✝
      -- st₀ : MAIDCompileState Player L B
      -- hst₀ : st₀.KernelNormalized σ
      -- hvars : st₀.VarsSubCtx Γ✝
      -- hρ_deps : ∀ j ∉ st₀.ctxDeps Γ✝, InsensitiveTo ρ j
      -- hl : Fintype Player := B.fintypePlayer
      -- ha : MAIDCompileState Player L B := MAIDCompileState.ofProg B (Prog.commit x who acts R k) hl✝ ha✝ hd✝ ρ st₀
      -- hd : FDistNodeData ha.toStruct := compiledFDistData ha σ ⋯
      -- hwf : TAssign ha.toStruct
      -- ⊢ FDist.map (fun a ↦ extractOutcome B (Prog.commit x who acts R k) ρ st₀.nextId (rawOfTAssign ha a))
      --     (List.foldl (evalStepFDist hd) (FDist.pure hwf) (List.drop st₀.nextId (List.finRange ha.nextId))) =
      --   nativeOutcomeDist B σ (Prog.commit x who acts R k) ρ st₀.nextId (rawOfTAssign ha hwf)
      sorry
  | reveal y who x hx k ih =>
      dsimp
      intro a₀
      -- Player : Type
      -- inst✝ : DecidableEq Player
      -- L : ExprLanguage
      -- E : VisExprKit Player L
      -- D : VisDistKit Player L
      -- U : VisPayoffKit Player L
      -- B : MAIDBackend Player L
      -- Γ : VisCtx Player L
      -- σ : Profile Player L
      -- this : Fintype Player := B.fintypePlayer
      -- Γ✝ : VisCtx Player L
      -- y : VarId
      -- who : Player
      -- x : VarId
      -- b✝ : L.Ty
      -- hx : VisHasVar Γ✝ x (VisBindTy.hidden who b✝)
      -- k : Prog Player L ((y, VisBindTy.pub b✝) :: Γ✝)
      -- ih : ∀ (hl : Legal k) (ha : DistinctActs k) (hd : NormalizedDists k),
      --   WF k →
      --     ∀ (hσ_norm : σ.NormalizedOn k) (ρ : RawNodeEnv L → VisEnv L ((y, VisBindTy.pub b✝) :: Γ✝))
      --       (st₀ : MAIDCompileState Player L B) (hst₀ : st₀.KernelNormalized σ),
      --       st₀.VarsSubCtx ((y, VisBindTy.pub b✝) :: Γ✝) →
      --         (∀ j ∉ st₀.ctxDeps ((y, VisBindTy.pub b✝) :: Γ✝), InsensitiveTo ρ j) →
      --           let x := B.fintypePlayer;
      --           let st := MAIDCompileState.ofProg B k hl ha hd ρ st₀;
      --           let data := compiledFDistData st σ ⋯;
      --           ∀ (a₀ : TAssign st.toStruct),
      --             FDist.map (fun a ↦ extractOutcome B k ρ st₀.nextId (rawOfTAssign st a))
      --                 (List.foldl (evalStepFDist data) (FDist.pure a₀) (List.drop st₀.nextId (List.finRange st.nextId))) =
      --               nativeOutcomeDist B σ k ρ st₀.nextId (rawOfTAssign st a₀)
      -- hl✝ : Legal (Prog.reveal y who x hx k)
      -- ha✝ : DistinctActs (Prog.reveal y who x hx k)
      -- hd✝ : NormalizedDists (Prog.reveal y who x hx k)
      -- hwf✝ : WF (Prog.reveal y who x hx k)
      -- hσ_norm : σ.NormalizedOn (Prog.reveal y who x hx k)
      -- ρ : RawNodeEnv L → VisEnv L Γ✝
      -- st₀ : MAIDCompileState Player L B
      -- hst₀ : st₀.KernelNormalized σ
      -- hvars : st₀.VarsSubCtx Γ✝
      -- hρ_deps : ∀ j ∉ st₀.ctxDeps Γ✝, InsensitiveTo ρ j
      -- hl : Fintype Player := B.fintypePlayer
      -- ha : MAIDCompileState Player L B := MAIDCompileState.ofProg B (Prog.reveal y who x hx k) hl✝ ha✝ hd✝ ρ st₀
      -- hd : FDistNodeData ha.toStruct := compiledFDistData ha σ ⋯
      -- hwf : TAssign ha.toStruct
      -- ⊢ FDist.map (fun a ↦ extractOutcome B (Prog.reveal y who x hx k) ρ st₀.nextId (rawOfTAssign ha a))
      --     (List.foldl (evalStepFDist hd) (FDist.pure hwf) (List.drop st₀.nextId (List.finRange ha.nextId))) =
      --   nativeOutcomeDist B σ (Prog.reveal y who x hx k) ρ st₀.nextId (rawOfTAssign ha hwf)
      sorry

-- Bridge lemma


open MAID in
/-- **Bridge lemma.** Mapping `extractOutcome` over the MAID assignment
distribution yields the Vegas outcome distribution. -/
theorem maid_map_extract_eq_outcomeDist
    (B : MAIDBackend Player L)
    {Γ : VisCtx Player L}
    (p : Prog Player L Γ)
    (env : VisEnv (Player := Player) L Γ)
    (σ : Profile (Player := Player) (L := L))
    (hl : Legal p) (ha : DistinctActs p)
    (hd : _root_.NormalizedDists p)
    (hwf : WF p)
    (hσ_norm : σ.NormalizedOn p) :
    let _ : Fintype Player := B.fintypePlayer
    let st := MAIDCompileState.ofProg B p hl ha hd (fun _ => env) .empty
    let S := st.toStruct
    let sem := MAIDCompileState.toSem st
    let hkn := ofProg_kernelNormalized B p σ hl ha hd hσ_norm
        (fun _ => env) .empty (MAIDCompileState.empty_kernelNormalized σ)
    let pol := compiledPolicy st σ hkn
    let extract : @TAssign Player _ B.fintypePlayer st.nextId S → U.Outcome :=
      fun a => extractOutcome B p (fun _ => env) 0 (rawOfTAssign st a)
    PMF.map extract (evalAssignDist S sem pol) =
      (outcomeDist σ p env).toPMF (outcomeDist_totalWeight_eq_one hd hσ_norm) := by
  intro _inst st S sem hkn pol extract
  -- Step 1: evalAssignDist = evalFold along the natural order
  let hnat := compiled_naturalOrder st
  let σ_topo := hnat.toTopologicalOrder
  rw [evalAssignDist_eq_evalFold S sem pol σ_topo]
  -- Step 2: evalFold = toPMF (evalFoldFDist)
  let data := compiledFDistData st σ hkn
  let hcompat := compiledFDistData_compatible st σ hkn
  rw [← evalFoldFDist_toPMF_eq_evalFold data sem pol hcompat σ_topo]
  -- Step 3: PMF.map extract (toPMF d) → toPMF (FDist.map extract d)
  have hfold_norm := evalFoldFDist_normalized data σ_topo
  have hmap_norm : (FDist.map extract (evalFoldFDist data σ_topo)).totalWeight = 1 := by
    rw [FDist.totalWeight_map]; exact hfold_norm
  rw [← FDist.toPMF_map (evalFoldFDist data σ_topo) extract hfold_norm hmap_norm]
  -- Step 4+5: FDist.map extract (evalFoldFDist) = nativeOutcomeDist = outcomeDist
  apply FDist.toPMF_congr
  -- evalFoldFDist data σ_topo = σ_topo.order.foldl ... = (List.finRange st.nextId).foldl ...
  -- Since st₀ = .empty, st₀.nextId = 0, drop 0 is trivial
  -- Apply foldFDist_map_extract_eq_nativeOutcomeDist then nativeOutcomeDist_eq_outcomeDist_init
  have key := foldFDist_map_extract_eq_nativeOutcomeDist B p σ hl ha hd
    hwf hσ_norm
    (fun _ => env) .empty (MAIDCompileState.empty_kernelNormalized σ)
    (by
      intro x hx
      simp [MAIDCompileState.empty] at hx)
    (fun _ _ _ _ => rfl) (defaultAssign st.toStruct)
  have : (MAIDCompileState.empty (B := B) (Player := Player)
    (L := L)).nextId = 0 := rfl
  rw [this, List.drop_zero] at key
  change FDist.map extract (σ_topo.order.foldl (evalStepFDist data)
    (FDist.pure (defaultAssign st.toStruct))) = _
  change FDist.map extract ((List.finRange st.nextId).foldl
    (evalStepFDist data) (FDist.pure (defaultAssign st.toStruct))) = _
  exact key.trans (nativeOutcomeDist_eq_outcomeDist_init B p σ env _)

-- Main theorem


open MAID in
/-- **B2: Vegas to MAID distribution equality.**
There exist a MAID policy and extraction function such that the MAID's
outcome marginal equals the Vegas semantics. Uses order-free `evalAssignDist`. -/
theorem vegas_maid_dist_eq
    (B : MAIDBackend Player L)
    {Γ : VisCtx Player L}
    (p : Prog Player L Γ)
    (env : VisEnv (Player := Player) L Γ)
    (σ : Profile (Player := Player) (L := L))
    (hl : Legal p) (ha : DistinctActs p)
    (hd : _root_.NormalizedDists p)
    (hwf : WF p)
    (hσ_norm : σ.NormalizedOn p) :
    let _ : Fintype Player := B.fintypePlayer
    let st := MAIDCompileState.ofProg B p hl ha hd (fun _ => env) .empty
    let S := st.toStruct
    let sem := MAIDCompileState.toSem st
    ∃ (pol : @Policy Player _ B.fintypePlayer st.nextId S)
      (extract : @TAssign Player _ B.fintypePlayer st.nextId S → U.Outcome),
      PMF.map extract (evalAssignDist S sem pol) =
        (outcomeDist σ p env).toPMF (outcomeDist_totalWeight_eq_one hd hσ_norm) := by
  let _ := B.fintypePlayer
  let st := MAIDCompileState.ofProg B p hl ha hd (fun _ => env) .empty
  let hkn := ofProg_kernelNormalized B p σ hl ha hd hσ_norm
      (fun _ => env) .empty (MAIDCompileState.empty_kernelNormalized σ)
  let pol := compiledPolicy st σ hkn
  let extract : @TAssign Player _ B.fintypePlayer st.nextId st.toStruct → U.Outcome :=
    fun a => extractOutcome B p (fun _ => env) 0 (rawOfTAssign st a)
  exact ⟨pol, extract,
    maid_map_extract_eq_outcomeDist B p env σ hl ha hd hwf hσ_norm⟩

end Distilled
