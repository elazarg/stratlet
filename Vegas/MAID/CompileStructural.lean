import Vegas.MAID.Compile

/-!
# Structural lemmas for MAIDCompileState

Lemmas about `lookupDeps`, `depsOfVars`, `ctxDeps`, `addNode`, `addVar`, and
`VarsSubCtx` — extracted from `Correctness.lean` so that downstream files
(e.g. `CompileV.lean`) can import lightweight structural facts without pulling
in the full correctness proof.
-/

namespace Vegas

open MAID

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {B : MAIDBackend Player L}

-- ────────────────────────────────────────────────
-- lookupDepsAux helper lemmas (no DecidableEq Player needed)
-- ────────────────────────────────────────────────

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

-- ────────────────────────────────────────────────
-- lookupDeps under addVar / addNode
-- ────────────────────────────────────────────────

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

-- ────────────────────────────────────────────────
-- depsOfVars under addVar
-- ────────────────────────────────────────────────

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

theorem MAIDCompileState.depsOfVars_addVar_eq_of_not_mem
    (st : MAIDCompileState Player L B)
    (x : VarId) (τ : BindTy Player L) (deps : Finset Nat)
    (hdeps : ∀ d ∈ deps, d < st.nextId) (ys : List VarId) (hx : x ∉ ys) :
    (st.addVar x τ deps hdeps).depsOfVars ys = st.depsOfVars ys := by
  induction ys with
  | nil => simp [depsOfVars]
  | cons y ys ih =>
    simp only [depsOfVars]
    have hne : y ≠ x := fun heq => hx (heq ▸ .head _)
    rw [st.lookupDeps_addVar_eq_of_ne x τ deps hdeps hne,
      ih (fun hmem => hx (List.mem_cons_of_mem _ hmem))]

-- ────────────────────────────────────────────────
-- ctxDeps under addVar / addNode
-- ────────────────────────────────────────────────

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

-- ────────────────────────────────────────────────
-- lookupDeps / depsOfVars subset lemmas
-- ────────────────────────────────────────────────

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

theorem MAIDCompileState.depsOfVars_subset_of_subset
    (st : MAIDCompileState Player L B)
    (as bs : List VarId)
    (h : ∀ x, x ∈ as → x ∈ bs) :
    st.depsOfVars as ⊆ st.depsOfVars bs := by
  induction as with
  | nil =>
      exact Finset.empty_subset _
  | cons a as' ih =>
      change st.lookupDeps a ∪ st.depsOfVars as' ⊆ st.depsOfVars bs
      apply Finset.union_subset
      · exact st.lookupDeps_subset_depsOfVars_of_mem (h a (by simp))
      · exact ih (fun z hz => h z (by simp [hz]))

-- ────────────────────────────────────────────────
-- viewDeps / pubCtxDeps subset lemmas
-- ────────────────────────────────────────────────

theorem MAIDCompileState.viewDeps_sub_ctxDeps
    (st : MAIDCompileState Player L B) (who : Player) (Γ : VCtx Player L) :
    st.viewDeps who Γ ⊆ st.ctxDeps Γ := by
  unfold MAIDCompileState.viewDeps MAIDCompileState.ctxDeps
  exact st.depsOfVars_subset_of_subset _ _ (fun x hx => viewVCtx_map_fst_sub hx)

omit [DecidableEq Player] in
private theorem erasePubVCtx_map_fst_sub (Γ : VCtx Player L) :
    ∀ x, x ∈ (erasePubVCtx Γ).map Prod.fst → x ∈ Γ.map Prod.fst := by
  induction Γ with
  | nil => simp [erasePubVCtx]
  | cons a Γ' ih =>
    intro x hx
    match a with
    | (y, .pub b) =>
      simp only [erasePubVCtx_cons_pub, List.map_cons, List.mem_cons] at hx ⊢
      exact hx.elim .inl (fun h => .inr (ih x h))
    | (y, .hidden p b) =>
      simp only [erasePubVCtx_cons_hidden, List.map_cons, List.mem_cons] at hx ⊢
      exact .inr (ih x hx)

theorem MAIDCompileState.pubCtxDeps_sub_ctxDeps
    (st : MAIDCompileState Player L B) (Γ : VCtx Player L) :
    st.pubCtxDeps Γ ⊆ st.ctxDeps Γ := by
  unfold MAIDCompileState.pubCtxDeps MAIDCompileState.ctxDeps
  exact st.depsOfVars_subset_of_subset _ _ (erasePubVCtx_map_fst_sub Γ)

-- ────────────────────────────────────────────────
-- Compound ctxDeps step lemmas
-- ────────────────────────────────────────────────

theorem MAIDCompileState.ctxDeps_letExpr_step
    (st : MAIDCompileState Player L B)
    {Γ : VCtx Player L} (x : VarId) {b : L.Ty}
    (hfreshΓ : Fresh x Γ)
    (hfreshVars : x ∉ st.vars.map Prod.fst) :
    (st.addVar x (.pub b) (st.pubCtxDeps Γ) (st.depsOfVars_lt _)).ctxDeps
      ((x, .pub b) :: Γ) = st.ctxDeps Γ := by
  rw [st.ctxDeps_addVar_cons_eq_of_fresh x (.pub b) (st.pubCtxDeps Γ)
    (st.depsOfVars_lt _) hfreshΓ hfreshVars]
  exact Finset.union_eq_right.mpr (st.pubCtxDeps_sub_ctxDeps Γ)

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

-- ────────────────────────────────────────────────
-- VarsSubCtx definition and lemmas
-- ────────────────────────────────────────────────

def MAIDCompileState.VarsSubCtx
    (st : MAIDCompileState Player L B) (Γ : VCtx Player L) : Prop :=
  ∀ x, x ∈ st.vars.map Prod.fst → x ∈ Γ.map Prod.fst

theorem MAIDCompileState.VarsSubCtx_addNode
    (st : MAIDCompileState Player L B) {Γ : VCtx Player L}
    (hvars : st.VarsSubCtx Γ) (nd : CompiledNode Player L B)
    (hdeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId) :
    (st.addNode nd hdeps).2.VarsSubCtx Γ := by
  intro x
  simpa [VarsSubCtx, addNode] using hvars x

theorem MAIDCompileState.VarsSubCtx_addVar
    (st : MAIDCompileState Player L B) {Γ : VCtx Player L}
    (hvars : st.VarsSubCtx Γ) (x : VarId) (τ : BindTy Player L)
    (deps : Finset Nat) (hdeps : ∀ d ∈ deps, d < st.nextId)
    (hfresh : Fresh x Γ) :
    (st.addVar x τ deps hdeps).VarsSubCtx ((x, τ) :: Γ) := by
  intro y hy
  have hy' : y ∈ st.vars.map Prod.fst ∨ y = x := by
    simpa [addVar, List.map_append] using hy
  simp only [List.map_cons, List.mem_cons, List.mem_map, Prod.exists, exists_and_right,
    exists_eq_right]
  rcases hy' with hy' | rfl
  · exact Or.inr (by simpa [List.mem_map] using hvars y hy')
  · exact Or.inl rfl

theorem MAIDCompileState.VarsSubCtx_letExpr_step
    (st : MAIDCompileState Player L B)
    {Γ : VCtx Player L}
    (hvars : st.VarsSubCtx Γ)
    (x : VarId) {b : L.Ty}
    (hfreshΓ : Fresh x Γ) :
    (st.addVar x (.pub b) (st.pubCtxDeps Γ) (st.depsOfVars_lt _)).VarsSubCtx
      ((x, .pub b) :: Γ) := by
  exact st.VarsSubCtx_addVar hvars x (.pub b) (st.pubCtxDeps Γ)
    (st.depsOfVars_lt _) hfreshΓ

theorem MAIDCompileState.VarsSubCtx_addNode_addVar_singleton_step
    (st : MAIDCompileState Player L B) {Γ : VCtx Player L}
    (hvars : st.VarsSubCtx Γ) (nd : CompiledNode Player L B)
    (hndeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId)
    (x : VarId) (τ : BindTy Player L) (hfreshΓ : Fresh x Γ) :
    (((st.addNode nd hndeps).2).addVar x τ {st.nextId}
      (by
        intro d hd
        simp_all only [Finset.mem_singleton]
        exact Nat.lt_add_one st.nextId)).VarsSubCtx ((x, τ) :: Γ) := by
  exact ((st.addNode nd hndeps).2).VarsSubCtx_addVar
    (st.VarsSubCtx_addNode hvars nd hndeps) x τ _ _ hfreshΓ

/-! ## ofProg monotonicity and preservation -/

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

/-- All nodes added by `addUtilityNodes` are utility nodes. -/
theorem MAIDCompileState.addUtilityNodes_all_utility
    (st : MAIDCompileState Player L B)
    (deps : Finset Nat) (hdeps : ∀ d ∈ deps, d < st.nextId)
    (ufn : Player → RawNodeEnv L → ℝ) (players : List Player)
    (i : Fin (st.addUtilityNodes deps hdeps ufn players).nextId)
    (hi : st.nextId ≤ i.val) :
    ∃ who, ((st.addUtilityNodes deps hdeps ufn players).descAt i).kind =
      NodeKind.utility who := by
  induction players generalizing st with
  | nil =>
    simp only [MAIDCompileState.addUtilityNodes] at i ⊢
    exact absurd i.isLt (by omega)
  | cons who rest ih =>
    simp only [MAIDCompileState.addUtilityNodes] at i ⊢
    by_cases heq : i.val = st.nextId
    · have hutdeps : ∀ d ∈ (CompiledNode.utility (B := B) who deps
          (ufn who)).parents ∪
          (CompiledNode.utility (B := B) who deps
            (ufn who)).obsParents, d < st.nextId := by
        intro d hd'
        rcases Finset.mem_union.mp hd' with h | h <;>
          simpa [CompiledNode.parents, CompiledNode.obsParents]
            using hdeps d h
      have hj_lt : i.val <
          (st.addNode (.utility who deps (ufn who))
            hutdeps).2.nextId := by
        simp [MAIDCompileState.addNode]; omega
      have hdesc :
          ((st.addNode (.utility who deps (ufn who))
            hutdeps).2.addUtilityNodes deps _ ufn rest).descAt
            ⟨i.val, i.isLt⟩ =
          .utility who deps (ufn who) := by
        rw [addUtilityNodes_descAt_old _ _ _ _ rest i.val hj_lt]
        rw [show (⟨i.val, hj_lt⟩ : Fin _) =
          ⟨st.nextId, Nat.lt_succ_self _⟩ from Fin.ext heq]
        exact st.addNode_descAt_new _ _
      exact ⟨who, by
        rw [show i = ⟨i.val, i.isLt⟩ from Fin.ext rfl]
        simp only [hdesc]; rfl⟩
    · have hutdeps : ∀ d ∈ (CompiledNode.utility (B := B) who deps
          (ufn who)).parents ∪
          (CompiledNode.utility (B := B) who deps
            (ufn who)).obsParents, d < st.nextId := by
        intro d hd'
        rcases Finset.mem_union.mp hd' with h | h <;>
          simpa [CompiledNode.parents, CompiledNode.obsParents]
            using hdeps d h
      exact ih (st.addNode (.utility who deps (ufn who))
        hutdeps).2 _ ⟨i.val, i.isLt⟩
        (by simp [MAIDCompileState.addNode]; omega)

/-- `ofProg` only increases `nextId`. -/
theorem MAIDCompileState.ofProg_nextId_le
    (B : MAIDBackend Player L) {Γ : VCtx Player L}
    (p : VegasCore Player L Γ) (hl hd)
    (ρ : RawNodeEnv L → VEnv L Γ)
    (st₀ : MAIDCompileState Player L B) :
    st₀.nextId ≤
      (MAIDCompileState.ofProg B p hl hd ρ st₀).nextId := by
  induction p generalizing st₀ with
  | ret u =>
    letI := B.fintypePlayer; simp only [MAIDCompileState.ofProg]
    rw [MAIDCompileState.addUtilityNodes_nextId]; omega
  | letExpr x e k ih =>
    exact ih hl hd
      (fun raw => VEnv.cons (L.eval e
        (VEnv.erasePubEnv (ρ raw))) (ρ raw))
      (st₀.addVar _ _ _ _)
  | sample x τ m D' k ih =>
    refine le_trans (Nat.le_succ _) ?_
    exact ih hl hd.2
      (fun raw => VEnv.cons
        (MAIDCompileState.readVal (B := B) raw τ.base
          st₀.nextId) (ρ raw))
      ((st₀.addNode _ _).2.addVar _ _ _ _)
  | commit x who R k ih =>
    rename_i Γ' b
    refine le_trans (Nat.le_succ _) ?_
    exact ih hl.2 hd
      (fun raw => VEnv.cons
        (MAIDCompileState.readVal (B := B) raw b
          st₀.nextId) (ρ raw))
      ((st₀.addNode _ _).2.addVar _ _ _ _)
  | reveal y who x hx k ih =>
    exact ih hl hd
      (fun raw =>
        let env := ρ raw
        let v : L.Val _ := VEnv.get env hx
        VEnv.cons (τ := .pub _) v env)
      (st₀.addVar _ _ _ _)

/-- `ofProg` preserves `descAt` for nodes below the initial `nextId`. -/
theorem MAIDCompileState.ofProg_descAt_old
    (B : MAIDBackend Player L) {Γ : VCtx Player L}
    (p : VegasCore Player L Γ) (hl hd)
    (ρ : RawNodeEnv L → VEnv L Γ)
    (st₀ : MAIDCompileState Player L B)
    (j : Nat) (hj : j < st₀.nextId) :
    let st := MAIDCompileState.ofProg B p hl hd ρ st₀
    (st.descAt ⟨j, Nat.lt_of_lt_of_le hj
      (ofProg_nextId_le B p hl hd ρ st₀)⟩) =
    st₀.descAt ⟨j, hj⟩ := by
  induction p generalizing st₀ with
  | ret u =>
    simp only [MAIDCompileState.ofProg]
    exact addUtilityNodes_descAt_old st₀ _ _ _ _ j hj
  | letExpr x e k ih =>
    simp only [MAIDCompileState.ofProg]
    exact ih hl hd _ (st₀.addVar _ _ _ _) hj
  | sample x τ m D' k ih =>
    change (MAIDCompileState.ofProg B k hl hd.2 _ _).descAt
      ⟨j, _⟩ = _
    rw [ih hl hd.2 _ _ (Nat.lt_succ_of_lt hj)]
    simp only [MAIDCompileState.descAt,
      MAIDCompileState.addVar, MAIDCompileState.addNode]
    congr 1
    rw [List.getElem_append_left (by
      rw [st₀.nodes_length_eq_nextId]; exact hj)]
  | commit x who R k ih =>
    change (MAIDCompileState.ofProg B k hl.2 hd _ _).descAt
      ⟨j, _⟩ = _
    rw [ih hl.2 hd _ _ (Nat.lt_succ_of_lt hj)]
    simp only [MAIDCompileState.descAt,
      MAIDCompileState.addVar, MAIDCompileState.addNode]
    congr 1
    rw [List.getElem_append_left (by
      rw [st₀.nodes_length_eq_nextId]; exact hj)]
  | reveal y who x hx k ih =>
    simp only [MAIDCompileState.ofProg]
    exact ih hl hd _ (st₀.addVar _ _ _ _) hj

-- ────────────────────────────────────────────────
-- toStruct structural lemmas
-- ────────────────────────────────────────────────

@[simp] theorem toStruct_kind (st : MAIDCompileState Player L B) (nd : Fin st.nextId) :
    st.toStruct.kind (fp := B.fintypePlayer) nd = (st.descAt nd).kind := rfl

theorem MAIDCompileState.mem_toStruct_parents_iff
    (st : MAIDCompileState Player L B)
    (nd : Fin st.nextId)
    {i : Nat} (hi : i < st.nextId) :
    (⟨i, hi⟩ : Fin st.nextId) ∈ st.toStruct.parents (fp := B.fintypePlayer) nd ↔
      i ∈ (st.descAt nd).parents := by
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
    (⟨i, hi⟩ : Fin st.nextId) ∈ st.toStruct.obsParents (fp := B.fintypePlayer) nd
       ↔ i ∈ (st.descAt nd).obsParents := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨d, hd, hEq⟩
    have hval : d.1 = i := by simpa using congrArg Fin.val hEq
    simpa [hval] using d.2
  · intro h
    refine Finset.mem_image.mpr ?_
    refine ⟨⟨i, h⟩, by simp, ?_⟩
    exact Fin.ext rfl

end Vegas
