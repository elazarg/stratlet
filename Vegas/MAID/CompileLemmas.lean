import Vegas.MAID.Compile

/-!
# Compilation lemmas

Structural lemmas about `lookupDeps`, `depsOfVars`, `ctxDeps`, `addNode`, `addVar`,
`VarsSubCtx`, and reveal-time tracking (`RevealConsistent`, `VarVisible`,
`computeReveals_consistent`, `computeReveals_parents_visible`, `compileVegasMAID`).
-/

namespace Vegas

open MAID

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
variable {B : MAIDBackend Player L}

-- ────────────────────────────────────────────────
-- lookupDepsAux helper lemmas (no DecidableEq Player needed)
-- ────────────────────────────────────────────────

section
omit [DecidableEq Player] [Fintype Player]

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
-- depsOfVars under addNode / addVar
-- ────────────────────────────────────────────────

@[simp] theorem MAIDCompileState.depsOfVars_addNode_eq
    (st : MAIDCompileState Player L B) (nd : CompiledNode Player L B)
    (hdeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId)
    (xs : List VarId) :
    (st.addNode nd hdeps).2.depsOfVars xs = st.depsOfVars xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp only [depsOfVars, addNode, lookupDeps]; congr 1

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

omit [DecidableEq Player] [Fintype Player] in
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
    simp only [MAIDCompileState.ofProg]
    rw [MAIDCompileState.addUtilityNodes_nextId]; omega
  | letExpr x e k ih =>
    exact ih hl hd
      (fun raw => VEnv.cons (L.eval e
        (VEnv.erasePubEnv (ρ raw))) (ρ raw))
      (st₀.addVar _ _ _ _)
  | sample x D' k ih =>
    rename_i Γ' b
    refine le_trans (Nat.le_succ _) ?_
    exact ih hl hd.2
      (fun raw => VEnv.cons
        (MAIDCompileState.readVal (B := B) raw b
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
  | sample x D' k ih =>
    change (MAIDCompileState.ofProg B k hl hd.2 _ _).descAt
      ⟨j, _⟩ = _
    rw [ih hl hd.2 _ _ (Nat.lt_succ_of_lt hj)]
    simp [MAIDCompileState.addVar, MAIDCompileState.addNode, hj]
  | commit x who R k ih =>
    change (MAIDCompileState.ofProg B k hl.2 hd _ _).descAt
      ⟨j, _⟩ = _
    rw [ih hl.2 hd _ _ (Nat.lt_succ_of_lt hj)]
    simp [MAIDCompileState.addVar, MAIDCompileState.addNode, hj]
  | reveal y who x hx k ih =>
    simp only [MAIDCompileState.ofProg]
    exact ih hl hd _ (st₀.addVar _ _ _ _) hj

-- ────────────────────────────────────────────────
-- toStruct structural lemmas
-- ────────────────────────────────────────────────

@[simp] theorem toStruct_kind (st : MAIDCompileState Player L B) (nd : Fin st.nextId) :
    st.toStruct.kind nd = (st.descAt nd).kind := rfl

theorem MAIDCompileState.mem_toStruct_parents_iff
    (st : MAIDCompileState Player L B)
    (nd : Fin st.nextId)
    {i : Nat} (hi : i < st.nextId) :
    (⟨i, hi⟩ : Fin st.nextId) ∈ st.toStruct.parents nd ↔
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
    (⟨i, hi⟩ : Fin st.nextId) ∈ st.toStruct.obsParents nd
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


/-! ## Reveal-time lemmas -/

/-- `addPublicNode` foldl advances `nextId` by the list length. -/
private theorem foldl_addPublicNode_nextId (rs : RevealState) (xs : List α) :
    (xs.foldl (fun rs' _ => rs'.addPublicNode) rs).nextId = rs.nextId + xs.length := by
  induction xs generalizing rs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [ih rs.addPublicNode]
      simp [RevealState.addPublicNode]; omega

/-- `addUtilityNodes` advances `nextId` by the list length. -/
private theorem addUtilityNodes_nextId {B : MAIDBackend Player L}
    (st : MAIDCompileState Player L B)
    (deps : Finset Nat) (hdeps : ∀ d ∈ deps, d < st.nextId)
    (ufn : Player → RawNodeEnv L → ℝ) (xs : List Player) :
    (st.addUtilityNodes deps hdeps ufn xs).nextId = st.nextId + xs.length := by
  induction xs generalizing st with
  | nil => simp [MAIDCompileState.addUtilityNodes]
  | cons x xs ih =>
      simp only [MAIDCompileState.addUtilityNodes, List.length_cons]
      rw [ih]
      simp [MAIDCompileState.addNode, Nat.add_assoc, Nat.add_comm 1]

/-- The reveal state's `nextId` matches the compiler's `nextId`.
    (Both walk the same program structure.) -/
theorem computeReveals_nextId_eq (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ) (hl : Legal p) (hd : NormalizedDists p)
    (ρ : RawNodeEnv L → VEnv (Player := Player) L Γ)
    (st : MAIDCompileState Player L B) (rs : RevealState)
    (hsync : rs.nextId = st.nextId) :
    (computeReveals B p rs).nextId =
      (MAIDCompileState.ofProg B p hl hd ρ st).nextId := by
  induction p generalizing st rs with
  | ret payoffs =>
      simp only [computeReveals, MAIDCompileState.ofProg]
      rw [foldl_addPublicNode_nextId, addUtilityNodes_nextId, hsync]
  | letExpr x e k ih => exact ih hl hd _ _ _ hsync
  | sample x D' k ih =>
      simp only [computeReveals, MAIDCompileState.ofProg]
      apply ih (hd := hd.2)
      simp [RevealState.addPublicNode, RevealState.bindVar,
            MAIDCompileState.addNode, MAIDCompileState.addVar, hsync]
  | commit x who R k ih =>
      simp only [computeReveals, MAIDCompileState.ofProg]
      apply ih (hd := hd)
      simp [RevealState.addPrivateNode, RevealState.bindVar,
            MAIDCompileState.addNode, MAIDCompileState.addVar, hsync]
  | reveal y who x hx k ih =>
      simp only [computeReveals, MAIDCompileState.ofProg]
      apply ih (hd := hd)
      cases rs.nodeOf x <;>
        simp [RevealState.aliasVar, MAIDCompileState.addVar, hsync]


/-! ## revealTime monotonicity -/

/-- `computeReveals` never increases `revealTime` at indices < nextId.
    (At index nextId, addPublicNode sets it to ↑nextId which is ≤ ⊤ = unset.) -/
theorem computeReveals_revealTime_le (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ)
    (rs : RevealState) (i : Nat) (hi : i < rs.nextId) :
    (computeReveals B p rs).revealTime i ≤ rs.revealTime i := by
  induction p generalizing rs with
  | ret =>
      simp only [computeReveals]
      generalize (Finset.univ (α := Player)).toList = players
      induction players generalizing rs with
      | nil => simp
      | cons _ rest ih =>
          simp only [List.foldl_cons]
          exact le_trans (ih _ (by simp [RevealState.addPublicNode]; omega)) (by
            simp only [RevealState.addPublicNode]
            rw [if_neg (show i ≠ rs.nextId from by omega)])
  | letExpr _ _ k ih => exact ih rs hi
  | sample x _ k ih =>
      simp only [computeReveals]
      exact le_trans (ih _ (by simp [RevealState.addPublicNode, RevealState.bindVar]; omega)) (by
        simp only [RevealState.addPublicNode, RevealState.bindVar]
        rw [if_neg (show i ≠ rs.nextId from by omega)])
  | commit x _ _ k ih =>
      simp only [computeReveals]
      exact le_trans (ih _ (by simp [RevealState.addPrivateNode, RevealState.bindVar]; omega)) (by
        simp [RevealState.addPrivateNode, RevealState.bindVar])
  | reveal y _ x _ k ih =>
      simp only [computeReveals]
      exact le_trans (ih _ (by
        simp only [RevealState.aliasVar]
        cases rs.nodeOf x <;> simp [hi])) (by
        simp only [RevealState.aliasVar]
        cases rs.nodeOf x with
        | none => exact le_refl _
        | some nid =>
            simp only
            by_cases h : i = nid
            · rw [if_pos h]; exact min_le_right _ _
            · rw [if_neg h])

/-! ## Reusable lemmas for addNode consistency -/

/-- RevealConsistent preserved by addNode (non-decision) + addPublicNode only. -/
private theorem revealConsistent_addNode'
    {st : MAIDCompileState Player L B} {rs : RevealState}
    (hcon : RevealConsistent st rs)
    (nd : CompiledNode Player L B) (hkind : ¬ ∃ p, nd.kind = .decision p)
    (hnd : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId) :
    RevealConsistent (st.addNode nd hnd).2 rs.addPublicNode where
  sync := by simp [RevealState.addPublicNode, MAIDCompileState.addNode, hcon.sync]
  chance := by
    intro nd' hk
    have hbound : nd'.val ≤ st.nextId := by
      have := nd'.isLt; simp [MAIDCompileState.addNode] at this; omega
    have hk_inner : ((st.addNode nd hnd).2.descAt ⟨nd'.val, by
        simp [MAIDCompileState.addNode]; omega⟩).kind = .chance := hk
    rcases Nat.lt_or_eq_of_le hbound with hlt | heq
    · rw [MAIDCompileState.addNode_descAt_old st nd hnd ⟨nd'.val, hlt⟩] at hk_inner
      simp only [RevealState.addPublicNode]
      rw [if_neg (show nd'.val ≠ rs.nextId from by rw [hcon.sync]; omega)]
      exact hcon.chance ⟨nd'.val, hlt⟩ hk_inner
    · simp only [RevealState.addPublicNode]
      rw [if_pos (show nd'.val = rs.nextId from by rw [hcon.sync]; omega)]
      simp [hcon.sync, heq]
  decision := by
    intro nd' p hk
    have hbound : nd'.val ≤ st.nextId := by
      have := nd'.isLt; simp [MAIDCompileState.addNode] at this; omega
    have hk_inner : ((st.addNode nd hnd).2.descAt ⟨nd'.val, by
        simp [MAIDCompileState.addNode]; omega⟩).kind = .decision p := hk
    rcases Nat.lt_or_eq_of_le hbound with hlt | heq
    · rw [MAIDCompileState.addNode_descAt_old st nd hnd ⟨nd'.val, hlt⟩] at hk_inner
      simp only [RevealState.addPublicNode]
      rw [if_neg (show nd'.val ≠ rs.nextId from by rw [hcon.sync]; omega)]
      exact hcon.decision ⟨nd'.val, hlt⟩ p hk_inner
    · exfalso
      rw [show (⟨nd'.val, _⟩ : Fin (st.addNode nd hnd).2.nextId) =
          ⟨st.nextId, by simp [MAIDCompileState.addNode]⟩ from Fin.ext heq] at hk_inner
      rw [MAIDCompileState.addNode_descAt_new st nd hnd] at hk_inner
      exact hkind ⟨p, hk_inner⟩
  nodeOf_lt := by
    intro v nid hnid
    simp only [RevealState.addPublicNode] at hnid
    change nid < st.nextId + 1
    exact Nat.lt_trans (hcon.nodeOf_lt v nid hnid) (Nat.lt_succ_self _)
  unset := by
    intro i hi
    have hi' : st.nextId + 1 ≤ i := by simpa [MAIDCompileState.addNode] using hi
    simp only [RevealState.addPublicNode]
    rw [if_neg (show i ≠ rs.nextId from by rw [hcon.sync]; omega)]
    exact hcon.unset i (by omega)

/-- RevealConsistent preserved by addNode (non-decision) + addVar + addPublicNode + bindVar. -/
private theorem revealConsistent_addChance'
    {st : MAIDCompileState Player L B} {rs : RevealState}
    (hcon : RevealConsistent st rs)
    (nd : CompiledNode Player L B) (hkind : ¬ ∃ p, nd.kind = .decision p)
    (hnd : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId)
    (x : VarId) (τ : BindTy Player L)
    (hdeps : ∀ d ∈ ({st.nextId} : Finset Nat), d < st.nextId + 1) :
    RevealConsistent
      ((st.addNode nd hnd).2.addVar x τ {st.nextId} hdeps)
      (rs.addPublicNode.bindVar x rs.nextId) := by
  have hnid1 : ((st.addNode nd hnd).2.addVar x τ {st.nextId} hdeps).nextId
      = st.nextId + 1 := by simp [MAIDCompileState.addNode, MAIDCompileState.addVar]
  exact {
    sync := by simp [RevealState.addPublicNode, RevealState.bindVar, hnid1, hcon.sync]
    chance := by
      intro nd' hk
      have hbound : nd'.val ≤ st.nextId := by rw [hnid1] at nd'; omega
      have hk_inner : ((st.addNode nd hnd).2.descAt ⟨nd'.val, by
          simp [MAIDCompileState.addNode]; omega⟩).kind = .chance := hk
      rcases Nat.lt_or_eq_of_le hbound with hlt | heq
      · rw [MAIDCompileState.addNode_descAt_old st nd hnd ⟨nd'.val, hlt⟩] at hk_inner
        simp only [RevealState.addPublicNode, RevealState.bindVar]
        rw [if_neg (show nd'.val ≠ rs.nextId from by rw [hcon.sync]; omega)]
        exact hcon.chance ⟨nd'.val, hlt⟩ hk_inner
      · simp only [RevealState.addPublicNode, RevealState.bindVar]
        rw [if_pos (show nd'.val = rs.nextId from by rw [hcon.sync]; omega)]
        simp [hcon.sync, heq]
    decision := by
      intro nd' p hk
      have hbound : nd'.val ≤ st.nextId := by rw [hnid1] at nd'; omega
      have hk_inner : ((st.addNode nd hnd).2.descAt ⟨nd'.val, by
          simp [MAIDCompileState.addNode]; omega⟩).kind = .decision p := hk
      rcases Nat.lt_or_eq_of_le hbound with hlt | heq
      · rw [MAIDCompileState.addNode_descAt_old st nd hnd ⟨nd'.val, hlt⟩] at hk_inner
        simp only [RevealState.addPublicNode, RevealState.bindVar]
        rw [if_neg (show nd'.val ≠ rs.nextId from by rw [hcon.sync]; omega)]
        exact hcon.decision ⟨nd'.val, hlt⟩ p hk_inner
      · exfalso
        rw [show (⟨nd'.val, _⟩ : Fin (st.addNode nd hnd).2.nextId) =
            ⟨st.nextId, by simp [MAIDCompileState.addNode]⟩ from Fin.ext heq] at hk_inner
        rw [MAIDCompileState.addNode_descAt_new st nd hnd] at hk_inner
        exact hkind ⟨p, hk_inner⟩
    nodeOf_lt := by
      intro v nid hnid
      simp only [RevealState.addPublicNode, RevealState.bindVar] at hnid
      rw [hnid1]
      by_cases hv : v = x
      · subst hv; simp at hnid; have := hcon.sync; omega
      · simp only [hv, ite_false] at hnid
        exact Nat.lt_trans (hcon.nodeOf_lt v nid hnid) (Nat.lt_succ_self _)
    unset := by
      intro i hi
      simp only [RevealState.addPublicNode, RevealState.bindVar]
      rw [if_neg (show i ≠ rs.nextId from by rw [hcon.sync]; omega)]
      exact hcon.unset i (by omega) }

/-- RevealConsistent preserved by addNode(.decision) + addVar + addPrivateNode + bindVar. -/
private theorem revealConsistent_addDecision'
    {st : MAIDCompileState Player L B} {rs : RevealState}
    (hcon : RevealConsistent st rs)
    (nd : CompiledNode Player L B) {who : Player} (hkind : nd.kind = .decision who)
    (hnd : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId)
    (x : VarId) (τ : BindTy Player L)
    (hdeps : ∀ d ∈ ({st.nextId} : Finset Nat), d < st.nextId + 1) :
    RevealConsistent
      ((st.addNode nd hnd).2.addVar x τ {st.nextId} hdeps)
      (rs.addPrivateNode.bindVar x rs.nextId) := by
  have hnid1 : ((st.addNode nd hnd).2.addVar x τ {st.nextId} hdeps).nextId
      = st.nextId + 1 := by simp [MAIDCompileState.addNode, MAIDCompileState.addVar]
  exact {
    sync := by simp [RevealState.addPrivateNode, RevealState.bindVar, hnid1, hcon.sync]
    chance := by
      intro nd' hk
      have hbound : nd'.val ≤ st.nextId := by rw [hnid1] at nd'; omega
      have hk_inner : ((st.addNode nd hnd).2.descAt ⟨nd'.val, by
          simp [MAIDCompileState.addNode]; omega⟩).kind = .chance := hk
      rcases Nat.lt_or_eq_of_le hbound with hlt | heq
      · rw [MAIDCompileState.addNode_descAt_old st nd hnd ⟨nd'.val, hlt⟩] at hk_inner
        exact hcon.chance ⟨nd'.val, hlt⟩ hk_inner
      · exfalso
        rw [show (⟨nd'.val, _⟩ : Fin (st.addNode nd hnd).2.nextId) =
            ⟨st.nextId, by simp [MAIDCompileState.addNode]⟩ from Fin.ext heq] at hk_inner
        rw [MAIDCompileState.addNode_descAt_new st nd hnd, hkind] at hk_inner
        simp at hk_inner
    decision := by
      intro nd' p hk
      have hbound : nd'.val ≤ st.nextId := by rw [hnid1] at nd'; omega
      have hk_inner : ((st.addNode nd hnd).2.descAt ⟨nd'.val, by
          simp [MAIDCompileState.addNode]; omega⟩).kind = .decision p := hk
      rcases Nat.lt_or_eq_of_le hbound with hlt | heq
      · rw [MAIDCompileState.addNode_descAt_old st nd hnd ⟨nd'.val, hlt⟩] at hk_inner
        simp only [RevealState.addPrivateNode, RevealState.bindVar]
        exact hcon.decision ⟨nd'.val, hlt⟩ p hk_inner
      · simp only [RevealState.addPrivateNode, RevealState.bindVar]
        rw [hcon.unset nd'.val (by omega)]
        exact WithTop.coe_lt_top _
    nodeOf_lt := by
      intro v nid hnid
      simp only [RevealState.addPrivateNode, RevealState.bindVar] at hnid
      rw [hnid1]
      by_cases hv : v = x
      · subst hv; simp at hnid; have := hcon.sync; omega
      · simp only [hv, ite_false] at hnid
        exact Nat.lt_trans (hcon.nodeOf_lt v nid hnid) (Nat.lt_succ_self _)
    unset := by
      intro i hi
      simp only [RevealState.addPrivateNode, RevealState.bindVar]
      exact hcon.unset i (by omega) }

/-- RevealConsistent preserved by reveal (addVar + match/min on revealTime + aliasVar). -/
private theorem revealConsistent_reveal'
    {st : MAIDCompileState Player L B} {rs : RevealState}
    (hcon : RevealConsistent st rs)
    (y x : VarId) (b : L.Ty) (deps : Finset Nat)
    (hdeps : ∀ d ∈ deps, d < st.nextId) :
    RevealConsistent
      (st.addVar y (.pub b) deps hdeps)
      ((match rs.nodeOf x with
        | some nid =>
            { rs with revealTime := fun i =>
                if i = nid then min (↑rs.nextId) (rs.revealTime i) else rs.revealTime i }
        | none => rs).aliasVar y x) := by
  have hav_nid : (st.addVar y (.pub b) deps hdeps).nextId = st.nextId := rfl
  constructor
  · simp only [RevealState.aliasVar, MAIDCompileState.addVar]; split <;> simp [hcon.sync]
  · intro nd hk
    have h := hcon.chance nd hk
    simp only [RevealState.aliasVar]
    split
    · rename_i nid hx_eq; simp only; by_cases heq : nd.val = nid
      · rw [if_pos heq, h, min_eq_right]
        have h1 := hcon.nodeOf_lt x nid hx_eq
        have h2 : nd.val ≤ rs.nextId := by rw [hcon.sync]; omega
        exact WithTop.coe_le_coe.mpr h2
      · rw [if_neg heq]; exact h
    · exact h
  · intro nd p hk
    have h := hcon.decision nd p hk
    simp only [RevealState.aliasVar]
    split
    · rename_i nid hx_eq; simp only; by_cases heq : nd.val = nid
      · rw [if_pos heq]
        have h1 := hcon.nodeOf_lt x nid hx_eq
        have h2 : nd.val < rs.nextId := by rw [hcon.sync]; omega
        exact lt_min (WithTop.coe_lt_coe.mpr h2) h
      · rw [if_neg heq]; exact h
    · exact h
  · intro v nid hnid
    change nid < st.nextId
    simp only [RevealState.aliasVar] at hnid
    cases hx_eq : rs.nodeOf x with
    | none =>
        simp only [hx_eq] at hnid
        by_cases hv : v = y
        · subst hv; simp at hnid
        · simp only [hv, ite_false] at hnid; exact hcon.nodeOf_lt v nid hnid
    | some nid' =>
        simp only [hx_eq] at hnid
        by_cases hv : v = y
        · subst hv
          simp only [↓reduceIte, Option.some.injEq] at hnid
          subst hnid
          exact hcon.nodeOf_lt x nid' hx_eq
        · simp only [hv, ite_false] at hnid; exact hcon.nodeOf_lt v nid hnid
  · intro i hi
    rw [hav_nid] at hi
    simp only [RevealState.aliasVar]
    split
    · rename_i nid hx_eq; simp only
      rw [if_neg (show i ≠ nid from by have := hcon.nodeOf_lt x nid hx_eq; omega)]
      exact hcon.unset i hi
    · exact hcon.unset i hi

/-! ## Main consistency theorem -/

/-- `computeReveals` produces a state consistent with `ofProg`:
    chance nodes have revealTime = index, decision nodes have revealTime > index. -/
theorem computeReveals_consistent (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ) (hl : Legal p) (hd : NormalizedDists p)
    (ρ : RawNodeEnv L → VEnv (Player := Player) L Γ)
    (st₀ : MAIDCompileState Player L B) (rs₀ : RevealState)
    (hcon₀ : RevealConsistent st₀ rs₀) :
    RevealConsistent
      (MAIDCompileState.ofProg B p hl hd ρ st₀)
      (computeReveals B p rs₀) := by
  induction p generalizing st₀ rs₀ with
  | ret payoffs =>
      simp only [computeReveals, MAIDCompileState.ofProg]
      -- addUtilityNodes adds only utility nodes; foldl adds public nodes
      -- Induction on the player list with deps as a free parameter.
      suffices ∀ (players : List Player) (deps : Finset Nat)
          (ufn : Player → RawNodeEnv L → ℝ)
          (st : MAIDCompileState Player L B) (rs : RevealState)
          (hdeps : ∀ d ∈ deps, d < st.nextId)
          (hcon : RevealConsistent st rs),
          RevealConsistent (st.addUtilityNodes deps hdeps ufn players)
            (players.foldl (fun rs' _ => rs'.addPublicNode) rs) by
        exact this _ _ _ st₀ rs₀ _ hcon₀
      intro players
      induction players with
      | nil => intro _ _ st rs _ hcon; simpa [MAIDCompileState.addUtilityNodes]
      | cons who rest ih_ret =>
          intro deps ufn st rs hdeps hcon
          simp only [MAIDCompileState.addUtilityNodes, List.foldl_cons]
          let und : CompiledNode Player L B := .utility who deps (ufn who)
          have hund_deps : ∀ d ∈ und.parents ∪ und.obsParents, d < st.nextId := by
            intro d hd'
            simp only [CompiledNode.parents, CompiledNode.obsParents, Finset.union_idempotent,
              und] at hd'
            exact hdeps d hd'
          exact ih_ret deps ufn (st.addNode und hund_deps).2 rs.addPublicNode
            (fun d hd => Nat.lt_trans (hdeps d hd) (Nat.lt_succ_self _))
            {
              sync := by simp [RevealState.addPublicNode, MAIDCompileState.addNode, hcon.sync]
              chance := by
                intro nd' hk
                have hbound : nd'.val ≤ st.nextId := by
                  have := nd'.isLt; simp [MAIDCompileState.addNode] at this; omega
                have hk_inner : ((st.addNode und hund_deps).2.descAt ⟨nd'.val, by
                    simp [MAIDCompileState.addNode]; omega⟩).kind = .chance := hk
                rcases Nat.lt_or_eq_of_le hbound with hlt | heq
                · rw [MAIDCompileState.addNode_descAt_old
                    st und hund_deps ⟨nd'.val, hlt⟩] at hk_inner
                  have := hcon.chance ⟨nd'.val, hlt⟩ hk_inner
                  simp only [RevealState.addPublicNode]
                  rw [if_neg (show nd'.val ≠ rs.nextId from by rw [hcon.sync]; omega)]
                  exact this
                · exfalso
                  rw [show (⟨nd'.val, _⟩ : Fin _) = ⟨st.nextId, by simp [MAIDCompileState.addNode]⟩
                      from Fin.ext heq] at hk_inner
                  rw [MAIDCompileState.addNode_descAt_new st und hund_deps] at hk_inner
                  simp [und, CompiledNode.kind] at hk_inner
              decision := by
                intro nd' p hk
                have hbound : nd'.val ≤ st.nextId := by
                  have := nd'.isLt; simp [MAIDCompileState.addNode] at this; omega
                have hk_inner : ((st.addNode und hund_deps).2.descAt ⟨nd'.val, by
                    simp [MAIDCompileState.addNode]; omega⟩).kind = .decision p := hk
                rcases Nat.lt_or_eq_of_le hbound with hlt | heq
                · rw [MAIDCompileState.addNode_descAt_old
                    st und hund_deps ⟨nd'.val, hlt⟩] at hk_inner
                  have := hcon.decision ⟨nd'.val, hlt⟩ p hk_inner
                  simp only [RevealState.addPublicNode]
                  rw [if_neg (show nd'.val ≠ rs.nextId from by rw [hcon.sync]; omega)]
                  exact this
                · exfalso
                  rw [show (⟨nd'.val, _⟩ : Fin _) = ⟨st.nextId, by simp [MAIDCompileState.addNode]⟩
                      from Fin.ext heq] at hk_inner
                  rw [MAIDCompileState.addNode_descAt_new st und hund_deps] at hk_inner
                  simp [und, CompiledNode.kind] at hk_inner
              nodeOf_lt := by
                intro v nid hnid
                simp only [RevealState.addPublicNode] at hnid
                change nid < st.nextId + 1
                exact Nat.lt_trans (hcon.nodeOf_lt v nid hnid) (Nat.lt_succ_self _)
              unset := by
                intro i hi
                have hi' : st.nextId + 1 ≤ i := by
                  simpa [MAIDCompileState.addNode] using hi
                simp only [RevealState.addPublicNode]
                rw [if_neg (show i ≠ rs.nextId from by rw [hcon.sync]; omega)]
                exact hcon.unset i (by omega)
            }
  | letExpr x e k ih =>
      simp only [computeReveals, MAIDCompileState.ofProg]
      exact ih hl hd _ _ _ ⟨hcon₀.sync, hcon₀.chance, hcon₀.decision, hcon₀.nodeOf_lt, hcon₀.unset⟩
  | sample x D' k ih =>
      rename_i Γ' b
      rename_i Γ'
      simp only [computeReveals, MAIDCompileState.ofProg]
      apply ih (hd := hd.2)
      -- Extract the chance node being added
      let cnd : CompiledNode Player L B :=
        .chance b (st₀.ctxDeps Γ') (fun raw => L.evalDist D' (VEnv.eraseSampleEnv (ρ raw)))
          (fun raw => hd.1 (ρ raw))
      have hcnd_kind : cnd.kind = .chance := rfl
      -- The deps proof from the compiler
      have hcnd_deps : ∀ d ∈ cnd.parents ∪ cnd.obsParents, d < st₀.nextId := by
        intro d hd'
        simp only [CompiledNode.parents, CompiledNode.obsParents, Finset.union_idempotent,
          cnd] at hd'
        exact st₀.depsOfVars_lt _ d hd'
      have hdeps : ∀ d ∈ ({st₀.nextId} : Finset Nat), d < st₀.nextId + 1 := by
        intro d hd'; simp at hd'; omega
      change RevealConsistent
        ((st₀.addNode cnd hcnd_deps).2.addVar x (.pub b) {st₀.nextId} hdeps)
        (rs₀.addPublicNode.bindVar x rs₀.nextId)
      have hnid1 : ((st₀.addNode cnd hcnd_deps).2.addVar x (.pub b) {st₀.nextId} hdeps).nextId
          = st₀.nextId + 1 := by simp [MAIDCompileState.addNode, MAIDCompileState.addVar]
      exact {
        sync := by simp [RevealState.addPublicNode, RevealState.bindVar, hnid1, hcon₀.sync]
        chance := by
          intro nd' hk
          have hbound : nd'.val ≤ st₀.nextId := by rw [hnid1] at nd'; omega
          have hk_inner : ((st₀.addNode cnd hcnd_deps).2.descAt ⟨nd'.val, by
              simp [MAIDCompileState.addNode]; omega⟩).kind = .chance := hk
          rcases Nat.lt_or_eq_of_le hbound with hlt | heq
          · rw [MAIDCompileState.addNode_descAt_old st₀ cnd hcnd_deps ⟨nd'.val, hlt⟩] at hk_inner
            have := hcon₀.chance ⟨nd'.val, hlt⟩ hk_inner
            simp only [RevealState.addPublicNode, RevealState.bindVar]
            rw [if_neg (show nd'.val ≠ rs₀.nextId from by rw [hcon₀.sync]; omega)]; exact this
          · simp only [RevealState.addPublicNode, RevealState.bindVar]
            rw [if_pos (show nd'.val = rs₀.nextId from by rw [hcon₀.sync]; omega)]
            simp [hcon₀.sync, heq]
        decision := by
          intro nd' p hk
          have hbound : nd'.val ≤ st₀.nextId := by rw [hnid1] at nd'; omega
          have hk_inner : ((st₀.addNode cnd hcnd_deps).2.descAt ⟨nd'.val, by
              simp [MAIDCompileState.addNode]; omega⟩).kind = .decision p := hk
          rcases Nat.lt_or_eq_of_le hbound with hlt | heq
          · rw [MAIDCompileState.addNode_descAt_old st₀ cnd hcnd_deps ⟨nd'.val, hlt⟩] at hk_inner
            have := hcon₀.decision ⟨nd'.val, hlt⟩ p hk_inner
            simp only [RevealState.addPublicNode, RevealState.bindVar]
            rw [if_neg (show nd'.val ≠ rs₀.nextId from by rw [hcon₀.sync]; omega)]; exact this
          · exfalso
            rw [show (⟨nd'.val, _⟩ : Fin (st₀.addNode cnd hcnd_deps).2.nextId) =
                ⟨st₀.nextId, by simp [MAIDCompileState.addNode]⟩ from Fin.ext heq] at hk_inner
            rw [MAIDCompileState.addNode_descAt_new st₀ cnd hcnd_deps] at hk_inner
            simp [cnd, CompiledNode.kind] at hk_inner
        nodeOf_lt := by
          intro v nid hnid
          simp only [RevealState.addPublicNode, RevealState.bindVar] at hnid
          rw [hnid1]
          by_cases hv : v = x
          · subst hv; simp at hnid; have := hcon₀.sync; omega
          · simp only [hv, ↓reduceIte] at hnid
            exact Nat.lt_trans (hcon₀.nodeOf_lt v nid hnid) (Nat.lt_succ_self _)
        unset := by
          intro i hi
          simp only [RevealState.addPublicNode, RevealState.bindVar]
          rw [if_neg (show i ≠ rs₀.nextId from by rw [hcon₀.sync]; omega)]
          exact hcon₀.unset i (by omega)
      }
  | commit x who R k ih =>
      rename_i Γ' b
      simp only [computeReveals, MAIDCompileState.ofProg]
      apply ih (hd := hd)
      let dnd : CompiledNode Player L B :=
        .decision b who (allValues B b) (allValues_ne_nil B b)
          (allValues_nodup B b) (st₀.viewDeps who Γ')
      have hdnd_kind : dnd.kind = .decision who := rfl
      have hdnd_deps : ∀ d ∈ dnd.parents ∪ dnd.obsParents, d < st₀.nextId := by
        intro d hd'
        simp only [CompiledNode.parents, CompiledNode.obsParents, Finset.union_idempotent,
          dnd] at hd'
        exact st₀.depsOfVars_lt _ d hd'
      have hdeps : ∀ d ∈ ({st₀.nextId} : Finset Nat), d < st₀.nextId + 1 := by
        intro d hd'; simp at hd'; omega
      change RevealConsistent
        ((st₀.addNode dnd hdnd_deps).2.addVar x (.hidden who b) {st₀.nextId} hdeps)
        (rs₀.addPrivateNode.bindVar x rs₀.nextId)
      have hnid1 : ((st₀.addNode dnd hdnd_deps).2.addVar x
        (.hidden who b) {st₀.nextId} hdeps).nextId
          = st₀.nextId + 1 := by simp [MAIDCompileState.addNode, MAIDCompileState.addVar]
      exact {
        sync := by simp [RevealState.addPrivateNode, RevealState.bindVar, hnid1, hcon₀.sync]
        chance := by
          intro nd' hk
          have hbound : nd'.val ≤ st₀.nextId := by rw [hnid1] at nd'; omega
          have hk_inner : ((st₀.addNode dnd hdnd_deps).2.descAt ⟨nd'.val, by
              simp [MAIDCompileState.addNode]; omega⟩).kind = .chance := hk
          rcases Nat.lt_or_eq_of_le hbound with hlt | heq
          · rw [MAIDCompileState.addNode_descAt_old st₀ dnd hdnd_deps ⟨nd'.val, hlt⟩] at hk_inner
            exact hcon₀.chance ⟨nd'.val, hlt⟩ hk_inner
          · exfalso
            rw [show (⟨nd'.val, _⟩ : Fin (st₀.addNode dnd hdnd_deps).2.nextId) =
                ⟨st₀.nextId, by simp [MAIDCompileState.addNode]⟩ from Fin.ext heq] at hk_inner
            rw [MAIDCompileState.addNode_descAt_new st₀ dnd hdnd_deps] at hk_inner
            simp [dnd, CompiledNode.kind] at hk_inner
        decision := by
          intro nd' p hk
          have hbound : nd'.val ≤ st₀.nextId := by rw [hnid1] at nd'; omega
          have hk_inner : ((st₀.addNode dnd hdnd_deps).2.descAt ⟨nd'.val, by
              simp [MAIDCompileState.addNode]; omega⟩).kind = .decision p := hk
          rcases Nat.lt_or_eq_of_le hbound with hlt | heq
          · rw [MAIDCompileState.addNode_descAt_old st₀ dnd hdnd_deps ⟨nd'.val, hlt⟩] at hk_inner
            have := hcon₀.decision ⟨nd'.val, hlt⟩ p hk_inner
            simp only [RevealState.addPrivateNode, RevealState.bindVar]; exact this
          · simp only [RevealState.addPrivateNode, RevealState.bindVar]
            rw [hcon₀.unset nd'.val (by omega)]
            exact WithTop.coe_lt_top _
        nodeOf_lt := by
          intro v nid hnid
          simp only [RevealState.addPrivateNode, RevealState.bindVar] at hnid
          rw [hnid1]
          by_cases hv : v = x
          · subst hv; simp at hnid; have := hcon₀.sync; omega
          · simp only [hv, ite_false] at hnid
            exact Nat.lt_trans (hcon₀.nodeOf_lt v nid hnid) (Nat.lt_succ_self _)
        unset := by
          intro i hi
          simp only [RevealState.addPrivateNode, RevealState.bindVar]
          exact hcon₀.unset i (by omega)
      }
  | reveal y who x hx k ih =>
      simp only [computeReveals, MAIDCompileState.ofProg]
      apply ih (hd := hd)
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp only [RevealState.aliasVar, MAIDCompileState.addVar]
        split <;> simp [hcon₀.sync]
      · intro nd hk
        have h := hcon₀.chance nd hk  -- addVar doesn't change descAt
        simp only [RevealState.aliasVar]
        split
        · rename_i nid hx_eq
          simp only; by_cases heq : nd.val = nid
          · rw [if_pos heq, h, min_eq_right]
            have h1 := hcon₀.nodeOf_lt x nid hx_eq
            have h2 : nd.val ≤ rs₀.nextId := by
              rw [hcon₀.sync]; omega
            exact WithTop.coe_le_coe.mpr h2
          · rw [if_neg heq]; exact h
        · exact h
      · intro nd p hk
        have h := hcon₀.decision nd p hk
        simp only [RevealState.aliasVar]
        split
        · rename_i nid hx_eq
          simp only; by_cases heq : nd.val = nid
          · rw [if_pos heq]
            have h1 := hcon₀.nodeOf_lt x nid hx_eq
            have h2 : nd.val < rs₀.nextId := by rw [hcon₀.sync]; omega
            exact lt_min (WithTop.coe_lt_coe.mpr h2) h
          · rw [if_neg heq]; exact h
        · exact h
      · intro v nid hnid
        change nid < st₀.nextId
        simp only [RevealState.aliasVar] at hnid
        cases hx_eq : rs₀.nodeOf x with
        | none =>
            simp only [hx_eq, Option.ite_none_left_eq_some] at hnid
            by_cases hv : v = y
            · subst hv; simp at hnid
            · simp only [hv, not_false_eq_true, true_and] at hnid
              exact hcon₀.nodeOf_lt v nid hnid
        | some nid' =>
            simp only [hx_eq] at hnid
            by_cases hv : v = y
            · subst hv
              simp only [reduceIte, Option.some.injEq] at hnid
              subst hnid
              exact hcon₀.nodeOf_lt x nid' hx_eq
            · simp only [hv, reduceIte] at hnid
              exact hcon₀.nodeOf_lt v nid hnid
      · -- unset
        intro i hi
        simp only [RevealState.aliasVar, MAIDCompileState.addVar] at hi ⊢
        cases hx_eq : rs₀.nodeOf x with
        | none =>
            simp only
            exact hcon₀.unset i hi
        | some nid' =>
            simp only
            rw [if_neg (show i ≠ nid' from by
              have := hcon₀.nodeOf_lt x nid' hx_eq; omega)]
            exact hcon₀.unset i hi

/-- If `i ∈ depsOfVars xs`, then `i ∈ lookupDeps x` for some `x ∈ xs`. -/
private theorem mem_depsOfVars_iff (st : MAIDCompileState Player L B)
    (xs : List VarId) (i : Nat) :
    i ∈ st.depsOfVars xs ↔ ∃ x ∈ xs, i ∈ st.lookupDeps x := by
  induction xs with
  | nil => simp [MAIDCompileState.depsOfVars]
  | cons y ys ih =>
      simp only [MAIDCompileState.depsOfVars, Finset.mem_union, ih, List.mem_cons]
      constructor
      · rintro (h | ⟨x, hx, hm⟩)
        · exact ⟨y, Or.inl rfl, h⟩
        · exact ⟨x, Or.inr hx, hm⟩
      · rintro ⟨x, (rfl | hx), hm⟩
        · left; exact hm
        · right; exact ⟨x, hx, hm⟩

/-- hprev transfer: old decision nodes' parent visibility is preserved through
    addNode (non-decision) + addPublicNode. -/
private theorem hprev_transfer_addNode
    {st : MAIDCompileState Player L B} {rs : RevealState}
    (hcon : RevealConsistent st rs)
    (nd : CompiledNode Player L B) (hkind : ¬ ∃ p, nd.kind = .decision p)
    (hnd : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId)
    (hp : ∀ (d : Fin st.nextId) (pw : Player),
      (st.descAt d).kind = .decision pw →
      ∀ (i : Nat) (hi : i ∈ (st.descAt d).parents),
        rs.revealTime i ≤ ↑d.val ∨
          (st.descAt ⟨i, Nat.lt_trans (st.descAt_parent_lt d hi) d.2⟩).kind = .decision pw) :
    ∀ (d : Fin (st.addNode nd hnd).2.nextId) (pw : Player),
      ((st.addNode nd hnd).2.descAt d).kind = .decision pw →
      ∀ (i : Nat) (hi : i ∈ ((st.addNode nd hnd).2.descAt d).parents),
        rs.addPublicNode.revealTime i ≤ ↑d.val ∨
          ((st.addNode nd hnd).2.descAt
              ⟨i, Nat.lt_trans ((st.addNode nd hnd).2.descAt_parent_lt d hi) d.2⟩).kind =
            .decision pw := by
  intro d' pw' hk' i hi'
  have hbound : d'.val ≤ st.nextId := by
    have := d'.isLt; simp [MAIDCompileState.addNode] at this; omega
  have hk_inner : ((st.addNode nd hnd).2.descAt ⟨d'.val, by
      simp [MAIDCompileState.addNode]; omega⟩).kind = .decision pw' := hk'
  rcases Nat.lt_or_eq_of_le hbound with hlt | heq
  · rw [MAIDCompileState.addNode_descAt_old st nd hnd ⟨d'.val, hlt⟩] at hk_inner
    have hi_inner : i ∈ (st.descAt ⟨d'.val, hlt⟩).parents := by
      have : i ∈ ((st.addNode nd hnd).2.descAt ⟨d'.val, by
        simp [MAIDCompileState.addNode]
        omega⟩).parents := hi'
      rwa [MAIDCompileState.addNode_descAt_old st nd hnd ⟨d'.val, hlt⟩] at this
    rcases hp ⟨d'.val, hlt⟩ pw' hk_inner i hi_inner with h | h
    · left; simp only [RevealState.addPublicNode]
      rw [if_neg (show i ≠ rs.nextId from by
        rw [hcon.sync]; have := st.descAt_parent_lt ⟨d'.val, hlt⟩ hi_inner; omega)]
      exact h
    · right
      change ((st.addNode nd hnd).2.descAt ⟨i, _⟩).kind = _
      rw [MAIDCompileState.addNode_descAt_old st nd hnd
        ⟨i, by have := st.descAt_parent_lt ⟨d'.val, hlt⟩ hi_inner; omega⟩]
      exact h
  · exfalso
    rw [show (⟨d'.val, _⟩ : Fin (st.addNode nd hnd).2.nextId) =
        ⟨st.nextId, by simp [MAIDCompileState.addNode]⟩ from Fin.ext heq] at hk_inner
    rw [MAIDCompileState.addNode_descAt_new st nd hnd] at hk_inner
    exact hkind ⟨pw', hk_inner⟩

/-- VarVisible extension for adding a pub variable (letExpr case). -/
private theorem varVisible_addVar_pub
    (st : MAIDCompileState Player L B) (rs : RevealState)
    (x : VarId) (b : L.Ty) (Γ : VCtx Player L)
    (hvars : st.VarsSubCtx Γ) (hfresh_x : Fresh x Γ)
    (deps : Finset Nat) (hdeps : ∀ d ∈ deps, d < st.nextId)
    (hvar : VarVisible Γ st rs)
    (hdeps_sub : deps ⊆ st.pubCtxDeps Γ) :
    VarVisible ((x, .pub b) :: Γ) (st.addVar x (.pub b) deps hdeps) rs := by
  intro who y σ hy i hi
  unfold viewVCtx at hy
  simp only [canSee, reduceIte, List.mem_cons, Prod.mk.injEq] at hy
  rcases hy with ⟨rfl, rfl⟩ | hy
  · rw [st.lookupDeps_addVar_eq_self_of_fresh y _ _ _ (fun hm => hfresh_x (hvars y hm))] at hi
    have hi_pub := hdeps_sub hi
    rw [MAIDCompileState.pubCtxDeps] at hi_pub
    obtain ⟨z, hz_mem, hz_dep⟩ := (mem_depsOfVars_iff st _ i).mp hi_pub
    have hz_view := erasePubVCtx_map_fst_sub_viewVCtx (Γ := Γ) (who := who) z hz_mem
    obtain ⟨⟨z', σ'⟩, hzs_mem, hzs_fst⟩ := List.mem_map.mp hz_view
    simp only at hzs_fst
    subst hzs_fst
    exact hvar who z' σ' hzs_mem i hz_dep
  · rw [st.lookupDeps_addVar_eq_of_ne x _ _ _ (by
      intro heq; subst heq
      exact hfresh_x (viewVCtx_map_fst_sub (p := who) (Γ := Γ)
        (List.mem_map.mpr ⟨(y, σ), hy, rfl⟩)))] at hi
    exact hvar who y σ hy i hi

/-- VarVisible extension for addNode(.chance)+addVar (sample case).
-/
private theorem varVisible_addNode_chance_addVar
    (st : MAIDCompileState Player L B) (rs : RevealState) (hcon : RevealConsistent st rs)
    (nd : CompiledNode Player L B) (_hnd_kind : nd.kind = .chance)
    (hnd : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId)
    (x : VarId) (τ : BindTy Player L) (Γ : VCtx Player L)
    (hvars : st.VarsSubCtx Γ) (hfresh_x : Fresh x Γ)
    (hdeps : ∀ d ∈ ({st.nextId} : Finset Nat), d < st.nextId + 1)
    (hvar : VarVisible Γ st rs) :
    VarVisible ((x, τ) :: Γ) ((st.addNode nd hnd).2.addVar x τ {st.nextId} hdeps)
      (rs.addPublicNode.bindVar x rs.nextId) := by
  have hnid : ((st.addNode nd hnd).2.addVar x τ {st.nextId} hdeps).nextId = st.nextId + 1 := by
    simp [MAIDCompileState.addNode, MAIDCompileState.addVar]
  intro who y σ hy i hi
  by_cases heq : y = x
  · subst heq
    rw [(st.addNode nd hnd).2.lookupDeps_addVar_eq_self_of_fresh y _ _ _
      (fun hm => hfresh_x ((st.VarsSubCtx_addNode hvars nd hnd) y hm))] at hi
    simp only [Finset.mem_singleton] at hi
    subst hi
    left; simp only [RevealState.addPublicNode, RevealState.bindVar]
    rw [if_pos hcon.sync.symm, hnid]
    exact_mod_cast (show rs.nextId ≤ st.nextId + 1 by have := hcon.sync; omega)
  · rw [(st.addNode nd hnd).2.lookupDeps_addVar_eq_of_ne x _ _ _ heq] at hi
    have hy' : (y, σ) ∈ viewVCtx who Γ := by
      unfold viewVCtx at hy; split at hy
      · simp only [List.mem_cons, Prod.mk.injEq] at hy
        rcases hy with ⟨rfl, _⟩ | hy
        · exact absurd rfl heq
        · exact hy
      · exact hy
    have hilt : i < st.nextId := st.lookupDeps_lt y i hi
    rcases hvar who y σ hy' i hi with h | h
    · left; simp only [RevealState.addPublicNode, RevealState.bindVar]
      rw [if_neg (show i ≠ rs.nextId from by rw [hcon.sync]; omega)]
      rw [hnid]
      exact le_trans h (WithTop.coe_le_coe.mpr (Nat.le_succ _))
    · right
      change ((st.addNode nd hnd).2.descAt ⟨i, by
        simp [MAIDCompileState.addNode]
        omega⟩).kind = _
      rw [MAIDCompileState.addNode_descAt_old st nd hnd ⟨i, hilt⟩]; exact h

/-- VarVisible extension for addNode(.decision)+addVar (commit case).
    Proof verified in run_code. -/
private theorem varVisible_addNode_decision_addVar
    (st : MAIDCompileState Player L B) (rs : RevealState) (_hcon : RevealConsistent st rs)
    (nd : CompiledNode Player L B) (who : Player) (_hnd_kind : nd.kind = .decision who)
    (hnd : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId)
    (x : VarId) (b : L.Ty) (Γ : VCtx Player L)
    (_hvars : st.VarsSubCtx Γ) (_hfresh_x : Fresh x Γ)
    (hdeps : ∀ d ∈ ({st.nextId} : Finset Nat), d < st.nextId + 1)
    (_hvar : VarVisible Γ st rs) :
    VarVisible ((x, .hidden who b) :: Γ)
      ((st.addNode nd hnd).2.addVar x (.hidden who b) {st.nextId} hdeps)
      (rs.addPrivateNode.bindVar x rs.nextId) := by
  have hnid : ((st.addNode nd hnd).2.addVar x (.hidden who b) {st.nextId} hdeps).nextId =
      st.nextId + 1 := by simp [MAIDCompileState.addNode, MAIDCompileState.addVar]
  intro p y σ hy i hi
  -- canSee dispatch: p = who sees x, p ≠ who doesn't
  by_cases hp : p = who
  · subst hp -- p replaces who
    by_cases heq : y = x
    · subst heq
      rw [(st.addNode nd hnd).2.lookupDeps_addVar_eq_self_of_fresh y _ _ _
        (fun hm => _hfresh_x ((st.VarsSubCtx_addNode _hvars nd hnd) y hm))] at hi
      simp only [Finset.mem_singleton] at hi
      subst hi
      right
      change ((st.addNode nd hnd).2.descAt
        ⟨st.nextId, by simp [MAIDCompileState.addNode]⟩).kind = _
      rw [MAIDCompileState.addNode_descAt_new st nd hnd]; exact _hnd_kind
    · rw [(st.addNode nd hnd).2.lookupDeps_addVar_eq_of_ne x _ _ _ heq] at hi
      have hy' : (y, σ) ∈ viewVCtx p Γ := by
        unfold viewVCtx at hy
        simp only [canSee, decide_true, ↓reduceIte, List.mem_cons, Prod.mk.injEq] at hy
        rcases hy with ⟨rfl, _⟩ | hy
        · exact absurd rfl heq
        · exact hy
      have hilt : i < st.nextId := st.lookupDeps_lt y i hi
      rcases _hvar p y σ hy' i hi with h | h
      · left; simp only [RevealState.addPrivateNode, RevealState.bindVar]
        rw [hnid]; exact le_trans h (WithTop.coe_le_coe.mpr (Nat.le_succ _))
      · right
        change ((st.addNode nd hnd).2.descAt
          ⟨i, by simp [MAIDCompileState.addNode]; omega⟩).kind = _
        rw [MAIDCompileState.addNode_descAt_old st nd hnd ⟨i, hilt⟩]; exact h
  · -- p ≠ who: x not visible
    have hy' : (y, σ) ∈ viewVCtx p Γ := by
      unfold viewVCtx at hy
      simp only [canSee, hp, decide_false, Bool.false_eq_true, reduceIte] at hy
      exact hy
    have hne : y ≠ x := by
      intro heq; subst heq
      exact _hfresh_x (viewVCtx_map_fst_sub (p := p) (Γ := Γ)
        (List.mem_map.mpr ⟨(y, σ), hy', rfl⟩))
    rw [(st.addNode nd hnd).2.lookupDeps_addVar_eq_of_ne x _ _ _ hne] at hi
    have hilt : i < st.nextId := st.lookupDeps_lt y i hi
    rcases _hvar p y σ hy' i hi with h | h
    · left; simp only [RevealState.addPrivateNode, RevealState.bindVar]
      rw [hnid]; exact le_trans h (WithTop.coe_le_coe.mpr (Nat.le_succ _))
    · right
      change ((st.addNode nd hnd).2.descAt ⟨i, by simp [MAIDCompileState.addNode]; omega⟩).kind = _
      rw [MAIDCompileState.addNode_descAt_old st nd hnd ⟨i, hilt⟩]; exact h

/-- VarVisible extension for reveal: copies x's deps to new pub var y. -/
private theorem varVisible_reveal
    (st : MAIDCompileState Player L B) (rs : RevealState)
    (y x : VarId) (b : L.Ty) (who : Player) (Γ : VCtx Player L)
    (hx : VHasVar (L := L) Γ x (.hidden who b))
    (hvars : st.VarsSubCtx Γ) (hfresh_y : Fresh y Γ)
    (hvar : VarVisible Γ st rs)
    (hdt : ∀ z nid, rs.nodeOf z = some nid → st.lookupDeps z ⊆ {nid})
    (hhn : ∀ z who b, VHasVar (L := L) Γ z (.hidden who b) → rs.nodeOf z ≠ none)
    (hcon : RevealConsistent st rs) :
    VarVisible ((y, .pub b) :: Γ)
      (st.addVar y (.pub b) (st.lookupDeps x) (st.lookupDeps_lt x))
      ((match rs.nodeOf x with
        | some nid => { rs with revealTime := fun i =>
            if i = nid then (min (↑rs.nextId) (rs.revealTime i)) else rs.revealTime i }
        | none => rs).aliasVar y x) := by
  have hnid_eq : (st.addVar y (.pub b) (st.lookupDeps x)
    (st.lookupDeps_lt x)).nextId = st.nextId := rfl
  intro p z σ hz i hi
  by_cases heq : z = y
  · -- z = y: deps = lookupDeps x
    subst heq
    rw [st.lookupDeps_addVar_eq_self_of_fresh z _ _ _ (fun hm => hfresh_y (hvars z hm))] at hi
    obtain ⟨nid, hnid⟩ := Option.ne_none_iff_exists'.mp (hhn x who _ hx)
    have hi_eq := Finset.mem_singleton.mp (hdt x nid hnid hi); subst hi_eq
    left; simp only [RevealState.aliasVar]; rw [hnid]
    -- goal: revealTime through match(some nid) at nid ≤ ↑addVar.nextId
    simp only [hnid_eq, ite_true]
    exact le_trans (min_le_left _ _) (by exact_mod_cast
      (show rs.nextId ≤ st.nextId by have := hcon.sync; omega))
  · rw [st.lookupDeps_addVar_eq_of_ne y _ _ _ heq] at hi
    have hz' : (z, σ) ∈ viewVCtx p Γ := by
      unfold viewVCtx at hz
      simp only [canSee, ↓reduceIte, List.mem_cons, Prod.mk.injEq] at hz
      rcases hz with ⟨rfl, _⟩ | hz
      · exact absurd rfl heq
      · exact hz
    rcases hvar p z σ hz' i hi with h | h
    · left
      cases hnx : rs.nodeOf x with
      | none =>
          simp only [RevealState.aliasVar, hnx, hnid_eq]; exact h
      | some nid =>
          simp only [RevealState.aliasVar, hnx, hnid_eq]
          by_cases heqi : i = nid
          · subst heqi; simp only [ite_true]; exact le_trans (min_le_right _ _) h
          · simp only [show ¬(i = nid) from heqi, ite_false]; exact h
    · right; exact h

/-- Decision parents in the compiled MAID are all visible to the player
    (the factored-observation property). -/
theorem computeReveals_parents_visible (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ) (hl : Legal p) (hd : NormalizedDists p)
    (hfresh : FreshBindings p)
    (ρ : RawNodeEnv L → VEnv (Player := Player) L Γ)
    (st₀ : MAIDCompileState Player L B) (rs₀ : RevealState)
    (hcon₀ : RevealConsistent st₀ rs₀)
    (hvars : st₀.VarsSubCtx Γ)
    -- The property holds for all decision nodes already in st₀
    (hprev : ∀ (d : Fin st₀.nextId) (pw : Player),
      (st₀.descAt d).kind = .decision pw →
      ∀ (i : Nat) (hi : i ∈ (st₀.descAt d).parents),
        rs₀.revealTime i ≤ ↑d.val ∨
          (st₀.descAt ⟨i, Nat.lt_trans (st₀.descAt_parent_lt d hi) d.2⟩).kind = .decision pw)
    -- VarVisible: visible deps are visible nodes (needed for commit case)
    (hvar₀ : VarVisible Γ st₀ rs₀)
    -- DepsTracked: nodeOf y = some nid → lookupDeps y ⊆ {nid}
    (hdt : ∀ y nid, rs₀.nodeOf y = some nid → st₀.lookupDeps y ⊆ {nid})
    -- HiddenHasNodeOf: hidden vars have nodeOf bindings
    (hhn : ∀ y who b, VHasVar (L := L) Γ y (.hidden who b) → rs₀.nodeOf y ≠ none)
    -- NodeOfSubCtx: nodeOf only set for vars in context
    (hnsc : ∀ y nid, rs₀.nodeOf y = some nid → y ∈ Γ.map Prod.fst) :
    let st := MAIDCompileState.ofProg B p hl hd ρ st₀
    let rs := computeReveals B p rs₀
    ∀ (d : Fin st.nextId) (p : Player),
      (st.descAt d).kind = .decision p →
      ∀ (i : Nat) (hi : i ∈ (st.descAt d).parents),
        rs.revealTime i ≤ ↑d.val ∨
          (∃ q, (st.descAt ⟨i, Nat.lt_trans (st.descAt_parent_lt d hi) d.2⟩).kind =
            .decision q ∧ q = p) := by
  induction p generalizing st₀ rs₀ with
  | ret payoffs =>
      simp only [computeReveals, MAIDCompileState.ofProg]
      suffices ∀ (players : List Player) (deps : Finset Nat)
          (ufn : Player → RawNodeEnv L → ℝ)
          (st : MAIDCompileState Player L B) (rs : RevealState)
          (hdeps : ∀ d ∈ deps, d < st.nextId) (hcon : RevealConsistent st rs)
          (hp : ∀ (d : Fin st.nextId) (pw : Player),
            (st.descAt d).kind = .decision pw →
            ∀ (i : Nat) (hi : i ∈ (st.descAt d).parents),
              rs.revealTime i ≤ ↑d.val ∨
                (st.descAt ⟨i, Nat.lt_trans (st.descAt_parent_lt d hi) d.2⟩).kind = .decision pw),
          ∀ (d : Fin (st.addUtilityNodes deps hdeps ufn players).nextId) (p : Player),
            ((st.addUtilityNodes deps hdeps ufn players).descAt d).kind = .decision p →
            ∀ (i : Nat) (hi : i ∈ ((st.addUtilityNodes deps hdeps ufn players).descAt d).parents),
              (players.foldl (fun rs' _ => rs'.addPublicNode) rs).revealTime i ≤ ↑d.val ∨
                ∃ q, ((st.addUtilityNodes deps hdeps ufn players).descAt
                  ⟨i, Nat.lt_trans
                      ((st.addUtilityNodes deps hdeps ufn players).descAt_parent_lt
                        d hi) d.2⟩).kind =
                    .decision q ∧ q = p by
        exact this _ _ _ st₀ rs₀ _ hcon₀ hprev
      intro players
      induction players with
      | nil => intro _ _ st rs _ _ hp; simpa [MAIDCompileState.addUtilityNodes]
      | cons pw rest ih =>
          intro deps ufn st rs hdeps hcon hp
          simp only [MAIDCompileState.addUtilityNodes, List.foldl_cons]
          let und : CompiledNode Player L B := .utility pw deps (ufn pw)
          have hund_deps : ∀ d ∈ und.parents ∪ und.obsParents, d < st.nextId := by
            intro d hd'
            simp only [CompiledNode.parents, CompiledNode.obsParents, Finset.union_idempotent,
              und] at hd'
            exact hdeps d hd'
          exact ih deps ufn _ _ (fun d hd => Nat.lt_trans (hdeps d hd) (Nat.lt_succ_self _))
            (revealConsistent_addNode' hcon und
              (by intro ⟨_, h⟩; simp [und, CompiledNode.kind] at h) hund_deps)
            (by -- hp for intermediate: old decisions preserved
                intro d' pw' hk' i hi'
                have hbound : d'.val ≤ st.nextId := by
                  have := d'.isLt; simp [MAIDCompileState.addNode] at this; omega
                have hk_inner : ((st.addNode und hund_deps).2.descAt ⟨d'.val, by
                    simp [MAIDCompileState.addNode]; omega⟩).kind = .decision pw' := hk'
                rcases Nat.lt_or_eq_of_le hbound with hlt | heq
                · -- old decision node
                  rw [MAIDCompileState.addNode_descAt_old
                    st und hund_deps ⟨d'.val, hlt⟩] at hk_inner
                  have hi_inner : i ∈ (st.descAt ⟨d'.val, hlt⟩).parents := by
                    rw [MAIDCompileState.addNode_descAt_old st und hund_deps ⟨d'.val, hlt⟩] at hi'
                    exact hi'
                  rcases hp ⟨d'.val, hlt⟩ pw' hk_inner i hi_inner with h | h
                  · left
                    simp only [RevealState.addPublicNode]
                    rw [if_neg (show i ≠ rs.nextId from by
                      rw [hcon.sync]
                      have := st.descAt_parent_lt ⟨d'.val, hlt⟩ hi_inner
                      omega)]
                    exact h
                  · right
                    change ((st.addNode und hund_deps).2.descAt ⟨i, _⟩).kind = _
                    rw [MAIDCompileState.addNode_descAt_old st und hund_deps
                      ⟨i, by have := st.descAt_parent_lt ⟨d'.val, hlt⟩ hi_inner; omega⟩]
                    exact h
                · -- new utility node: not decision
                  exfalso
                  rw [show (⟨d'.val, _⟩ : Fin _) = ⟨st.nextId, by simp [MAIDCompileState.addNode]⟩
                      from Fin.ext heq] at hk_inner
                  rw [MAIDCompileState.addNode_descAt_new st und hund_deps] at hk_inner
                  simp [und, CompiledNode.kind] at hk_inner)
  | letExpr x e k ih =>
      simp only [computeReveals, MAIDCompileState.ofProg]
      exact ih hl hd hfresh.2 _ _ _
        ⟨hcon₀.sync, hcon₀.chance, hcon₀.decision, hcon₀.nodeOf_lt, hcon₀.unset⟩
        (st₀.VarsSubCtx_addVar hvars x _ _ _ hfresh.1) hprev
        (varVisible_addVar_pub st₀ rs₀ x _ _ hvars hfresh.1 _ _ hvar₀ (Finset.Subset.refl _))
        (by intro z nid hnid
            by_cases hz : z = x
            · subst hz; exact absurd (hnsc z nid hnid) hfresh.1
            · rw [st₀.lookupDeps_addVar_eq_of_ne x _ _ _ hz]; exact hdt z nid hnid)
        (by -- hhn: new pub var x is not hidden; old hidden vars: nodeOf unchanged
            intro z who' b' hv; cases hv with
            | there hv' => exact hhn z who' b' hv')
        (by -- hnsc: nodeOf only in context; addVar extends context
            intro z nid hnid
            simp only [List.map_cons, List.mem_cons]
            right; exact hnsc z nid hnid)
  | sample x D' k ih =>
      rename_i Γ' b
      rename_i Γ'
      simp only [computeReveals, MAIDCompileState.ofProg]
      let cnd : CompiledNode Player L B :=
        .chance b (st₀.ctxDeps Γ') (fun raw => L.evalDist D' (VEnv.eraseSampleEnv (ρ raw)))
          (fun raw => hd.1 (ρ raw))
      have hcnd_deps : ∀ d ∈ cnd.parents ∪ cnd.obsParents, d < st₀.nextId := by
        intro d hd'
        simp only [CompiledNode.parents, CompiledNode.obsParents, Finset.union_idempotent,
          cnd] at hd'
        exact st₀.depsOfVars_lt _ d hd'
      have hdeps : ∀ d ∈ ({st₀.nextId} : Finset Nat), d < st₀.nextId + 1 := by
        intro d hd'; simp at hd'; omega
      exact ih hl hd.2 hfresh.2 _ _ _
        (revealConsistent_addChance' hcon₀ cnd
          (by intro ⟨_, h⟩; simp [cnd, CompiledNode.kind] at h) hcnd_deps x (.pub b) hdeps)
        ((st₀.addNode cnd hcnd_deps).2.VarsSubCtx_addVar
            (st₀.VarsSubCtx_addNode hvars cnd hcnd_deps)
          x _ _ _ hfresh.1)
        (hprev_transfer_addNode hcon₀ cnd
          (by intro ⟨_, h⟩; simp [cnd, CompiledNode.kind] at h) hcnd_deps hprev)
        (varVisible_addNode_chance_addVar st₀ rs₀ hcon₀ cnd
          (by simp [cnd, CompiledNode.kind]) hcnd_deps x (.pub b) _ hvars hfresh.1 hdeps hvar₀)
        (by -- hdt: x→{nextId}⊆{nextId}, y≠x → from hdt
            intro z nid hnid
            simp only [RevealState.addPublicNode, RevealState.bindVar] at hnid
            by_cases hz : z = x
            · subst hz
              simp only [↓reduceIte, Option.some.injEq] at hnid
              subst hnid
              rw [(st₀.addNode cnd hcnd_deps).2.lookupDeps_addVar_eq_self_of_fresh z _ _ _
                (fun hm => hfresh.1 ((st₀.VarsSubCtx_addNode hvars cnd hcnd_deps) z hm))]
              rw [hcon₀.sync]
            · simp only [hz, reduceIte] at hnid
              rw [(st₀.addNode cnd hcnd_deps).2.lookupDeps_addVar_eq_of_ne x _ _ _ hz]
              exact hdt z nid hnid)
        (by -- hhn: hidden vars have nodeOf; new var x: bindVar sets it
            intro z who' b' hv
            simp only [RevealState.addPublicNode, RevealState.bindVar]
            cases hv with
            | there hv' =>
                by_cases hz : z = x
                · subst hz; simp
                · simp only [hz, ↓reduceIte, ne_eq]
                  exact hhn z who' b' hv')
        (by -- hnsc: x in new context; old vars via hnsc
            intro z nid hnid
            simp only [RevealState.addPublicNode, RevealState.bindVar] at hnid
            simp only [List.map_cons, List.mem_cons]
            by_cases hz : z = x
            · left; exact hz
            · right
              simp only [hz, reduceIte] at hnid
              exact hnsc z nid hnid)
  | commit x who R k ih =>
      -- THE key case: new decision node + IH for continuation.
      -- New node's parents = viewDeps who Γ'. By hvar₀, each dep has
      -- revealTime ≤ nextId = d.val or is who's decision. ✓
      -- Old nodes: preserved by addNode, revealTime only decreases. ✓
      rename_i Γ' b
      simp only [computeReveals, MAIDCompileState.ofProg]
      let dnd : CompiledNode Player L B :=
        .decision b who (allValues B b) (allValues_ne_nil B b)
          (allValues_nodup B b) (st₀.viewDeps who Γ')
      have hdnd_deps : ∀ d ∈ dnd.parents ∪ dnd.obsParents, d < st₀.nextId := by
        intro d hd'
        simp only [CompiledNode.parents, CompiledNode.obsParents, Finset.union_idempotent,
          dnd] at hd'
        exact st₀.depsOfVars_lt _ d hd'
      have hdeps : ∀ d ∈ ({st₀.nextId} : Finset Nat), d < st₀.nextId + 1 := by
        intro d hd'; simp at hd'; omega
      exact ih hl.2 hd hfresh.2 _ _ _
        (revealConsistent_addDecision' hcon₀ dnd rfl hdnd_deps x (.hidden who b) hdeps)
        ((st₀.addNode dnd hdnd_deps).2.VarsSubCtx_addVar
          (st₀.VarsSubCtx_addNode hvars dnd hdnd_deps)
          x _ _ _ hfresh.1)
        (by -- hprev: old decisions + NEW decision
            intro d' pw' hk' i hi'
            have hbound : d'.val ≤ st₀.nextId := by
              have := d'.isLt
              simp [MAIDCompileState.addNode, MAIDCompileState.addVar] at this
              omega
            rcases Nat.lt_or_eq_of_le hbound with hlt | heq
            · -- OLD decision node
              have hk_old : (st₀.descAt ⟨d'.val, hlt⟩).kind = .decision pw' := by
                rw [← MAIDCompileState.addNode_descAt_old st₀ dnd hdnd_deps ⟨d'.val, hlt⟩]
                exact hk'
              have hi_old : i ∈ (st₀.descAt ⟨d'.val, hlt⟩).parents := by
                rw [← MAIDCompileState.addNode_descAt_old st₀ dnd hdnd_deps ⟨d'.val, hlt⟩]
                exact hi'
              have hilt : i < st₀.nextId := Nat.lt_trans (st₀.descAt_parent_lt ⟨d'.val, hlt⟩ hi_old)
                (by omega)
              rcases hprev ⟨d'.val, hlt⟩ pw' hk_old i hi_old with h | h
              · left
                simp only [RevealState.addPrivateNode, RevealState.bindVar]; exact h
              · right
                have : ((st₀.addNode dnd hdnd_deps).2.addVar x (.hidden who b)
                      {st₀.nextId} hdeps).descAt
                    ⟨i, by
                      simp [MAIDCompileState.addNode, MAIDCompileState.addVar]
                      omega⟩ =
                    st₀.descAt ⟨i, hilt⟩ := by
                  change (st₀.addNode dnd hdnd_deps).2.descAt ⟨i, _⟩ = _
                  exact MAIDCompileState.addNode_descAt_old st₀ dnd hdnd_deps ⟨i, hilt⟩
                rw [this]; exact h
            · -- NEW decision: convert d' → st₀.nextId, extract pw'=who and parents=viewDeps
              have hdesc_new : (st₀.addNode dnd hdnd_deps).2.descAt
                  ⟨st₀.nextId, by simp [MAIDCompileState.addNode]⟩ = dnd :=
                MAIDCompileState.addNode_descAt_new st₀ dnd hdnd_deps
              -- Convert via show + hdesc_new
              have hpw : pw' = who := by
                have : dnd.kind = .decision pw' := by
                  have h1 := hk'
                  rw [show d' = ⟨
                        st₀.nextId,
                        by simp [MAIDCompileState.addNode, MAIDCompileState.addVar]⟩
                      from Fin.ext heq] at h1
                  change ((st₀.addNode dnd hdnd_deps).2.descAt ⟨st₀.nextId, _⟩).kind = _ at h1
                  rw [hdesc_new] at h1; exact h1
                simp only [dnd, CompiledNode.kind, NodeKind.decision.injEq] at this; exact this.symm
              subst hpw
              have hi_dnd : i ∈ dnd.parents := by
                have h1 := hi'; rw [show d' = (⟨st₀.nextId, by
                  simp only [MAIDCompileState.addVar, MAIDCompileState.addNode,
                    lt_add_iff_pos_right, zero_lt_one]⟩ : Fin _) from Fin.ext heq] at h1
                change i ∈ ((st₀.addNode dnd hdnd_deps).2.descAt ⟨st₀.nextId, _⟩).parents at h1
                rw [hdesc_new] at h1; exact h1
              have hi_vd : i ∈ st₀.viewDeps pw' Γ' := by
                simp only [CompiledNode.parents, dnd] at hi_dnd; exact hi_dnd
              rw [MAIDCompileState.viewDeps] at hi_vd
              obtain ⟨y, hy_mem, hy_dep⟩ := (mem_depsOfVars_iff st₀ _ i).mp hi_vd
              obtain ⟨⟨y', σ⟩, hys_mem, hys_fst⟩ := List.mem_map.mp hy_mem
              simp only at hys_fst
              subst hys_fst
              rcases hvar₀ pw' y' σ hys_mem i hy_dep with h | h
              · left; simp only [RevealState.addPrivateNode, RevealState.bindVar]
                exact le_trans h (by rw [heq])
              · right
                have hilt : i < st₀.nextId := st₀.depsOfVars_lt _ i hi_vd
                have : ((st₀.addNode dnd hdnd_deps).2.addVar x
                  (.hidden pw' b) {st₀.nextId} hdeps).descAt
                    ⟨i, by simp [MAIDCompileState.addNode, MAIDCompileState.addVar]; omega⟩ =
                    st₀.descAt ⟨i, hilt⟩ := by
                  change (st₀.addNode dnd hdnd_deps).2.descAt ⟨i, _⟩ = _
                  exact MAIDCompileState.addNode_descAt_old st₀ dnd hdnd_deps ⟨i, hilt⟩
                rw [this]; exact h)
        (varVisible_addNode_decision_addVar st₀ rs₀ hcon₀ dnd who
          rfl hdnd_deps x b _ hvars hfresh.1 hdeps hvar₀)
        (by intro z nid hnid
            simp only [RevealState.addPrivateNode, RevealState.bindVar] at hnid
            by_cases hz : z = x
            · subst hz
              simp only [↓reduceIte, Option.some.injEq] at hnid
              subst hnid
              rw [(st₀.addNode dnd hdnd_deps).2.lookupDeps_addVar_eq_self_of_fresh z _ _ _
                (fun hm => hfresh.1 ((st₀.VarsSubCtx_addNode hvars dnd hdnd_deps) z hm))]
              rw [hcon₀.sync]
            · simp only [hz, ite_false] at hnid
              rw [(st₀.addNode dnd hdnd_deps).2.lookupDeps_addVar_eq_of_ne x _ _ _ hz]
              exact hdt z nid hnid)
        (by intro z who' b' hv
            simp only [RevealState.addPrivateNode, RevealState.bindVar]
            cases hv with
            | here => simp
            | there hv' =>
                by_cases hz : z = x
                · subst hz; simp
                · simp only [hz, ite_false]; exact hhn z who' b' hv')
        (by intro z nid hnid
            simp only [RevealState.addPrivateNode, RevealState.bindVar] at hnid
            simp only [List.map_cons, List.mem_cons]
            by_cases hz : z = x
            · left; exact hz
            · right; simp only [hz, ite_false] at hnid; exact hnsc z nid hnid)
  | reveal y who x hx k ih =>
      simp only [computeReveals, MAIDCompileState.ofProg]
      exact ih hl hd hfresh.2 _ _ _
        (revealConsistent_reveal' hcon₀ y x _ _ _)
        (st₀.VarsSubCtx_addVar hvars y _ _ _ hfresh.1)
        (by -- hprev: addVar doesn't change descAt, reveal only decreases revealTime
            intro d pw hk i hi
            rcases hprev d pw hk i hi with h | h
            · left; exact le_trans (by
                simp only [RevealState.aliasVar]
                split
                · rename_i nid hx_eq; simp only
                  by_cases heq : i = nid
                  · rw [if_pos heq]; exact min_le_right _ _
                  · rw [if_neg heq]
                · exact le_refl _) h
            · right; exact h)
        (varVisible_reveal st₀ rs₀ y x _ who _ hx hvars hfresh.1 hvar₀ hdt hhn hcon₀)
        (by -- hdt: z=y → copy from x; z≠y → from hdt
            intro z nid hnid
            simp only [RevealState.aliasVar] at hnid
            by_cases hz : z = y
            · subst hz
              simp only [reduceIte] at hnid
              rw [st₀.lookupDeps_addVar_eq_self_of_fresh z _ _ _
                (fun hm => hfresh.1 (hvars z hm))]
              split at hnid <;> exact hdt x nid hnid
            · simp only [hz, ite_false] at hnid
              rw [st₀.lookupDeps_addVar_eq_of_ne y _ _ _ hz]
              split at hnid <;> exact hdt z nid hnid)
        (by -- hhn: y is pub (not hidden); old vars: aliasVar only changes y's nodeOf
            intro z who' b' hv
            cases hv with
            | there hv' =>
                simp only [RevealState.aliasVar]
                by_cases hz : z = y
                · -- z = y: nodeOf through aliasVar+match = nodeOf x
                  subst hz
                  change ((match rs₀.nodeOf x with
                    | some nid => { rs₀ with revealTime := _ }
                    | none => rs₀).aliasVar z x).nodeOf z ≠ none
                  simp only [RevealState.aliasVar]
                  cases rs₀.nodeOf x <;> simp only [↓reduceIte, ne_eq]
                  · exact hhn x who _ hx
                  · exact hhn x who _ hx
                · -- z ≠ y: same structure, use cases on rs₀.nodeOf x
                  cases rs₀.nodeOf x
                  · -- none: aliasVar.nodeOf z = if z=y then rs₀.nodeOf x else rs₀.nodeOf z
                    simp only
                    rw [if_neg hz]; exact hhn z who' b' hv'
                  · -- some nid: same
                    simp only
                    rw [if_neg hz]; exact hhn z who' b' hv')
        (by -- hnsc: y in new context; old vars via hnsc
            intro z nid hnid
            simp only [RevealState.aliasVar] at hnid
            simp only [List.map_cons, List.mem_cons]
            by_cases hz : z = y
            · left; exact hz
            · right; simp only [hz, ite_false] at hnid; split at hnid <;> exact hnsc z nid hnid)

/-- The main experimental compilation function: Vegas program → VegasMAID. -/
noncomputable def compileVegasMAID
    (B : MAIDBackend Player L)
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (hfresh : FreshBindings p)
    (hpub : ∀ y who b, VHasVar (L := L) Γ y (.hidden who b) → False)
    (env : VEnv (Player := Player) L Γ) :
    let st := MAIDCompileState.ofProg B p hl hd (fun _ => env) .empty
    VegasMAID Player st.nextId :=
  let st := MAIDCompileState.ofProg B p hl hd (fun _ => env) .empty
  let rs := computeReveals B p .empty
  let hcon : RevealConsistent .empty .empty :=
    ⟨rfl, fun nd => nd.elim0, fun nd => nd.elim0,
     fun _ _ h => by simp [RevealState.empty] at h,
     fun _ _ => rfl⟩
  toVegasMAID B st rs
    (computeReveals_consistent B p hl hd _ _ _ hcon)
    (computeReveals_parents_visible B p hl hd hfresh _ _ _ hcon
      (by intro x hx; simp [MAIDCompileState.empty] at hx)
      (fun d => d.elim0)
      (by intro who y σ hy i hi; exfalso;
          simp [MAIDCompileState.empty, MAIDCompileState.lookupDeps,
                MAIDCompileState.lookupDepsAux] at hi)
      (by intro y nid h; simp [RevealState.empty] at h)
      (by intro y who b hv; exact (hpub y who b hv).elim)
      (by intro y nid h; simp [RevealState.empty] at h))

end Vegas
