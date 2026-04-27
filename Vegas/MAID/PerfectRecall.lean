import Vegas.MAID.Defs

/-!
# Perfect Recall for VegasMAID

A well-formed Vegas program (`FreshBindings p`) compiles to a VegasMAID struct
with perfect recall (`Struct.PerfectRecall`).

All supporting lemmas work at the `MAIDCompileState` level (with `descAt`).
The final theorem translates to the `compiledStruct` (= `VegasMAID.toStruct`)
level, exploiting `obsParents = parents` definitionally.
-/

namespace Vegas

open MAID

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr} {B : MAIDBackend Player L}

/-! ## Helper lemmas -/

/-- For all compiled nodes, `parents = obsParents`. -/
theorem CompiledNode.parents_eq_obsParents' (nd : CompiledNode Player L B) :
    nd.parents = nd.obsParents := by
  cases nd <;> rfl

/-- A parent in `MAIDCompileState.toStruct` has strictly smaller `val`. -/
private theorem MAIDCompileState.toStruct_parent_val_lt'
    (st : MAIDCompileState Player L B)
    (a b : Fin st.nextId)
    (h : a ∈ st.toStruct.parents b) :
    a.val < b.val := by
  change a ∈ (st.descAt b).parents.attach.image _ at h
  rw [Finset.mem_image] at h
  obtain ⟨⟨x, hx⟩, _, heq⟩ := h
  exact (congr_arg Fin.val heq) ▸ st.descAt_parent_lt b hx

/-- `IsAncestor d₁ d₂` implies `d₁.val < d₂.val`. -/
private theorem MAIDCompileState.isAncestor_val_lt'
    (st : MAIDCompileState Player L B)
    (d₁ d₂ : Fin st.nextId)
    (h : st.toStruct.IsAncestor d₁ d₂) :
    d₁.val < d₂.val := by
  induction h with
  | single hp => exact st.toStruct_parent_val_lt' _ _ hp
  | tail _ hp ih => exact Nat.lt_trans ih (st.toStruct_parent_val_lt' _ _ hp)

/-! ## viewDeps monotonicity helpers -/

/-- `addNode` does not change `viewDeps` (since it does not change `vars`). -/
private theorem MAIDCompileState.viewDeps_addNode_eq'
    (st : MAIDCompileState Player L B)
    (nd : CompiledNode Player L B)
    (hdeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId)
    (who : Player) (Γ : VCtx Player L) :
    (st.addNode nd hdeps).2.viewDeps who Γ = st.viewDeps who Γ := by
  unfold viewDeps
  have : ∀ xs : List VarId,
      (st.addNode nd hdeps).2.depsOfVars xs = st.depsOfVars xs := by
    intro xs; induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [depsOfVars]
      rw [MAIDCompileState.lookupDeps_addNode, ih]
  exact this _

/-! ## Core property: same-player decisions have monotone observation sets -/

/-- The decision-monotonicity invariant for a compile state. -/
private def MAIDCompileState.DecisionMonotone' (st : MAIDCompileState Player L B) : Prop :=
  ∀ (who : Player) (d₁ d₂ : Fin st.nextId),
    (st.descAt d₁).kind = .decision who →
    (st.descAt d₂).kind = .decision who →
    d₁.val < d₂.val →
    d₁.val ∈ (st.descAt d₂).obsParents ∧
      (st.descAt d₁).obsParents ⊆ (st.descAt d₂).obsParents

/-- Decision nodes' IDs and obsParents are all in `viewDeps who Γ`. -/
private def MAIDCompileState.DecisionVisible'
    (st : MAIDCompileState Player L B) (Γ : VCtx Player L) : Prop :=
  ∀ (who : Player) (d : Fin st.nextId),
    (st.descAt d).kind = .decision who →
    d.val ∈ st.viewDeps who Γ ∧
      (st.descAt d).obsParents ⊆ st.viewDeps who Γ

/-! ## DecisionMonotone preservation lemmas -/

/-- `addUtilityNodes` preserves `DecisionMonotone'` (new nodes are all utility). -/
private theorem MAIDCompileState.DecisionMonotone_addUtilityNodes'
    (st : MAIDCompileState Player L B)
    (deps : Finset Nat) (hdeps : ∀ d ∈ deps, d < st.nextId)
    (ufn : Player → RawNodeEnv L → ℝ) (players : List Player)
    (hmon : st.DecisionMonotone') :
    (st.addUtilityNodes deps hdeps ufn players).DecisionMonotone' := by
  intro who d₁ d₂ hk₁ hk₂ hlt
  have old₁ : d₁.val < st.nextId := by
    by_contra hge; push Not at hge
    have ⟨w, hw⟩ := addUtilityNodes_all_utility st deps hdeps ufn players d₁ hge
    rw [hw] at hk₁; exact nomatch hk₁
  have old₂ : d₂.val < st.nextId := by
    by_contra hge; push Not at hge
    have ⟨w, hw⟩ := addUtilityNodes_all_utility st deps hdeps ufn players d₂ hge
    rw [hw] at hk₂; exact nomatch hk₂
  have h₁ : (st.addUtilityNodes deps hdeps ufn players).descAt d₁ =
      st.descAt ⟨d₁.val, old₁⟩ := by
    convert addUtilityNodes_descAt_old st deps hdeps ufn players d₁.val old₁ using 2
  have h₂ : (st.addUtilityNodes deps hdeps ufn players).descAt d₂ =
      st.descAt ⟨d₂.val, old₂⟩ := by
    convert addUtilityNodes_descAt_old st deps hdeps ufn players d₂.val old₂ using 2
  rw [h₁] at hk₁ ⊢; rw [h₂] at hk₂ ⊢
  exact hmon who ⟨d₁.val, old₁⟩ ⟨d₂.val, old₂⟩ hk₁ hk₂ hlt

/-- `addVar` of a fresh variable preserves `DecisionVisible'` for extended context. -/
private theorem MAIDCompileState.DecisionVisible_addVar_cons'
    (st : MAIDCompileState Player L B)
    (x : VarId) (τ : BindTy Player L) (deps : Finset Nat)
    (hdeps : ∀ d ∈ deps, d < st.nextId)
    {Γ : VCtx Player L}
    (hfreshΓ : Fresh x Γ)
    (hvis : st.DecisionVisible' Γ) :
    (st.addVar x τ deps hdeps).DecisionVisible' ((x, τ) :: Γ) := by
  intro who d hkd
  have hkd' : (st.descAt d).kind = .decision who := hkd
  obtain ⟨hmem, hsub⟩ := hvis who d hkd'
  have hview_sub : st.viewDeps who Γ ⊆
      (st.addVar x τ deps hdeps).viewDeps who ((x, τ) :: Γ) := by
    intro d' hd'
    unfold viewDeps
    simp only [viewVCtx]
    split
    · simp only [List.map, depsOfVars]
      exact Finset.mem_union_right _
        (depsOfVars_addVar_eq_of_fresh st x τ deps hdeps
          ((viewVCtx who Γ).map Prod.fst)
          (fun h => hfreshΓ (viewVCtx_map_fst_sub h)) ▸ hd')
    · exact depsOfVars_addVar_eq_of_fresh st x τ deps hdeps
        ((viewVCtx who Γ).map Prod.fst)
        (fun h => hfreshΓ (viewVCtx_map_fst_sub h)) ▸ hd'
  exact ⟨hview_sub hmem, fun d' hd' => hview_sub (hsub hd')⟩

/-- `addNode` of non-decision + `addVar` preserves `DecisionMonotone'`. -/
private theorem MAIDCompileState.DecisionMonotone_addNode_addVar_nonDec'
    (st : MAIDCompileState Player L B)
    (nd : CompiledNode Player L B)
    (hndeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId)
    (x : VarId) (τ : BindTy Player L)
    (hdeps : ∀ d ∈ ({st.nextId} : Finset Nat), d < (st.addNode nd hndeps).2.nextId)
    (hmon : st.DecisionMonotone')
    (hnotDec : ∀ who, nd.kind ≠ .decision who) :
    ((st.addNode nd hndeps).2.addVar x τ {st.nextId} hdeps).DecisionMonotone' := by
  intro who d₁ d₂ hk₁ hk₂ hlt
  have old (d : Fin _) (hkd : (((st.addNode nd hndeps).2.addVar x τ _ hdeps).descAt d).kind =
      .decision who) : d.val < st.nextId := by
    by_contra hge; push Not at hge
    have heq : d.val = st.nextId := by
      have := d.isLt; simp [MAIDCompileState.addVar, MAIDCompileState.addNode] at this; omega
    have hdesc : ((st.addNode nd hndeps).2.addVar x τ _ hdeps).descAt d = nd := by
      simp [MAIDCompileState.addVar, MAIDCompileState.addNode, heq]
    rw [hdesc] at hkd; exact absurd hkd (fun h => hnotDec who h)
  have old₁ := old d₁ hk₁; have old₂ := old d₂ hk₂
  have hdesc (d : Fin _) (hold : d.val < st.nextId) :
      ((st.addNode nd hndeps).2.addVar x τ _ hdeps).descAt d = st.descAt ⟨d.val, hold⟩ := by
    simp [MAIDCompileState.addVar, MAIDCompileState.addNode, show d.val < st.nextId from hold]
  rw [hdesc d₁ old₁] at hk₁ ⊢; rw [hdesc d₂ old₂] at hk₂ ⊢
  exact hmon who ⟨d₁.val, old₁⟩ ⟨d₂.val, old₂⟩ hk₁ hk₂ hlt

/-- `addNode + addVar` of non-decision node preserves `DecisionVisible'`. -/
private theorem MAIDCompileState.DecisionVisible_addNode_addVar_cons'
    (st : MAIDCompileState Player L B)
    (nd : CompiledNode Player L B)
    (hndeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId)
    (x : VarId) (τ : BindTy Player L)
    (hdeps : ∀ d ∈ ({st.nextId} : Finset Nat), d < (st.addNode nd hndeps).2.nextId)
    {Γ : VCtx Player L} (hfreshΓ : Fresh x Γ)
    (hvis : st.DecisionVisible' Γ)
    (hnotDec : ∀ who, nd.kind ≠ .decision who) :
    ((st.addNode nd hndeps).2.addVar x τ {st.nextId} hdeps).DecisionVisible'
      ((x, τ) :: Γ) := by
  intro who d hkd
  have hold : d.val < st.nextId := by
    by_contra hge; push Not at hge
    have heq : d.val = st.nextId := by
      have := d.isLt; simp [MAIDCompileState.addVar, MAIDCompileState.addNode] at this; omega
    have hdesc : ((st.addNode nd hndeps).2.addVar x τ _ hdeps).descAt d = nd := by
      simp [MAIDCompileState.addVar, MAIDCompileState.addNode, heq]
    rw [hdesc] at hkd; exact absurd hkd (fun h => hnotDec who h)
  have hdesc : ((st.addNode nd hndeps).2.addVar x τ _ hdeps).descAt d =
      st.descAt ⟨d.val, hold⟩ := by
    simp [MAIDCompileState.addVar, MAIDCompileState.addNode, show d.val < st.nextId from hold]
  rw [hdesc] at hkd ⊢
  obtain ⟨hmem, hsub⟩ := hvis who ⟨d.val, hold⟩ hkd
  have hview_sub : st.viewDeps who Γ ⊆
      ((st.addNode nd hndeps).2.addVar x τ _ hdeps).viewDeps who ((x, τ) :: Γ) := by
    intro d' hd'
    have hd'' : d' ∈ (st.addNode nd hndeps).2.viewDeps who Γ :=
      viewDeps_addNode_eq' st nd hndeps who Γ ▸ hd'
    unfold viewDeps at hd'' ⊢
    simp only [viewVCtx]
    split
    · simp only [List.map, depsOfVars]
      exact Finset.mem_union_right _
        (depsOfVars_addVar_eq_of_fresh (st.addNode nd hndeps).2 x τ _ hdeps
          ((viewVCtx who Γ).map Prod.fst)
          (fun h => hfreshΓ (viewVCtx_map_fst_sub h)) ▸ hd'')
    · exact depsOfVars_addVar_eq_of_fresh (st.addNode nd hndeps).2 x τ _ hdeps
        ((viewVCtx who Γ).map Prod.fst)
        (fun h => hfreshΓ (viewVCtx_map_fst_sub h)) ▸ hd''
  exact ⟨hview_sub hmem, fun d' hd' => hview_sub (hsub hd')⟩

/-- Helper: descAt for the addNode+addVar state equals st's descAt for old nodes. -/
private theorem MAIDCompileState.descAt_addNode_addVar'
    (st : MAIDCompileState Player L B)
    (nd : CompiledNode Player L B)
    (hndeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId)
    (x : VarId) (τ : BindTy Player L)
    (hdeps : ∀ d ∈ ({st.nextId} : Finset Nat), d < (st.addNode nd hndeps).2.nextId)
    (d : Fin ((st.addNode nd hndeps).2.addVar x τ {st.nextId} hdeps).nextId)
    (hold : d.val < st.nextId) :
    ((st.addNode nd hndeps).2.addVar x τ {st.nextId} hdeps).descAt d =
      st.descAt ⟨d.val, hold⟩ := by
  simp [MAIDCompileState.addVar, MAIDCompileState.addNode, show d.val < st.nextId from hold]

private theorem MAIDCompileState.descAt_addNode_addVar_new'
    (st : MAIDCompileState Player L B)
    (nd : CompiledNode Player L B)
    (hndeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId)
    (x : VarId) (τ : BindTy Player L)
    (hdeps : ∀ d ∈ ({st.nextId} : Finset Nat), d < (st.addNode nd hndeps).2.nextId)
    (d : Fin ((st.addNode nd hndeps).2.addVar x τ {st.nextId} hdeps).nextId)
    (heq : d.val = st.nextId) :
    ((st.addNode nd hndeps).2.addVar x τ {st.nextId} hdeps).descAt d = nd := by
  simp [MAIDCompileState.addVar, MAIDCompileState.addNode, heq]

private theorem MAIDCompileState.val_lt_or_eq_of_addNode_addVar'
    (st : MAIDCompileState Player L B)
    (nd : CompiledNode Player L B)
    (hndeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId)
    (x : VarId) (τ : BindTy Player L)
    (hdeps : ∀ d ∈ ({st.nextId} : Finset Nat), d < (st.addNode nd hndeps).2.nextId)
    (d : Fin ((st.addNode nd hndeps).2.addVar x τ {st.nextId} hdeps).nextId) :
    d.val < st.nextId ∨ d.val = st.nextId := by
  have := d.isLt; simp [MAIDCompileState.addVar, MAIDCompileState.addNode] at this; omega

/-- `addNode(.decision) + addVar` preserves `DecisionMonotone'` using `DecisionVisible'`. -/
private theorem MAIDCompileState.DecisionMonotone_addNode_addVar_decision'
    (st : MAIDCompileState Player L B)
    (nd : CompiledNode Player L B)
    (hndeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId)
    (x : VarId) (τ : BindTy Player L)
    (hdeps : ∀ d ∈ ({st.nextId} : Finset Nat), d < (st.addNode nd hndeps).2.nextId)
    {Γ : VCtx Player L} (owner : Player)
    (hmon : st.DecisionMonotone')
    (hvis : st.DecisionVisible' Γ)
    (hobs : nd.obsParents = st.viewDeps owner Γ)
    (hkind : nd.kind = .decision owner) :
    ((st.addNode nd hndeps).2.addVar x τ {st.nextId} hdeps).DecisionMonotone' := by
  intro who d₁ d₂ hk₁ hk₂ hlt
  rcases st.val_lt_or_eq_of_addNode_addVar' nd hndeps x τ hdeps d₁ with old₁ | new₁
  · rw [st.descAt_addNode_addVar' nd hndeps x τ hdeps d₁ old₁] at hk₁ ⊢
    rcases st.val_lt_or_eq_of_addNode_addVar' nd hndeps x τ hdeps d₂ with old₂ | new₂
    · rw [st.descAt_addNode_addVar' nd hndeps x τ hdeps d₂ old₂] at hk₂ ⊢
      exact hmon who ⟨d₁.val, old₁⟩ ⟨d₂.val, old₂⟩ hk₁ hk₂ hlt
    · rw [st.descAt_addNode_addVar_new' nd hndeps x τ hdeps d₂ new₂] at hk₂ ⊢
      rw [hobs]
      have hwho : who = owner := by rw [hkind] at hk₂; exact (NodeKind.decision.inj hk₂).symm
      rw [hwho] at hk₁
      exact hvis owner ⟨d₁.val, old₁⟩ hk₁
  · rcases st.val_lt_or_eq_of_addNode_addVar' nd hndeps x τ hdeps d₂ with old₂ | new₂
    · omega
    · omega

/-- `addNode(.decision) + addVar` preserves `DecisionVisible'` for commit context extension. -/
private theorem MAIDCompileState.DecisionVisible_addNode_addVar_cons_decision'
    (st : MAIDCompileState Player L B)
    (nd : CompiledNode Player L B)
    (hndeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId)
    (x : VarId) (τ : BindTy Player L)
    (hdeps : ∀ d ∈ ({st.nextId} : Finset Nat), d < (st.addNode nd hndeps).2.nextId)
    {Γ : VCtx Player L} (hfreshΓ : Fresh x Γ)
    (hvis : st.DecisionVisible' Γ)
    (owner : Player) (bty : L.Ty)
    (hobs : nd.obsParents = st.viewDeps owner Γ)
    (hkind : nd.kind = .decision owner)
    (hcanSee : τ = .hidden owner bty)
    (hfreshVars : x ∉ st.vars.map Prod.fst) :
    ((st.addNode nd hndeps).2.addVar x τ {st.nextId} hdeps).DecisionVisible'
      ((x, τ) :: Γ) := by
  have hview_sub : ∀ who, st.viewDeps who Γ ⊆
      ((st.addNode nd hndeps).2.addVar x τ _ hdeps).viewDeps who ((x, τ) :: Γ) := by
    intro who d' hd'
    have hd'' : d' ∈ (st.addNode nd hndeps).2.viewDeps who Γ :=
      viewDeps_addNode_eq' st nd hndeps who Γ ▸ hd'
    unfold viewDeps at hd'' ⊢
    simp only [viewVCtx]; split
    · simp only [List.map, depsOfVars]
      exact Finset.mem_union_right _
        (depsOfVars_addVar_eq_of_fresh (st.addNode nd hndeps).2 x τ _ hdeps
          ((viewVCtx who Γ).map Prod.fst)
          (fun h => hfreshΓ (viewVCtx_map_fst_sub h)) ▸ hd'')
    · exact depsOfVars_addVar_eq_of_fresh (st.addNode nd hndeps).2 x τ _ hdeps
        ((viewVCtx who Γ).map Prod.fst)
        (fun h => hfreshΓ (viewVCtx_map_fst_sub h)) ▸ hd''
  intro who d hkd
  rcases st.val_lt_or_eq_of_addNode_addVar' nd hndeps x τ hdeps d with hold | hnew
  · rw [st.descAt_addNode_addVar' nd hndeps x τ hdeps d hold] at hkd ⊢
    obtain ⟨hmem, hsub⟩ := hvis who ⟨d.val, hold⟩ hkd
    exact ⟨hview_sub who hmem, fun d' hd' => hview_sub who (hsub hd')⟩
  · rw [st.descAt_addNode_addVar_new' nd hndeps x τ hdeps d hnew] at hkd ⊢
    have hwho : who = owner := by rw [hkind] at hkd; exact (NodeKind.decision.inj hkd).symm
    subst hwho
    constructor
    · unfold viewDeps viewVCtx
      rw [hcanSee]
      simp only [canSee, decide_true, ↓reduceIte, List.map_cons]
      simp only [depsOfVars]
      apply Finset.mem_union_left
      have hfv : x ∉ (st.addNode nd hndeps).2.vars.map Prod.fst := by
        simp only [MAIDCompileState.addNode]; exact hfreshVars
      rw [lookupDeps_addVar_eq_self_of_fresh _ x _ _ _ hfv, hnew]
      simp
    · rw [hobs]; exact hview_sub who

/-- Generalized induction: `ofProg` preserves `DecisionMonotone'` when started
from a state satisfying both `DecisionMonotone'` and `DecisionVisible'`. -/
private theorem MAIDCompileState.ofProg_preserves_decision_monotone'
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ) (hl : Legal p)
    (hd : NormalizedDists p) (hfresh : FreshBindings p)
    (ρ : RawNodeEnv L → VEnv (Player := Player) L Γ)
    (st₀ : MAIDCompileState Player L B)
    (hmon : st₀.DecisionMonotone')
    (hvis : st₀.DecisionVisible' Γ)
    (hvs : ∀ y, y ∈ st₀.vars.map Prod.fst → y ∈ Γ.map Prod.fst) :
    (MAIDCompileState.ofProg B p hl hd ρ st₀).DecisionMonotone' := by
  induction p generalizing st₀ with
  | ret payoffs =>
    simp only [ofProg]
    exact DecisionMonotone_addUtilityNodes' st₀ _ _ _ _ hmon
  | letExpr _ _ k ih =>
    simp only [ofProg]
    refine ih hl hd hfresh.2 _ _ hmon (DecisionVisible_addVar_cons' st₀ _ _ _ _ hfresh.1 hvis) ?_
    intro y hy
    simp only [MAIDCompileState.addVar, List.map_append, List.mem_append, List.map] at hy
    rcases hy with h | h
    · exact List.mem_cons_of_mem _ (hvs y h)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h; exact List.Mem.head _
  | sample _ _ k ih =>
    refine ih hl hd.2 hfresh.2 _ _ ?_ ?_ ?_
    · exact DecisionMonotone_addNode_addVar_nonDec' st₀ _ _ _ _ _ hmon
        (fun who h => by simp [CompiledNode.kind] at h)
    · exact DecisionVisible_addNode_addVar_cons' st₀ _ _ _ _ _ hfresh.1 hvis
        (fun who h => by simp [CompiledNode.kind] at h)
    · intro y hy
      simp only [MAIDCompileState.addVar, MAIDCompileState.addNode,
        List.map_append, List.mem_append, List.map] at hy
      rcases hy with h | h
      · exact List.mem_cons_of_mem _ (hvs y h)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h; exact List.Mem.head _
  | commit x who_c R k ih =>
    refine ih hl.2 hd hfresh.2 _ _ ?_ ?_ ?_
    · exact DecisionMonotone_addNode_addVar_decision' st₀ _ _ _ _ _ who_c hmon hvis rfl rfl
    · exact DecisionVisible_addNode_addVar_cons_decision'
        st₀ _ _ _ _ _ hfresh.1 hvis who_c _ rfl rfl rfl
        (fun h => hfresh.1 (hvs _ h))
    · intro y hy
      simp only [MAIDCompileState.addVar, MAIDCompileState.addNode,
        List.map_append, List.mem_append, List.map] at hy
      rcases hy with h | h
      · exact List.mem_cons_of_mem _ (hvs y h)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h; exact List.Mem.head _
  | reveal _ _ _ _ k ih =>
    refine ih hl hd hfresh.2 _ _ ?_ ?_ ?_
    · exact hmon
    · exact DecisionVisible_addVar_cons' st₀ _ _ _ _ hfresh.1 hvis
    · intro y hy
      simp only [MAIDCompileState.addVar, List.map_append, List.mem_append, List.map] at hy
      rcases hy with h | h
      · exact List.mem_cons_of_mem _ (hvs y h)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h; exact List.Mem.head _

/-- For any two decision nodes of the same player with `d₁.val < d₂.val`,
`d₁` is a direct obsParent of `d₂` and d₁'s obsParents are a subset of d₂'s. -/
private theorem MAIDCompileState.ofProg_decision_obs_monotone'
    {Γ : VCtx Player L}
    (p : VegasCore Player L Γ) (env : VEnv (Player := Player) L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (hfresh : FreshBindings p) :
    let st := MAIDCompileState.ofProg B p hl hd (fun _ => env) .empty
    ∀ (who : Player) (d₁ d₂ : Fin st.nextId),
      (st.descAt d₁).kind = .decision who →
      (st.descAt d₂).kind = .decision who →
      d₁.val < d₂.val →
      d₁.val ∈ (st.descAt d₂).obsParents ∧
        (st.descAt d₁).obsParents ⊆ (st.descAt d₂).obsParents := by
  intro st
  exact ofProg_preserves_decision_monotone' p hl hd hfresh (fun _ => env)
    .empty
    (fun _ d₁ _ _ _ _ => absurd d₁.isLt (Nat.not_lt_zero _))
    (fun _ d _ => absurd d.isLt (Nat.not_lt_zero _))
    (fun _ h => by simp [MAIDCompileState.empty] at h)

/-! ## Main theorem -/

/-- The compiled VegasMAID structure has perfect recall. -/
theorem compiledStruct_perfectRecallV
    (B : MAIDBackend Player L) {Γ : VCtx Player L}
    (p : VegasCore Player L Γ) (env : VEnv (Player := Player) L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (hfresh : FreshBindings p)
    (hpub : ∀ y who b, VHasVar (L := L) Γ y (.hidden who b) → False) :
    (compiledStruct B p env hl hd hfresh hpub).PerfectRecall := by
  set st := compiledState B p env hl hd with hst
  set S := compiledStruct B p env hl hd hfresh hpub
  have core := MAIDCompileState.ofProg_decision_obs_monotone' (B := B) p env hl hd hfresh
  -- S.kind, S.parents are definitionally equal to st.toStruct's
  -- S.obsParents = S.parents (VegasMAID property)
  -- Helper to convert between S.parents and descAt.parents
  have mem_parents_iff : ∀ (nd : Fin st.nextId) {i : Nat} (hi : i < st.nextId),
      (⟨i, hi⟩ : Fin st.nextId) ∈ S.parents nd ↔
        i ∈ (st.descAt nd).parents :=
    fun nd _ hi => st.mem_toStruct_parents_iff nd hi
  unfold Struct.PerfectRecall
  constructor
  · -- Part 1: Temporal ordering
    intro who d₁ d₂ hk₁ hk₂ hne
    -- S.kind = (st.descAt _).kind definitionally
    change (st.descAt d₁).kind = _ at hk₁
    change (st.descAt d₂).kind = _ at hk₂
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
    · left
      apply Struct.parent_isAncestor
      change ⟨d₁.val, d₁.isLt⟩ ∈ S.parents d₂
      rw [mem_parents_iff d₂ d₁.isLt, CompiledNode.parents_eq_obsParents']
      exact (core who d₁ d₂ hk₁ hk₂ hlt).1
    · right
      apply Struct.parent_isAncestor
      change ⟨d₂.val, d₂.isLt⟩ ∈ S.parents d₁
      rw [mem_parents_iff d₁ d₂.isLt, CompiledNode.parents_eq_obsParents']
      exact (core who d₂ d₁ hk₂ hk₁ hgt).1
  · -- Part 2: Full observation
    intro who d₁ d₂ hk₁ hk₂ hanc
    change (st.descAt d₁).kind = _ at hk₁
    change (st.descAt d₂).kind = _ at hk₂
    -- S.IsAncestor implies val ordering (parents are same as st.toStruct)
    have hlt : d₁.val < d₂.val := st.isAncestor_val_lt' d₁ d₂ hanc
    obtain ⟨hmem, hsub⟩ := core who d₁ d₂ hk₁ hk₂ hlt
    constructor
    · -- d₁ ∈ S.obsParents d₂; since obsParents = parents, show d₁ ∈ S.parents d₂
      change ⟨d₁.val, d₁.isLt⟩ ∈ S.parents d₂
      rw [mem_parents_iff d₂ d₁.isLt, CompiledNode.parents_eq_obsParents']
      exact hmem
    · -- ∀ x ∈ S.obsParents d₁, x ∈ S.obsParents d₂
      -- S.obsParents = S.parents definitionally (VegasMAID.toStruct)
      -- parents = obsParents on CompiledNode (parents_eq_obsParents')
      intro x hx
      -- hx : x ∈ S.obsParents d₁ = S.parents d₁ (def'l)
      -- Convert to descAt level: x.val ∈ (st.descAt d₁).obsParents
      have hx' : x.val ∈ (st.descAt d₁).obsParents := by
        rw [← CompiledNode.parents_eq_obsParents']
        exact (mem_parents_iff d₁ x.isLt).mp hx
      -- Apply hsub at descAt level
      have hx₂ : x.val ∈ (st.descAt d₂).obsParents := hsub hx'
      -- Convert back: show x ∈ S.obsParents d₂ = S.parents d₂
      change ⟨x.val, x.isLt⟩ ∈ S.parents d₂
      rw [mem_parents_iff d₂ x.isLt, CompiledNode.parents_eq_obsParents']
      exact hx₂

end Vegas
