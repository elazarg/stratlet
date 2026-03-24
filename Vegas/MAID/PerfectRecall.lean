import Vegas.MAID.Compile
import Vegas.MAID.Correctness

/-!
# Compiled Perfect Recall

A well-formed Vegas program (`WF p`) compiles to a MAID struct with perfect
recall (`Struct.PerfectRecall`).
-/

namespace Vegas

open MAID

variable {P : Type} [DecidableEq P] {L : IExpr} {B : MAIDBackend P L}

/-! ## Helper lemmas -/

/-- For all compiled nodes, `parents = obsParents`. -/
theorem CompiledNode.parents_eq_obsParents (nd : CompiledNode P L B) :
    nd.parents = nd.obsParents := by
  cases nd <;> rfl

/-- A parent in `toStruct` has strictly smaller `val`. -/
private theorem MAIDCompileState.toStruct_parent_val_lt
    (st : MAIDCompileState P L B)
    (a b : Fin st.nextId)
    (h : letI : Fintype P := B.fintypePlayer; a ∈ st.toStruct.parents b) :
    a.val < b.val := by
  letI : Fintype P := B.fintypePlayer
  change a ∈ (st.descAt b).parents.attach.image _ at h
  rw [Finset.mem_image] at h
  obtain ⟨⟨x, hx⟩, _, heq⟩ := h
  exact (congr_arg Fin.val heq) ▸ st.descAt_parent_lt b hx

/-- `IsAncestor d₁ d₂` implies `d₁.val < d₂.val`. -/
theorem MAIDCompileState.isAncestor_val_lt
    (st : MAIDCompileState P L B)
    (d₁ d₂ : Fin st.nextId)
    (h : letI : Fintype P := B.fintypePlayer; st.toStruct.IsAncestor d₁ d₂) :
    d₁.val < d₂.val := by
  letI : Fintype P := B.fintypePlayer
  induction h with
  | single hp => exact st.toStruct_parent_val_lt _ _ hp
  | tail _ hp ih => exact Nat.lt_trans ih (st.toStruct_parent_val_lt _ _ hp)

/-! ## viewDeps monotonicity helpers -/

/-- `addNode` does not change `viewDeps` (since it does not change `vars`). -/
theorem MAIDCompileState.viewDeps_addNode_eq
    (st : MAIDCompileState P L B)
    (nd : CompiledNode P L B)
    (hdeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId)
    (who : P) (Γ : VCtx P L) :
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
def MAIDCompileState.DecisionMonotone (st : MAIDCompileState P L B) : Prop :=
  ∀ (who : P) (d₁ d₂ : Fin st.nextId),
    (st.descAt d₁).kind = .decision who →
    (st.descAt d₂).kind = .decision who →
    d₁.val < d₂.val →
    d₁.val ∈ (st.descAt d₂).obsParents ∧
      (st.descAt d₁).obsParents ⊆ (st.descAt d₂).obsParents

/-- Decision nodes' IDs and obsParents are all in `viewDeps who Γ`. -/
def MAIDCompileState.DecisionVisible
    (st : MAIDCompileState P L B) (Γ : VCtx P L) : Prop :=
  ∀ (who : P) (d : Fin st.nextId),
    (st.descAt d).kind = .decision who →
    d.val ∈ st.viewDeps who Γ ∧
      (st.descAt d).obsParents ⊆ st.viewDeps who Γ

/-! ## DecisionMonotone preservation lemmas -/

/-- `addUtilityNodes` preserves `DecisionMonotone` (new nodes are all utility). -/
private theorem MAIDCompileState.DecisionMonotone_addUtilityNodes
    (st : MAIDCompileState P L B)
    (deps : Finset Nat) (hdeps : ∀ d ∈ deps, d < st.nextId)
    (ufn : P → RawNodeEnv L → ℝ) (players : List P)
    (hmon : st.DecisionMonotone) :
    (st.addUtilityNodes deps hdeps ufn players).DecisionMonotone := by
  intro who d₁ d₂ hk₁ hk₂ hlt
  have old₁ : d₁.val < st.nextId := by
    by_contra hge; push_neg at hge
    have ⟨w, hw⟩ := addUtilityNodes_all_utility st deps hdeps ufn players d₁ hge
    rw [hw] at hk₁; exact nomatch hk₁
  have old₂ : d₂.val < st.nextId := by
    by_contra hge; push_neg at hge
    have ⟨w, hw⟩ := addUtilityNodes_all_utility st deps hdeps ufn players d₂ hge
    rw [hw] at hk₂; exact nomatch hk₂
  -- Rewrite descAt to old state using descAt_old + Fin casting
  have h₁ : (st.addUtilityNodes deps hdeps ufn players).descAt d₁ =
      st.descAt ⟨d₁.val, old₁⟩ := by
    convert addUtilityNodes_descAt_old st deps hdeps ufn players d₁.val old₁ using 2
  have h₂ : (st.addUtilityNodes deps hdeps ufn players).descAt d₂ =
      st.descAt ⟨d₂.val, old₂⟩ := by
    convert addUtilityNodes_descAt_old st deps hdeps ufn players d₂.val old₂ using 2
  rw [h₁] at hk₁ ⊢; rw [h₂] at hk₂ ⊢
  exact hmon who ⟨d₁.val, old₁⟩ ⟨d₂.val, old₂⟩ hk₁ hk₂ hlt

/-- `addVar` of a fresh variable preserves `DecisionVisible` for extended context.
Key facts: (1) old visible vars have unchanged lookupDeps, (2) viewVCtx only grows. -/
private theorem MAIDCompileState.DecisionVisible_addVar_cons
    (st : MAIDCompileState P L B)
    (x : VarId) (τ : BindTy P L) (deps : Finset Nat)
    (hdeps : ∀ d ∈ deps, d < st.nextId)
    {Γ : VCtx P L}
    (hfreshΓ : Fresh x Γ)
    (hvis : st.DecisionVisible Γ) :
    (st.addVar x τ deps hdeps).DecisionVisible ((x, τ) :: Γ) := by
  intro who d hkd
  -- addVar doesn't change nodes or nextId, so descAt is the same
  have hkd' : (st.descAt d).kind = .decision who := hkd
  obtain ⟨hmem, hsub⟩ := hvis who d hkd'
  -- Need: d.val ∈ (addVar ...).viewDeps who ((x,τ)::Γ)
  -- and obsParents ⊆ (addVar ...).viewDeps who ((x,τ)::Γ)
  -- Key: viewDeps who Γ in st ⊆ viewDeps who ((x,τ)::Γ) in (addVar ...)
  have hview_sub : st.viewDeps who Γ ⊆
      (st.addVar x τ deps hdeps).viewDeps who ((x, τ) :: Γ) := by
    intro d' hd'
    unfold viewDeps
    simp only [viewVCtx]
    split
    · -- canSee who τ = true
      simp only [List.map, depsOfVars]
      exact Finset.mem_union_right _
        (depsOfVars_addVar_eq_of_fresh st x τ deps hdeps
          ((viewVCtx who Γ).map Prod.fst)
          (fun h => hfreshΓ (viewVCtx_map_fst_sub h)) ▸ hd')
    · -- canSee who τ = false
      exact depsOfVars_addVar_eq_of_fresh st x τ deps hdeps
        ((viewVCtx who Γ).map Prod.fst)
        (fun h => hfreshΓ (viewVCtx_map_fst_sub h)) ▸ hd'
  exact ⟨hview_sub hmem, fun d' hd' => hview_sub (hsub hd')⟩

/-- `addNode` of non-decision + `addVar` preserves `DecisionMonotone`. -/
private theorem MAIDCompileState.DecisionMonotone_addNode_addVar_nonDec
    (st : MAIDCompileState P L B)
    (nd : CompiledNode P L B)
    (hndeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId)
    (x : VarId) (τ : BindTy P L)
    (hdeps : ∀ d ∈ ({st.nextId} : Finset Nat), d < (st.addNode nd hndeps).2.nextId)
    (hmon : st.DecisionMonotone)
    (hnotDec : ∀ who, nd.kind ≠ .decision who) :
    ((st.addNode nd hndeps).2.addVar x τ {st.nextId} hdeps).DecisionMonotone := by
  -- addVar doesn't change nodes/nextId, so it suffices to show for addNode
  -- The new state has nextId = st.nextId + 1, new node is nd (not a decision)
  intro who d₁ d₂ hk₁ hk₂ hlt
  -- Any node at index st.nextId is nd, which is not a decision
  have old (d : Fin _) (hkd : (((st.addNode nd hndeps).2.addVar x τ _ hdeps).descAt d).kind =
      .decision who) : d.val < st.nextId := by
    by_contra hge; push_neg at hge
    have heq : d.val = st.nextId := by
      have := d.isLt; simp [MAIDCompileState.addVar, MAIDCompileState.addNode] at this; omega
    have hdesc : ((st.addNode nd hndeps).2.addVar x τ _ hdeps).descAt d = nd := by
      change ((st.nodes ++ [(st.nextId, nd)])[d.val]'(by
        simp [MAIDCompileState.addNode, MAIDCompileState.addVar, st.nodes_length_eq_nextId]
        omega)).2 = nd
      rw [List.getElem_append_right (by rw [st.nodes_length_eq_nextId]; omega)]
      simp [st.nodes_length_eq_nextId, heq]
    rw [hdesc] at hkd; exact absurd hkd (fun h => hnotDec who h)
  have old₁ := old d₁ hk₁; have old₂ := old d₂ hk₂
  have hdesc (d : Fin _) (hold : d.val < st.nextId) :
      ((st.addNode nd hndeps).2.addVar x τ _ hdeps).descAt d = st.descAt ⟨d.val, hold⟩ := by
    change ((st.nodes ++ [(st.nextId, nd)])[d.val]'(by
      simp [MAIDCompileState.addNode, MAIDCompileState.addVar, st.nodes_length_eq_nextId]
      omega)).2 = (st.nodes[d.val]'(by rw [st.nodes_length_eq_nextId]; exact hold)).2
    congr 1
    exact List.getElem_append_left (by rw [st.nodes_length_eq_nextId]; exact hold)
  rw [hdesc d₁ old₁] at hk₁ ⊢; rw [hdesc d₂ old₂] at hk₂ ⊢
  exact hmon who ⟨d₁.val, old₁⟩ ⟨d₂.val, old₂⟩ hk₁ hk₂ hlt

/-- `addNode + addVar` of non-decision node preserves `DecisionVisible`. -/
private theorem MAIDCompileState.DecisionVisible_addNode_addVar_cons
    (st : MAIDCompileState P L B)
    (nd : CompiledNode P L B)
    (hndeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId)
    (x : VarId) (τ : BindTy P L)
    (hdeps : ∀ d ∈ ({st.nextId} : Finset Nat), d < (st.addNode nd hndeps).2.nextId)
    {Γ : VCtx P L} (hfreshΓ : Fresh x Γ)
    (hvis : st.DecisionVisible Γ)
    (hnotDec : ∀ who, nd.kind ≠ .decision who) :
    ((st.addNode nd hndeps).2.addVar x τ {st.nextId} hdeps).DecisionVisible
      ((x, τ) :: Γ) := by
  intro who d hkd
  -- Node at st.nextId is nd (non-decision), so d must be an old node
  have hold : d.val < st.nextId := by
    by_contra hge; push_neg at hge
    have heq : d.val = st.nextId := by
      have := d.isLt; simp [MAIDCompileState.addVar, MAIDCompileState.addNode] at this; omega
    have hdesc : ((st.addNode nd hndeps).2.addVar x τ _ hdeps).descAt d = nd := by
      change ((st.nodes ++ [(st.nextId, nd)])[d.val]'(by
        simp [MAIDCompileState.addNode, MAIDCompileState.addVar,
          st.nodes_length_eq_nextId]; omega)).2 = nd
      rw [List.getElem_append_right (by rw [st.nodes_length_eq_nextId]; omega)]
      simp [st.nodes_length_eq_nextId, heq]
    rw [hdesc] at hkd; exact absurd hkd (fun h => hnotDec who h)
  -- Reduce descAt to old state
  have hdesc : ((st.addNode nd hndeps).2.addVar x τ _ hdeps).descAt d =
      st.descAt ⟨d.val, hold⟩ := by
    change ((st.nodes ++ [(st.nextId, nd)])[d.val]'(by
      simp [MAIDCompileState.addNode, MAIDCompileState.addVar,
        st.nodes_length_eq_nextId]; omega)).2 =
      (st.nodes[d.val]'(by rw [st.nodes_length_eq_nextId]; exact hold)).2
    congr 1
    exact List.getElem_append_left (by rw [st.nodes_length_eq_nextId]; exact hold)
  rw [hdesc] at hkd ⊢
  obtain ⟨hmem, hsub⟩ := hvis who ⟨d.val, hold⟩ hkd
  -- viewDeps monotonicity: st.viewDeps ⊆ new viewDeps (addNode preserves, addVar+cons grows)
  have hview_sub : st.viewDeps who Γ ⊆
      ((st.addNode nd hndeps).2.addVar x τ _ hdeps).viewDeps who ((x, τ) :: Γ) := by
    intro d' hd'
    -- addNode doesn't change viewDeps
    have hd'' : d' ∈ (st.addNode nd hndeps).2.viewDeps who Γ :=
      viewDeps_addNode_eq st nd hndeps who Γ ▸ hd'
    -- addVar + cons grows viewDeps (same as DecisionVisible_addVar_cons proof)
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

/-- Helper: descAt for the addNode+addVar state equals st₀'s descAt for old nodes,
and equals the new node for the new index. -/
private theorem MAIDCompileState.descAt_addNode_addVar
    (st : MAIDCompileState P L B)
    (nd : CompiledNode P L B)
    (hndeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId)
    (x : VarId) (τ : BindTy P L)
    (hdeps : ∀ d ∈ ({st.nextId} : Finset Nat), d < (st.addNode nd hndeps).2.nextId)
    (d : Fin ((st.addNode nd hndeps).2.addVar x τ {st.nextId} hdeps).nextId)
    (hold : d.val < st.nextId) :
    ((st.addNode nd hndeps).2.addVar x τ {st.nextId} hdeps).descAt d =
      st.descAt ⟨d.val, hold⟩ := by
  change ((st.nodes ++ [(st.nextId, nd)])[d.val]'(by
    simp [MAIDCompileState.addNode, MAIDCompileState.addVar,
      st.nodes_length_eq_nextId]; omega)).2 =
    (st.nodes[d.val]'(by rw [st.nodes_length_eq_nextId]; exact hold)).2
  congr 1
  exact List.getElem_append_left (by rw [st.nodes_length_eq_nextId]; exact hold)

private theorem MAIDCompileState.descAt_addNode_addVar_new
    (st : MAIDCompileState P L B)
    (nd : CompiledNode P L B)
    (hndeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId)
    (x : VarId) (τ : BindTy P L)
    (hdeps : ∀ d ∈ ({st.nextId} : Finset Nat), d < (st.addNode nd hndeps).2.nextId)
    (d : Fin ((st.addNode nd hndeps).2.addVar x τ {st.nextId} hdeps).nextId)
    (heq : d.val = st.nextId) :
    ((st.addNode nd hndeps).2.addVar x τ {st.nextId} hdeps).descAt d = nd := by
  change ((st.nodes ++ [(st.nextId, nd)])[d.val]'(by
    simp [MAIDCompileState.addNode, MAIDCompileState.addVar,
      st.nodes_length_eq_nextId]; omega)).2 = nd
  rw [List.getElem_append_right (by rw [st.nodes_length_eq_nextId]; omega)]
  simp [st.nodes_length_eq_nextId, heq]

private theorem MAIDCompileState.val_lt_or_eq_of_addNode_addVar
    (st : MAIDCompileState P L B)
    (nd : CompiledNode P L B)
    (hndeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId)
    (x : VarId) (τ : BindTy P L)
    (hdeps : ∀ d ∈ ({st.nextId} : Finset Nat), d < (st.addNode nd hndeps).2.nextId)
    (d : Fin ((st.addNode nd hndeps).2.addVar x τ {st.nextId} hdeps).nextId) :
    d.val < st.nextId ∨ d.val = st.nextId := by
  have := d.isLt; simp [MAIDCompileState.addVar, MAIDCompileState.addNode] at this; omega

/-- `addNode(.decision) + addVar` preserves `DecisionMonotone` using `DecisionVisible`. -/
private theorem MAIDCompileState.DecisionMonotone_addNode_addVar_decision
    (st : MAIDCompileState P L B)
    (nd : CompiledNode P L B)
    (hndeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId)
    (x : VarId) (τ : BindTy P L)
    (hdeps : ∀ d ∈ ({st.nextId} : Finset Nat), d < (st.addNode nd hndeps).2.nextId)
    {Γ : VCtx P L} (owner : P)
    (hmon : st.DecisionMonotone)
    (hvis : st.DecisionVisible Γ)
    (hobs : nd.obsParents = st.viewDeps owner Γ)
    (hkind : nd.kind = .decision owner) :
    ((st.addNode nd hndeps).2.addVar x τ {st.nextId} hdeps).DecisionMonotone := by
  intro who d₁ d₂ hk₁ hk₂ hlt
  rcases st.val_lt_or_eq_of_addNode_addVar nd hndeps x τ hdeps d₁ with old₁ | new₁
  · rw [st.descAt_addNode_addVar nd hndeps x τ hdeps d₁ old₁] at hk₁ ⊢
    rcases st.val_lt_or_eq_of_addNode_addVar nd hndeps x τ hdeps d₂ with old₂ | new₂
    · rw [st.descAt_addNode_addVar nd hndeps x τ hdeps d₂ old₂] at hk₂ ⊢
      exact hmon who ⟨d₁.val, old₁⟩ ⟨d₂.val, old₂⟩ hk₁ hk₂ hlt
    · rw [st.descAt_addNode_addVar_new nd hndeps x τ hdeps d₂ new₂] at hk₂ ⊢
      rw [hobs]
      have hwho : who = owner := by rw [hkind] at hk₂; exact (NodeKind.decision.inj hk₂).symm
      rw [hwho] at hk₁
      exact hvis owner ⟨d₁.val, old₁⟩ hk₁
  · rcases st.val_lt_or_eq_of_addNode_addVar nd hndeps x τ hdeps d₂ with old₂ | new₂
    · omega
    · omega

/-- `addNode(.decision) + addVar` preserves `DecisionVisible` for commit context extension. -/
private theorem MAIDCompileState.DecisionVisible_addNode_addVar_cons_decision
    (st : MAIDCompileState P L B)
    (nd : CompiledNode P L B)
    (hndeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId)
    (x : VarId) (τ : BindTy P L)
    (hdeps : ∀ d ∈ ({st.nextId} : Finset Nat), d < (st.addNode nd hndeps).2.nextId)
    {Γ : VCtx P L} (hfreshΓ : Fresh x Γ)
    (hvis : st.DecisionVisible Γ)
    (owner : P) (bty : L.Ty)
    (hobs : nd.obsParents = st.viewDeps owner Γ)
    (hkind : nd.kind = .decision owner)
    (hcanSee : τ = .hidden owner bty)
    (hfreshVars : x ∉ st.vars.map Prod.fst) :
    ((st.addNode nd hndeps).2.addVar x τ {st.nextId} hdeps).DecisionVisible
      ((x, τ) :: Γ) := by
  -- viewDeps monotonicity (same as non-decision case)
  have hview_sub : ∀ who, st.viewDeps who Γ ⊆
      ((st.addNode nd hndeps).2.addVar x τ _ hdeps).viewDeps who ((x, τ) :: Γ) := by
    intro who d' hd'
    have hd'' : d' ∈ (st.addNode nd hndeps).2.viewDeps who Γ :=
      viewDeps_addNode_eq st nd hndeps who Γ ▸ hd'
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
  rcases st.val_lt_or_eq_of_addNode_addVar nd hndeps x τ hdeps d with hold | hnew
  · -- Old node: use hvis + viewDeps monotonicity
    rw [st.descAt_addNode_addVar nd hndeps x τ hdeps d hold] at hkd ⊢
    obtain ⟨hmem, hsub⟩ := hvis who ⟨d.val, hold⟩ hkd
    exact ⟨hview_sub who hmem, fun d' hd' => hview_sub who (hsub hd')⟩
  · -- New node (d.val = st.nextId): this is the decision node for owner
    rw [st.descAt_addNode_addVar_new nd hndeps x τ hdeps d hnew] at hkd ⊢
    -- From hkd: nd.kind = .decision who, so who = owner
    have hwho : who = owner := by rw [hkind] at hkd; exact (NodeKind.decision.inj hkd).symm
    subst hwho
    constructor
    · -- st.nextId ∈ viewDeps owner ((x, τ)::Γ)
      unfold viewDeps viewVCtx
      rw [hcanSee]
      simp only [canSee, decide_true, ↓reduceIte, List.map_cons]
      simp only [depsOfVars]
      apply Finset.mem_union_left
      have hfv : x ∉ (st.addNode nd hndeps).2.vars.map Prod.fst := by
        simp only [MAIDCompileState.addNode]; exact hfreshVars
      rw [lookupDeps_addVar_eq_self_of_fresh _ x _ _ _ hfv, hnew]
      simp
    · rw [hobs]; exact hview_sub who

/-- Generalized induction: `ofProg` preserves `DecisionMonotone` when started
from a state satisfying both `DecisionMonotone` and `DecisionVisible`. -/
private theorem MAIDCompileState.ofProg_preserves_decision_monotone
    {Γ : VCtx P L}
    (p : VegasCore P L Γ) (hl : Legal p)
    (hd : NormalizedDists p) (hfresh : FreshBindings p)
    (ρ : RawNodeEnv L → VEnv (Player := P) L Γ)
    (st₀ : MAIDCompileState P L B)
    (hmon : st₀.DecisionMonotone)
    (hvis : st₀.DecisionVisible Γ)
    (hvs : ∀ y, y ∈ st₀.vars.map Prod.fst → y ∈ Γ.map Prod.fst) :
    (MAIDCompileState.ofProg B p hl hd ρ st₀).DecisionMonotone := by
  induction p generalizing st₀ with
  | ret payoffs =>
    simp only [ofProg]
    exact DecisionMonotone_addUtilityNodes st₀ _ _ _ _ hmon
  | letExpr _ _ k ih =>
    simp only [ofProg]
    refine ih hl hd hfresh.2 _ _ hmon (DecisionVisible_addVar_cons st₀ _ _ _ _ hfresh.1 hvis) ?_
    intro y hy
    simp only [MAIDCompileState.addVar, List.map_append, List.mem_append, List.map] at hy
    rcases hy with h | h
    · exact List.mem_cons_of_mem _ (hvs y h)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h; exact List.Mem.head _
  | sample _ _ _ _ k ih =>
    refine ih hl hd.2 hfresh.2 _ _ ?_ ?_ ?_
    · exact DecisionMonotone_addNode_addVar_nonDec st₀ _ _ _ _ _ hmon
        (fun who h => by simp [CompiledNode.kind] at h)
    · exact DecisionVisible_addNode_addVar_cons st₀ _ _ _ _ _ hfresh.1 hvis
        (fun who h => by simp [CompiledNode.kind] at h)
    · intro y hy
      simp only [MAIDCompileState.addVar, MAIDCompileState.addNode,
        List.map_append, List.mem_append, List.map] at hy
      rcases hy with h | h
      · exact List.mem_cons_of_mem _ (hvs y h)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h; exact List.Mem.head _
  | commit x who_c R k ih =>
    refine ih hl.2 hd hfresh.2 _ _ ?_ ?_ ?_
    · exact DecisionMonotone_addNode_addVar_decision st₀ _ _ _ _ _ who_c hmon hvis rfl rfl
    · exact DecisionVisible_addNode_addVar_cons_decision
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
    · exact DecisionVisible_addVar_cons st₀ _ _ _ _ hfresh.1 hvis
    · intro y hy
      simp only [MAIDCompileState.addVar, List.map_append, List.mem_append, List.map] at hy
      rcases hy with h | h
      · exact List.mem_cons_of_mem _ (hvs y h)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h; exact List.Mem.head _

/-- For any two decision nodes of the same player with `d₁.val < d₂.val`,
`d₁` is a direct obsParent of `d₂` and d₁'s obsParents are a subset of d₂'s.
This is the key invariant maintained by the sequential compiler. -/
theorem MAIDCompileState.ofProg_decision_obs_monotone
    {Γ : VCtx P L}
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (hwf : WF p) :
    let st := MAIDCompileState.ofProg B p hl hd (fun _ => env) .empty
    ∀ (who : P) (d₁ d₂ : Fin st.nextId),
      (st.descAt d₁).kind = .decision who →
      (st.descAt d₂).kind = .decision who →
      d₁.val < d₂.val →
      d₁.val ∈ (st.descAt d₂).obsParents ∧
        (st.descAt d₁).obsParents ⊆ (st.descAt d₂).obsParents := by
  intro st
  exact ofProg_preserves_decision_monotone p hl hd hwf.1 (fun _ => env)
    .empty
    -- empty state is trivially DecisionMonotone
    (fun _ d₁ _ _ _ _ => absurd d₁.isLt (Nat.not_lt_zero _))
    -- empty state is trivially DecisionVisible
    (fun _ d _ => absurd d.isLt (Nat.not_lt_zero _))
    -- empty vars
    (fun _ h => by simp [MAIDCompileState.empty] at h)

/-! ## Main theorem -/

/-- A well-formed Vegas program compiles to a MAID struct with perfect recall. -/
theorem compiledStruct_perfectRecall
    (B : MAIDBackend P L)
    {Γ : VCtx P L}
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (hwf : WF p) :
    let _ : Fintype P := B.fintypePlayer
    (MAIDCompileState.ofProg B p hl hd (fun _ => env) .empty).toStruct.PerfectRecall := by
  intro _inst
  letI : Fintype P := B.fintypePlayer
  set st := MAIDCompileState.ofProg B p hl hd (fun _ => env) .empty with hst
  have core := MAIDCompileState.ofProg_decision_obs_monotone (B := B) p env hl hd hwf
  -- core is about the same `st` by definition
  unfold Struct.PerfectRecall
  constructor
  · -- Part 1: Temporal ordering
    intro who d₁ d₂ hk₁ hk₂ hne
    simp only [toStruct_kind] at hk₁ hk₂
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
    · left
      apply Struct.parent_isAncestor
      rw [st.mem_toStruct_parents_iff d₂ d₁.isLt, CompiledNode.parents_eq_obsParents]
      exact (core who d₁ d₂ hk₁ hk₂ hlt).1
    · right
      apply Struct.parent_isAncestor
      rw [st.mem_toStruct_parents_iff d₁ d₂.isLt, CompiledNode.parents_eq_obsParents]
      exact (core who d₂ d₁ hk₂ hk₁ hgt).1
  · -- Part 2: Full observation
    intro who d₁ d₂ hk₁ hk₂ hanc
    simp only [toStruct_kind] at hk₁ hk₂
    have hlt : d₁.val < d₂.val := st.isAncestor_val_lt d₁ d₂ hanc
    obtain ⟨hmem, hsub⟩ := core who d₁ d₂ hk₁ hk₂ hlt
    exact ⟨(st.mem_toStruct_obsParents_iff d₂ d₁.isLt).mpr hmem,
           fun x hx =>
             (st.mem_toStruct_obsParents_iff d₂ x.isLt).mpr
               (hsub ((st.mem_toStruct_obsParents_iff d₁ x.isLt).mp hx))⟩

end Vegas
