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

/-- For any two decision nodes of the same player with `d₁.val < d₂.val`,
`d₁` is a direct obsParent of `d₂` and d₁'s obsParents are a subset of d₂'s.
This is the key invariant maintained by the sequential compiler. -/
theorem MAIDCompileState.ofProg_decision_obs_monotone
    {Γ : VCtx P L}
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hl : Legal p) (ha : DistinctActs p) (hd : NormalizedDists p)
    (hwf : WF p) :
    let st := MAIDCompileState.ofProg B p hl ha hd (fun _ => env) .empty
    ∀ (who : P) (d₁ d₂ : Fin st.nextId),
      (st.descAt d₁).kind = .decision who →
      (st.descAt d₂).kind = .decision who →
      d₁.val < d₂.val →
      d₁.val ∈ (st.descAt d₂).obsParents ∧
        (st.descAt d₁).obsParents ⊆ (st.descAt d₂).obsParents := by
  sorry

/-! ## Main theorem -/

/-- A well-formed Vegas program compiles to a MAID struct with perfect recall. -/
theorem compiledStruct_perfectRecall
    (B : MAIDBackend P L)
    {Γ : VCtx P L}
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ)
    (hl : Legal p) (ha : DistinctActs p) (hd : NormalizedDists p)
    (hwf : WF p) :
    let _ : Fintype P := B.fintypePlayer
    (MAIDCompileState.ofProg B p hl ha hd (fun _ => env) .empty).toStruct.PerfectRecall := by
  intro _inst
  letI : Fintype P := B.fintypePlayer
  set st := MAIDCompileState.ofProg B p hl ha hd (fun _ => env) .empty with hst
  have core := MAIDCompileState.ofProg_decision_obs_monotone (B := B) p env hl ha hd hwf
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
