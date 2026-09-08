/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.FieldMap

/-!
# Source views and compiled choice reads

Every declared commitment read names a visible source binding. Reconstructing
the source view from these reads loses no information. This statement concerns
the node's declared choice reads, not a player's full graph-history information.
-/

noncomputable section

namespace Vegas.ToEventGraph

open EventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

omit [DecidableEq P] in
theorem mem_fieldRefsOfCtx_iff
    {Γ : VCtx P L}
    (fieldOf : {name : VarId} → {bindTy : BindTy P L} → VHasVar Γ name bindTy → Nat)
    (ref : FieldRef L) :
    ref ∈ fieldRefsOfCtx fieldOf ↔
      ∃ name bindTy, ∃ binding : VHasVar Γ name bindTy,
        ref = { field := fieldOf binding, ty := bindTy.base } := by
  induction Γ with
  | nil =>
      simp only [fieldRefsOfCtx_nil, Finset.notMem_empty, false_iff, not_exists]
      intro name bindTy binding
      exact nomatch binding
  | cons head tail ih =>
      rcases head with ⟨name, bindTy⟩
      rw [fieldRefsOfCtx_cons, Finset.mem_insert, ih]
      constructor
      · rintro (hhead | ⟨name', bindTy', binding, htail⟩)
        · exact ⟨name, bindTy, .here, hhead⟩
        · exact ⟨name', bindTy', .there binding, htail⟩
      · rintro ⟨name', bindTy', binding, heq⟩
        cases binding with
        | here => exact Or.inl heq
        | there binding => exact Or.inr ⟨name', bindTy', binding, heq⟩

/-- Visibility-tagged source values reconstructed from a node's declared
choice reads. -/
def visibleEnvOfReadEnv {Γ : VCtx P L} (state : BuildState P L Γ) (who : P)
    (reads : ReadEnv L (visibleFieldRefs state who)) : VEnv L (viewVCtx who Γ) :=
  fun _ _ binding => reads.read (state.fieldRefOfView who binding)
    (fieldRefOfView_mem_visibleFieldRefs state who binding)

theorem visibleEnvOfReadEnv_erase
    {Γ : VCtx P L} (state : BuildState P L Γ) (who : P)
    (reads : ReadEnv L (visibleFieldRefs state who)) :
    (visibleEnvOfReadEnv state who reads).eraseEnv = viewEnvOfReadEnv state who reads := by
  funext name ty binding
  let lifted := HasVar.toVHasVar (Player := P) (L := L) binding
  have h := VEnv.eraseEnv_toErased_eq (visibleEnvOfReadEnv state who reads) binding
  rw [VEnv.eraseEnv_get_of_erased] at h
  apply eq_of_heq
  exact HEq.trans h.symm (cast_heq _ _).symm

/-- The compiler's source-view decoder retains every declared choice read. -/
theorem viewEnvOfReadEnv_injective
    {Γ : VCtx P L} (state : BuildState P L Γ) (who : P) :
    Function.Injective (viewEnvOfReadEnv state who) := by
  intro left right heq
  apply ReadEnv.ext
  intro ref href
  obtain ⟨name, bindTy, binding, rfl⟩ :=
    (mem_fieldRefsOfCtx_iff _ ref).mp href
  have hview : (visibleEnvOfReadEnv state who left).eraseEnv =
      (visibleEnvOfReadEnv state who right).eraseEnv := by
    simpa only [visibleEnvOfReadEnv_erase] using heq
  have h := congrFun (congrFun (congrFun hview name) bindTy.base) binding.toErased
  simpa only [VEnv.eraseEnv_get_of_erased, visibleEnvOfReadEnv, BuildState.fieldRefOfView] using h

omit [DecidableEq P] in
private theorem exists_fieldRef_value
    {Γ : VCtx P L}
    (fieldOf : {name : VarId} → {bindTy : BindTy P L} → VHasVar Γ name bindTy → Nat)
    (wctx : WFCtx Γ) (hinjective : FieldOfNameInjective fieldOf)
    (env : VEnv L Γ) (ref : FieldRef L) (href : ref ∈ fieldRefsOfCtx fieldOf) :
    ∃ value : L.Val ref.ty,
      ∀ {name bindTy} (binding : VHasVar Γ name bindTy),
        ref = { field := fieldOf binding, ty := bindTy.base } → HEq value (env.get binding) := by
  obtain ⟨name, bindTy, binding, rfl⟩ := (mem_fieldRefsOfCtx_iff fieldOf ref).mp href
  refine ⟨env.get binding, ?_⟩
  intro otherName otherTy other heq
  have hname : name = otherName := hinjective binding other (congrArg FieldRef.field heq)
  subst otherName
  have hty : bindTy = otherTy := HasVar.type_unique wctx binding other
  subst otherTy
  have hbinding : binding = other := HasVar.eq_of_nodup wctx binding other
  subst other
  exact HEq.rfl

/-- Store exactly a typed source environment in its allocated read footprint.
Injectivity rules out merging the values of distinct source variables. -/
def readEnvOfSourceEnv
    {Γ : VCtx P L}
    (fieldOf : {name : VarId} → {bindTy : BindTy P L} → VHasVar Γ name bindTy → Nat)
    (wctx : WFCtx Γ) (hinjective : FieldOfNameInjective fieldOf)
    (env : VEnv L Γ) : ReadEnv L (fieldRefsOfCtx fieldOf) where
  read ref href := Classical.choose (exists_fieldRef_value fieldOf wctx hinjective env ref href)

omit [DecidableEq P] in
theorem readEnvOfSourceEnv_read
    {Γ : VCtx P L}
    (fieldOf : {name : VarId} → {bindTy : BindTy P L} → VHasVar Γ name bindTy → Nat)
    (wctx : WFCtx Γ) (hinjective : FieldOfNameInjective fieldOf)
    (env : VEnv L Γ) {name bindTy} (binding : VHasVar Γ name bindTy) :
    (readEnvOfSourceEnv fieldOf wctx hinjective env).read
      { field := fieldOf binding, ty := bindTy.base } (fieldRefOfCtx_mem fieldOf binding) =
        env.get binding := by
  apply eq_of_heq
  exact Classical.choose_spec
    (exists_fieldRef_value fieldOf wctx hinjective env _
      (fieldRefOfCtx_mem fieldOf binding)) binding rfl

omit [DecidableEq P] in
private theorem eraseEnv_of_lookup {Γ : VCtx P L}
    (env : Env L.Val (eraseVCtx Γ)) :
    VEnv.eraseEnv (fun name bindTy (binding : VHasVar Γ name bindTy) =>
      env name bindTy.base binding.toErased : VEnv L Γ) = env := by
  induction Γ with
  | nil => funext name ty binding; exact nomatch binding
  | cons head tail ih =>
      funext name ty binding
      cases binding with
      | here => rfl
      | there binding =>
          exact congrFun (congrFun (congrFun
            (ih (fun name ty binding => env name ty (.there binding))) name) ty) binding

/-- Every typed source view has a corresponding declared-read environment
when source bindings have distinct allocated fields. -/
theorem viewEnvOfReadEnv_surjective
    {Γ : VCtx P L} (state : BuildState P L Γ) (who : P)
    (hinjective : FieldOfNameInjective state.fieldOf) :
    Function.Surjective (viewEnvOfReadEnv state who) := by
  intro visible
  let values : VEnv L (viewVCtx who Γ) :=
    fun name bindTy binding => visible name bindTy.base binding.toErased
  let fieldOf : {name : VarId} → {bindTy : BindTy P L} →
      VHasVar (viewVCtx who Γ) name bindTy → Nat :=
    fun binding => state.fieldOf binding.ofViewVCtx
  have hfields : FieldOfNameInjective fieldOf := by
    intro name bindTy left otherName otherTy right h
    exact hinjective left.ofViewVCtx right.ofViewVCtx h
  let reads := readEnvOfSourceEnv fieldOf (state.wctx.viewVCtx (p := who)) hfields values
  refine ⟨reads, ?_⟩
  rw [← visibleEnvOfReadEnv_erase]
  have hvalues : visibleEnvOfReadEnv state who reads = values := by
    funext name bindTy binding
    exact readEnvOfSourceEnv_read fieldOf _ hfields values binding
  rw [hvalues]
  exact eraseEnv_of_lookup visible

/-- A compiled commitment's declared read environment and its source-visible
environment have exactly the same information. Allocation injectivity is a
proved compiler invariant; this equivalence does not include graph histories. -/
def sourceViewEquiv
    {Γ : VCtx P L} (state : BuildState P L Γ) (who : P)
    (hinjective : FieldOfNameInjective state.fieldOf) :
    ReadEnv L (visibleFieldRefs state who) ≃ Env L.Val (eraseVCtx (viewVCtx who Γ)) :=
  Equiv.ofBijective (viewEnvOfReadEnv state who)
    ⟨viewEnvOfReadEnv_injective state who, viewEnvOfReadEnv_surjective state who hinjective⟩

end Vegas.ToEventGraph
