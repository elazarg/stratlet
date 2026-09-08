/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.SourceAdequacy
import Vegas.Compile.SourceView
import Vegas.Core.Strategy

/-!
# Source decision kernels and compiled node code

Source policies consume source views. Compiled commitment code consumes its
declared graph reads. This module translates one decision kernel between these
interfaces and proves exact probability laws at matching stores. The sample
law is exact as well. These are local compiler lemmas; they do not identify
whole source policies with the history-dependent policies of the graph game.
-/

noncomputable section

namespace Vegas.ToEventGraph

open EventGraph GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A compiler field map relates a source environment to a graph store. -/
def BuildState.Agrees {Γ : VCtx P L} (state : BuildState P L Γ)
    (store : Store L) (env : VEnv L Γ) : Prop :=
  ∀ {name bindTy} (h : VHasVar Γ name bindTy),
    Store.getAs store (state.fieldOf h) bindTy.base = some (env.get h)

theorem BuildState.Agrees.available {Γ : VCtx P L}
    {state : BuildState P L Γ} {store : Store L} {env : VEnv L Γ}
    (h : state.Agrees store env) :
    ∀ {name bindTy} (binding : VHasVar Γ name bindTy),
      ∃ value, Store.getAs store (state.fieldOf binding) bindTy.base = some value :=
  fun binding => ⟨env.get binding, h binding⟩

/-- A source decision needs agreement only on its player's visible bindings.
Unrelated sealed choices may still be absent from a parallel graph store. -/
def BuildState.ViewAgrees {Γ : VCtx P L} (state : BuildState P L Γ)
    (who : P) (store : Store L) (env : VEnv L Γ) : Prop :=
  ∀ {name bindTy} (binding : VHasVar (viewVCtx who Γ) name bindTy),
    Store.getAs store (state.fieldOf binding.ofViewVCtx) bindTy.base =
      some ((env.toView who).get binding)

theorem BuildState.Agrees.view {Γ : VCtx P L}
    {state : BuildState P L Γ} {store : Store L} {env : VEnv L Γ}
    (h : state.Agrees store env) (who : P) : state.ViewAgrees who store env :=
  fun binding => h binding.ofViewVCtx

/-- Matching graph reads recover exactly the source-visible environment. -/
theorem viewEnvOfReadEnv_eq_sourceView
    {Γ : VCtx P L} (state : BuildState P L Γ) (who : P)
    (store : Store L) (env : VEnv L Γ) (hagrees : state.ViewAgrees who store env)
    (reads : ReadEnv L (visibleFieldRefs state who))
    (hreads : ReadEnv.ofStore? store (visibleFieldRefs state who) = some reads) :
    viewEnvOfReadEnv state who reads = (env.toView who).eraseEnv := by
  rw [← visibleEnvOfReadEnv_erase]
  apply congrArg VEnv.eraseEnv
  funext name bindTy binding
  have hread := ReadEnv.ofStore?_read hreads
    (fieldRefOfView_mem_visibleFieldRefs state who binding)
  exact Option.some.inj (hread.symm.trans (hagrees binding))

/-- Compiled sample code has the source law at every matching store. -/
theorem eventDistOf_eval_eq_source
    {Γ : VCtx P L} {ty : L.Ty} (state : BuildState P L Γ)
    (dist : L.DistExpr (erasePubVCtx Γ) ty)
    (store : Store L) (env : VEnv L Γ) (hagrees : state.Agrees store env)
    (reads : ReadEnv L (eventDistOf state dist).reads)
    (hreads : ReadEnv.ofStore? store (eventDistOf state dist).reads = some reads) :
    (eventDistOf state dist).eval reads = L.evalDist dist env.eraseSampleEnv := by
  apply eventDistOf_eval_eq_eval
  intro name depTy binding hmem
  have h := eventDistOf_readEnv_agrees_sourceEnvOfStore_of_readEnv
    state dist store hagrees.available reads hreads binding hmem
  rw [sourceEnvOfStore_eq_of_get state store hagrees.available env hagrees] at h
  exact h

/-- Compile a source decision kernel using only the commitment's declared
reads. The resulting law includes a proof of the compiled guard. -/
def compileSourceDecision
    {Γ : VCtx P L} {name : VarId} {ty : L.Ty}
    (state : BuildState P L Γ) (who : P)
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (policy : (visible : Env L.Val (eraseVCtx (viewVCtx who Γ))) →
      FinDist {value : L.Val ty // evalGuard guard value visible = true})
    (reads : ReadEnv L (eventGuardOf state who guard).choiceReads) :
    FinDist {value : L.Val ty // (eventGuardOf state who guard).eval value reads = true} :=
  (policy (viewEnvOfReadEnv state who reads)).map fun choice =>
    ⟨choice.1, (eventGuardOf_eval_eq_eval state who guard choice.1 reads).trans choice.2⟩

/-- Erasing guard evidence from a compiled decision gives exactly its source
decision law, not merely the same set of possible values. -/
theorem compileSourceDecision_law
    {Γ : VCtx P L} {name : VarId} {ty : L.Ty}
    (state : BuildState P L Γ) (who : P)
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (policy : (visible : Env L.Val (eraseVCtx (viewVCtx who Γ))) →
      FinDist {value : L.Val ty // evalGuard guard value visible = true})
    (store : Store L) (env : VEnv L Γ) (hagrees : state.ViewAgrees who store env)
    (reads : ReadEnv L (eventGuardOf state who guard).choiceReads)
    (hreads : ReadEnv.ofStore? store (eventGuardOf state who guard).choiceReads = some reads) :
    (compileSourceDecision state who guard policy reads).map Subtype.val =
      (policy ((env.toView who).eraseEnv)).map Subtype.val := by
  simp only [compileSourceDecision, FinDist.map_comp, Function.comp_def]
  have hview := viewEnvOfReadEnv_eq_sourceView state who store env hagrees reads hreads
  exact congrArg (fun visible => (policy visible).map Subtype.val) hview

/-- Translate an arbitrary declared-read decision back to source views using
the compiler's lossless field allocation. No fallback or restriction on the
target decision kernel is needed. -/
def backtranslateSourceDecision
    {Γ : VCtx P L} {name : VarId} {ty : L.Ty}
    (state : BuildState P L Γ) (who : P)
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (hinjective : FieldOfNameInjective state.fieldOf)
    (policy : (reads : ReadEnv L (eventGuardOf state who guard).choiceReads) →
      FinDist {value : L.Val ty // (eventGuardOf state who guard).eval value reads = true})
    (visible : Env L.Val (eraseVCtx (viewVCtx who Γ))) :
    FinDist {value : L.Val ty // evalGuard guard value visible = true} := by
  let reads := (sourceViewEquiv state who hinjective).symm visible
  exact (policy reads).map fun choice => ⟨choice.1, by
    have hview : viewEnvOfReadEnv state who reads = visible :=
      (sourceViewEquiv state who hinjective).apply_symm_apply visible
    rw [← hview]
    exact (eventGuardOf_eval_eq_eval state who guard choice.1 reads).symm.trans choice.2⟩

/-- Back-translation preserves every declared-read decision law. Its witness
depends on the player's policy, not on opponents or a complete profile. -/
theorem backtranslateSourceDecision_law
    {Γ : VCtx P L} {name : VarId} {ty : L.Ty}
    (state : BuildState P L Γ) (who : P)
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (hinjective : FieldOfNameInjective state.fieldOf)
    (policy : (reads : ReadEnv L (eventGuardOf state who guard).choiceReads) →
      FinDist {value : L.Val ty // (eventGuardOf state who guard).eval value reads = true})
    (reads : ReadEnv L (eventGuardOf state who guard).choiceReads) :
    (backtranslateSourceDecision state who guard hinjective policy
      (viewEnvOfReadEnv state who reads)).map Subtype.val =
        (policy reads).map Subtype.val := by
  have hchosen : (sourceViewEquiv state who hinjective).symm
      (viewEnvOfReadEnv state who reads) = reads :=
    (sourceViewEquiv state who hinjective).symm_apply_apply reads
  simp only [backtranslateSourceDecision, FinDist.map_comp, Function.comp_def]
  exact congrArg (fun input => (policy input).map Subtype.val) hchosen

/-- Compiling the back-translated decision recovers the original guarded
target law at every input. -/
theorem compile_backtranslateSourceDecision
    {Γ : VCtx P L} {name : VarId} {ty : L.Ty}
    (state : BuildState P L Γ) (who : P)
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (hinjective : FieldOfNameInjective state.fieldOf)
    (policy : (reads : ReadEnv L (eventGuardOf state who guard).choiceReads) →
      FinDist {value : L.Val ty // (eventGuardOf state who guard).eval value reads = true})
    (reads : ReadEnv L (eventGuardOf state who guard).choiceReads) :
    compileSourceDecision state who guard
      (backtranslateSourceDecision state who guard hinjective policy) reads = policy reads := by
  apply FinDist.map_injective Subtype.val_injective
  simpa only [compileSourceDecision, FinDist.map_comp, Function.comp_def] using
    backtranslateSourceDecision_law state who guard hinjective policy reads

/-- Back-translating a compiled source decision recovers its original guarded
source law at every source view. -/
theorem backtranslate_compileSourceDecision
    {Γ : VCtx P L} {name : VarId} {ty : L.Ty}
    (state : BuildState P L Γ) (who : P)
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (hinjective : FieldOfNameInjective state.fieldOf)
    (policy : (visible : Env L.Val (eraseVCtx (viewVCtx who Γ))) →
      FinDist {value : L.Val ty // evalGuard guard value visible = true})
    (visible : Env L.Val (eraseVCtx (viewVCtx who Γ))) :
    backtranslateSourceDecision state who guard hinjective
      (compileSourceDecision state who guard policy) visible = policy visible := by
  apply FinDist.map_injective Subtype.val_injective
  simp only [backtranslateSourceDecision, compileSourceDecision,
    FinDist.map_comp, Function.comp_def]
  exact congrArg (fun input => (policy input).map Subtype.val)
    ((sourceViewEquiv state who hinjective).apply_symm_apply visible)

end Vegas.ToEventGraph
