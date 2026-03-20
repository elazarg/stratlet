import Mathlib.Probability.ProbabilityMassFunction.Basic
import Vegas.Scope

/-!
# Vegas strategies

This file contains the game-theoretic strategy notions for Vegas.

Unlike evaluator-facing `OperationalProfile`s, these strategies are indexed by
actual player views. An operational profile is obtained by projecting a full
erased environment to the corresponding visible environment at each commit
site.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- The visible erased environment available to player `who` in context `Γ`. -/
abbrev ViewEnv (who : P) (Γ : VCtx P L) : Type :=
  Env L.Val (eraseVCtx (viewVCtx who Γ))

/-- A deterministic choice rule indexed by a player's actual view. -/
abbrev PureKernel (who : P) (Γ : VCtx P L) (b : L.Ty) : Type :=
  ViewEnv (P := P) (L := L) who Γ → L.Val b

/-- A behavioral choice rule indexed by a player's actual view. -/
abbrev BehavioralKernel (who : P) (Γ : VCtx P L) (b : L.Ty) : Type :=
  ViewEnv (P := P) (L := L) who Γ → FDist (L.Val b)

/-- A player's pure Vegas strategy: one deterministic action for each visible
decision state. -/
structure PureStrategy (who : P) where
  commit : {Γ : VCtx P L} → {b : L.Ty} → (x : VarId) →
    (R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool) →
    PureKernel (P := P) (L := L) who Γ b

/-- A player's behavioral Vegas strategy: one action distribution for each
visible decision state. -/
structure BehavioralStrategy (who : P) where
  commit : {Γ : VCtx P L} → {b : L.Ty} → (x : VarId) →
    (R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool) →
    BehavioralKernel (P := P) (L := L) who Γ b
  normalized : {Γ : VCtx P L} → {b : L.Ty} → (x : VarId) →
    (R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool) →
    (view : ViewEnv (P := P) (L := L) who Γ) →
    FDist.totalWeight (commit x R view) = 1

/-- A pure strategy distribution for one player. -/
abbrev MixedStrategy (who : P) : Type :=
  PMF (PureStrategy (P := P) (L := L) who)

/-- Joint pure strategies. -/
abbrev PureProfile : Type :=
  ∀ who, PureStrategy (P := P) (L := L) who

/-- Joint behavioral strategies. -/
abbrev BehavioralProfile : Type :=
  ∀ who, BehavioralStrategy (P := P) (L := L) who

/-- Joint mixed strategies. -/
abbrev MixedProfile : Type :=
  ∀ who, MixedStrategy (P := P) (L := L) who

private theorem visibleVars_cons_of_canSee_true
    {who : P} {y : VarId} {σ : BindTy P L} {Γ : VCtx P L}
    (hsee : canSee who σ = true) :
    visibleVars (L := L) who ((y, σ) :: Γ) =
      insert y (visibleVars (L := L) who Γ) := by
  cases σ with
  | pub b =>
      simp [visibleVars]
  | hidden owner b =>
      by_cases hown : who = owner
      · simp [visibleVars, hown]
      · simp [canSee, hown] at hsee

private theorem visibleVars_cons_of_canSee_false
    {who : P} {y : VarId} {σ : BindTy P L} {Γ : VCtx P L}
    (hsee : canSee who σ = false) :
    visibleVars (L := L) who ((y, σ) :: Γ) =
      visibleVars (L := L) who Γ := by
  cases σ with
  | pub b =>
      simp [canSee] at hsee
  | hidden owner b =>
      by_cases hown : who = owner
      · simp [canSee, hown] at hsee
      · simp [visibleVars, hown]

private theorem mem_visibleVars_of_view_member
    {who : P} {Γ : VCtx P L} {x : VarId} :
    x ∈ (viewVCtx who Γ).map Prod.fst →
      x ∈ visibleVars (L := L) who Γ := by
  induction Γ with
  | nil =>
      intro hx
      simp [viewVCtx] at hx
  | cons hd tl ih =>
      obtain ⟨y, σ⟩ := hd
      cases hsee : canSee who σ with
      | true =>
        intro hx
        have hview : viewVCtx who ((y, σ) :: tl) = (y, σ) :: viewVCtx who tl := by
          simp [viewVCtx, hsee]
        rw [hview] at hx
        simp only [List.map, List.mem_cons] at hx
        rcases hx with rfl | htl
        · rw [visibleVars_cons_of_canSee_true (L := L) hsee]
          exact Finset.mem_insert_self _ _
        · rw [visibleVars_cons_of_canSee_true (L := L) hsee]
          exact Finset.mem_insert_of_mem (ih htl)
      | false =>
        intro hx
        have hview : viewVCtx who ((y, σ) :: tl) = viewVCtx who tl := by
          simp [viewVCtx, hsee]
        rw [hview] at hx
        rw [visibleVars_cons_of_canSee_false (L := L) hsee]
        exact ih hx

private theorem view_member_visible
    {who : P} {Γ : VCtx P L} {x : VarId} {τ : BindTy P L}
    (h : VHasVar (L := L) (viewVCtx who Γ) x τ) :
    x ∈ visibleVars (L := L) who Γ :=
  mem_visibleVars_of_view_member (L := L) (VHasVar.mem_map_fst h)

/-- Project a full erased environment to the visible erased environment for
player `who`. -/
noncomputable def projectViewEnv (who : P) {Γ : VCtx P L}
    (env : Env L.Val (eraseVCtx Γ)) :
    ViewEnv (P := P) (L := L) who Γ := by
  intro x τ h
  rcases HasVar.toVHasVar (Player := P) (L := L) (Γ := viewVCtx who Γ) h with
    ⟨σ, hv, ⟨hτ⟩⟩
  cases hτ
  exact env _ _ (VHasVar.toErased (Player := P) (L := L) (VHasVar.ofViewVCtx (p := who) hv))

theorem projectViewEnv_eq_of_obsEq
    {who : P} {Γ : VCtx P L}
    {ρ₁ ρ₂ : Env L.Val (eraseVCtx Γ)}
    (hobs : ObsEq (L := L) (Γ := Γ) who ρ₁ ρ₂) :
    projectViewEnv (P := P) (L := L) who ρ₁ =
      projectViewEnv (P := P) (L := L) who ρ₂ := by
  funext x τ h
  dsimp [projectViewEnv]
  rcases HasVar.toVHasVar (Player := P) (L := L) (Γ := viewVCtx who Γ) h with
    ⟨σ, hv, ⟨hτ⟩⟩
  cases hτ
  exact hobs x σ.base
    (VHasVar.toErased (Player := P) (L := L) (VHasVar.ofViewVCtx (p := who) hv))
    (view_member_visible (L := L) hv)

/-- Operationalize a behavioral strategy at one commit site by first projecting
the full state down to the committer's visible state. -/
noncomputable def BehavioralStrategy.toOperationalKernel
    {who : P} (σ : BehavioralStrategy (P := P) (L := L) who)
    {Γ : VCtx P L} {b : L.Ty}
    (x : VarId) (R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool) :
    CommitKernel P L who Γ b :=
  fun env => σ.commit x R (projectViewEnv (P := P) (L := L) who env)

/-- Operationalize a pure strategy at one commit site as a point mass. -/
noncomputable def PureStrategy.toOperationalKernel
    {who : P} (σ : PureStrategy (P := P) (L := L) who)
    {Γ : VCtx P L} {b : L.Ty}
    (x : VarId) (R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool) :
    CommitKernel P L who Γ b :=
  fun env => FDist.pure (σ.commit x R (projectViewEnv (P := P) (L := L) who env))

/-- Turn a deterministic strategy into a behavioral one. -/
noncomputable def PureStrategy.toBehavioral
    {who : P} (σ : PureStrategy (P := P) (L := L) who) :
    BehavioralStrategy (P := P) (L := L) who where
  commit := fun {Γ} {b} x R view => FDist.pure (σ.commit (Γ := Γ) (b := b) x R view)
  normalized := by
    intro Γ b x R view
    simp [FDist.totalWeight_pure]

/-- Determinize a pure profile into a behavioral profile. -/
noncomputable def PureProfile.toBehavioral (σ : PureProfile (P := P) (L := L)) :
    BehavioralProfile (P := P) (L := L) :=
  fun who => (σ who).toBehavioral

/-- Assemble a behavioral profile into the evaluator-facing operational
profile. -/
noncomputable def BehavioralProfile.toOperationalProfile
    (σ : BehavioralProfile (P := P) (L := L)) :
    OperationalProfile P L where
  commit := fun who x R env => (σ who).toOperationalKernel x R env

/-- Assemble a pure profile into the evaluator-facing operational profile. -/
noncomputable def PureProfile.toOperationalProfile
    (σ : PureProfile (P := P) (L := L)) :
    OperationalProfile P L :=
  (σ.toBehavioral).toOperationalProfile

theorem BehavioralProfile.toOperationalProfile_normalizedOn
    (σ : BehavioralProfile (P := P) (L := L))
    (p : VegasCore P L Γ) :
    (σ.toOperationalProfile).NormalizedOn p := by
  induction p with
  | ret u => trivial
  | letExpr x e k ih => exact ih
  | sample x τ m D' k ih => exact ih
  | commit x who R k ih =>
      exact ⟨(fun env => (σ who).normalized x R (projectViewEnv (P := P) (L := L) who env)), ih⟩
  | reveal y who x hx k ih => exact ih

theorem PureProfile.toOperationalProfile_normalizedOn
    (σ : PureProfile (P := P) (L := L))
    (p : VegasCore P L Γ) :
    (σ.toOperationalProfile).NormalizedOn p :=
  (σ.toBehavioral).toOperationalProfile_normalizedOn p

theorem BehavioralStrategy.toOperationalKernel_respectsObservation
    {who : P} (σ : BehavioralStrategy (P := P) (L := L) who)
    {Γ : VCtx P L} {b : L.Ty}
    (x : VarId) (R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool) :
    KernelRespectsObservation (L := L) (Γ := Γ) (who := who)
      (σ.toOperationalKernel x R) := by
  intro ρ₁ ρ₂ hobs
  unfold BehavioralStrategy.toOperationalKernel
  rw [projectViewEnv_eq_of_obsEq (L := L) hobs]

theorem BehavioralProfile.toOperationalProfile_respectsObservation
    (σ : BehavioralProfile (P := P) (L := L))
    {Γ : VCtx P L} (p : VegasCore P L Γ) :
    OperationalProfileRespectsObservation (L := L) σ.toOperationalProfile p := by
  induction p with
  | ret u => trivial
  | letExpr x e k ih => exact ih
  | sample x τ m D' k ih => exact ih
  | commit x who R k ih =>
      exact ⟨(σ who).toOperationalKernel_respectsObservation x R, ih⟩
  | reveal y who x hx k ih => exact ih

end Vegas
