import Mathlib.Probability.ProbabilityMassFunction.Basic
import Vegas.Scope

/-!
# Vegas view kernels

Reusable view-indexed kernel primitives for Vegas strategies.

The user-facing strategic objects now live in the fixed-program modules
`Vegas.Strategic` and `Vegas.PureStrategic`. This file keeps only the common
view/projection machinery they share.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- The visible erased environment available to player `who` in context `Γ`. -/
abbrev ViewEnv (who : P) (Γ : VCtx P L) : Type :=
  Env L.Val (eraseVCtx (viewVCtx who Γ))

/-- A deterministic choice rule indexed by a player's actual view. -/
abbrev PureKernel (who : P) (Γ : VCtx P L) (b : L.Ty) : Type :=
  ViewEnv who Γ → L.Val b

/-- A behavioral choice rule indexed by a player's actual view. -/
abbrev BehavioralKernel (who : P) (Γ : VCtx P L) (b : L.Ty) : Type :=
  ViewEnv who Γ → FDist (L.Val b)

private theorem visibleVars_cons_of_canSee_true
    {who : P} {y : VarId} {σ : BindTy P L} {Γ : VCtx P L}
    (hsee : canSee who σ = true) :
    visibleVars who ((y, σ) :: Γ) =
      insert y (visibleVars who Γ) := by
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
    visibleVars who ((y, σ) :: Γ) =
      visibleVars who Γ := by
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
      x ∈ visibleVars who Γ := by
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
        · rw [visibleVars_cons_of_canSee_true hsee]
          exact Finset.mem_insert_self _ _
        · rw [visibleVars_cons_of_canSee_true hsee]
          exact Finset.mem_insert_of_mem (ih htl)
      | false =>
        intro hx
        have hview : viewVCtx who ((y, σ) :: tl) = viewVCtx who tl := by
          simp [viewVCtx, hsee]
        rw [hview] at hx
        rw [visibleVars_cons_of_canSee_false hsee]
        exact ih hx

private theorem view_member_visible
    {who : P} {Γ : VCtx P L} {x : VarId} {τ : BindTy P L}
    (h : VHasVar (viewVCtx who Γ) x τ) :
    x ∈ visibleVars who Γ :=
  mem_visibleVars_of_view_member (HasVar.mem_map_fst h)

/-- Project a full erased environment to the visible erased environment for
player `who`. Defined recursively on the context for clean reduction. -/
noncomputable def projectViewEnv (who : P) {Γ : VCtx P L}
    (env : Env L.Val (eraseVCtx Γ)) :
    ViewEnv who Γ := by
  intro x τ h
  rcases HasVar.toVHasVar (Γ := viewVCtx who Γ) h with
    ⟨σ, hv, ⟨hτ⟩⟩
  cases hτ
  exact env _ _ (VHasVar.toErased (VHasVar.ofViewVCtx (p := who) hv))

/-- `projectViewEnv` at a specific view variable equals some env lookup at the
corresponding erased variable. The specific HasVar proof comes from the
toVHasVar→ofViewVCtx→toErased chain. -/
theorem projectViewEnv_apply {who : P} {Γ : VCtx P L}
    (env : Env L.Val (eraseVCtx Γ))
    {y : VarId} {σ : L.Ty} (h_view : HasVar (eraseVCtx (viewVCtx who Γ)) y σ) :
    ∃ hy : HasVar (eraseVCtx Γ) y σ, projectViewEnv who env y σ h_view = env y σ hy := by
  dsimp [projectViewEnv]
  rcases HasVar.toVHasVar h_view with ⟨σ_bt, hv, ⟨hτ⟩⟩
  subst hτ
  exact ⟨hv.ofViewVCtx.toErased, rfl⟩

/-- Projecting an erased `VEnv` to a player's view agrees with first taking the
structured `VEnv.toView` projection and then erasing it.

This is the canonical bridge between the strategy-facing erased view API
(`projectViewEnv`) and the visibility-structured environment API
(`VEnv.toView`). It needs `WFCtx Γ` because the two sides route through
different `HasVar` witnesses; unique variable names make those witnesses
proof-irrelevant. -/
theorem projectViewEnv_eraseEnv_eq_toView
    {who : P} {Γ : VCtx P L}
    (hctx : WFCtx Γ) (env : VEnv (Player := P) L Γ) :
    projectViewEnv who (VEnv.eraseEnv env) =
      VEnv.eraseEnv (VEnv.toView who env) := by
  funext x τ h
  dsimp [projectViewEnv]
  rcases HasVar.toVHasVar (Γ := viewVCtx who Γ) h with
    ⟨σ, hv, ⟨hτ⟩⟩
  cases hτ
  have hnodup_view : ((eraseVCtx (viewVCtx who Γ)).map Prod.fst).Nodup := by
    rw [eraseVCtx_map_fst]
    exact WFCtx.viewVCtx hctx
  have hh : h = hv.toErased := HasVar.eq_of_nodup hnodup_view h hv.toErased
  rw [hh]
  simp [VEnv.toView]

theorem projectViewEnv_eq_of_obsEq
    {who : P} {Γ : VCtx P L}
    {ρ₁ ρ₂ : Env L.Val (eraseVCtx Γ)}
    (hobs : ObsEq (Γ := Γ) who ρ₁ ρ₂) :
    projectViewEnv who ρ₁ =
      projectViewEnv who ρ₂ := by
  funext x τ h
  dsimp [projectViewEnv]
  rcases HasVar.toVHasVar (Γ := viewVCtx who Γ) h with
    ⟨σ, hv, ⟨hτ⟩⟩
  cases hτ
  exact hobs x σ.base
    (VHasVar.toErased (VHasVar.ofViewVCtx (p := who) hv))
    (view_member_visible hv)

/-- If the views through `VEnv.cons v₁ env₁` and `VEnv.cons v₂ env₂` agree,
then the views through `env₁` and `env₂` agree (on old variables). -/
theorem projectViewEnv_cons_eq
    {who : P} {Γ : VCtx P L} {x : VarId} {τ : BindTy P L}
    {env₁ env₂ : VEnv L Γ}
    {v₁ v₂ : L.Val τ.base}
    (hnodup : (((x, τ) :: Γ).map Prod.fst).Nodup)
    (h : projectViewEnv who
        (VEnv.eraseEnv (VEnv.cons (x := x) v₁ env₁)) =
      projectViewEnv who
        (VEnv.eraseEnv (VEnv.cons (x := x) v₂ env₂))) :
    projectViewEnv who
        (VEnv.eraseEnv env₁) =
      projectViewEnv who
        (VEnv.eraseEnv env₂) := by
  -- Step 1: projectViewEnv eq → ObsEq for extended context
  -- (converse of projectViewEnv_eq_of_obsEq — needs viewVCtx/HasVar infrastructure)
  -- nodup of erased context names (from hnodup + eraseVCtx preserves names)
  have hnodup_e : ((eraseVCtx ((x, τ) :: Γ)).map Prod.fst).Nodup := by
    rwa [eraseVCtx_map_fst]
  have hobs_ext : ObsEq (Γ := (x, τ) :: Γ) who
      (VEnv.eraseEnv (VEnv.cons v₁ env₁)) (VEnv.eraseEnv (VEnv.cons v₂ env₂)) := by
    intro y' σ₀ hy' hvis'
    -- y' is visible → construct HasVar in eraseVCtx(viewVCtx) via Classical
    have hmem : y' ∈ ((x, τ) :: Γ).map Prod.fst :=
      mem_visibleVars_map_fst hvis'
    -- Get a view HasVar for y'
    have hmem_view := mem_viewVCtx_map_fst_of_visible hvis'
    rw [← eraseVCtx_map_fst] at hmem_view
    rcases List.mem_map.mp hmem_view with ⟨⟨y_name, σ_b⟩, h_mem_e, hfst⟩
    -- y_name = y' (from hfst), σ_b is the erased type in viewVCtx
    have h_view : HasVar (eraseVCtx (viewVCtx who ((x, τ) :: Γ))) y' σ_b := by
      rw [← hfst]; exact HasVar.ofMem h_mem_e
    -- projectViewEnv_apply: projectViewEnv who ρ y' σ_b h_view = ρ y' σ_b hy_v for some hy_v
    rcases projectViewEnv_apply (VEnv.eraseEnv (VEnv.cons v₁ env₁)) h_view with ⟨hy_v₁, hpv₁⟩
    rcases projectViewEnv_apply (VEnv.eraseEnv (VEnv.cons v₂ env₂)) h_view with ⟨hy_v₂, hpv₂⟩
    -- From h: projectViewEnv eq at h_view
    have h_pt := congr_fun (congr_fun (congr_fun h y') σ_b) h_view
    -- h_pt: pv₁ = pv₂. By apply: ρ₁ y' σ_b hy_v₁ = ρ₂ y' σ_b hy_v₂
    rw [hpv₁, hpv₂] at h_pt
    -- h_pt: ρ₁ y' σ_b hy_v₁ = ρ₂ y' σ_b hy_v₂
    -- By type_unique: σ₀ = σ_b
    have htype := HasVar.type_unique hnodup_e hy' hy_v₁
    subst htype
    -- By eq_of_nodup: hy' = hy_v₁ and hy' = hy_v₂
    rw [HasVar.eq_of_nodup hnodup_e hy' hy_v₁]
    conv_rhs => rw [HasVar.eq_of_nodup hnodup_e hy_v₁ hy_v₂]
    exact h_pt
  -- Step 2: ObsEq for (x,τ)::Γ restricted to old vars → ObsEq for Γ
  have hobs : ObsEq (Γ := Γ) who (VEnv.eraseEnv env₁) (VEnv.eraseEnv env₂) := by
    intro y' σ₀ hy' hvis'
    have hvis_ext : y' ∈ visibleVars who ((x, τ) :: Γ) := by
      cases τ with
      | pub b => simp [visibleVars, hvis']
      | hidden owner b =>
        simp only [visibleVars]
        split <;> simp_all [Finset.mem_insert]
    have := hobs_ext y' σ₀ (.there hy') hvis_ext
    simp only [VEnv.eraseEnv, Env.cons] at this
    exact this
  exact projectViewEnv_eq_of_obsEq hobs

/-- If `canSee who τ` and the views through `VEnv.cons v₁ env₁` and
`VEnv.cons v₂ env₂` agree, then `v₁ = v₂`. -/
theorem projectViewEnv_cons_head_eq
    {who : P} {Γ : VCtx P L} {x : VarId} {τ : BindTy P L}
    {env₁ env₂ : VEnv L Γ}
    {v₁ v₂ : L.Val τ.base}
    (hnodup : (((x, τ) :: Γ).map Prod.fst).Nodup)
    (hsee : canSee who τ = true)
    (h : projectViewEnv who
        (VEnv.eraseEnv (VEnv.cons (x := x) v₁ env₁)) =
      projectViewEnv who
        (VEnv.eraseEnv (VEnv.cons (x := x) v₂ env₂))) :
    v₁ = v₂ := by
  have hvm : viewVCtx who ((x, τ) :: Γ) = (x, τ) :: viewVCtx who Γ := by
    simp [viewVCtx, hsee]
  have h_view : HasVar (eraseVCtx (viewVCtx who ((x, τ) :: Γ))) x τ.base := by
    rw [hvm]; exact HasVar.here
  have hnodup_e : ((eraseVCtx ((x, τ) :: Γ)).map Prod.fst).Nodup := by
    rwa [eraseVCtx_map_fst]
  rcases projectViewEnv_apply (VEnv.eraseEnv (VEnv.cons v₁ env₁)) h_view with ⟨hy₁, hpv₁⟩
  rcases projectViewEnv_apply (VEnv.eraseEnv (VEnv.cons v₂ env₂)) h_view with ⟨hy₂, hpv₂⟩
  have h_eq := congr_fun (congr_fun (congr_fun h x) τ.base) h_view
  rw [hpv₁, hpv₂] at h_eq
  rw [HasVar.eq_of_nodup hnodup_e hy₁ HasVar.here,
      HasVar.eq_of_nodup hnodup_e hy₂ HasVar.here] at h_eq
  simp only [VEnv.eraseEnv, Env.cons] at h_eq
  exact h_eq

end Vegas
