import Vegas.WF

/-!
# Visibility scoping and observation

This file separates Vegas's raw operational core from the static visibility
discipline it is intended to model.

The core syntax is typed over full erased environments. The predicates here
recover the intended information-flow discipline extrinsically:

- `visibleVars who Γ` characterizes what player `who` can observe in context `Γ`
- `GuardUsesOnly who x Γ R` states that commit guard `R` depends only on the
  proposed action `x` and variables visible to `who`
- `ViewScoped p` is the recursive scoping judgment for raw Vegas programs
- `KernelRespectsObservation` / `OmniscientOperationalProfileRespectsObservation` state
  that operational kernels are invariant under observationally equivalent states

These predicates let us reason about visibility without re-encoding it into the
raw core syntax.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Variable identifiers publicly observable in a visibility context. -/
def publicVars : VCtx P L → Finset VarId
  | [] => ∅
  | (x, .pub _) :: Γ => insert x (publicVars Γ)
  | (_, .hidden _ _) :: Γ => publicVars Γ

/-- Variable identifiers observable to player `who` in a visibility context. -/
def visibleVars (who : P) : VCtx P L → Finset VarId
  | [] => ∅
  | (x, .pub _) :: Γ => insert x (visibleVars who Γ)
  | (x, .hidden owner _) :: Γ =>
      if who = owner then insert x (visibleVars who Γ) else visibleVars who Γ

/-- Public variables are visible to every player. -/
theorem publicVars_subset_visibleVars
    (who : P) {Γ : VCtx P L} :
    publicVars (P := P) (L := L) Γ ⊆ visibleVars (L := L) who Γ := by
  induction Γ with
  | nil =>
      intro _ hx
      simp [publicVars] at hx
  | cons hd tl ih =>
      obtain ⟨z, τ⟩ := hd
      cases τ with
      | pub b =>
          intro y hy
          rcases Finset.mem_insert.mp hy with rfl | hy
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (ih hy)
      | hidden owner b =>
          by_cases hown : who = owner
          · intro y hy
            simpa [visibleVars, hown] using Finset.mem_insert_of_mem (ih hy)
          · simpa [publicVars, visibleVars, hown] using ih

/-- Every visible variable comes from the ambient visibility context. -/
theorem mem_visibleVars_map_fst
    {who : P} {Γ : VCtx P L} {x : VarId} :
    x ∈ visibleVars (L := L) who Γ → x ∈ Γ.map Prod.fst := by
  induction Γ with
  | nil =>
      intro hx
      simp [visibleVars] at hx
  | cons hd tl ih =>
      obtain ⟨z, τ⟩ := hd
      cases τ with
      | pub b =>
          intro hx
          rcases Finset.mem_insert.mp (by simpa [visibleVars] using hx) with rfl | htl
          · simp
          · exact List.mem_cons_of_mem _ (ih htl)
      | hidden owner b =>
          by_cases hown : who = owner
          · intro hx
            subst hown
            rcases Finset.mem_insert.mp (by simpa [visibleVars] using hx) with rfl | htl
            · simp
            · exact List.mem_cons_of_mem _ (ih htl)
          · intro hx
            exact List.mem_cons_of_mem _ (ih (by simpa [visibleVars, hown] using hx))

/-- Erasing visibility annotations preserves the variable-name projection. -/
theorem eraseVCtx_map_fst {P : Type} {L : IExpr} {Γ : VCtx P L} :
    (eraseVCtx Γ).map Prod.fst = Γ.map Prod.fst := by
  induction Γ with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨x, τ⟩ := hd
      simp [eraseVCtx, ih]

/-- Two erased environments are observationally equivalent for player `who`
    when they agree on every variable visible to `who`. -/
def ObsEq {Γ : VCtx P L} (who : P)
    (ρ₁ ρ₂ : Env L.Val (eraseVCtx Γ)) : Prop :=
  AgreesOn ρ₁ ρ₂ (visibleVars (L := L) who Γ)

theorem ObsEq.refl {Γ : VCtx P L} (who : P)
    (ρ : Env L.Val (eraseVCtx Γ)) :
    ObsEq (L := L) (Γ := Γ) who ρ ρ :=
  fun _ _ _ _ => rfl

theorem ObsEq.symm {Γ : VCtx P L} {who : P}
    {ρ₁ ρ₂ : Env L.Val (eraseVCtx Γ)}
    (h : ObsEq (L := L) (Γ := Γ) who ρ₁ ρ₂) :
    ObsEq (L := L) (Γ := Γ) who ρ₂ ρ₁ := by
  intro x τ hx hmem
  exact (h x τ hx hmem).symm

theorem ObsEq.trans {Γ : VCtx P L} {who : P}
    {ρ₁ ρ₂ ρ₃ : Env L.Val (eraseVCtx Γ)}
    (h₁₂ : ObsEq (L := L) (Γ := Γ) who ρ₁ ρ₂)
    (h₂₃ : ObsEq (L := L) (Γ := Γ) who ρ₂ ρ₃) :
    ObsEq (L := L) (Γ := Γ) who ρ₁ ρ₃ := by
  intro x τ hx hmem
  exact Eq.trans (h₁₂ x τ hx hmem) (h₂₃ x τ hx hmem)

/-- Plain-context membership implies name membership in the context's variable
    projection. -/
theorem HasVar.mem_map_fst {Γ : Ctx L.Ty} {x : VarId} {τ : L.Ty} :
    HasVar Γ x τ → x ∈ Γ.map Prod.fst := by
  intro h
  induction h with
  | here => simp
  | there _ ih => exact List.mem_cons_of_mem _ ih

/-- If two erased environments agree on `S`, then extending both with the same
    fresh variable/value yields agreement on `insert x S`. -/
theorem AgreesOn.cons_insert_of_fresh
    {P : Type} {L : IExpr} {Γ : VCtx P L}
    {ρ₁ ρ₂ : Env L.Val (eraseVCtx Γ)}
    {S : Finset VarId} {x : VarId} {b : L.Ty} {a : L.Val b}
    (hfresh : Fresh (P := P) (L := L) x Γ)
    (h : AgreesOn ρ₁ ρ₂ S) :
    AgreesOn (Env.cons (x := x) a ρ₁) (Env.cons (x := x) a ρ₂) (insert x S) := by
  intro y τ hy hmem
  cases hy with
  | here => rfl
  | there hy' =>
      have hne : y ≠ x := by
        intro hyx
        apply hfresh
        rw [← eraseVCtx_map_fst (P := P) (L := L) (Γ := Γ)]
        simpa [hyx] using HasVar.mem_map_fst (L := L) hy'
      have hmemS : y ∈ S := by
        rcases Finset.mem_insert.mp hmem with rfl | hs
        · exact False.elim (hne rfl)
        · exact hs
      simpa using h y τ hy' hmemS

/-- Payoff expressions are already typed over the public context. This predicate
    exists as a named scoping layer for the paper-facing static discipline. -/
def PayoffUsesOnlyPublic
    {Γ : VCtx P L}
    (_payoffs : List (P × L.Expr (erasePubVCtx Γ) L.int)) : Prop := True

/-- A commit guard may depend only on the proposed value and variables visible
    to the committing player. -/
def GuardUsesOnly
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    (R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool) : Prop :=
  L.exprDeps R ⊆ insert x (visibleVars (L := L) who Γ)

/-- Player-private distributions are still intrinsically scoped by their
    syntax. This predicate exists to keep the extrinsic scoping story uniform. -/
def PrivateDistUsesOnly
    {Γ : VCtx P L} {who : P} {b : L.Ty}
    (_D : L.DistExpr (eraseVCtx (flattenVCtx (viewVCtx who Γ))) b) : Prop := True

/-- Recursive visibility-scoping judgment for raw Vegas programs. The only
    nontrivial new obligation after the guard refactor is at commit nodes. -/
def ViewScoped :
    {Γ : VCtx P L} → VegasCore P L Γ → Prop
  | _, .ret payoffs => PayoffUsesOnlyPublic (P := P) (L := L) payoffs
  | _, .letExpr _ _ k => ViewScoped k
  | _, .sample _ _ k => ViewScoped k
  | Γ, .commit x who R k =>
      GuardUsesOnly (L := L) (Γ := Γ) (x := x) (who := who) R ∧ ViewScoped k
  | _, .reveal _ _ _ _ k => ViewScoped k

/-- Full well-formedness: fresh bindings, reveal completeness, and view scoping. -/
def WF {Γ : VCtx P L} (p : VegasCore P L Γ) : Prop :=
  FreshBindings p ∧ RevealComplete [] p ∧ ViewScoped p

/-- Observation-respecting behavioral kernels depend only on the owner's
    observable state. -/
def KernelRespectsObservation
    {Γ : VCtx P L} {who : P} {b : L.Ty}
    (κ : Env L.Val (eraseVCtx Γ) → FDist (L.Val b)) : Prop :=
  ∀ ρ₁ ρ₂, ObsEq (L := L) (Γ := Γ) who ρ₁ ρ₂ → κ ρ₁ = κ ρ₂

/-- Observation-respecting raw profiles choose the same commit distribution on
    observationally equivalent states at every commit site. -/
def OmniscientOperationalProfileRespectsObservation (σ : OmniscientOperationalProfile P L) :
    {Γ : VCtx P L} → VegasCore P L Γ → Prop
  | _, .ret _ => True
  | _, .letExpr _ _ k => OmniscientOperationalProfileRespectsObservation σ k
  | _, .sample _ _ k => OmniscientOperationalProfileRespectsObservation σ k
  | Γ, .commit x who R k =>
      KernelRespectsObservation (L := L) (Γ := Γ) (who := who) (σ.commit who x R) ∧
      OmniscientOperationalProfileRespectsObservation σ k
  | _, .reveal _ _ _ _ k => OmniscientOperationalProfileRespectsObservation σ k

/-- Convenience projection from a scoped commit node to its guard-scoping fact. -/
theorem ViewScoped.commit_guard_usesOnly
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (hsc : ViewScoped (.commit x who R k)) :
    GuardUsesOnly (L := L) (Γ := Γ) (x := x) (who := who) R :=
  hsc.1

/-- Guard evaluation is invariant under observationally equivalent erased
    environments, provided the guard only depends on the committer's view and
    the proposed action variable is fresh in the context. -/
theorem evalGuard_eq_of_obsEq
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    (hfresh : Fresh (P := P) (L := L) x Γ)
    (hR : GuardUsesOnly (L := L) (Γ := Γ) (x := x) (who := who) R)
    {a : L.Val b}
    {ρ₁ ρ₂ : Env L.Val (eraseVCtx Γ)}
    (hobs : ObsEq (L := L) (Γ := Γ) who ρ₁ ρ₂) :
    evalGuard (Player := P) (L := L) R a ρ₁ =
      evalGuard (Player := P) (L := L) R a ρ₂ := by
  unfold evalGuard
  apply congrArg L.toBool
  apply L.expr_deps_sound
  exact AgreesOn.mono
    (AgreesOn.cons_insert_of_fresh (P := P) (L := L) (Γ := Γ)
      (x := x) (b := b) (a := a) hfresh hobs)
    hR

/-- Observation-respecting kernels agree on observationally equivalent states. -/
theorem KernelRespectsObservation.eq_of_obsEq
    {Γ : VCtx P L} {who : P} {b : L.Ty}
    {κ : Env L.Val (eraseVCtx Γ) → FDist (L.Val b)}
    (hκ : KernelRespectsObservation (L := L) (Γ := Γ) (who := who) κ)
    {ρ₁ ρ₂ : Env L.Val (eraseVCtx Γ)}
    (hobs : ObsEq (L := L) (Γ := Γ) who ρ₁ ρ₂) :
    κ ρ₁ = κ ρ₂ :=
  hκ ρ₁ ρ₂ hobs

/-- Chosen witness for `IExpr.extendAfterHead`. -/
noncomputable def extendAfterHeadExpr
    {Γ : Ctx L.Ty} {x y : VarId} {τ σ b : L.Ty}
    (e : L.Expr ((x, τ) :: Γ) b) :
    L.Expr ((x, τ) :: (y, σ) :: Γ) b :=
  Classical.choose (L.extendAfterHead e)

theorem eval_extendAfterHeadExpr
    {Γ : Ctx L.Ty} {x y : VarId} {τ σ b : L.Ty}
    (e : L.Expr ((x, τ) :: Γ) b)
    (vx : L.Val τ) (vy : L.Val σ) (env : Env L.Val Γ) :
    L.eval (extendAfterHeadExpr (L := L) (x := x) (y := y) (τ := τ) (σ := σ) e)
      (Env.cons (x := x) vx (Env.cons (x := y) vy env)) =
    L.eval e (Env.cons (x := x) vx env) :=
  (Classical.choose_spec (L.extendAfterHead e)) vx vy env

/-- Chosen witness for `IExpr.dropAfterHead`. -/
noncomputable def dropAfterHeadExpr
    {Γ : Ctx L.Ty} {x y : VarId} {τ σ b : L.Ty}
    (e : L.Expr ((x, τ) :: (y, σ) :: Γ) b)
    (hy : y ∉ L.exprDeps e) :
    L.Expr ((x, τ) :: Γ) b :=
  Classical.choose (L.dropAfterHead e hy)

theorem eval_dropAfterHeadExpr
    {Γ : Ctx L.Ty} {x y : VarId} {τ σ b : L.Ty}
    (e : L.Expr ((x, τ) :: (y, σ) :: Γ) b)
    (hy : y ∉ L.exprDeps e)
    (vx : L.Val τ) (vy : L.Val σ) (env : Env L.Val Γ) :
    L.eval (dropAfterHeadExpr (L := L) (x := x) (y := y) (τ := τ) (σ := σ) e hy)
      (Env.cons (x := x) vx env) =
    L.eval e (Env.cons (x := x) vx (Env.cons (x := y) vy env)) :=
  (Classical.choose_spec (L.dropAfterHead e hy)) vx vy env

/-- A freshly introduced hidden variable owned by another player is not visible
    in the extended context. -/
theorem not_mem_visibleVars_hidden_other
    {Γ : VCtx P L} {x : VarId} {who owner : P} {τ : L.Ty}
    (hfresh : Fresh (P := P) (L := L) x Γ)
    (hneq : who ≠ owner) :
    x ∉ visibleVars (L := L) who ((x, .hidden owner τ) :: Γ) := by
  intro hx
  apply hfresh
  exact mem_visibleVars_map_fst (L := L) (who := who) (by simpa [visibleVars, hneq] using hx)

/-- For a distinct player, the freshly committed hidden value is outside the
    allowed dependency set of the next guard. -/
theorem GuardUsesOnly.not_mem_hidden_other
    {Γ : VCtx P L}
    {x₁ x₂ : VarId} {who₁ who₂ : P} {b₁ b₂ : L.Ty}
    {R : L.Expr ((x₂, b₂) :: eraseVCtx ((x₁, .hidden who₁ b₁) :: Γ)) L.bool}
    (hR : GuardUsesOnly (L := L) (Γ := ((x₁, .hidden who₁ b₁) :: Γ))
      (x := x₂) (who := who₂) R)
    (hfresh₁ : Fresh (P := P) (L := L) x₁ Γ)
    (hfresh₂ : Fresh (P := P) (L := L) x₂ ((x₁, .hidden who₁ b₁) :: Γ))
    (hneq : who₂ ≠ who₁) :
    x₁ ∉ L.exprDeps R := by
  intro hx
  have hx' := hR hx
  rcases Finset.mem_insert.mp hx' with hxeq | hxvis
  · apply hfresh₂
    simp [hxeq]
  · exact (not_mem_visibleVars_hidden_other (L := L) (Γ := Γ)
      (x := x₁) (who := who₂) (owner := who₁) (τ := b₁) hfresh₁ hneq) hxvis

/-- An operational profile satisfying
`OmniscientOperationalProfileRespectsObservation` chooses the same commit
    kernel output on observationally equivalent states at every commit site. -/
theorem OmniscientOperationalProfileRespectsObservation.commit_eq_of_obsEq
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    {σ : OmniscientOperationalProfile P L}
    (hσ : OmniscientOperationalProfileRespectsObservation (L := L) σ (.commit x who R k))
    {ρ₁ ρ₂ : Env L.Val (eraseVCtx Γ)}
    (hobs : ObsEq (L := L) (Γ := Γ) who ρ₁ ρ₂) :
    σ.commit who x R ρ₁ = σ.commit who x R ρ₂ :=
  hσ.1 ρ₁ ρ₂ hobs

end Vegas
