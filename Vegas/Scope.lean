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
- `Scoped p` is the recursive scoping judgment for raw Vegas programs
- `KernelRespectsObservation` / `ProfileRespectsObservation` state that
  behavioral strategies are invariant under observationally equivalent states

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
      intro x hx
      simpa [publicVars, visibleVars] using hx
  | cons hd tl ih =>
      obtain ⟨x, τ⟩ := hd
      cases τ with
      | pub b =>
          intro y hy
          simp [publicVars, visibleVars] at hy ⊢
          rcases hy with rfl | hy
          · exact Or.inl rfl
          · exact Or.inr (ih hy)
      | hidden owner b =>
          by_cases hown : who = owner
          · intro y hy
            simp [visibleVars, hown]
            exact Or.inr (by simpa [hown] using ih hy)
          · simpa [publicVars, visibleVars, hown] using ih

/-- Erasing visibility annotations preserves the variable-name projection. -/
theorem eraseVCtx_map_fst {Γ : VCtx P L} :
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
    {Γ : VCtx P L}
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
def Scoped :
    {Γ : VCtx P L} → VegasCore P L Γ → Prop
  | _, .ret payoffs => PayoffUsesOnlyPublic (P := P) (L := L) payoffs
  | _, .letExpr _ _ k => Scoped k
  | _, .sample _ _ _ _ k => Scoped k
  | Γ, .commit x who R k => GuardUsesOnly (L := L) (Γ := Γ) (x := x) (who := who) R ∧ Scoped k
  | _, .reveal _ _ _ _ k => Scoped k

/-- Full paper-facing static discipline: SSA/reveal well-formedness plus
    visibility scoping. -/
def ScopedProg {Γ : VCtx P L} (p : VegasCore P L Γ) : Prop :=
  WFProg p ∧ Scoped p

/-- Observation-respecting behavioral kernels depend only on the owner's
    observable state. -/
def KernelRespectsObservation
    {Γ : VCtx P L} {who : P} {b : L.Ty}
    (κ : Env L.Val (eraseVCtx Γ) → FDist (L.Val b)) : Prop :=
  ∀ ρ₁ ρ₂, ObsEq (L := L) (Γ := Γ) who ρ₁ ρ₂ → κ ρ₁ = κ ρ₂

/-- Observation-respecting raw profiles choose the same commit distribution on
    observationally equivalent states at every commit site. -/
def ProfileRespectsObservation (σ : Profile P L) :
    {Γ : VCtx P L} → VegasCore P L Γ → Prop
  | _, .ret _ => True
  | _, .letExpr _ _ k => ProfileRespectsObservation σ k
  | _, .sample _ _ _ _ k => ProfileRespectsObservation σ k
  | Γ, .commit x who R k =>
      KernelRespectsObservation (L := L) (Γ := Γ) (who := who) (σ.commit who x R) ∧
      ProfileRespectsObservation σ k
  | _, .reveal _ _ _ _ k => ProfileRespectsObservation σ k

/-- Convenience projection from a scoped commit node to its guard-scoping fact. -/
theorem Scoped.commit_guard_usesOnly
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (hsc : Scoped (.commit x who R k)) :
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

/-- A profile satisfying `ProfileRespectsObservation` chooses the same commit
    kernel output on observationally equivalent states at every commit site. -/
theorem ProfileRespectsObservation.commit_eq_of_obsEq
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    {σ : Profile P L}
    (hσ : ProfileRespectsObservation (L := L) σ (.commit x who R k))
    {ρ₁ ρ₂ : Env L.Val (eraseVCtx Γ)}
    (hobs : ObsEq (L := L) (Γ := Γ) who ρ₁ ρ₂) :
    σ.commit who x R ρ₁ = σ.commit who x R ρ₂ :=
  hσ.1 ρ₁ ρ₂ hobs

end Vegas
