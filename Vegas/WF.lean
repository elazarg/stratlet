import Vegas.VegasSimple

/-!
# Vegas well-formedness and side conditions

Static predicates on Vegas protocols: SSA-style freshness, reveal completeness,
legality, admissibility, and normalization obligations.
-/

namespace Vegas

def Fresh {P : Type} {L : Vegas.IExpr}
    (x : VarId) (Γ : Vegas.VCtx P L) : Prop :=
  x ∉ Γ.map Prod.fst

def WFCtx {P : Type} {L : Vegas.IExpr}
    (Γ : Vegas.VCtx P L) : Prop :=
  (Γ.map Prod.fst).Nodup

instance {P : Type} {L : Vegas.IExpr} {x : VarId}
    {Γ : Vegas.VCtx P L} : Decidable (Fresh (P := P) (L := L) x Γ) :=
  inferInstanceAs (Decidable (x ∉ _))

def FreshBindings {P : Type} [DecidableEq P]
    {L : Vegas.IExpr}
:
    {Γ : Vegas.VCtx P L} → Vegas.VegasCore P L Γ → Prop
  | _, .ret _ => True
  | Γ, .letExpr x _ k => Fresh x Γ ∧ FreshBindings k
  | Γ, .sample x _ k => Fresh x Γ ∧ FreshBindings k
  | Γ, .commit x _ _ k => Fresh x Γ ∧ FreshBindings k
  | Γ, .reveal y _ _ _ k => Fresh y Γ ∧ FreshBindings k

def decidableFreshBindings {P : Type} [DecidableEq P]
    {L : Vegas.IExpr}
:
    {Γ : Vegas.VCtx P L} → (p : Vegas.VegasCore P L Γ) → Decidable (FreshBindings p)
  | _, .ret _ => .isTrue trivial
  | _, .letExpr _ _ k => @instDecidableAnd _ _ (inferInstance) (decidableFreshBindings k)
  | _, .sample _ _ k => @instDecidableAnd _ _ (inferInstance) (decidableFreshBindings k)
  | _, .commit _ _ _ k => @instDecidableAnd _ _ (inferInstance) (decidableFreshBindings k)
  | _, .reveal _ _ _ _ k => @instDecidableAnd _ _ (inferInstance) (decidableFreshBindings k)

instance {P : Type} [DecidableEq P]
    {L : Vegas.IExpr}
    {Γ : Vegas.VCtx P L} {p : Vegas.VegasCore P L Γ} :
    Decidable (FreshBindings p) := decidableFreshBindings p

/-- Every committed secret is revealed exactly once. `pending` tracks
    commit variables awaiting revelation. -/
def RevealComplete {P : Type} [DecidableEq P]
    {L : Vegas.IExpr}
:
    {Γ : Vegas.VCtx P L} → List VarId → Vegas.VegasCore P L Γ → Prop
  | _, pending, .ret _ => pending = []
  | _, pending, .letExpr _ _ k => RevealComplete pending k
  | _, pending, .sample _ _ k => RevealComplete pending k
  | _, pending, .commit x _ _ k => RevealComplete (x :: pending) k
  | _, pending, .reveal _ _ x _ k =>
    x ∈ pending ∧ RevealComplete (pending.filter (· ≠ x)) k

instance : DecidableEq VarId := inferInstanceAs (DecidableEq Nat)

def decidableRevealComplete {P : Type} [DecidableEq P]
    {L : Vegas.IExpr}
:
    {Γ : Vegas.VCtx P L} →
    (pending : List VarId) → (p : Vegas.VegasCore P L Γ) →
    Decidable (RevealComplete pending p)
  | _, _, .ret _ => inferInstanceAs (Decidable (_ = []))
  | _, pending, .letExpr _ _ k => decidableRevealComplete pending k
  | _, pending, .sample _ _ k => decidableRevealComplete pending k
  | _, pending, .commit x _ _ k => decidableRevealComplete (x :: pending) k
  | _, pending, .reveal _ _ x _ k =>
    @instDecidableAnd _ _ (inferInstance) (decidableRevealComplete (pending.filter (· ≠ x)) k)

instance {P : Type} [DecidableEq P]
    {L : Vegas.IExpr}
    {pending : List VarId} {Γ : Vegas.VCtx P L} {p : Vegas.VegasCore P L Γ} :
    Decidable (RevealComplete pending p) := decidableRevealComplete pending p

@[simp] theorem WFCtx_nil {P : Type} {L : IExpr} :
    WFCtx (P := P) (L := L) [] := List.nodup_nil

theorem WFCtx.cons {P : Type} {L : IExpr}
    {x : VarId} {τ : BindTy P L} {Γ : VCtx P L}
    (hfresh : Fresh x Γ) (hwf : WFCtx Γ) :
    WFCtx ((x, τ) :: Γ) := by
  change (((x, τ) :: Γ).map Prod.fst).Nodup
  exact List.Nodup.cons hfresh hwf

theorem WFCtx.tail {P : Type} {L : IExpr}
    {x : VarId} {τ : BindTy P L} {Γ : VCtx P L} :
    WFCtx ((x, τ) :: Γ) → WFCtx Γ := by
  intro h; exact (List.nodup_cons.mp h).2

theorem WFCtx.fresh_head {P : Type} {L : IExpr}
    {x : VarId} {τ : BindTy P L} {Γ : VCtx P L} :
    WFCtx ((x, τ) :: Γ) → Fresh x Γ := by
  intro h; exact (List.nodup_cons.mp h).1

theorem VHasVar.mem_map_fst {P : Type} {L : IExpr}
    {Γ : VCtx P L} {x : VarId} {τ : BindTy P L} :
    VHasVar (L := L) Γ x τ → x ∈ Γ.map Prod.fst := by
  intro h; induction h with
  | here => simp
  | there _ ih => exact List.mem_cons_of_mem _ ih

theorem VHasVar.unique {P : Type} {L : IExpr}
    {Γ : VCtx P L} {x : VarId} {τ₁ τ₂ : BindTy P L}
    (hwf : WFCtx Γ) (h1 : VHasVar (L := L) Γ x τ₁)
    (h2 : VHasVar (L := L) Γ x τ₂) :
    τ₁ = τ₂ := by
  induction h1 with
  | here =>
    match h2 with
    | .here => rfl
    | .there h2' => exact absurd (VHasVar.mem_map_fst h2') hwf.fresh_head
  | there h1' ih =>
    match h2 with
    | .here => exact absurd (VHasVar.mem_map_fst h1') hwf.fresh_head
    | .there h2' => exact ih hwf.tail h2'


theorem viewVCtx_map_fst_sub {P : Type} [DecidableEq P] {L : IExpr}
    {x : VarId} {p : P} {Γ : VCtx P L} :
    x ∈ (viewVCtx p Γ).map Prod.fst → x ∈ Γ.map Prod.fst := by
  induction Γ with
  | nil =>
    intro h
    have : False := by
      simp [Vegas.viewVCtx] at h
    exact False.elim this
  | cons hd tl ih =>
    obtain ⟨y, τ⟩ := hd
    cases hsee : Vegas.canSee (Player := P) (L := L) p τ with
    | false =>
      intro h
      have hview : viewVCtx p ((y, τ) :: tl) = viewVCtx p tl := by
        simp [viewVCtx, Vegas.viewVCtx, hsee]
      rw [hview] at h
      exact List.mem_cons_of_mem _ (ih h)
    | true =>
      intro h
      have hview : viewVCtx p ((y, τ) :: tl) = (y, τ) :: viewVCtx p tl := by
        simp [viewVCtx, Vegas.viewVCtx, hsee]
      rw [hview] at h
      simp only [List.map, List.mem_cons] at h ⊢
      rcases h with rfl | htl
      · exact Or.inl rfl
      · exact Or.inr (ih htl)

theorem Fresh_viewVCtx {P : Type} [DecidableEq P] {L : IExpr}
    {x : VarId} {p : P} {Γ : VCtx P L}
    (hfresh : Fresh x Γ) : Fresh x (viewVCtx p Γ) :=
  fun hmem => hfresh (viewVCtx_map_fst_sub hmem)

def Legal {P : Type} [DecidableEq P]
    {L : Vegas.IExpr}
:
    {Γ : Vegas.VCtx P L} → Vegas.VegasCore P L Γ → Prop
  | _, .ret _ => True
  | _, .letExpr _ _ k => Legal k
  | _, .sample _ _ k => Legal k
  | Γ, .commit _ _who (b := b) R k =>
    (∀ env : Env L.Val (Vegas.eraseVCtx Γ),
        ∃ a : L.Val b, Vegas.evalGuard (Player := P) (L := L) R a env = true) ∧
    Legal k
  | _, .reveal _ _ _ _ k => Legal k

def FairPlayProfile {P : Type} [DecidableEq P]
    {L : Vegas.IExpr}
    (σ : Vegas.OmniscientOperationalProfile P L) :
    {Γ : Vegas.VCtx P L} → Vegas.VegasCore P L Γ → Prop
  | _, .ret _ => True
  | _, .letExpr _ _ k => FairPlayProfile σ k
  | _, .sample _ _ k => FairPlayProfile σ k
  | _, .commit x who R k =>
    (∀ env, FDist.Supported (σ.commit who x R env)
      (fun a => Vegas.evalGuard (Player := P) (L := L) R a env = true)) ∧
    FairPlayProfile σ k
  | _, .reveal _ _ _ _ k => FairPlayProfile σ k

namespace DistExpr

abbrev Normalized {Γ : VCtxSimple} {b : BaseTy}
    (D : DistExpr (erasePubVCtx Γ) b) : Prop :=
  ∀ env : VEnvSimple Γ,
    FDist.totalWeight (evalDistExpr D (VEnv.eraseSampleEnv env)) = 1

end DistExpr

def NormalizedDists {P : Type} [DecidableEq P]
    {L : Vegas.IExpr}
:
    {Γ : Vegas.VCtx P L} → Vegas.VegasCore P L Γ → Prop
  | _, .ret _ => True
  | _, .letExpr _ _ k => NormalizedDists k
  | _, .sample _ D' k =>
    (∀ env, FDist.totalWeight (L.evalDist D' (VEnv.eraseSampleEnv env)) = 1) ∧
    NormalizedDists k
  | _, .commit _ _ _ k => NormalizedDists k
  | _, .reveal _ _ _ _ k => NormalizedDists k

def OmniscientOperationalProfile.NormalizedOn {P : Type} [DecidableEq P]
    {L : Vegas.IExpr}
    (σ : Vegas.OmniscientOperationalProfile P L) :
    {Γ : Vegas.VCtx P L} → Vegas.VegasCore P L Γ → Prop
  | _, .ret _ => True
  | _, .letExpr _ _ k => σ.NormalizedOn k
  | _, .sample _ _ k => σ.NormalizedOn k
  | _, .commit x who R k =>
    (∀ view, FDist.totalWeight (σ.commit who x R view) = 1) ∧ σ.NormalizedOn k
  | _, .reveal _ _ _ _ k => σ.NormalizedOn k

theorem DistExpr.Normalized_ite {Γ : CtxSimple} {b : BaseTy}
    {c : Expr Γ .bool} {t f : DistExpr Γ b}
    (ht : ∀ env, FDist.totalWeight (evalDistExpr t env) = 1)
    (hf : ∀ env, FDist.totalWeight (evalDistExpr f env) = 1) :
    ∀ env, FDist.totalWeight (evalDistExpr (.ite c t f) env) = 1 := by
  intro env
  by_cases hc : evalExpr c env
  · simp only [evalDistExpr, hc]; exact ht env
  · simp only [evalDistExpr, hc]; exact hf env

end Vegas
