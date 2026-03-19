import Vegas.VegasSimple

/-!
# Vegas well-formedness and side conditions

Static predicates on Vegas protocols: SSA-style freshness, reveal completeness,
legality, admissibility, and normalization obligations.
-/

namespace Vegas

def Fresh {P : Type} {L : Vegas.ExprLanguage}
    (x : VarId) (Γ : Vegas.Ctx P L) : Prop :=
  x ∉ Γ.map Prod.fst

def WFCtx {P : Type} {L : Vegas.ExprLanguage}
    (Γ : Vegas.Ctx P L) : Prop :=
  (Γ.map Prod.fst).Nodup

instance {P : Type} {L : Vegas.ExprLanguage} {x : VarId}
    {Γ : Vegas.Ctx P L} : Decidable (Fresh (P := P) (L := L) x Γ) :=
  inferInstanceAs (Decidable (x ∉ _))

def WF {P : Type} [DecidableEq P]
    {L : Vegas.ExprLanguage}
    [E : Vegas.ExprKit P L]
    [D : Vegas.DistKit P L]
:
    {Γ : Vegas.Ctx P L} → Vegas.VegasCore P L Γ → Prop
  | _, .ret _ => True
  | Γ, .letExpr x _ k => Fresh x Γ ∧ WF k
  | Γ, .sample x _ _ _ k => Fresh x Γ ∧ WF k
  | Γ, .commit x _ _ _ k => Fresh x Γ ∧ WF k
  | Γ, .reveal y _ _ _ k => Fresh y Γ ∧ WF k

def decidableWF {P : Type} [DecidableEq P]
    {L : Vegas.ExprLanguage}
    [E : Vegas.ExprKit P L]
    [D : Vegas.DistKit P L]
:
    {Γ : Vegas.Ctx P L} → (p : Vegas.VegasCore P L Γ) → Decidable (WF p)
  | _, .ret _ => .isTrue trivial
  | _, .letExpr _ _ k => @instDecidableAnd _ _ (inferInstance) (decidableWF k)
  | _, .sample _ _ _ _ k => @instDecidableAnd _ _ (inferInstance) (decidableWF k)
  | _, .commit _ _ _ _ k => @instDecidableAnd _ _ (inferInstance) (decidableWF k)
  | _, .reveal _ _ _ _ k => @instDecidableAnd _ _ (inferInstance) (decidableWF k)

instance {P : Type} [DecidableEq P]
    {L : Vegas.ExprLanguage}
    [E : Vegas.ExprKit P L]
    [D : Vegas.DistKit P L]

    {Γ : Vegas.Ctx P L} {p : Vegas.VegasCore P L Γ} :
    Decidable (WF p) := decidableWF p

/-- Every committed secret is revealed exactly once. `pending` tracks
    commit variables awaiting revelation. -/
def RevealComplete {P : Type} [DecidableEq P]
    {L : Vegas.ExprLanguage}
    [E : Vegas.ExprKit P L]
    [D : Vegas.DistKit P L]
:
    {Γ : Vegas.Ctx P L} → List VarId → Vegas.VegasCore P L Γ → Prop
  | _, pending, .ret _ => pending = []
  | _, pending, .letExpr _ _ k => RevealComplete pending k
  | _, pending, .sample _ _ _ _ k => RevealComplete pending k
  | _, pending, .commit x _ _ _ k => RevealComplete (x :: pending) k
  | _, pending, .reveal _ _ x _ k =>
    x ∈ pending ∧ RevealComplete (pending.filter (· ≠ x)) k

instance : DecidableEq VarId := inferInstanceAs (DecidableEq Nat)

def decidableRevealComplete {P : Type} [DecidableEq P]
    {L : Vegas.ExprLanguage}
    [E : Vegas.ExprKit P L]
    [D : Vegas.DistKit P L]
:
    {Γ : Vegas.Ctx P L} →
    (pending : List VarId) → (p : Vegas.VegasCore P L Γ) →
    Decidable (RevealComplete pending p)
  | _, _, .ret _ => inferInstanceAs (Decidable (_ = []))
  | _, pending, .letExpr _ _ k => decidableRevealComplete pending k
  | _, pending, .sample _ _ _ _ k => decidableRevealComplete pending k
  | _, pending, .commit x _ _ _ k => decidableRevealComplete (x :: pending) k
  | _, pending, .reveal _ _ x _ k =>
    @instDecidableAnd _ _ (inferInstance) (decidableRevealComplete (pending.filter (· ≠ x)) k)

instance {P : Type} [DecidableEq P]
    {L : Vegas.ExprLanguage}
    [E : Vegas.ExprKit P L]
    [D : Vegas.DistKit P L]

    {pending : List VarId} {Γ : Vegas.Ctx P L} {p : Vegas.VegasCore P L Γ} :
    Decidable (RevealComplete pending p) := decidableRevealComplete pending p

/-- Full well-formedness: SSA freshness AND every committed secret is revealed. -/
def WFProg {P : Type} [DecidableEq P]
    {L : Vegas.ExprLanguage}
    [E : Vegas.ExprKit P L]
    [D : Vegas.DistKit P L]

    {Γ : Vegas.Ctx P L}
    (p : Vegas.VegasCore P L Γ) : Prop :=
  WF p ∧ RevealComplete [] p


@[simp] theorem WFCtx_nil {P : Type} {L : ExprLanguage} :
    WFCtx (P := P) (L := L) [] := List.nodup_nil

theorem WFCtx.cons {P : Type} {L : ExprLanguage}
    {x : VarId} {τ : BindTy P L} {Γ : Ctx P L}
    (hfresh : Fresh x Γ) (hwf : WFCtx Γ) :
    WFCtx ((x, τ) :: Γ) := by
  change (((x, τ) :: Γ).map Prod.fst).Nodup
  exact List.Nodup.cons hfresh hwf

theorem WFCtx.tail {P : Type} {L : ExprLanguage}
    {x : VarId} {τ : BindTy P L} {Γ : Ctx P L} :
    WFCtx ((x, τ) :: Γ) → WFCtx Γ := by
  intro h; exact (List.nodup_cons.mp h).2

theorem WFCtx.fresh_head {P : Type} {L : ExprLanguage}
    {x : VarId} {τ : BindTy P L} {Γ : Ctx P L} :
    WFCtx ((x, τ) :: Γ) → Fresh x Γ := by
  intro h; exact (List.nodup_cons.mp h).1

theorem HasVar.mem_map_fst {P : Type} {L : ExprLanguage}
    {Γ : Ctx P L} {x : VarId} {τ : BindTy P L} :
    HasVar (L := L) Γ x τ → x ∈ Γ.map Prod.fst := by
  intro h; induction h with
  | here => simp
  | there _ ih => exact List.mem_cons_of_mem _ ih

theorem HasVar.unique {P : Type} {L : ExprLanguage}
    {Γ : Ctx P L} {x : VarId} {τ₁ τ₂ : BindTy P L}
    (hwf : WFCtx Γ) (h1 : HasVar (L := L) Γ x τ₁) (h2 : HasVar (L := L) Γ x τ₂) :
    τ₁ = τ₂ := by
  induction h1 with
  | here =>
    match h2 with
    | .here => rfl
    | .there h2' => exact absurd (HasVar.mem_map_fst h2') hwf.fresh_head
  | there h1' ih =>
    match h2 with
    | .here => exact absurd (HasVar.mem_map_fst h1') hwf.fresh_head
    | .there h2' => exact ih hwf.tail h2'


theorem viewCtx_map_fst_sub {P : Type} [DecidableEq P] {L : ExprLanguage}
    {x : VarId} {p : P} {Γ : Ctx P L} :
    x ∈ (viewCtx p Γ).map Prod.fst → x ∈ Γ.map Prod.fst := by
  induction Γ with
  | nil =>
    intro h
    have : False := by
      simp [Vegas.viewCtx] at h
    exact False.elim this
  | cons hd tl ih =>
    obtain ⟨y, τ⟩ := hd
    cases hsee : Vegas.canSee (Player := P) (L := L) p τ with
    | false =>
      intro h
      have hview : viewCtx p ((y, τ) :: tl) = viewCtx p tl := by
        simp [viewCtx, Vegas.viewCtx, hsee]
      rw [hview] at h
      exact List.mem_cons_of_mem _ (ih h)
    | true =>
      intro h
      have hview : viewCtx p ((y, τ) :: tl) = (y, τ) :: viewCtx p tl := by
        simp [viewCtx, Vegas.viewCtx, hsee]
      rw [hview] at h
      simp only [List.map, List.mem_cons] at h ⊢
      rcases h with rfl | htl
      · exact Or.inl rfl
      · exact Or.inr (ih htl)

theorem Fresh_viewCtx {P : Type} [DecidableEq P] {L : ExprLanguage}
    {x : VarId} {p : P} {Γ : Ctx P L}
    (hfresh : Fresh x Γ) : Fresh x (viewCtx p Γ) :=
  fun hmem => hfresh (viewCtx_map_fst_sub hmem)

theorem Fresh_flattenCtx {P : Type} {L : ExprLanguage}
    {x : VarId} {Γ : Ctx P L}
    (hfresh : Fresh x Γ) : Fresh x (flattenCtx Γ) := by
  unfold Fresh at *; rwa [flattenCtx_map_fst]

theorem WFCtx_flattenCtx {P : Type} {L : ExprLanguage}
    {Γ : Ctx P L}
    (hwf : WFCtx Γ) : WFCtx (flattenCtx Γ) := by
  unfold WFCtx at *; rwa [flattenCtx_map_fst]


def Legal {P : Type} [DecidableEq P]
    {L : Vegas.ExprLanguage}
    [E : Vegas.ExprKit P L]
    [D : Vegas.DistKit P L]
:
    {Γ : Vegas.Ctx P L} → Vegas.VegasCore P L Γ → Prop
  | _, .ret _ => True
  | _, .letExpr _ _ k => Legal k
  | _, .sample _ _ _ _ k => Legal k
  | Γ, .commit _ who acts R k =>
    (∀ view : Vegas.Env (Player := P) L (Vegas.viewCtx who Γ),
        ∃ a ∈ acts, Vegas.evalGuard (Player := P) (L := L) E R a view = true) ∧ Legal k
  | _, .reveal _ _ _ _ k => Legal k

def DistinctActs {P : Type} [DecidableEq P]
    {L : Vegas.ExprLanguage}
    [E : Vegas.ExprKit P L]
    [D : Vegas.DistKit P L]
:
    {Γ : Vegas.Ctx P L} → Vegas.VegasCore P L Γ → Prop
  | _, .ret _ => True
  | _, .letExpr _ _ k => DistinctActs k
  | _, .sample _ _ _ _ k => DistinctActs k
  | _, .commit _ _ acts _ k => acts.Nodup ∧ DistinctActs k
  | _, .reveal _ _ _ _ k => DistinctActs k

def AdmissibleProfile {P : Type} [DecidableEq P]
    {L : Vegas.ExprLanguage}
    [E : Vegas.ExprKit P L]
    [D : Vegas.DistKit P L]

    (σ : Vegas.Profile P L) :
    {Γ : Vegas.Ctx P L} → Vegas.VegasCore P L Γ → Prop
  | _, .ret _ => True
  | _, .letExpr _ _ k => AdmissibleProfile σ k
  | _, .sample _ _ _ _ k => AdmissibleProfile σ k
  | _, .commit x who acts R k =>
    (∀ view, FDist.Supported (σ.commit who x acts R view)
      (fun a => a ∈ acts ∧ Vegas.evalGuard (Player := P) (L := L) E R a view = true)) ∧
    AdmissibleProfile σ k
  | _, .reveal _ _ _ _ k => AdmissibleProfile σ k

def DistExprNormalized {P : Type} [DecidableEq P]
    {L : Vegas.ExprLanguage}
    [D : Vegas.DistKit P L]
    {Γ : Vegas.Ctx P L} {b : L.Ty}
    (D' : D.DistExpr Γ b) : Prop :=
  ∀ env : Vegas.Env (Player := P) L Γ, FDist.totalWeight (D.eval D' env) = 1

namespace DistExpr

abbrev Normalized (D : DistExpr Γ b) : Prop :=
  DistExprNormalized (P := Player) (L := simpleExpr) D

end DistExpr

def NormalizedDists {P : Type} [DecidableEq P]
    {L : Vegas.ExprLanguage}
    [E : Vegas.ExprKit P L]
    [D : Vegas.DistKit P L]
:
    {Γ : Vegas.Ctx P L} → Vegas.VegasCore P L Γ → Prop
  | _, .ret _ => True
  | _, .letExpr _ _ k => NormalizedDists k
  | _, .sample _ _ _ D' k => DistExprNormalized (P := P) (L := L) D' ∧ NormalizedDists k
  | _, .commit _ _ _ _ k => NormalizedDists k
  | _, .reveal _ _ _ _ k => NormalizedDists k

def Profile.NormalizedOn {P : Type} [DecidableEq P]
    {L : Vegas.ExprLanguage}
    [E : Vegas.ExprKit P L]
    [D : Vegas.DistKit P L]

    (σ : Vegas.Profile P L) :
    {Γ : Vegas.Ctx P L} → Vegas.VegasCore P L Γ → Prop
  | _, .ret _ => True
  | _, .letExpr _ _ k => σ.NormalizedOn k
  | _, .sample _ _ _ _ k => σ.NormalizedOn k
  | _, .commit x who acts R k =>
    (∀ view, FDist.totalWeight (σ.commit who x acts R view) = 1) ∧ σ.NormalizedOn k
  | _, .reveal _ _ _ _ k => σ.NormalizedOn k

theorem DistExpr.Normalized_ite {Γ : CtxSimple} {b : BaseTy}
    {c : Expr Γ .bool} {t f : DistExpr Γ b}
    (ht : t.Normalized) (hf : f.Normalized) :
    (DistExpr.ite c t f).Normalized := by
  intro env
  change FDist.totalWeight (evalDistExpr (DistExpr.ite c t f) env) = 1
  by_cases hc : evalExpr c env
  · simp only [evalDistExpr, hc]
    exact ht env
  · simp only [evalDistExpr, hc]
    exact hf env

end Vegas
