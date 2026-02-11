import Vegas.LetProtocol.Proto
import Vegas.LetProtocol.ProtoLemmas
import Vegas.LetProb.WDistLemmas

/-!
# ProtoEquiv: Protocol rewrite kit

Semantic equivalence for protocol programs via denotations.

## Design

Instead of a custom `ProgEq` relation, we work with the **denotation**
`sem p : Profile → L.Env Γ → WDist W (L.Val τ)` and state all equivalences
as `sem p = sem q` (propositional equality on functions). This gives us
full `rw`/`simp` support for free, since Lean's tactic infrastructure
works with `Eq`.

## Main definitions

- `sem` — denotation of a `ProtoProg` as a function from profiles and envs to `WDist`
- `@[simp]` lemmas: `sem_ret`, `sem_letDet`, `sem_observe`, `sem_sample`, `sem_choose`
- Commuting conversions: `sem_observe_fuse`, `sem_letDet_observe_commute`,
  `sem_sample_observe_commute`
-/

namespace Proto

open Defs Prog

variable {L : Language}
variable {W : Type} [WeightModel W]

-- ============================================================
-- 1) Denotation: sem
-- ============================================================

/-- The semantic denotation of a `ProtoProg`: maps a profile and
    environment to a weighted distribution over values.

    All program equivalences are stated as `sem p = sem q`,
    which is `Eq` on functions — compatible with `rw`/`simp`. -/
def sem (p : ProtoProg (W := W) Γ τ) : Profile (L := L) (W := W) → L.Env Γ → WDist W (L.Val τ) :=
  fun σ env => evalProto σ p env

/-- `ProgEq` is just equality of denotations. Provided as notation
    for backward compatibility and readability. -/
abbrev ProgEq {Γ : L.Ctx} {τ : L.Ty} (p q : ProtoProg (W := W) Γ τ) : Prop :=
  sem p = sem q

-- ============================================================
-- 2) Simp lemmas: unfold sem through each constructor
-- ============================================================

@[simp] theorem sem_ret (e : L.Expr Γ τ) :
    sem (.ret e : ProtoProg (W := W) Γ τ) = fun _σ env => WDist.pure (L.eval e env) :=
  funext fun _ => funext fun _ => rfl

@[simp] theorem sem_letDet (e : L.Expr Γ τ') (k : ProtoProg (W := W) (τ' :: Γ) τ) :
    sem (ProtoProg.letDet e k) = fun σ env => sem k σ (L.eval e env, env) :=
  funext fun _ => funext fun _ => rfl

@[simp] theorem sem_observe (c : L.Expr Γ L.bool) (k : ProtoProg (W := W) Γ τ) :
    sem (ProtoProg.observe c k) = fun σ env =>
      if L.toBool (L.eval c env) then sem k σ env else WDist.zero := by
  funext σ env
  simp [sem]

@[simp] theorem sem_sample (id : YieldId) (v : View Γ)
    (K : ObsKernel (W := W) v τ') (k : ProtoProg (W := W) (τ' :: Γ) τ) :
    sem (ProtoProg.sample id v K k) = fun σ env =>
      WDist.bind (K (v.proj env)) (fun x => sem k σ (x, env)) :=
  funext fun _ => funext fun _ => rfl

@[simp] theorem sem_choose (id : YieldId) (who : Player) (v : View Γ)
    (A : Act v τ') (k : ProtoProg (W := W) (L := L) (τ' :: Γ) τ) :
    sem (ProtoProg.choose id who v A k) = fun σ env =>
      WDist.bind (σ.choose who id v A (v.proj env))
        (fun x => sem k σ (x, env)) :=
  funext fun _ => funext fun _ => rfl

-- ============================================================
-- 3) Congruence: follows from sem lemmas + congr
-- ============================================================

theorem sem_letDet_congr (e : L.Expr Γ τ')
    {k₁ k₂ : ProtoProg (W := W) (τ' :: Γ) τ}
    (hk : sem k₁ = sem k₂) :
    sem (ProtoProg.letDet e k₁) = sem (ProtoProg.letDet e k₂) := by
  simp [hk]

theorem sem_observe_congr (c : L.Expr Γ L.bool)
    {k₁ k₂ : ProtoProg (W := W) Γ τ}
    (hk : sem k₁ = sem k₂) :
    sem (ProtoProg.observe c k₁) = sem (ProtoProg.observe c k₂) := by
  simp [hk]

theorem sem_sample_congr {Γ : L.Ctx} {τ τ' : L.Ty}
    (id : YieldId) (v : View Γ) (K : ObsKernel (W := W) v τ')
    {k₁ k₂ : ProtoProg (W := W) (τ' :: Γ) τ}
    (hk : sem k₁ = sem k₂) :
    sem (ProtoProg.sample id v K k₁) = sem (ProtoProg.sample id v K k₂) := by
  simp [hk]

theorem sem_choose_congr {Γ : L.Ctx} {τ τ' : L.Ty}
    (id : YieldId) (who : Player) (v : View Γ)
    (A : Act v τ')
    {k₁ k₂ : ProtoProg (W := W) (τ' :: Γ) τ}
    (hk : sem k₁ = sem k₂) :
    sem (ProtoProg.choose id who v A k₁) = sem (ProtoProg.choose id who v A k₂) := by
  simp [hk]

-- ============================================================
-- 4) Commuting conversions
-- ============================================================

/-- Observe fusion: two consecutive observes fuse into a single
    `andBool` observe. -/
theorem sem_observe_fuse (EL : ExprLaws L)
    {Γ τ} (c₁ c₂ : L.Expr Γ L.bool) (k : ProtoProg (W := W) Γ τ) :
    sem (ProtoProg.observe c₁ (ProtoProg.observe c₂ k))
      = sem (ProtoProg.observe (EL.andBool c₁ c₂) k) := by
  ext σ env
  -- Key law: `andBool` corresponds to boolean conjunction on evaluation.
  have hand :
      L.toBool (L.eval (EL.andBool c₁ c₂) env)
        = (L.toBool (L.eval c₁ env) && L.toBool (L.eval c₂ env)) := by
    simpa using EL.toBool_eval_andBool (c₁ := c₁) (c₂ := c₂) (env := env)
  by_cases h1 : L.toBool (L.eval c₁ env)
  · by_cases h2 : L.toBool (L.eval c₂ env)
    · simp [sem_observe, h1, h2, hand]
    · simp [sem_observe, h1, h2, hand]
  · simp [sem_observe, h1, hand]

/-- letDet commutes past an independent observe:
    `letDet e (observe (weaken c) k)` ≡ `observe c (letDet e k)`
    when `c` does not mention the bound variable. -/
theorem sem_letDet_observe_commute (EL : ExprLaws L)
    {Γ τ τ'}
    (e : L.Expr Γ τ')
    (c : L.Expr Γ L.bool)
    (k : ProtoProg (W := W) (τ' :: Γ) τ) :
    sem (ProtoProg.letDet e (ProtoProg.observe (EL.weaken c) k))
      = sem (ProtoProg.observe c (ProtoProg.letDet e k)) := by
  simp only [sem_letDet, sem_observe]
  ext σ env
  rw [EL.eval_weaken]

/-- sample commutes past an independent observe:
    `sample id v K (observe (weaken c) k)` ≡
    `observe c (sample id v K k)`
    when `c` does not mention the bound variable. -/
theorem sem_sample_observe_commute (EL : ExprLaws L)
    {Γ τ τ'}
    (id : YieldId) (v : View Γ)
    (K : ObsKernel (W := W) v τ')
    (c : L.Expr Γ L.bool)
    (k : ProtoProg (W := W) (τ' :: Γ) τ) :
    sem (.sample id v K (ProtoProg.observe (EL.weaken c) k))
      = sem (ProtoProg.observe c (.sample id v K k)) := by
  ext σ env
  simp only [sem_sample, sem_observe]
  by_cases h : L.toBool (L.eval c env)
  · simp only [h, reduceIte]
    congr 1
    ext x
    rw [EL.eval_weaken]
    simp [h]
  · simp only [h, Bool.false_eq_true, reduceIte]
    conv_lhs => arg 2; ext x; rw [EL.eval_weaken]
    simp only [h, Bool.false_eq_true, ↓reduceIte]
    exact WDist.bind_zero_right _

-- ============================================================
-- 5) applyProfile preserves sem equality
-- ============================================================

open ProtoProg

@[simp] lemma applyProfile_doStmt
    (π : PProfile (L := L) (W := W)) (s : CmdStmtProto Γ) (k : ProtoProg (W := W) Γ τ) :
    applyProfile π (Prog.doStmt s k) = Prog.doStmt s (applyProfile π k) := by
  rfl

@[simp] lemma applyProfile_observe
    (π : PProfile (L := L) (W := W)) (c : L.Expr Γ L.bool) (k : ProtoProg (W := W) Γ τ) :
    applyProfile π (Prog.doStmt (CmdStmtObs.observe c) k)
      = Prog.doStmt (CmdStmtObs.observe c) (applyProfile π k) := by
  rfl


/-- If `sem p = sem q` and `π` is a partial profile, then
    `sem (applyProfile π p) = sem (applyProfile π q)`. -/
theorem sem_applyProfile_congr
    {Γ τ} (π : PProfile (L := L) (W := W))
    {p q : ProtoProg (W := W) Γ τ}
    (hpq : sem p = sem q) :
    sem (applyProfile π p) = sem (applyProfile π q) := by
  ext σ env
  -- Override σ at the sites where π provides a decision kernel.
  let σπ : Profile (L := L) (W := W) :=
    { σ with
      choose := fun {Γ τ} who id v A =>
        match π.choose? who id v A with
        | some Kdec => Kdec
        | none      => σ.choose who id v A }
  -- Core fact: evaluating `applyProfile π r` under σ equals evaluating `r` under σπ.
  have h_apply :
      ∀ {Γ τ} (r : ProtoProg (W := W) Γ τ) (env : L.Env Γ),
        sem (applyProfile π r) σ env = sem r σπ env := by
    intro Γ τ r env
    induction r with
    | ret e =>
      simp_all only [σπ]
      rfl
    | letDet e k ih =>
      simp_all only [σπ]
      apply ih
    | doStmt s k ih =>
      cases s with
      | observe cond =>
        change sem (ProtoProg.observe cond (applyProfile π k)) σ env =
              sem (ProtoProg.observe cond k) σπ env
        simp [sem_observe]
        simp_all only [σπ]
    | doBind c k ih =>
      cases c with
      | sample id v K =>
        simp only [sem, evalProto, ProtoSem, applyProfile, evalWith_doBind]
        congr
        funext
        apply ih
      | choose id who v A =>
        simp only [applyProfile]
        cases h : π.choose? who id v A
        · simp only [sem, evalProto, Prog.evalWith_doBind]
          congr 1
          · simp [σπ, h]
          · funext
            apply ih
        · simp only [sem, evalProto, Prog.evalWith_doBind]
          congr 1
          · simp [σπ, h]
          · funext
            apply ih
  rw [h_apply p env, h_apply q env]
  exact congr_fun (congr_fun hpq σπ) env


end Proto
