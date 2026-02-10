import Vegas.ProtoLet
import Vegas.ProbLetLemmas
import Vegas.WDistLemmas
import Vegas.ProgCoreLemmas

/-!
# ProtoLetLemmas: sanity lemmas for ProtoLet

This file is intentionally "lightweight but sharp":
- simp lemmas for the ProtoSem handlers and eval
- semantic invariants: profile-independence when NoChoose
- correctness bridge to ProbLet for NoChoose programs
- observe laws (fusion), plus a few mass/probability facts
- yield id bookkeeping for encoder-side sanity
No equilibrium existence, no measure theory, no reachability machinery.
-/

namespace ProtoLet

open GameDefs ProgCore
variable {L : Language}
variable (EL : ExprLaws L)

namespace ProtoProg


-- ============================================================
-- 11) Sanity: "partial information is enforced"
-- ============================================================

/--
**Partial-information sanity lemma (core statement).**

Both chance and decision yields are *view-parametric*: if two environments project to the same
visible environment, then the primitive step distribution at that yield site is the same.

This is the formal content of "resolvers/kernels can only depend on `Env v.Δ`".
-/
lemma handleBind_depends_only_on_view
    (σ : Profile)
    {Γ : L.Ctx} {τ : L.Ty}
    (c : CmdBindProto Γ τ)
    {env₁ env₂ : L.Env Γ}
    (hproj : match c with
      | .sample _id v _K => v.proj env₁ = v.proj env₂
      | .choose _id _who v _A => v.proj env₁ = v.proj env₂) :
    (ProtoSem σ).handleBind c env₁ =
    (ProtoSem σ).handleBind c env₂ := by
  cases c with
  | sample id v K =>
      -- handleBind = K (v.proj env)
      simp [ProtoSem, hproj]
  | choose id who v A =>
      -- handleBind = σ.choose ... (v.proj env)
      simp [ProtoSem, hproj]

/--
A convenient specialization for decision yields:

If `v.proj env₁ = v.proj env₂` then the profile-induced distribution
at this decision yield is equal.
-/
lemma choose_depends_only_on_view
    (σ : Profile)
    {Γ : L.Ctx} {τ : L.Ty}
    (id : YieldId) (who : Player) (v : View Γ) (A : Act v τ)
    {env₁ env₂ : L.Env Γ} (h : v.proj env₁ = v.proj env₂) :
    (ProtoSem σ).handleBind (.choose id who v A) env₁ =
    (ProtoSem σ).handleBind (.choose id who v A) env₂ := by
  simpa using (handleBind_depends_only_on_view σ
    (c := .choose id who v A) (env₁ := env₁) (env₂ := env₂) h)

-- ============================================================
-- 12) A tiny runnable game
-- ============================================================

namespace Examples

open ProtoLet

/-
This example is intentionally tiny:

- initial context is empty `Γ := []`
- a single decision yield by player 0 choosing a boolean
- the program returns the chosen boolean
- utility pays 1 to player 0 iff the result is `true`, else 0
-/

-- Empty context helper.
abbrev Γ0 : L.Ctx := []

-- A view that reveals nothing (Δ = []), so the decision
-- cannot depend on any secrets in Γ.
def vEmpty : View (L := L) Γ0 where
  Δ := []
  proj := fun _env => ()

-- Offer both boolean values as legal actions.
def A_bool : Act (v := vEmpty) L.bool :=
  fun _obs => [L.fromBool true, L.fromBool false]

/-- One-step protocol: player 0 chooses a bool, then return it. -/
def p_chooseBool (EL : ExprLaws L) :
    ProtoProg Γ0 L.bool :=
  ProtoProg.choose
    (id := 0) (who := 0) (v := vEmpty)
    (A := A_bool)
    (ProtoProg.ret EL.vz)

/-- Utility: player 0 gets 1 if result is true; others get 0. -/
def u_bool [DecidableEq (L.Val L.bool)] :
    Utility L.bool :=
  fun b who =>
    if who = 0
    then (if b = L.fromBool true then (1 : Real) else 0)
    else 0

def G_chooseBool (EL : ExprLaws L)
    [DecidableEq (L.Val L.bool)] :
    Game (L := L) Γ0 where
  τ := L.bool
  p := p_chooseBool EL
  u := u_bool

end Examples



-- ------------------------------------------------------------
-- 0) simp expansions for evalProto
-- ------------------------------------------------------------

@[simp] lemma evalProto_ret {Γ τ} (σ : Profile) (e : L.Expr Γ τ) (env : L.Env Γ) :
    evalProto σ (.ret e) env = WDist.pure (L.eval e env) := rfl

@[simp] lemma evalProto_letDet {Γ τ τ'} (σ : Profile)
    (e : L.Expr Γ τ') (k : ProtoProg (τ' :: Γ) τ) (env : L.Env Γ) :
    evalProto σ (.letDet e k) env =
      evalProto σ k (L.eval e env, env) := rfl

@[simp] lemma evalProto_observe {Γ τ} (σ : Profile)
    (c : L.Expr Γ L.bool) (k : ProtoProg Γ τ) (env : L.Env Γ) :
    evalProto σ (.observe c k) env =
      if L.toBool (L.eval c env) then evalProto σ k env else WDist.zero := by
  by_cases h : L.toBool (L.eval c env)
  · simp [EffWDist, ProbLet.EffWDist, ProtoProg.observe, evalProto,
          ProtoSem, ProgCore.evalWith, ProgCore.evalProg_gen, h]
  · simp [EffWDist, ProbLet.EffWDist, ProtoProg.observe, evalProto,
          ProtoSem, ProgCore.evalWith, ProgCore.evalProg_gen, h]

@[simp] lemma evalProto_sample_bind {Γ τ τ'} (σ : Profile)
    (id : YieldId) (v : View Γ) (K : ObsKernel v τ')
    (k : ProtoProg (τ' :: Γ) τ) (env : L.Env Γ) :
    evalProto σ (.sample id v K k) env =
      WDist.bind (K (v.proj env)) (fun x => evalProto σ k (x, env)) := rfl

@[simp] lemma evalProto_choose_bind {Γ τ τ'} (σ : Profile)
    (id : YieldId) (who : Player) (v : View Γ) (A : Act v τ')
    (k : ProtoProg (τ' :: Γ) τ) (env : L.Env Γ) :
    evalProto σ (.choose id who v A k) env =
      WDist.bind (σ.choose who id v A (v.proj env))
        (fun x => evalProto σ k (x, env)) := rfl


-- ------------------------------------------------------------
-- 1) profile irrelevance for NoChoose programs
-- ------------------------------------------------------------

theorem evalProto_profile_indep {Γ τ}
    (p : ProtoProg Γ τ) (hp : NoChoose p)
    (σ₁ σ₂ : Profile) (env : L.Env Γ) :
    evalProto σ₁ p env = evalProto σ₂ p env := by
  -- structural recursion on p; choose-case impossible by hp
  induction p with
  | ret e => rfl
  | letDet e k ih => exact ih hp _
  | doStmt s k ih =>
      cases s with
      | observe cond =>
          exact congr_arg
            (WDist.bind ((ProtoSem σ₁).handleStmt
              (.observe cond) env))
            (funext (fun _ => ih hp _))
  | doBind c k ih =>
      cases c with
      | sample id v K =>
          change WDist.bind (K (v.proj env))
              (fun x => evalProto σ₁ k (x, env)) =
            WDist.bind (K (v.proj env))
              (fun x => evalProto σ₂ k (x, env))
          congr 1; funext x; exact ih hp _
      | choose id who v A =>
          exact absurd hp (by trivial)


-- ------------------------------------------------------------
-- 2) observe laws (fusion), inherited from ProgCore/ProbLet style
-- ------------------------------------------------------------

theorem observe_fuse {Γ τ} (σ : Profile)
    (c₁ c₂ : L.Expr Γ L.bool) (k : ProtoProg Γ τ) :
    (fun env => evalProto σ (.observe c₁ (.observe c₂ k)) env)
      =
    (fun env => evalProto σ (.observe (EL.andBool c₁ c₂) k) env) := by
  funext env
  by_cases h1 : L.toBool (L.eval c₁ env)
  · by_cases h2 : L.toBool (L.eval c₂ env)
    · simp [h1, h2, EL.toBool_eval_andBool]
    · simp [h1, h2, EL.toBool_eval_andBool]
  · simp [h1, EL.toBool_eval_andBool]


-- ------------------------------------------------------------
-- 3) applyProfile: basic structural facts
-- ------------------------------------------------------------

/-- Every `choose` node in `p` is resolved by the partial profile `π`. -/
def AllChooseResolved (π : PProfile (L := L)) {Γ : L.Ctx} {τ : L.Ty} :
    ProtoProg Γ τ → Prop
  | .ret _        => True
  | .letDet _ k   => AllChooseResolved π k
  | .doStmt _ k   => AllChooseResolved π k
  | .doBind c k   =>
      match c with
      | .sample _ _ _          => AllChooseResolved π k
      | .choose _id who v A    =>
          (∃ Kdec, π.choose? who _id v A = some Kdec) ∧ AllChooseResolved π k

@[simp] lemma NoChoose_applyProfile {Γ τ} (π : PProfile (L := L))
    (p : ProtoProg Γ τ) :
    NoChoose (applyProfile π p) ↔
      AllChooseResolved π p := by
  induction p with
  | ret => exact Iff.rfl
  | letDet e k ih => exact ih
  | doStmt s k ih => exact ih
  | doBind c k ih =>
      cases c with
      | sample id v K => exact ih
      | choose id who v A =>
          simp only [applyProfile]
          cases hπ : π.choose? who id v A with
          | none =>
              -- NoChoose is False; AllChooseResolved needs ∃ Kdec, none = some
              constructor
              · intro h; exact absurd h (by trivial)
              · intro ⟨⟨_, h⟩, _⟩; exact absurd h (by simp [hπ])
          | some Kdec =>
              -- choose→sample; NoChoose ↔ tail; AllChooseResolved ↔ ∃.. ∧ tail
              constructor
              · intro h; exact ⟨⟨Kdec, hπ⟩, ih.mp h⟩
              · intro ⟨_, h⟩; exact ih.mpr h

/-- applyProfile does not change the list of yield ids (it may change *kind*, choose→sample). -/
theorem yieldIds_applyProfile {Γ τ} (π : PProfile (L := L))
    (p : ProtoProg Γ τ) :
    yieldIds (applyProfile π p) = yieldIds p := by
  induction p with
  | ret => rfl
  | letDet e k ih => simpa [applyProfile, yieldIds] using ih
  | doStmt s k ih => simpa [applyProfile, yieldIds] using ih
  | doBind c k ih =>
      cases c with
      | sample => simp [applyProfile, yieldIds, ih]
      | choose id who v A =>
          simp only [applyProfile]
          cases π.choose? who id v A <;> simp [yieldIds, ih]


-- ------------------------------------------------------------
-- 4) Semantic compatibility: applyProfile vs evalProto
-- ------------------------------------------------------------

/--
If a total profile `σ` extends a partial profile `π`
(i.e. agrees on every site where `π` is defined),
then evaluating `p` under `σ` equals evaluating `(applyProfile π p)` under the same `σ`.
-/
def Extends (σ : Profile (L := L)) (π : PProfile (L := L)) : Prop :=
  ∀ {Γ τ} (who : Player) (id : YieldId) (v : View Γ) (A : Act v τ)
    (Kdec : L.Env v.Δ → WDist (L.Val τ)),
    π.choose? who id v A = some Kdec →
      σ.choose who id v A = Kdec

theorem evalProto_applyProfile_of_extends
    (σ : Profile) (π : PProfile (L := L))
    (hExt : Extends σ π) :
    ∀ {Γ τ} (p : ProtoProg Γ τ) (env : L.Env Γ),
      evalProto σ (applyProfile π p) env
        =
      evalProto σ p env := by
  intro Γ τ p
  induction p with
  | ret e =>
      intro env
      simp [applyProfile, evalProto]
      rfl
  | letDet e k ih =>
      intro env
      simp only [evalProto, applyProfile, evalWith_letDet]
      apply ih
  | doStmt s k ih =>
      intro env
      cases s with
      | observe cond =>
          by_cases h : L.toBool (L.eval cond env)
          · simp only [evalProto, ProtoSem, EffWDist, ProbLet.EffWDist, applyProfile,
            evalWith_doStmt, h, reduceIte, WDist.bind_pure]
            apply ih
          · simp [applyProfile, evalProto, ProtoSem, EffWDist, ProbLet.EffWDist, h]
  | doBind c k ih =>
      intro env
      cases c with
      | sample id v K =>
          change WDist.bind (K (v.proj env)) (fun x => evalProto σ (applyProfile π k) (x, env)) =
                 WDist.bind (K (v.proj env)) (fun x => evalProto σ k (x, env))
          congr 1; funext x; exact ih (x, env)
      | choose id who v A =>
          cases hπ : π.choose? who id v A with
          | none =>
              simp only [applyProfile, hπ]
              exact congr_arg (WDist.bind (σ.choose who id v A (v.proj env)))
                (funext (fun x => ih (x, env)))
          | some Kdec =>
              simp only [applyProfile, hπ]
              have hσ := hExt who id v A Kdec hπ
              subst hσ
              exact congr_arg (WDist.bind (σ.choose who id v A (v.proj env)))
                (funext (fun x => ih (x, env)))

-- ------------------------------------------------------------
-- 5) Bridge to ProbLet for NoChoose programs (significant theorem)
-- ------------------------------------------------------------

theorem evalProto_eq_evalP_toProbNoChoose
    {Γ τ} (σ : Profile)
    (p : ProtoProg Γ τ) (h : NoChoose p) (env : L.Env Γ) :
    evalProto σ p env
      =
    ProbLet.evalP (toProbNoChoose p h) env := by
  -- proof by recursion on p, the doBind case can only be sample
  induction p with
  | ret e => rfl
  | letDet e k ih => exact ih h _
  | doStmt s k ih =>
      cases s with
      | observe cond =>
          -- Both ProtoSem and ProbSem have the same observe handler, so the
          -- WDist.bind first arg is definitionally equal; only the continuation differs.
          exact congr_arg
            (WDist.bind ((ProtoSem σ).handleStmt (.observe cond) env))
            (funext (fun _ => ih h env))
  | doBind c k ih =>
      cases c with
      | sample id v K =>
          -- Both sides: WDist.bind (K (v.proj env)) (fun x => ...)
          change WDist.bind (K (v.proj env))
              (fun x => evalProto σ k (x, env)) =
            WDist.bind (K (v.proj env))
              (fun x => ProbLet.evalP
                (toProbNoChoose k h) (x, env))
          congr 1; funext x; exact ih h (x, env)
      | choose id who v A =>
          exact absurd h (by trivial)


-- ------------------------------------------------------------
-- 6) toProb? agrees with toProbNoChoose (when defined)
-- ------------------------------------------------------------

theorem toProb?_eq_toProbNoChoose
    {Γ τ} (p : ProtoProg (L := L) Γ τ) (h : NoChoose p) :
    toProb? p = some (toProbNoChoose p h) := by
  induction p with
  | ret => rfl
  | letDet e k ih => simp [toProb?, toProbNoChoose, ih h]
  | doStmt s k ih => simp [toProb?, toProbNoChoose, ih h]
  | doBind c k ih =>
      cases c with
      | sample id v K => simp [toProb?, toProbNoChoose, ih h]
      | choose => exact absurd h (by trivial)

theorem toProb?_some_iff_NoChoose
    {Γ τ} (p : ProtoProg (L := L) Γ τ) :
    (∃ q, toProb? p = some q) ↔ NoChoose p := by
  constructor
  · -- forward: if toProb? returns some, then NoChoose
    intro ⟨q, hq⟩
    induction p with
    | ret => trivial
    | letDet e k ih =>
        simp only [toProb?] at hq
        cases hk : toProb? k with
        | none => simp [hk] at hq
        | some qk => exact ih qk hk
    | doStmt s k ih =>
        simp only [toProb?] at hq
        cases hk : toProb? k with
        | none => simp [hk] at hq
        | some qk => exact ih qk hk
    | doBind c k ih =>
        cases c with
        | sample id v K =>
            simp only [toProb?] at hq
            cases hk : toProb? k with
            | none => simp [hk] at hq
            | some qk => exact ih qk hk
        | choose => simp [toProb?] at hq
  · -- backward: if NoChoose, then toProb? returns some
    intro h
    exact ⟨_, toProb?_eq_toProbNoChoose p h⟩


-- ------------------------------------------------------------
-- 7) WF / legality: small reusable lemmas
-- ------------------------------------------------------------

@[simp] lemma SupportedOn_pure {α} (a : α) (S : α → Prop) :
    SupportedOn (WDist.pure a) S ↔ S a := by
  simp [SupportedOn, WDist.pure]

@[simp] lemma SupportedOn_zero {α} (S : α → Prop) :
    SupportedOn (WDist.zero : WDist α) S := by
  intro a w hmem
  simp [WDist.zero] at hmem

lemma WFOnProg.letDet {Reach : ReachSpec} {σ : Profile}
    {Γ : L.Ctx} {τ τ' : L.Ty}
    {x : L.Expr Γ τ'} {k : ProtoProg (τ' :: Γ) τ}
    (h : WFOnProg Reach σ (.letDet x k)) :
    WFOnProg Reach σ k := h

lemma WFOnProg.doBind_choose_left
    {Reach : ReachSpec} {σ : Profile}
    {Γ : L.Ctx} {τ τ' : L.Ty} {id : YieldId} {who : Player}
    {v : View Γ} {A : Act v τ'}
    {k : ProtoProg (τ' :: Γ) τ}
    (h : WFOnProg Reach σ (.doBind (.choose id who v A) k)) :
    ∀ env : L.Env Γ, Reach env → LegalAt σ who id v A (v.proj env) :=
  h.1

lemma WFOnProg.doBind_choose_right
    {Reach : ReachSpec} {σ : Profile}
    {Γ : L.Ctx} {τ τ' : L.Ty} {id : YieldId} {who : Player}
    {v : View Γ} {A : Act v τ'}
    {k : ProtoProg (τ' :: Γ) τ}
    (h : WFOnProg Reach σ (.doBind (.choose id who v A) k)) :
    WFOnProg Reach σ k :=
  h.2

/-- WF propagates past a sample-bind to the continuation. -/
theorem WFOnProg_of_sample_tail
    (Reach : ReachSpec (L := L)) (σ : Profile)
    {Γ τ τ'} (id : YieldId) (v : View Γ)
    (K : ObsKernel v τ')
    (k : ProtoProg (τ' :: Γ) τ)
    (hWF : WFOnProg Reach σ
      (.doBind (.sample id v K) k)) :
    WFOnProg Reach σ k :=
  hWF.2

lemma WFOnProg_doBind_choose
    {L} {Reach : ReachSpec (L := L)} {σ : Profile}
    {Γ : L.Ctx} {τ τ' : L.Ty}
    {id : YieldId} {who : Player}
    {v : View Γ} {A : Act v τ}
    {k : ProtoProg (τ :: Γ) τ'} :
    WFOnProg Reach σ (.doBind (.choose id who v A) k) →
      (∀ env : L.Env Γ, Reach env → LegalAt σ who id v A (v.proj env)) :=
  fun h => h.1

-- If WF holds for a program whose next command is choose,
-- you can extract the local condition and WF for the continuation.
lemma WFOnProg_doBind_choose_iff
    {L} {Reach : ReachSpec (L := L)} {σ : Profile}
    {Γ : L.Ctx} {τ τ' : L.Ty}
    {id : YieldId} {who : Player}
    {v : View Γ} {A : Act v τ}
    {k : ProtoProg (τ :: Γ) τ'} :
    WFOnProg Reach σ (.doBind (.choose id who v A) k)
      ↔
      ( (∀ env : L.Env Γ, Reach env → LegalAt σ who id v A (v.proj env))
        ∧ WFOnProg Reach σ k ) := by
  simp [WFOnProg]

/-- Property P must hold for every `choose` node in the program. -/
def ForAllChooses
    {L} (P :
      {Γ : L.Ctx} → {τ : L.Ty} →
      (who : Player) → (id : YieldId) →
      (v : View Γ) → (A : Act v τ) → Prop) :
    {Γ : L.Ctx} → {τ : L.Ty} → ProtoProg (L := L) Γ τ → Prop
  | _, _, .ret _        => True
  | _, _, .letDet _ k   => ForAllChooses P k
  | _, _, .doStmt _ k   => ForAllChooses P k
  | _, _, .doBind c k   =>
      (match c with
       | .sample _id _v _K => True
       | .choose id who v A => P who id v A)
      ∧ (ForAllChooses P k)

lemma WFOnProg_forAllChooses
    {L} {Reach : ReachSpec (L := L)} {σ : Profile} :
  ∀ {Γ τ} (p : ProtoProg Γ τ),
    WFOnProg Reach σ p →
    ForAllChooses
      (fun {Γ} {_} who id v A =>
        ∀ env : L.Env Γ, Reach env → LegalAt σ who id v A (v.proj env))
      p := by
  intro Γ τ p
  induction p with
  | ret _ =>
      intro _; trivial
  | letDet _ k ih =>
      intro h; simpa [ForAllChooses, WFOnProg] using ih h
  | doStmt _ k ih =>
      intro h; simpa [ForAllChooses, WFOnProg] using ih h
  | doBind c k ih =>
      intro h
      -- unfold WFOnProg at this node
      cases c with
      | sample id v K =>
          exact ⟨trivial, ih h.2⟩
      | choose id who v A =>
          exact ⟨h.1, ih h.2⟩

-- direct, no “reachability from semantics” yet:
lemma WFOnProg_implies_LegalAt_at_head_choose
    {L} {Reach : ReachSpec (L := L)} {σ : Profile}
    {Γ : L.Ctx} {τ τ' : L.Ty}
    {id : YieldId} {who : Player}
    {v : View Γ} {A : Act v τ}
    {k : ProtoProg (τ :: Γ) τ'} :
    WFOnProg Reach σ (.doBind (.choose id who v A) k) →
      (∀ env : L.Env Γ, Reach env → LegalAt σ who id v A (v.proj env)) :=
  fun h => h.1

-- ------------------------------------------------------------
-- 8) Mass / probability (ties into WFChanceOnProg)
-- ------------------------------------------------------------

theorem mass_evalProto_ret {Γ τ} (σ : Profile) (e : L.Expr Γ τ) (env : L.Env Γ) :
    (evalProto σ (.ret e) env).mass = 1 := by
  simp [WDist.mass_pure]

theorem mass_evalProto_observe_le {Γ τ} (σ : Profile)
    (c : L.Expr Γ L.bool) (k : ProtoProg Γ τ) (env : L.Env Γ) :
    (evalProto σ (.observe c k) env).mass ≤ (evalProto σ k env).mass := by
  -- Expose the WDist.bind structure through evalProto/evalWith/evalProg_gen
  change (WDist.bind
    ((ProtoSem σ).handleStmt (.observe c) env)
    (fun _ => evalProto σ k env)).mass ≤
    (evalProto σ k env).mass
  -- handleStmt reduces to if-then-else
  simp only [ProtoSem_handleStmt_observe]
  split
  · simp [WDist.bind_pure]
  · simp [WDist.bind_zero, WDist.mass_zero]

end ProtoProg
end ProtoLet
