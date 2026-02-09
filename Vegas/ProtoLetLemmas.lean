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
    (σ : Profile (L := L))
    {Γ : L.Ctx} {τ : L.Ty}
    (c : CmdBindProto (L := L) Γ τ)
    {env₁ env₂ : L.Env Γ}
    (hproj : match c with
      | .sample _id v _K => v.proj env₁ = v.proj env₂
      | .choose _id _who v _A => v.proj env₁ = v.proj env₂) :
    (ProtoSem (L := L) σ).handleBind c env₁ =
    (ProtoSem (L := L) σ).handleBind c env₂ := by
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
    (σ : Profile (L := L))
    {Γ : L.Ctx} {τ : L.Ty}
    (id : YieldId) (who : Player) (v : View (L := L) Γ) (A : Act (L := L) v τ)
    {env₁ env₂ : L.Env Γ} (h : v.proj env₁ = v.proj env₂) :
    (ProtoSem (L := L) σ).handleBind (.choose (L := L) id who v A) env₁ =
    (ProtoSem (L := L) σ).handleBind (.choose (L := L) id who v A) env₂ := by
  simpa using (handleBind_depends_only_on_view (L := L) σ
    (c := .choose (L := L) id who v A) (env₁ := env₁) (env₂ := env₂) h)

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
def A_bool : Act (L := L) (v := vEmpty (L := L)) L.bool :=
  fun _obs => [L.fromBool true, L.fromBool false]

/-- One-step protocol: player 0 chooses a bool, then return it. -/
def p_chooseBool (EL : ExprLaws L) :
    ProtoProg (L := L) Γ0 L.bool :=
  ProtoProg.choose (L := L)
    (id := 0) (who := 0) (v := vEmpty (L := L))
    (A := A_bool (L := L))
    (ProtoProg.ret (L := L) EL.vz)

/-- Utility: player 0 gets 1 if result is true; others get 0. -/
def u_bool [DecidableEq (L.Val L.bool)] :
    Utility (L := L) L.bool :=
  fun b who =>
    if who = 0
    then (if b = L.fromBool true then (1 : Real) else 0)
    else 0

def G_chooseBool (EL : ExprLaws L)
    [DecidableEq (L.Val L.bool)] :
    Game (L := L) Γ0 where
  τ := L.bool
  p := p_chooseBool (L := L) EL
  u := u_bool (L := L)

end Examples



-- ------------------------------------------------------------
-- 0) simp expansions for evalProto
-- ------------------------------------------------------------

@[simp] lemma evalProto_ret {Γ τ} (σ : Profile (L := L)) (e : L.Expr Γ τ) (env : L.Env Γ) :
    evalProto (L := L) σ (.ret e) env = WDist.pure (L.eval e env) := rfl

@[simp] lemma evalProto_letDet {Γ τ τ'} (σ : Profile (L := L))
    (e : L.Expr Γ τ') (k : ProtoProg (L := L) (τ' :: Γ) τ) (env : L.Env Γ) :
    evalProto (L := L) σ (.letDet e k) env =
      evalProto (L := L) σ k (L.eval e env, env) := rfl

@[simp] lemma evalProto_observe {Γ τ} (σ : Profile (L := L))
    (c : L.Expr Γ L.bool) (k : ProtoProg (L := L) Γ τ) (env : L.Env Γ) :
    evalProto (L := L) σ (.observe c k) env =
      if L.toBool (L.eval c env) then evalProto (L := L) σ k env else WDist.zero := by
  by_cases h : L.toBool (L.eval c env)
  · simp [EffWDist, ProbLet.EffWDist, ProtoProg.observe, evalProto,
          ProtoSem, ProgCore.evalWith, ProgCore.evalProg_gen, h]
  · simp [EffWDist, ProbLet.EffWDist, ProtoProg.observe, evalProto,
          ProtoSem, ProgCore.evalWith, ProgCore.evalProg_gen, h]

@[simp] lemma evalProto_sample_bind {Γ τ τ'} (σ : Profile (L := L))
    (id : YieldId) (v : View (L := L) Γ) (K : ObsKernel (L := L) v τ')
    (k : ProtoProg (L := L) (τ' :: Γ) τ) (env : L.Env Γ) :
    evalProto (L := L) σ (.sample id v K k) env =
      WDist.bind (K (v.proj env)) (fun x => evalProto (L := L) σ k (x, env)) := rfl

@[simp] lemma evalProto_choose_bind {Γ τ τ'} (σ : Profile (L := L))
    (id : YieldId) (who : Player) (v : View (L := L) Γ) (A : Act (L := L) v τ')
    (k : ProtoProg (L := L) (τ' :: Γ) τ) (env : L.Env Γ) :
    evalProto (L := L) σ (.choose id who v A k) env =
      WDist.bind (σ.choose who id v A (v.proj env))
        (fun x => evalProto (L := L) σ k (x, env)) := rfl


-- ------------------------------------------------------------
-- 1) profile irrelevance for NoChoose programs
-- ------------------------------------------------------------

theorem evalProto_profile_indep {Γ τ}
    (p : ProtoProg (L := L) Γ τ) (hp : NoChoose (L := L) p)
    (σ₁ σ₂ : Profile (L := L)) (env : L.Env Γ) :
    evalProto (L := L) σ₁ p env = evalProto (L := L) σ₂ p env := by
  -- structural recursion on p; choose-case impossible by hp
  induction p with
  | ret e => rfl
  | letDet e k ih =>
      simp only [evalProto_letDet]
      exact ih hp _
  | doStmt s k ih =>
      cases s with
      | observe cond =>
          simp only [evalProto_observe]
          split <;> [exact ih hp _; rfl]
  | doBind c k ih =>
      cases c with
      | sample id v K =>
          simp only [evalProto_sample_bind]
          congr 1; funext x; exact ih hp _
      | choose id who v A =>
          exact absurd hp (by trivial)


-- ------------------------------------------------------------
-- 2) observe laws (fusion), inherited from ProgCore/ProbLet style
-- ------------------------------------------------------------

theorem observe_fuse {Γ τ} (σ : Profile (L := L))
    (c₁ c₂ : L.Expr Γ L.bool) (k : ProtoProg (L := L) Γ τ) :
    (fun env => evalProto (L := L) σ (.observe c₁ (.observe c₂ k)) env)
      =
    (fun env => evalProto (L := L) σ (.observe (EL.andBool c₁ c₂) k) env) := by
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
    ProtoProg (L := L) Γ τ → Prop
  | .ret _        => True
  | .letDet _ k   => AllChooseResolved π k
  | .doStmt _ k   => AllChooseResolved π k
  | .doBind c k   =>
      match c with
      | .sample _ _ _          => AllChooseResolved π k
      | .choose _id who v A    =>
          (∃ Kdec, π.choose? who _id v A = some Kdec) ∧ AllChooseResolved π k

@[simp] lemma NoChoose_applyProfile {Γ τ} (π : PProfile (L := L))
    (p : ProtoProg (L := L) Γ τ) :
    NoChoose (L := L) (applyProfile (L := L) π p) ↔
      AllChooseResolved (L := L) π p := by
  sorry

/-- applyProfile does not change the list of yield ids (it may change *kind*, choose→sample). -/
theorem yieldIds_applyProfile {Γ τ} (π : PProfile (L := L))
    (p : ProtoProg (L := L) Γ τ) :
    yieldIds (L := L) (applyProfile (L := L) π p) = yieldIds (L := L) p := by
  induction p with
  | ret => rfl
  | letDet e k ih => simpa [applyProfile, yieldIds] using ih
  | doStmt s k ih => simpa [applyProfile, yieldIds] using ih
  | doBind c k ih =>
      cases c <;> simp [applyProfile, yieldIds, ih]
      -- choose case: both branches preserve the head id
      sorry


-- ------------------------------------------------------------
-- 4) Semantic compatibility: applyProfile vs evalProto
-- ------------------------------------------------------------

/--
If a total profile `σ` extends a partial profile `π`
(i.e. agrees on every site where `π` is defined),
then evaluating `p` under `σ` equals evaluating `(applyProfile π p)` under the same `σ`.
-/
def Extends (σ : Profile (L := L)) (π : PProfile (L := L)) : Prop :=
  ∀ {Γ τ} (who : Player) (id : YieldId) (v : View (L := L) Γ) (A : Act (L := L) v τ)
    (Kdec : L.Env v.Δ → WDist (L.Val τ)),
    π.choose? who id v A = some Kdec →
      σ.choose who id v A = Kdec

theorem evalProto_applyProfile_of_extends
    (σ : Profile (L := L)) (π : PProfile (L := L))
    (hExt : Extends (L := L) σ π) :
    ∀ {Γ τ} (p : ProtoProg (L := L) Γ τ) (env : L.Env Γ),
      evalProto σ (applyProfile (L := L) π p) env
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
    {Γ τ} (σ : Profile (L := L))
    (p : ProtoProg (L := L) Γ τ) (h : NoChoose (L := L) p) (env : L.Env Γ) :
    evalProto (L := L) σ p env
      =
    ProbLet.evalP (L := L) (toProbNoChoose (L := L) p h) env := by
  -- proof by recursion on p, the doBind case can only be sample
  induction p with
  | ret e => sorry
  | letDet e k ih => sorry
  | doStmt s k ih =>
      cases s with
      | observe cond => sorry
  | doBind c k ih =>
      cases c with
      | sample id v K => sorry
      | choose id who v A =>
          -- impossible: NoChoose (.doBind (.choose ..) k) = False
          exact absurd h (by trivial)


-- ------------------------------------------------------------
-- 6) toProb? agrees with toProbNoChoose (when defined)
-- ------------------------------------------------------------

theorem toProb?_some_iff_NoChoose
    {Γ τ} (p : ProtoProg (L := L) Γ τ) :
    (∃ q, toProb? (L := L) p = some q) ↔ NoChoose (L := L) p := by
  -- direction: if some, no choose occurred; converse: structural recursion.
  sorry

theorem toProb?_eq_toProbNoChoose
    {Γ τ} (p : ProtoProg (L := L) Γ τ) (h : NoChoose (L := L) p) :
    toProb? (L := L) p = some (toProbNoChoose (L := L) p h) := by
  sorry


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

/-- If σ is WF on p, then it is legal at every `choose` site
    encountered in p (reachable envs). -/
theorem WFOnProg.implies_legalAt
    (Reach : ReachSpec (L := L)) (σ : Profile (L := L))
    {Γ τ} (p : ProtoProg (L := L) Γ τ)
    (hWF : WFOnProg (L := L) Reach σ p) :
    -- statement best expressed via an auxiliary predicate;
    -- placeholder conclusion until "AllChoose" fold is defined.
    True := by
  trivial

/-- WF propagates past a sample-bind to the continuation. -/
theorem WFOnProg_of_sample_tail
    (Reach : ReachSpec (L := L)) (σ : Profile (L := L))
    {Γ τ τ'} (id : YieldId) (v : View (L := L) Γ)
    (K : ObsKernel (L := L) v τ')
    (k : ProtoProg (L := L) (τ' :: Γ) τ)
    (hWF : WFOnProg (L := L) Reach σ
      (.doBind (.sample id v K) k)) :
    WFOnProg (L := L) Reach σ k := by
  sorry


-- ------------------------------------------------------------
-- 8) Mass / probability (ties into WFChanceOnProg)
-- ------------------------------------------------------------

theorem mass_evalProto_ret {Γ τ} (σ : Profile (L := L)) (e : L.Expr Γ τ) (env : L.Env Γ) :
    (evalProto (L := L) σ (.ret e) env).mass = 1 := by
  simp [WDist.mass_pure]

theorem mass_evalProto_observe_le {Γ τ} (σ : Profile (L := L))
    (c : L.Expr Γ L.bool) (k : ProtoProg (L := L) Γ τ) (env : L.Env Γ) :
    (evalProto (L := L) σ (.observe c k) env).mass ≤ (evalProto (L := L) σ k env).mass := by
  -- reduces to WDist.mass_observe_le-like lemma once expanded
  sorry

end ProtoProg
end ProtoLet
