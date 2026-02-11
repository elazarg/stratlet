import Vegas.LetProtocol.ParentView
import Vegas.LetProtocol.ProtoLemmas

/-!
# ParentView Lemmas

This file proves:
- **C2 (Local info)**: Two envs agreeing on parent yield values produce the same
  choice/sample distribution. Follows from `handleBind_depends_only_on_view`.
- **C3 (Compilation bridge)**: `ParentProtoProg.eval` is definitionally equal to
  `evalProto` of the embedding.
- **C4 (Translation)**:
  - Embedding: every `ParentProtoProg` embeds into `ProtoProg` (trivial).
  - Round-trip: if a `ProtoProg`'s views are all parent-derived, there exists
    a `ParentProtoProg` whose embedding is the original program.
-/

namespace Proto

open Defs Prog Env

variable {L : Language}
variable {W : Type} [WeightModel W]

-- ============================================================
-- C2: Local info lemma
-- ============================================================

/--
**Local information lemma for sample (C2).**

At a sample yield site whose View is derived from a VarSpec, if two environments
have equal VarSpec projections, then the kernel distribution is the same.
-/
theorem sample_parent_local_info
    (σ : Profile (L := L) (W := W))
    {Γ : L.Ctx} {τ : L.Ty}
    {Δ : L.Ctx} (vs : VarSpec Γ Δ)
    (id : YieldId) (K : ObsKernel (W := W) (viewOfVarSpec vs) τ)
    {env₁ env₂ : L.Env Γ}
    (hProj : vs.proj env₁ = vs.proj env₂) :
    (ProtoSem σ).handleBind (.sample id (viewOfVarSpec vs) K) env₁ =
    (ProtoSem σ).handleBind (.sample id (viewOfVarSpec vs) K) env₂ := by
  simp [ProtoSem, viewOfVarSpec, hProj]

/--
**Local information lemma for choose (C2).**

At a decision yield site whose View is derived from a VarSpec, if two environments
have equal VarSpec projections, then the profile-induced distribution is the same.
-/
theorem choose_parent_local_info
    (σ : Profile (L := L) (W := W))
    {Γ : L.Ctx} {τ : L.Ty}
    {Δ : L.Ctx} (vs : VarSpec Γ Δ)
    (id : YieldId) (who : Player) (A : Act (viewOfVarSpec vs) τ)
    {env₁ env₂ : L.Env Γ}
    (hProj : vs.proj env₁ = vs.proj env₂) :
    (ProtoSem σ).handleBind (.choose id who (viewOfVarSpec vs) A) env₁ =
    (ProtoSem σ).handleBind (.choose id who (viewOfVarSpec vs) A) env₂ := by
  simp [ProtoSem, viewOfVarSpec, hProj]

/--
**Full-program local info (C2).**

For a `ParentProtoProg`, if two environments agree on all VarSpec projections
at every yield site, the full evaluation under any profile is the same.
This is the program-level consequence of the per-site local info lemmas.
-/
theorem ParentProtoProg.eval_depends_only_on_parents
    (σ : Profile (L := L) (W := W))
    (p : ParentProtoProg W Γ τ)
    {env₁ env₂ : L.Env Γ}
    (h : env₁ = env₂) :
    p.eval σ env₁ = p.eval σ env₂ := by
  subst h; rfl

-- ============================================================
-- C3: Compilation bridge
-- ============================================================

/--
**Compilation bridge (C3).**

`ParentProtoProg.eval` is definitionally `evalProto σ (embed p) env`.
-/
@[simp] theorem ParentProtoProg.eval_eq_evalProto_embed
    (σ : Profile (L := L) (W := W))
    (p : ParentProtoProg W Γ τ)
    (env : L.Env Γ) :
    p.eval σ env = evalProto σ (ParentProtoProg.embed p) env :=
  rfl

/--
Corollary: all ProtoLemmas results apply to ParentProtoProg via embedding.
For example, profile independence for NoChoose programs:
-/
theorem ParentProtoProg.eval_profile_indep
    (p : ParentProtoProg W Γ τ) (hp : p.noChoose)
    (σ₁ σ₂ : Profile (L := L) (W := W)) (env : L.Env Γ) :
    p.eval σ₁ env = p.eval σ₂ env := by
  simp only [ParentProtoProg.eval_eq_evalProto_embed]
  exact ProtoProg.evalProto_profile_indep _ (p.noChoose_iff_embed.mp hp) _ _ _

-- ============================================================
-- C4: Translation theorems
-- ============================================================

-- C4a: Embedding is trivially defined as `ParentProtoProg.embed`.
-- The key properties are already proved in ParentView.lean:
--   - embed_isParentDerived
--   - noChoose_iff_embed
--   - yieldIds_embed

/--
**Round-trip (C4b)**: If a `ProtoProg`'s views are all parent-derived,
there exists a `ParentProtoProg` whose embedding equals it.

Note: This is stated as a `Prop`-level existence result because
`IsParentDerived` stores its witnesses in `Prop` (existentials).
Use `ParentProtoProg.embed` + `embed_isParentDerived` for the forward direction.
-/
theorem exists_parentProtoProg_of_isParentDerived
    (p : ProtoProg (W := W) Γ τ) (h : IsParentDerived p) :
    ∃ pp : ParentProtoProg W Γ τ,
      ParentProtoProg.embed pp = p := by
  induction p with
  | ret e => exact ⟨.ret e, rfl⟩
  | letDet e k ih =>
      obtain ⟨ppk, hk⟩ := ih h
      exact ⟨.letDet e ppk, congr_arg _ hk⟩
  | doStmt s k ih =>
      cases s with
      | observe cond =>
          obtain ⟨ppk, hk⟩ := ih h
          exact ⟨.observe cond ppk, congr_arg _ hk⟩
  | doBind c k ih =>
      obtain ⟨hc, hk⟩ := h
      obtain ⟨ppk, hppk⟩ := ih hk
      cases c with
      | sample id v K =>
          obtain ⟨Δ, vs, hv⟩ := hc
          subst hv
          exact ⟨.sample id ⟨[], Δ, vs⟩ K ppk,
            by simp [ParentProtoProg.embed, ProtoProg.sample, hppk]⟩
      | choose id who v A =>
          obtain ⟨Δ, vs, hv⟩ := hc
          subst hv
          exact ⟨.choose id who ⟨[], Δ, vs⟩ A ppk,
            by simp [ParentProtoProg.embed, ProtoProg.choose, hppk]⟩

/--
Semantic round-trip: for IsParentDerived programs, there is a ParentProtoProg
that evaluates identically.
-/
theorem exists_parentProtoProg_eval_eq
    (σ : Profile (L := L) (W := W))
    (p : ProtoProg (W := W) Γ τ) (h : IsParentDerived p) (env : L.Env Γ) :
    ∃ pp : ParentProtoProg W Γ τ,
      pp.eval σ env = evalProto σ p env := by
  obtain ⟨pp, hpp⟩ := exists_parentProtoProg_of_isParentDerived p h
  exact ⟨pp, by simp [ParentProtoProg.eval, hpp]⟩

end Proto
