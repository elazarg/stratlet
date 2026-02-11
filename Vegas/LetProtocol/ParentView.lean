import Vegas.LetProtocol.Proto

/-!
# ParentView: Parent-Set Bayes-Net View for ProtoProg

Instead of providing an arbitrary `View` (projection function), this module lets
you specify which previous yield IDs are visible. This is the "parent-set" /
Bayes-net-style specification.

The key idea:
- A `ParentSpec` is a list of `YieldId`s that are visible at a node.
- A `VarSpec` provides concrete de Bruijn variables for the projection.
- `ParentProtoProg` mirrors `ProtoProg` but carries `ParentSite` instead of `View`.
- `embed` converts back to `ProtoProg` by forgetting the parent-spec metadata.
-/

namespace Proto

open Defs Prog Env

variable {L : Language}
variable {W : Type} [WeightModel W]

-- ============================================================
-- 1) ParentSpec: which yields are visible
-- ============================================================

/-- Which previous yield IDs are visible at a decision/sample node. -/
abbrev ParentSpec : Type := List YieldId

-- ============================================================
-- 2) VarSpec: concrete sub-context extraction
-- ============================================================

/-- A `VarSpec Γ Δ` witnesses that `Δ` is a sub-context of `Γ`,
    given by a list of variables that extract each position of `Δ` from `Γ`. -/
inductive VarSpec : L.Ctx → L.Ctx → Type where
  | nil : VarSpec Γ []
  | cons : Var Γ τ → VarSpec Γ Δ → VarSpec Γ (τ :: Δ)

/-- Extract an environment `Env Δ` from `Env Γ` using a `VarSpec`. -/
def VarSpec.proj : VarSpec Γ Δ → L.Env Γ → L.Env Δ
  | .nil, _ => ()
  | .cons x rest, env => (env.get x, rest.proj env)

/-- VarSpec projection is determined by the projected variable values. -/
theorem VarSpec.proj_eq_of_vars_eq
    (vs : VarSpec Γ Δ)
    {env₁ env₂ : L.Env Γ}
    (h : ∀ {τ} (x : Var Γ τ), env₁.get x = env₂.get x) :
    vs.proj env₁ = vs.proj env₂ := by
  induction vs with
  | nil => rfl
  | cons x rest ih => exact Prod.ext (h x) ih

/-- Build a `View` from a `VarSpec`. -/
def viewOfVarSpec (vs : VarSpec Γ Δ) : View Γ where
  Δ := Δ
  proj := vs.proj

-- ============================================================
-- 3) VarSpec utilities: weakening, empty
-- ============================================================

/-- Weaken a `VarSpec` to work in an extended context. -/
def VarSpec.weaken : VarSpec Γ Δ → VarSpec (τ :: Γ) Δ
  | .nil => .nil
  | .cons x rest => .cons (.vs x) rest.weaken

/-- The empty var spec: reveals nothing. -/
def VarSpec.empty : VarSpec Γ [] := .nil

/-- A single-variable var spec. -/
def VarSpec.single (x : Var (Ty := L.Ty) Γ τ) : VarSpec Γ [τ] :=
  .cons x .nil

-- ============================================================
-- 4) ParentSite and ParentProtoProg
-- ============================================================

/-- A `ParentSite` records parent information for a single yield site:
    the declared parent ids, the visible sub-context, and the variables
    that implement the projection. -/
structure ParentSite (Γ : L.Ctx) where
  parents : ParentSpec
  Δ : L.Ctx
  vars : VarSpec Γ Δ

/--
A `ParentProtoProg` mirrors `ProtoProg` but carries `ParentSite` instead of
raw `View` at each yield site. This is the "separate inductive" approach.
-/
inductive ParentProtoProg (W : Type) [WeightModel W] : L.Ctx → L.Ty → Type where
  | ret : L.Expr Γ τ → ParentProtoProg W Γ τ
  | letDet : L.Expr Γ τ' → ParentProtoProg W (τ' :: Γ) τ → ParentProtoProg W Γ τ
  | observe : L.Expr Γ L.bool → ParentProtoProg W Γ τ → ParentProtoProg W Γ τ
  | sample : YieldId → (ps : ParentSite Γ) →
      ObsKernel (W := W) (viewOfVarSpec ps.vars) τ' →
      ParentProtoProg W (τ' :: Γ) τ → ParentProtoProg W Γ τ
  | choose : YieldId → Player → (ps : ParentSite Γ) →
      Act (viewOfVarSpec ps.vars) τ' →
      ParentProtoProg W (τ' :: Γ) τ → ParentProtoProg W Γ τ

namespace ParentProtoProg

/-- Embed a `ParentProtoProg` into a `ProtoProg` by forgetting parent info. -/
def embed : ParentProtoProg W Γ τ → ProtoProg (W := W) Γ τ
  | .ret e => .ret e
  | .letDet e k => .letDet e (embed k)
  | .observe c k => ProtoProg.observe c (embed k)
  | .sample id ps K k =>
      ProtoProg.sample id (viewOfVarSpec ps.vars) K (embed k)
  | .choose id who ps A k =>
      ProtoProg.choose id who (viewOfVarSpec ps.vars) A (embed k)

/-- Evaluate a `ParentProtoProg` under a profile, via embedding. -/
def eval (σ : Profile (L := L) (W := W)) (p : ParentProtoProg W Γ τ) (env : L.Env Γ) :
    WDist W (L.Val τ) :=
  evalProto σ (embed p) env

/-- Collect yield ids from a `ParentProtoProg`. -/
def yieldIds : ParentProtoProg W Γ τ → List YieldId
  | .ret _ => []
  | .letDet _ k => yieldIds k
  | .observe _ k => yieldIds k
  | .sample id _ _ k => id :: yieldIds k
  | .choose id _ _ _ k => id :: yieldIds k

/-- Collect parent specs from a `ParentProtoProg`. -/
def parentSpecs : ParentProtoProg W Γ τ → List ParentSpec
  | .ret _ => []
  | .letDet _ k => parentSpecs k
  | .observe _ k => parentSpecs k
  | .sample _ ps _ k => ps.parents :: parentSpecs k
  | .choose _ _ ps _ k => ps.parents :: parentSpecs k

/-- A `ParentProtoProg` has no remaining decision yields. -/
def noChoose : ParentProtoProg W Γ τ → Prop
  | .ret _ => True
  | .letDet _ k => noChoose k
  | .observe _ k => noChoose k
  | .sample _ _ _ k => noChoose k
  | .choose _ _ _ _ _ => False

end ParentProtoProg

-- ============================================================
-- 5) Predicate: a ProtoProg's views are all parent-derived
-- ============================================================

/--
Predicate on a `ProtoProg`: every `View` at a yield site is
the `viewOfVarSpec` of some `VarSpec`. This characterizes
"parent-derivable" programs without requiring a separate syntax.
-/
def IsParentDerived : ProtoProg (L := L) (W := W) Γ τ → Prop
  | .ret _ => True
  | .letDet _ k => IsParentDerived k
  | .doStmt _ k => IsParentDerived k
  | .doBind c k =>
      (match c with
       | .sample _id v _K =>
           ∃ (Δ : L.Ctx) (vs : VarSpec Γ Δ), v = viewOfVarSpec vs
       | .choose _id _who v _A =>
           ∃ (Δ : L.Ctx) (vs : VarSpec Γ Δ), v = viewOfVarSpec vs)
      ∧ IsParentDerived k

-- ============================================================
-- 6) Embedding theorems
-- ============================================================

/-- Every `ParentProtoProg` embeds to a parent-derived `ProtoProg`. -/
theorem ParentProtoProg.embed_isParentDerived
    (p : ParentProtoProg W Γ τ) :
    IsParentDerived (ParentProtoProg.embed p) := by
  induction p with
  | ret _ => trivial
  | letDet _ _ ih => exact ih
  | observe _ _ ih => exact ih
  | sample id ps K _ ih =>
      exact ⟨⟨ps.Δ, ps.vars, rfl⟩, ih⟩
  | choose id who ps A _ ih =>
      exact ⟨⟨ps.Δ, ps.vars, rfl⟩, ih⟩

/-- NoChoose is preserved by embedding. -/
theorem ParentProtoProg.noChoose_iff_embed
    (p : ParentProtoProg W Γ τ) :
    p.noChoose ↔ NoChoose (ParentProtoProg.embed p) := by
  induction p with
  | ret _ =>
      constructor
      · intro; trivial
      · intro; trivial
  | letDet _ _ ih => exact ih
  | observe _ _ ih =>
      simp only [ParentProtoProg.noChoose, ParentProtoProg.embed,
        ProtoProg.observe, NoChoose]
      exact ih
  | sample _ _ _ _ ih =>
      simp only [ParentProtoProg.noChoose, ParentProtoProg.embed,
        ProtoProg.sample, NoChoose]
      exact ih
  | choose _ _ _ _ _ _ =>
      constructor
      · intro h; exact absurd h id
      · intro h; exact absurd h id

/-- Yield ids of embedded program match. -/
theorem ParentProtoProg.yieldIds_embed
    (p : ParentProtoProg W Γ τ) :
    Proto.yieldIds (ParentProtoProg.embed p) = p.yieldIds := by
  induction p with
  | ret _ => rfl
  | letDet _ _ ih =>
      simp only [ParentProtoProg.embed, ProtoProg.letDet,
        Proto.yieldIds, ParentProtoProg.yieldIds]
      exact ih
  | observe _ _ ih =>
      simp only [ParentProtoProg.embed, ProtoProg.observe,
        Proto.yieldIds, ParentProtoProg.yieldIds]
      exact ih
  | sample _ _ _ _ ih =>
      simp only [ParentProtoProg.embed, ProtoProg.sample,
        Proto.yieldIds, ParentProtoProg.yieldIds]
      exact congr_arg _ ih
  | choose _ _ _ _ _ ih =>
      simp only [ParentProtoProg.embed, ProtoProg.choose,
        Proto.yieldIds, ParentProtoProg.yieldIds]
      exact congr_arg _ ih

end Proto
