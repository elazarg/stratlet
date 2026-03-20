import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Vegas.FDist

/-!
# Generic protocol interface

This file records the generic value and protocol interface that the Vegas
development depends on.

Design:

- `IExpr` packages the concrete expression layer (types, values,
  syntax, evaluation, dependency tracking, and soundness laws).
- The visibility-aware protocol structure (`VCtx`, `VHasVar`, `VEnv`) is
  generic over `IExpr`.
- Erasure functions (`eraseVCtx`, `erasePubVCtx`) project visibility contexts
  down to plain contexts consumed by `IExpr.eval`/`evalDist`.
- `VegasCore` constructors reference `L.Expr`/`L.DistExpr` over erased
  contexts.
-/

namespace Vegas

/-- Variable identifiers for both plain and visibility-tagged contexts. -/
abbrev VarId : Type := Nat

/-- A plain typed context indexed by variable identifiers. -/
abbrev Ctx (Ty : Type) := List (VarId × Ty)

/-- Typed membership in a plain context. -/
inductive HasVar {Ty : Type} : Ctx Ty → VarId → Ty → Type where
  | here {Γ x τ} : HasVar ((x, τ) :: Γ) x τ
  | there {Γ x y τ τ'} : HasVar Γ x τ → HasVar ((y, τ') :: Γ) x τ

/-- Runtime environments for plain contexts. -/
def Env {Ty : Type} (Val : Ty → Type) : Ctx Ty → Type :=
  fun Γ => ∀ x τ, HasVar Γ x τ → Val τ

namespace Env

def empty {Ty : Type} (Val : Ty → Type) : Env Val ([] : Ctx Ty) :=
  fun _ _ h => nomatch h

def cons {Ty : Type} {Val : Ty → Type} {Γ : Ctx Ty} {x : VarId} {τ : Ty}
    (v : Val τ) (env : Env Val Γ) : Env Val ((x, τ) :: Γ) :=
  fun _ _ h =>
    match h with
    | .here => v
    | .there h' => env _ _ h'

def get {Ty : Type} {Val : Ty → Type} {Γ : Ctx Ty} {x : VarId} {τ : Ty}
    (env : Env Val Γ) (h : HasVar Γ x τ) : Val τ :=
  env x τ h

@[simp] theorem cons_get_here {Ty : Type} {Val : Ty → Type} {Γ : Ctx Ty}
    {x : VarId} {τ : Ty} {v : Val τ} {env : Env Val Γ} :
    (Env.cons v env).get (HasVar.here (Γ := Γ) (x := x) (τ := τ)) = v := rfl

@[simp] theorem cons_get_there {Ty : Type} {Val : Ty → Type} {Γ : Ctx Ty}
    {x y : VarId} {τ σ : Ty} {v : Val τ} {env : Env Val Γ}
    {h : HasVar Γ y σ} :
    (Env.cons (x := x) v env).get (HasVar.there h) = env.get h := rfl

theorem cons_ext {Ty : Type} {Val : Ty → Type} {Γ : Ctx Ty}
    {x : VarId} {τ : Ty}
    {v₁ v₂ : Val τ} {env₁ env₂ : Env Val Γ}
    (hv : v₁ = v₂) (henv : env₁ = env₂) :
    cons (x := x) (τ := τ) v₁ env₁ = cons (x := x) (τ := τ) v₂ env₂ := by
  subst hv; subst henv; rfl

end Env

/-- Two environments agree on a set of variable identifiers. -/
def AgreesOn {Ty : Type} {Val : Ty → Type} {Γ : Ctx Ty}
    (ρ₁ ρ₂ : Env Val Γ) (xs : Finset VarId) : Prop :=
  ∀ x τ (h : HasVar Γ x τ), x ∈ xs → ρ₁ x τ h = ρ₂ x τ h

theorem AgreesOn.mono {Ty : Type} {Val : Ty → Type} {Γ : Ctx Ty}
    {ρ₁ ρ₂ : Env Val Γ} {S T : Finset VarId}
    (h : AgreesOn ρ₁ ρ₂ T) (hST : S ⊆ T) : AgreesOn ρ₁ ρ₂ S :=
  fun x τ hx hm => h x τ hx (hST hm)

/-- Core PL interface for the Vegas layer.

Packages the concrete expression layer: types, values, expression syntax,
distribution syntax, evaluation functions, dependency tracking, and
dependency-soundness laws. Expressions and distributions are typed over
plain `Ctx Ty` (no visibility annotations). -/
structure IExpr where
  Ty : Type
  Val : Ty → Type
  decEqTy : DecidableEq Ty
  decEqVal : ∀ {τ : Ty}, DecidableEq (Val τ)
  bool : Ty
  toBool : Val bool → Bool
  int : Ty
  toInt : Val int → Int
  Expr : Ctx Ty → Ty → Type
  eval : {Γ : Ctx Ty} → {τ : Ty} → Expr Γ τ → Env Val Γ → Val τ
  exprDeps : {Γ : Ctx Ty} → {τ : Ty} → Expr Γ τ → Finset VarId
  DistExpr : Ctx Ty → Ty → Type
  evalDist : {Γ : Ctx Ty} → {τ : Ty} →
    DistExpr Γ τ → Env Val Γ → @FDist (Val τ) decEqVal
  distDeps : {Γ : Ctx Ty} → {τ : Ty} → DistExpr Γ τ → Finset VarId
  expr_deps_sound :
    ∀ {Γ : Ctx Ty} {τ : Ty} (e : Expr Γ τ) (ρ₁ ρ₂ : Env Val Γ),
      AgreesOn ρ₁ ρ₂ (exprDeps e) → eval e ρ₁ = eval e ρ₂
  dist_deps_sound :
    ∀ {Γ : Ctx Ty} {τ : Ty} (d : DistExpr Γ τ) (ρ₁ ρ₂ : Env Val Γ),
      AgreesOn ρ₁ ρ₂ (distDeps d) → evalDist d ρ₁ = evalDist d ρ₂

attribute [instance] IExpr.decEqTy IExpr.decEqVal

/-- Visibility-aware binding types over an abstract language. -/
inductive BindTy (Player : Type) (L : IExpr) where
  | pub (τ : L.Ty)
  | hidden (owner : Player) (τ : L.Ty)

instance {Player : Type} [DecidableEq Player] {L : IExpr} :
    DecidableEq (BindTy Player L)
  | .pub τ₁, .pub τ₂ =>
      match decEq τ₁ τ₂ with
      | isTrue h => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
  | .hidden p₁ τ₁, .hidden p₂ τ₂ =>
      match decEq p₁ p₂, decEq τ₁ τ₂ with
      | isTrue hp, isTrue hτ => isTrue (by cases hp; cases hτ; rfl)
      | isFalse hp, _ => isFalse (by intro h; cases h; exact hp rfl)
      | _, isFalse hτ => isFalse (by intro h; cases h; exact hτ rfl)
  | .pub _, .hidden _ _ => isFalse (by intro h; cases h)
  | .hidden _ _, .pub _ => isFalse (by intro h; cases h)

namespace BindTy

def base {Player : Type} {L : IExpr} : BindTy Player L → L.Ty
  | .pub τ => τ
  | .hidden _ τ => τ

end BindTy

/-- Visibility-tagged contexts indexed by variable identifiers. -/
abbrev VCtx (Player : Type) (L : IExpr) : Type :=
  List (VarId × BindTy Player L)

/-- Typed membership in a visibility-tagged context. -/
inductive VHasVar {Player : Type} {L : IExpr} :
    VCtx Player L → VarId → BindTy Player L → Type where
  | here {Γ x τ} : VHasVar ((x, τ) :: Γ) x τ
  | there {Γ x y τ τ'} : VHasVar Γ x τ → VHasVar ((y, τ') :: Γ) x τ

/-- Runtime environments for visibility-tagged contexts. -/
def VEnv {Player : Type} (L : IExpr) : VCtx Player L → Type :=
  fun Γ => ∀ x τ, VHasVar (L := L) Γ x τ → L.Val τ.base

namespace VEnv

def empty {Player : Type} (L : IExpr) : VEnv (Player := Player) L [] :=
  fun _ _ h => nomatch h

def cons {Player : Type} {L : IExpr} {Γ : VCtx Player L} {x : VarId}
    {τ : BindTy Player L}
    (v : L.Val τ.base) (env : VEnv (Player := Player) L Γ) :
    VEnv (Player := Player) L ((x, τ) :: Γ) :=
  fun _ _ h =>
    match h with
    | .here => v
    | .there h' => env _ _ h'

theorem cons_ext {Player : Type} {L : IExpr} {Γ : VCtx Player L}
    {x : VarId} {τ : BindTy Player L}
    {v₁ v₂ : L.Val τ.base} {env₁ env₂ : VEnv (Player := Player) L Γ}
    (hv : v₁ = v₂) (henv : env₁ = env₂) :
    cons (x := x) (τ := τ) v₁ env₁ = cons (x := x) (τ := τ) v₂ env₂ := by
  subst hv; subst henv; rfl

def get {Player : Type} {L : IExpr} {Γ : VCtx Player L} {x : VarId}
    {τ : BindTy Player L}
    (env : VEnv (Player := Player) L Γ) (h : VHasVar (L := L) Γ x τ) :
    L.Val τ.base :=
  env x τ h

@[simp] theorem cons_get_here {Player : Type} {L : IExpr}
    {Γ : VCtx Player L} {x : VarId} {τ : BindTy Player L}
    {v : L.Val τ.base} {env : VEnv (Player := Player) L Γ} :
    (VEnv.cons v env).get (VHasVar.here (Γ := Γ) (x := x) (τ := τ)) = v := rfl

@[simp] theorem cons_get_there {Player : Type} {L : IExpr}
    {Γ : VCtx Player L} {x y : VarId} {τ σ : BindTy Player L}
    {v : L.Val τ.base} {env : VEnv (Player := Player) L Γ}
    {h : VHasVar (L := L) Γ y σ} :
    (VEnv.cons (x := x) v env).get (VHasVar.there h) = env.get h := rfl

end VEnv

/-- Public observability predicate. -/
def canSee {Player : Type} [DecidableEq Player] {L : IExpr}
    (p : Player) : BindTy Player L → Bool
  | .pub _ => true
  | .hidden q _ => decide (p = q)

/-- Player-local visible subcontext. -/
def viewVCtx {Player : Type} [DecidableEq Player] {L : IExpr}
    (p : Player) : VCtx Player L → VCtx Player L
  | [] => []
  | (x, τ) :: Γ =>
      if canSee p τ then (x, τ) :: viewVCtx p Γ else viewVCtx p Γ

namespace VHasVar

def ofViewVCtx {Player : Type} [DecidableEq Player] {L : IExpr}
    {p : Player} {Γ : VCtx Player L} {x : VarId} {τ : BindTy Player L} :
    VHasVar (L := L) (viewVCtx p Γ) x τ → VHasVar (L := L) Γ x τ := by
  induction Γ with
  | nil => intro h; exact nomatch h
  | cons hd tl ih =>
    obtain ⟨y, σ⟩ := hd
    simp only [viewVCtx]
    split
    · intro h
      match h with
      | .here => exact .here
      | .there h' => exact .there (ih h')
    · intro h
      exact .there (ih h)

end VHasVar

/-- Public-only fragment of a visibility context. -/
def pubVCtx {Player : Type} {L : IExpr} : VCtx Player L → VCtx Player L
  | [] => []
  | (x, .pub τ) :: Γ => (x, .pub τ) :: pubVCtx Γ
  | (_, .hidden _ _) :: Γ => pubVCtx Γ

namespace VHasVar

def ofPubVCtx {Player : Type} {L : IExpr}
    {Γ : VCtx Player L} {x : VarId} {τ : BindTy Player L} :
    VHasVar (L := L) (pubVCtx Γ) x τ → VHasVar (L := L) Γ x τ := by
  induction Γ with
  | nil => intro h; exact nomatch h
  | cons hd tl ih =>
    obtain ⟨y, σ⟩ := hd
    match σ with
    | .pub υ =>
      simp only [pubVCtx]
      intro h
      match h with
      | .here => exact .here
      | .there h' => exact .there (ih h')
    | .hidden q υ =>
      simp only [pubVCtx]
      intro h
      exact .there (ih h)

def ofPubToView {Player : Type} [DecidableEq Player] {L : IExpr}
    {p : Player} {Γ : VCtx Player L} {x : VarId} {τ : BindTy Player L} :
    VHasVar (L := L) (pubVCtx Γ) x τ → VHasVar (L := L) (viewVCtx p Γ) x τ := by
  induction Γ with
  | nil => intro h; exact nomatch h
  | cons hd tl ih =>
    obtain ⟨y, σ⟩ := hd
    intro h
    match σ with
    | .pub τ =>
      simp only [pubVCtx] at h
      simp only [viewVCtx, canSee]
      match h with
      | .here => exact .here
      | .there h' => exact .there (ih h')
    | .hidden q τ =>
      simp only [pubVCtx] at h
      simp only [viewVCtx]
      split
      · exact .there (ih h)
      · exact ih h

end VHasVar

/-- Flatten a visibility context to a public context with the same variables. -/
def flattenVCtx {Player : Type} {L : IExpr} :
    VCtx Player L → VCtx Player L
  | [] => []
  | (x, τ) :: Γ => (x, .pub τ.base) :: flattenVCtx Γ

@[simp] theorem flattenVCtx_nil {Player : Type} {L : IExpr} :
    flattenVCtx (Player := Player) (L := L) [] = [] := rfl

@[simp] theorem flattenVCtx_cons {Player : Type} {L : IExpr}
    {x : VarId} {τ : BindTy Player L} {Γ : VCtx Player L} :
    flattenVCtx ((x, τ) :: Γ) = (x, .pub τ.base) :: flattenVCtx Γ := rfl

theorem flattenVCtx_map_fst {Player : Type} {L : IExpr}
    {Γ : VCtx Player L} :
    (flattenVCtx Γ).map Prod.fst = Γ.map Prod.fst := by
  induction Γ with
  | nil => rfl
  | cons hd tl ih => simp [flattenVCtx, ih]

theorem flattenVCtx_length {Player : Type} {L : IExpr}
    {Γ : VCtx Player L} :
    (flattenVCtx Γ).length = Γ.length := by
  have h := congrArg List.length (flattenVCtx_map_fst (Γ := Γ))
  simp only [List.length_map] at h
  exact h

theorem flattenVCtx_idempotent {Player : Type} {L : IExpr}
    {Γ : VCtx Player L} :
    flattenVCtx (flattenVCtx Γ) = flattenVCtx Γ := by
  induction Γ with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨x, τ⟩ := hd
    simp [flattenVCtx, BindTy.base, ih]

namespace VHasVar

def toFlatten {Player : Type} {L : IExpr}
    {Γ : VCtx Player L} {x : VarId} {τ : BindTy Player L} :
    VHasVar (L := L) Γ x τ → VHasVar (L := L) (flattenVCtx Γ) x (.pub τ.base)
  | .here => .here
  | .there h => .there h.toFlatten

def unflatten {Player : Type} {L : IExpr}
    {Γ : VCtx Player L} {x : VarId} {τ : L.Ty} :
    VHasVar (L := L) (flattenVCtx Γ) x (.pub τ) →
    (σ : BindTy Player L) × VHasVar (L := L) Γ x σ × PLift (σ.base = τ) :=
  match Γ with
  | [] => fun h => nomatch h
  | (_, σ) :: _ => fun h =>
    match h with
    | .here => ⟨σ, .here, ⟨rfl⟩⟩
    | .there h' =>
      let ⟨σ', hv, ⟨hτ⟩⟩ := unflatten h'
      ⟨σ', .there hv, ⟨hτ⟩⟩

end VHasVar

/-- Erase visibility annotations, keeping variable names and base types. -/
def eraseVCtx {Player : Type} {L : IExpr} :
    VCtx Player L → Ctx L.Ty
  | [] => []
  | (x, τ) :: Γ => (x, τ.base) :: eraseVCtx Γ

@[simp] theorem eraseVCtx_nil {Player : Type} {L : IExpr} :
    eraseVCtx (Player := Player) (L := L) [] = [] := rfl

@[simp] theorem eraseVCtx_cons {Player : Type} {L : IExpr}
    {x : VarId} {τ : BindTy Player L} {Γ : VCtx Player L} :
    eraseVCtx ((x, τ) :: Γ) = (x, τ.base) :: eraseVCtx Γ := rfl

/-- Erase visibility, keeping only public variables. -/
def erasePubVCtx {Player : Type} {L : IExpr} :
    VCtx Player L → Ctx L.Ty
  | [] => []
  | (x, .pub τ) :: Γ => (x, τ) :: erasePubVCtx Γ
  | (_, .hidden _ _) :: Γ => erasePubVCtx Γ

@[simp] theorem erasePubVCtx_nil {Player : Type} {L : IExpr} :
    erasePubVCtx (Player := Player) (L := L) [] = [] := rfl

@[simp] theorem erasePubVCtx_cons_pub {Player : Type} {L : IExpr}
    {x : VarId} {τ : L.Ty} {Γ : VCtx Player L} :
    erasePubVCtx ((x, BindTy.pub τ) :: Γ) = (x, τ) :: erasePubVCtx Γ := rfl

@[simp] theorem erasePubVCtx_cons_hidden {Player : Type} {L : IExpr}
    {x : VarId} {p : Player} {τ : L.Ty} {Γ : VCtx Player L} :
    erasePubVCtx ((x, BindTy.hidden p τ) :: Γ) = erasePubVCtx Γ := rfl

/-- Key lemma: flattening then erasing is the same as just erasing. -/
theorem eraseVCtx_flattenVCtx {Player : Type} {L : IExpr}
    {Γ : VCtx Player L} :
    eraseVCtx (flattenVCtx Γ) = eraseVCtx Γ := by
  induction Γ with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨x, τ⟩ := hd
    simp [flattenVCtx, eraseVCtx, BindTy.base, ih]

/-- Erasure of pubVCtx equals erasePubVCtx. -/
theorem eraseVCtx_pubVCtx {Player : Type} {L : IExpr}
    {Γ : VCtx Player L} :
    eraseVCtx (pubVCtx Γ) = erasePubVCtx Γ := by
  induction Γ with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨x, τ⟩ := hd
    match τ with
    | .pub b => simp [pubVCtx, erasePubVCtx, BindTy.base, ih]
    | .hidden p b => simp [pubVCtx, erasePubVCtx, ih]

/-- A VHasVar proof induces a HasVar proof in the erased context. -/
def VHasVar.toErased {Player : Type} {L : IExpr}
    {Γ : VCtx Player L} {x : VarId} {τ : BindTy Player L} :
    VHasVar (L := L) Γ x τ → HasVar (eraseVCtx Γ) x τ.base
  | .here => .here
  | .there h => .there h.toErased

/-- A HasVar in eraseVCtx lifts back to a VHasVar. -/
def HasVar.toVHasVar {Player : Type} {L : IExpr} :
    {Γ : VCtx Player L} → {x : VarId} → {b : L.Ty} →
    HasVar (eraseVCtx Γ) x b →
    (τ : BindTy Player L) × VHasVar (L := L) Γ x τ × PLift (τ.base = b)
  | (_, τ) :: _, _, _, .here => ⟨τ, .here, ⟨rfl⟩⟩
  | _ :: _, _, _, .there h =>
    let ⟨τ', hv, ⟨hb⟩⟩ := toVHasVar h
    ⟨τ', .there hv, ⟨hb⟩⟩

/-- A VHasVar in pubVCtx induces a HasVar in erasePubVCtx. -/
def VHasVar.toErasedPub {Player : Type} {L : IExpr}
    {Γ : VCtx Player L} {x : VarId} {τ : BindTy Player L} :
    VHasVar (L := L) (pubVCtx Γ) x τ → HasVar (erasePubVCtx Γ) x τ.base := by
  intro h
  have h' := h.toErased
  rw [eraseVCtx_pubVCtx] at h'
  exact h'

namespace VEnv

/-- Erase visibility from a VEnv, producing a plain Env over eraseVCtx. -/
def eraseEnv {Player : Type} {L : IExpr} :
    {Γ : VCtx Player L} → VEnv (Player := Player) L Γ →
    Env L.Val (eraseVCtx Γ)
  | [], _ => Env.empty L.Val
  | (_, _) :: _, env =>
    Env.cons (env.get .here) (eraseEnv (fun a b h => env a b (.there h)))

/-- Erase visibility, keeping only public variables. -/
def erasePubEnv {Player : Type} {L : IExpr} :
    {Γ : VCtx Player L} → VEnv (Player := Player) L Γ →
    Env L.Val (erasePubVCtx Γ)
  | [], _ => Env.empty L.Val
  | ((_, .pub _) :: Γ'), env =>
    Env.cons (env.get .here)
      (erasePubEnv (Γ := Γ') (fun a b h => env a b (VHasVar.there h)))
  | ((_, .hidden _ _) :: Γ'), env =>
    erasePubEnv (Γ := Γ') (fun a b h => env a b (VHasVar.there h))

/-- Project a VEnv to the visible subcontext of player `p`. -/
def toView {Player : Type} [DecidableEq Player] {L : IExpr} (p : Player)
    {Γ : VCtx Player L} (env : VEnv (Player := Player) L Γ) :
    VEnv (Player := Player) L (viewVCtx p Γ) :=
  fun x τ h => env x τ h.ofViewVCtx

/-- Project a VEnv to the public subcontext. -/
def toPub {Player : Type} {L : IExpr} {Γ : VCtx Player L}
    (env : VEnv (Player := Player) L Γ) :
    VEnv (Player := Player) L (pubVCtx Γ) :=
  fun x τ h => env x τ h.ofPubVCtx

/-- Flatten a VEnv to a public-only VEnv with the same variables. -/
def toFlat {Player : Type} {L : IExpr} {Γ : VCtx Player L}
    (env : VEnv (Player := Player) L Γ) :
    VEnv (Player := Player) L (flattenVCtx Γ) := by
  induction Γ with
  | nil => exact VEnv.empty L
  | cons hd tl ih =>
    obtain ⟨_, σ⟩ := hd
    let v : L.Val σ.base := env.get .here
    exact VEnv.cons (L := L) (τ := .pub σ.base) v
      (ih (fun a b c => env a b (.there c)))

/-- Flatten the visible subcontext. -/
def toFlatView {Player : Type} [DecidableEq Player] {L : IExpr}
    (p : Player) {Γ : VCtx Player L} (env : VEnv (Player := Player) L Γ) :
    VEnv (Player := Player) L (flattenVCtx (viewVCtx p Γ)) :=
  VEnv.toFlat (VEnv.toView p env)

end VEnv

/-- Whether a value is sampled publicly by nature, privately by nature, or by
the owning player. -/
inductive SampleMode {Player : Type} {L : IExpr} :
    BindTy Player L → Type where
  | NaturePub {τ} : SampleMode (.pub τ)
  | NaturePriv {owner τ} : SampleMode (.hidden owner τ)
  | PlayerPriv {owner τ} : SampleMode (.hidden owner τ)

/-- The context exposed to a distribution expression for a given sampling mode. -/
abbrev distVCtx {Player : Type} [DecidableEq Player] {L : IExpr}
    (τ : BindTy Player L) (m : SampleMode τ)
    (Γ : VCtx Player L) : VCtx Player L :=
  match τ, m with
  | .pub _, .NaturePub => pubVCtx Γ
  | .hidden _ _, .NaturePriv => pubVCtx Γ
  | .hidden p _, .PlayerPriv => flattenVCtx (viewVCtx p Γ)

namespace VEnv

/-- Project an environment to the visibility required for sampling in mode `m`. -/
def projectDist {Player : Type} [DecidableEq Player] {L : IExpr}
    {Γ : VCtx Player L}
    (τ : BindTy Player L) (m : SampleMode τ)
    (env : VEnv (Player := Player) L Γ) :
    VEnv (Player := Player) L (distVCtx τ m Γ) :=
  match τ, m with
  | .pub _, .NaturePub => env.toPub
  | .hidden _ _, .NaturePriv => env.toPub
  | .hidden p _, .PlayerPriv => env.toFlatView p

/-- Erase the distribution-projected VEnv to a plain Env. -/
def eraseDistEnv {Player : Type} [DecidableEq Player] {L : IExpr}
    {Γ : VCtx Player L}
    (τ : BindTy Player L) (m : SampleMode τ)
    (env : VEnv (Player := Player) L Γ) :
    Env L.Val (eraseVCtx (distVCtx τ m Γ)) :=
  VEnv.eraseEnv (VEnv.projectDist τ m env)

end VEnv

/-- Canonical outcome type: finitely-supported integer payoffs per player.
    Derived from the protocol's `ret` constructor rather than parameterized. -/
abbrev Outcome (Player : Type) [DecidableEq Player] := Player →₀ Int

/-- Evaluate a list of per-player payoff expressions into an outcome. -/
noncomputable def evalPayoffs {Player : Type} [DecidableEq Player]
    {L : IExpr} {Γ : VCtx Player L}
    (payoffs : List (Player × L.Expr (erasePubVCtx Γ) L.int))
    (env : VEnv (Player := Player) L Γ) : Outcome Player :=
  payoffs.foldl
    (fun acc (p, e) =>
      acc + Finsupp.single p (L.toInt (L.eval e (VEnv.erasePubEnv env))))
    0

/-- Evaluate a commit guard against a proposed action and the full erased
    environment. Visibility is enforced by dependency constraints on `R`,
    not by restricting the environment type. -/
def evalGuard {Player : Type} [DecidableEq Player] {L : IExpr}
    {Γ : VCtx Player L} {b : L.Ty}
    {x : VarId}
    (R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool)
    (a : L.Val b) (env : Env L.Val (eraseVCtx Γ)) : Bool :=
  L.toBool (L.eval R (Env.cons a env))

/- Generic Vegas-style protocol syntax over an expression language. -/
inductive VegasCore (Player : Type) [DecidableEq Player] (L : IExpr) :
    VCtx Player L → Type where
  | ret {Γ} (payoffs : List (Player × L.Expr (erasePubVCtx Γ) L.int)) :
      VegasCore Player L Γ
  | letExpr {Γ} (x : VarId) {b : L.Ty}
      (e : L.Expr (erasePubVCtx Γ) b)
      (k : VegasCore Player L ((x, .pub b) :: Γ)) :
      VegasCore Player L Γ
  | sample {Γ} (x : VarId) (τ : BindTy Player L) (m : SampleMode τ)
      (D' : L.DistExpr (eraseVCtx (distVCtx τ m Γ)) τ.base)
      (k : VegasCore Player L ((x, τ) :: Γ)) :
      VegasCore Player L Γ
  | commit {Γ} (x : VarId) (who : Player) {b : L.Ty}
      (R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool)
      (k : VegasCore Player L ((x, .hidden who b) :: Γ)) :
      VegasCore Player L Γ
  | reveal {Γ} (y : VarId) (who : Player) (x : VarId) {b : L.Ty}
      (hx : VHasVar (L := L) Γ x (.hidden who b))
      (k : VegasCore Player L ((y, .pub b) :: Γ)) :
      VegasCore Player L Γ

/-- Generic commit kernels: given the full erased environment, produce a
    distribution over action values. Visibility is a side condition on the
    kernel's dependency set, not a type constraint. -/
abbrev CommitKernel (Player : Type) [DecidableEq Player] (L : IExpr)
    (_who : Player) (Γ : VCtx Player L) (b : L.Ty) : Type :=
  Env L.Val (eraseVCtx Γ) → FDist (L.Val b)

/-- Generic profiles for Vegas-style commit nodes. -/
structure Profile (Player : Type) [DecidableEq Player]
    (L : IExpr) where
  commit : {Γ : VCtx Player L} → {b : L.Ty} → (who : Player) →
    (x : VarId) →
    (R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool) →
    CommitKernel Player L who Γ b

/-- Partial generic profiles with optional commit kernels. -/
structure PProfile (Player : Type) [DecidableEq Player]
    (L : IExpr) where
  commit? : {Γ : VCtx Player L} → {b : L.Ty} → (who : Player) →
    (x : VarId) →
    (R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool) →
    Option (CommitKernel Player L who Γ b)

def PProfile.toProfile {Player : Type} [DecidableEq Player]
    {L : IExpr}
    (π : PProfile Player L) (fallback : Profile Player L) :
    Profile Player L where
  commit := fun {Γ} {b} who x R env =>
    match π.commit? (Γ := Γ) (b := b) who x R with
    | some k => k env
    | none => fallback.commit who x R env

/-- Extra assumptions needed only for finite-backend compilation. -/
structure FiniteValuation (L : IExpr) where
  fintypeVal : ∀ τ : L.Ty, Fintype (L.Val τ)

namespace FiniteValuation

instance instFintypeVal (L : IExpr) (LF : FiniteValuation L)
    (τ : L.Ty) : Fintype (L.Val τ) :=
  LF.fintypeVal τ

/-- The finite branching factor of values of type `τ`. -/
noncomputable def domainSize (L : IExpr) (LF : FiniteValuation L)
    (τ : L.Ty) : Nat :=
  let _ := instFintypeVal L LF τ
  Fintype.card (L.Val τ)

/-- A canonical encoding of values as `Fin domainSize`. -/
noncomputable def encodeFin (L : IExpr) (LF : FiniteValuation L)
    (τ : L.Ty) : L.Val τ ≃ Fin (LF.domainSize L τ) :=
  let _ := instFintypeVal L LF τ
  Fintype.equivFin (L.Val τ)

end FiniteValuation

end Vegas
