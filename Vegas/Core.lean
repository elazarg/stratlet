import Vegas.FDist
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Generic protocol interface

This file records the generic value and protocol interface that the Vegas
development depends on.

Design:

- `ExprLanguage` hides the concrete value layer.
- the visibility-aware protocol structure is generic over that layer.
- finiteness is not part of the language identity.
- backend compilation to finite game models can add `FiniteValuation`
  assumptions only where needed.
-/

namespace Vegas

/-- A de Bruijn-style context for a backend expression language. -/
abbrev TypeCtx (Ty : Type) := List Ty

/-- Variables in a typed context. -/
inductive TypeVar {Ty : Type} : TypeCtx Ty → Ty → Type where
  | vz : TypeVar (τ :: Γ) τ
  | vs : TypeVar Γ τ → TypeVar (τ' :: Γ) τ

/-- Environments for a backend expression language. -/
def TypeEnv {Ty : Type} (Val : Ty → Type) : TypeCtx Ty → Type
  | [] => PUnit
  | τ :: Γ => Val τ × TypeEnv Val Γ

namespace TypeEnv

def get {Ty : Type} {Val : Ty → Type} :
    {Γ : TypeCtx Ty} → {τ : Ty} → TypeEnv Val Γ → @TypeVar Ty Γ τ → Val τ
  | _ :: _, _, env, .vz => env.1
  | _ :: _, _, env, .vs x => get env.2 x

end TypeEnv

/-- Core PL interface for the Vegas layer. -/
structure ExprLanguage where
  Ty : Type
  decEqTy : DecidableEq Ty
  Val : Ty → Type
  decEqVal : ∀ {τ : Ty}, DecidableEq (Val τ)
  bool : Ty
  toBool : Val bool → Bool
  int : Ty
  toInt : Val int → Int

attribute [instance] ExprLanguage.decEqTy ExprLanguage.decEqVal

namespace ExprLanguage

abbrev CtxSimple (L : ExprLanguage) : Type := Vegas.TypeCtx L.Ty
abbrev Var (L : ExprLanguage) (Γ : L.CtxSimple) (τ : L.Ty) : Type := @Vegas.TypeVar L.Ty Γ τ
abbrev EnvSimple (L : ExprLanguage) (Γ : L.CtxSimple) : Type := Vegas.TypeEnv L.Val Γ

end ExprLanguage

/-- Variable identifiers for visibility-tagged Vegas contexts. -/
abbrev VarId : Type := Nat

/-- Visibility-aware binding types over an abstract language. -/
inductive BindTy (Player : Type) (L : ExprLanguage) where
  | pub (τ : L.Ty)
  | hidden (owner : Player) (τ : L.Ty)

instance {Player : Type} [DecidableEq Player] {L : ExprLanguage} :
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

def base {Player : Type} {L : ExprLanguage} : BindTy Player L → L.Ty
  | .pub τ => τ
  | .hidden _ τ => τ

end BindTy

/-- Visibility-tagged contexts indexed by variable identifiers. -/
abbrev Ctx (Player : Type) (L : ExprLanguage) : Type :=
  List (VarId × BindTy Player L)

/-- Typed membership in a visibility-tagged context. -/
inductive HasVar {Player : Type} {L : ExprLanguage} :
    Ctx Player L → VarId → BindTy Player L → Type where
  | here {Γ x τ} : HasVar ((x, τ) :: Γ) x τ
  | there {Γ x y τ τ'} : HasVar Γ x τ → HasVar ((y, τ') :: Γ) x τ

/-- Runtime environments for visibility-tagged contexts. -/
def Env {Player : Type} (L : ExprLanguage) : Ctx Player L → Type :=
  fun Γ => ∀ x τ, HasVar (L := L) Γ x τ → L.Val τ.base

namespace Env

def empty {Player : Type} (L : ExprLanguage) : Env (Player := Player) L [] :=
  fun _ _ h => nomatch h

def cons {Player : Type} {L : ExprLanguage} {Γ : Ctx Player L} {x : VarId}
    {τ : BindTy Player L}
    (v : L.Val τ.base) (env : Env (Player := Player) L Γ) :
    Env (Player := Player) L ((x, τ) :: Γ) :=
  fun _ _ h =>
    match h with
    | .here => v
    | .there h' => env _ _ h'

theorem cons_ext {Player : Type} {L : ExprLanguage} {Γ : Ctx Player L}
    {x : VarId} {τ : BindTy Player L}
    {v₁ v₂ : L.Val τ.base} {env₁ env₂ : Env (Player := Player) L Γ}
    (hv : v₁ = v₂) (henv : env₁ = env₂) :
    cons (x := x) (τ := τ) v₁ env₁ = cons (x := x) (τ := τ) v₂ env₂ := by
  subst hv; subst henv; rfl

def get {Player : Type} {L : ExprLanguage} {Γ : Ctx Player L} {x : VarId}
    {τ : BindTy Player L}
    (env : Env (Player := Player) L Γ) (h : HasVar (L := L) Γ x τ) :
    L.Val τ.base :=
  env x τ h

@[simp] theorem cons_get_here {Player : Type} {L : ExprLanguage} {Γ : Ctx Player L}
    {x : VarId} {τ : BindTy Player L} {v : L.Val τ.base}
    {env : Env (Player := Player) L Γ} :
    (Env.cons v env).get (HasVar.here (Γ := Γ) (x := x) (τ := τ)) = v := rfl

@[simp] theorem cons_get_there {Player : Type} {L : ExprLanguage} {Γ : Ctx Player L}
    {x y : VarId} {τ σ : BindTy Player L}
    {v : L.Val τ.base} {env : Env (Player := Player) L Γ}
    {h : HasVar (L := L) Γ y σ} :
    (Env.cons (x := x) v env).get (HasVar.there h) = env.get h := rfl

end Env

/-- Public observability predicate. -/
def canSee {Player : Type} [DecidableEq Player] {L : ExprLanguage}
    (p : Player) : BindTy Player L → Bool
  | .pub _ => true
  | .hidden q _ => decide (p = q)

/-- Player-local visible subcontext. -/
def viewCtx {Player : Type} [DecidableEq Player] {L : ExprLanguage}
    (p : Player) : Ctx Player L → Ctx Player L
  | [] => []
  | (x, τ) :: Γ =>
      if canSee p τ then (x, τ) :: viewCtx p Γ else viewCtx p Γ

namespace HasVar

def ofViewCtx {Player : Type} [DecidableEq Player] {L : ExprLanguage} {p : Player}
    {Γ : Ctx Player L} {x : VarId} {τ : BindTy Player L} :
    HasVar (L := L) (viewCtx p Γ) x τ → HasVar (L := L) Γ x τ := by
  induction Γ with
  | nil => intro h; exact nomatch h
  | cons hd tl ih =>
    obtain ⟨y, σ⟩ := hd
    simp only [viewCtx]
    split
    · intro h
      match h with
      | .here => exact .here
      | .there h' => exact .there (ih h')
    · intro h
      exact .there (ih h)

end HasVar

/-- Public-only fragment of a visibility context. -/
def pubCtx {Player : Type} {L : ExprLanguage} : Ctx Player L → Ctx Player L
  | [] => []
  | (x, .pub τ) :: Γ => (x, .pub τ) :: pubCtx Γ
  | (_, .hidden _ _) :: Γ => pubCtx Γ

namespace HasVar

def ofPubCtx {Player : Type} {L : ExprLanguage}
    {Γ : Ctx Player L} {x : VarId} {τ : BindTy Player L} :
    HasVar (L := L) (pubCtx Γ) x τ → HasVar (L := L) Γ x τ := by
  induction Γ with
  | nil => intro h; exact nomatch h
  | cons hd tl ih =>
    obtain ⟨y, σ⟩ := hd
    match σ with
    | .pub υ =>
      simp only [pubCtx]
      intro h
      match h with
      | .here => exact .here
      | .there h' => exact .there (ih h')
    | .hidden q υ =>
      simp only [pubCtx]
      intro h
      exact .there (ih h)

def ofPubToView {Player : Type} [DecidableEq Player] {L : ExprLanguage} {p : Player}
    {Γ : Ctx Player L} {x : VarId} {τ : BindTy Player L} :
    HasVar (L := L) (pubCtx Γ) x τ → HasVar (L := L) (viewCtx p Γ) x τ := by
  induction Γ with
  | nil => intro h; exact nomatch h
  | cons hd tl ih =>
    obtain ⟨y, σ⟩ := hd
    intro h
    match σ with
    | .pub τ =>
      simp only [pubCtx] at h
      simp only [viewCtx, canSee]
      match h with
      | .here => exact .here
      | .there h' => exact .there (ih h')
    | .hidden q τ =>
      simp only [pubCtx] at h
      simp only [viewCtx]
      split
      · exact .there (ih h)
      · exact ih h

end HasVar

/-- Flatten a visibility context to a public context with the same variables. -/
def flattenCtx {Player : Type} {L : ExprLanguage} : Ctx Player L → Ctx Player L
  | [] => []
  | (x, τ) :: Γ => (x, .pub τ.base) :: flattenCtx Γ

@[simp] theorem flattenCtx_nil {Player : Type} {L : ExprLanguage} :
    flattenCtx (Player := Player) (L := L) [] = [] := rfl

@[simp] theorem flattenCtx_cons {Player : Type} {L : ExprLanguage}
    {x : VarId} {τ : BindTy Player L} {Γ : Ctx Player L} :
    flattenCtx ((x, τ) :: Γ) = (x, .pub τ.base) :: flattenCtx Γ := rfl

theorem flattenCtx_map_fst {Player : Type} {L : ExprLanguage} {Γ : Ctx Player L} :
    (flattenCtx Γ).map Prod.fst = Γ.map Prod.fst := by
  induction Γ with
  | nil => rfl
  | cons hd tl ih => simp [flattenCtx, ih]

theorem flattenCtx_length {Player : Type} {L : ExprLanguage} {Γ : Ctx Player L} :
    (flattenCtx Γ).length = Γ.length := by
  have h := congrArg List.length (flattenCtx_map_fst (Γ := Γ))
  simp only [List.length_map] at h
  exact h

theorem flattenCtx_idempotent {Player : Type} {L : ExprLanguage} {Γ : Ctx Player L} :
    flattenCtx (flattenCtx Γ) = flattenCtx Γ := by
  induction Γ with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨x, τ⟩ := hd
    simp [flattenCtx, BindTy.base, ih]

/-- Erase variable ids and visibility, keeping only backend value types. -/
def eraseCtx {Player : Type} {L : ExprLanguage} : Ctx Player L → L.CtxSimple
  | [] => []
  | (_, τ) :: Γ => τ.base :: eraseCtx Γ

namespace HasVar

def toFlatten {Player : Type} {L : ExprLanguage}
    {Γ : Ctx Player L} {x : VarId} {τ : BindTy Player L} :
    HasVar (L := L) Γ x τ → HasVar (L := L) (flattenCtx Γ) x (.pub τ.base)
  | .here => .here
  | .there h => .there h.toFlatten

def unflatten {Player : Type} {L : ExprLanguage} {Γ : Ctx Player L} {x : VarId} {τ : L.Ty} :
    HasVar (L := L) (flattenCtx Γ) x (.pub τ) →
    (σ : BindTy Player L) × HasVar (L := L) Γ x σ × PLift (σ.base = τ) :=
  match Γ with
  | [] => fun h => nomatch h
  | (_, σ) :: _ => fun h =>
    match h with
    | .here => ⟨σ, .here, ⟨rfl⟩⟩
    | .there h' =>
      let ⟨σ', hv, ⟨hτ⟩⟩ := unflatten h'
      ⟨σ', .there hv, ⟨hτ⟩⟩

end HasVar

namespace Env

def toView {Player : Type} [DecidableEq Player] {L : ExprLanguage} (p : Player)
    {Γ : Ctx Player L} (env : Env (Player := Player) L Γ) :
    Env (Player := Player) L (viewCtx p Γ) :=
  fun x τ h => env x τ h.ofViewCtx

def toPub {Player : Type} {L : ExprLanguage} {Γ : Ctx Player L}
    (env : Env (Player := Player) L Γ) :
    Env (Player := Player) L (pubCtx Γ) :=
  fun x τ h => env x τ h.ofPubCtx

def toFlat {Player : Type} {L : ExprLanguage} {Γ : Ctx Player L}
    (env : Env (Player := Player) L Γ) :
    Env (Player := Player) L (flattenCtx Γ) := by
  induction Γ with
  | nil => exact Env.empty L
  | cons hd tl ih =>
    obtain ⟨_, σ⟩ := hd
    let v : L.Val σ.base := env.get .here
    exact Env.cons (L := L) (τ := .pub σ.base) v
      (ih (fun a b c => env a b (.there c)))

def toFlatView {Player : Type} [DecidableEq Player] {L : ExprLanguage} (p : Player)
    {Γ : Ctx Player L} (env : Env (Player := Player) L Γ) :
    Env (Player := Player) L (flattenCtx (viewCtx p Γ)) :=
  Env.toFlat (Env.toView p env)

end Env

/-- Visibility-aware expression interface for Vegas-style syntax layers. -/
class ExprKit (Player : Type) (L : ExprLanguage) where
  Expr : Ctx Player L → L.Ty → Type
  eval : {Γ : Ctx Player L} → {τ : L.Ty} →
    Expr Γ τ → Env (Player := Player) L Γ → L.Val τ
  deps : {Γ : Ctx Player L} → {τ : L.Ty} → Expr Γ τ → List VarId

/-- Visibility-aware finite-support distribution interface. -/
class DistKit (Player : Type) (L : ExprLanguage) where
  DistExpr : Ctx Player L → L.Ty → Type
  eval : {Γ : Ctx Player L} → {τ : L.Ty} →
    DistExpr Γ τ → Env (Player := Player) L Γ → FDist (L.Val τ)
  deps : {Γ : Ctx Player L} → {τ : L.Ty} → DistExpr Γ τ → List VarId

/-- Canonical outcome type: finitely-supported integer payoffs per player.
    Derived from the protocol's `ret` constructor rather than parameterized. -/
abbrev Outcome (Player : Type) [DecidableEq Player] := Player →₀ Int

/-- Evaluate a list of per-player payoff expressions into an outcome. -/
noncomputable def evalPayoffs {Player : Type} [DecidableEq Player] {L : ExprLanguage}
    [E : ExprKit Player L] {Γ : Ctx Player L}
    (payoffs : List (Player × E.Expr Γ L.int))
    (env : Env (Player := Player) L Γ) : Outcome Player :=
  payoffs.foldl (fun acc (p, e) => acc + Finsupp.single p (L.toInt (E.eval e env))) 0

/-- Whether a value is sampled publicly by nature, privately by nature, or by
the owning player. -/
inductive SampleMode {Player : Type} {L : ExprLanguage} : BindTy Player L → Type where
  | NaturePub {τ} : SampleMode (.pub τ)
  | NaturePriv {owner τ} : SampleMode (.hidden owner τ)
  | PlayerPriv {owner τ} : SampleMode (.hidden owner τ)

/-- The context exposed to a distribution expression for a given sampling mode. -/
abbrev distCtx {Player : Type} [DecidableEq Player] {L : ExprLanguage}
    (τ : BindTy Player L) (m : SampleMode τ) (Γ : Ctx Player L) : Ctx Player L :=
  match τ, m with
  | .pub _, .NaturePub => pubCtx Γ
  | .hidden _ _, .NaturePriv => pubCtx Γ
  | .hidden p _, .PlayerPriv => flattenCtx (viewCtx p Γ)

namespace Env

/-- Project an environment to the visibility required for sampling in mode `m`. -/
def projectDist {Player : Type} [DecidableEq Player] {L : ExprLanguage} {Γ : Ctx Player L}
    (τ : BindTy Player L) (m : SampleMode τ)
    (env : Env (Player := Player) L Γ) :
    Env (Player := Player) L (distCtx τ m Γ) :=
  match τ, m with
  | .pub _, .NaturePub => env.toPub
  | .hidden _ _, .NaturePriv => env.toPub
  | .hidden p _, .PlayerPriv => env.toFlatView p

end Env

/-- Evaluate a commit guard against a proposed action and the committing
player's current view. -/
def evalGuard {Player : Type} [DecidableEq Player] {L : ExprLanguage}
    (E : ExprKit Player L) {Γ : Ctx Player L} {b : L.Ty}
    {who : Player} {x : VarId}
    (R : E.Expr ((x, .pub b) :: flattenCtx (viewCtx who Γ)) L.bool)
    (a : L.Val b) (view : Env (Player := Player) L (viewCtx who Γ)) : Bool :=
  L.toBool (E.eval R (Env.cons (Player := Player) (L := L) (x := x) (τ := .pub b) a view.toFlat))

/- Generic Vegas-style protocol syntax over a visibility-aware expression
language. -/
inductive VegasCore (Player : Type) [DecidableEq Player] (L : ExprLanguage)
    [E : ExprKit Player L] [D : DistKit Player L] :
    Ctx Player L → Type where
  | ret (payoffs : List (Player × E.Expr Γ L.int)) : VegasCore Player L Γ
  | letExpr (x : VarId) {b : L.Ty} (e : E.Expr Γ b)
      (k : VegasCore Player L ((x, .pub b) :: Γ)) :
      VegasCore Player L Γ
  | sample (x : VarId) (τ : BindTy Player L) (m : SampleMode τ)
      (D' : D.DistExpr (distCtx τ m Γ) τ.base)
      (k : VegasCore Player L ((x, τ) :: Γ)) :
      VegasCore Player L Γ
  | commit (x : VarId) (who : Player) {b : L.Ty}
      (acts : List (L.Val b))
      (R : E.Expr ((x, .pub b) :: flattenCtx (viewCtx who Γ)) L.bool)
      (k : VegasCore Player L ((x, .hidden who b) :: Γ)) :
      VegasCore Player L Γ
  | reveal (y : VarId) (who : Player) (x : VarId) {b : L.Ty}
      (hx : HasVar (L := L) Γ x (.hidden who b))
      (k : VegasCore Player L ((y, .pub b) :: Γ)) :
      VegasCore Player L Γ

/-- Generic commit kernels indexed by a player view. -/
abbrev CommitKernel (Player : Type) [DecidableEq Player] (L : ExprLanguage)
    (who : Player) (Γ : Ctx Player L) (b : L.Ty) : Type :=
  Env (Player := Player) L (viewCtx who Γ) → FDist (L.Val b)

/-- Generic profiles for Vegas-style commit nodes. -/
structure Profile (Player : Type) [DecidableEq Player] (L : ExprLanguage)
    [E : ExprKit Player L] [D : DistKit Player L] where
  commit : {Γ : Ctx Player L} → {b : L.Ty} → (who : Player) →
    (x : VarId) → (acts : List (L.Val b)) →
    (R : E.Expr ((x, .pub b) :: flattenCtx (viewCtx who Γ)) L.bool) →
    CommitKernel Player L who Γ b

/-- Partial generic profiles with optional commit kernels. -/
structure PProfile (Player : Type) [DecidableEq Player] (L : ExprLanguage)
    [E : ExprKit Player L] [D : DistKit Player L] where
  commit? : {Γ : Ctx Player L} → {b : L.Ty} → (who : Player) →
    (x : VarId) → (acts : List (L.Val b)) →
    (R : E.Expr ((x, .pub b) :: flattenCtx (viewCtx who Γ)) L.bool) →
    Option (CommitKernel Player L who Γ b)

def PProfile.toProfile {Player : Type} [DecidableEq Player] {L : ExprLanguage}
    [E : ExprKit Player L] [D : DistKit Player L]
    (π : PProfile Player L) (fallback : Profile Player L) :
    Profile Player L where
  commit := fun {Γ} {b} who x acts R view =>
    match π.commit? (Γ := Γ) (b := b) who x acts R with
    | some k => k view
    | none => fallback.commit who x acts R view

/-- Extra assumptions needed only for finite-backend compilation. -/
structure FiniteValuation (L : ExprLanguage) where
  fintypeVal : ∀ τ : L.Ty, Fintype (L.Val τ)

namespace FiniteValuation

instance instFintypeVal (L : ExprLanguage) (LF : FiniteValuation L) (τ : L.Ty) :
    Fintype (L.Val τ) :=
  LF.fintypeVal τ

/-- The finite branching factor of values of type `τ`. -/
noncomputable def domainSize (L : ExprLanguage) (LF : FiniteValuation L) (τ : L.Ty) : Nat :=
  let _ := instFintypeVal L LF τ
  Fintype.card (L.Val τ)

/-- A canonical encoding of values as `Fin domainSize`. -/
noncomputable def encodeFin (L : ExprLanguage) (LF : FiniteValuation L) (τ : L.Ty) :
    L.Val τ ≃ Fin (LF.domainSize L τ) :=
  let _ := instFintypeVal L LF τ
  Fintype.equivFin (L.Val τ)

end FiniteValuation

/-- Backend-facing expression interface: evaluation and dependency extraction. -/
structure IExprKit (L : ExprLanguage) where
  Expr : L.CtxSimple → L.Ty → Type
  eval : {Γ : L.CtxSimple} → {τ : L.Ty} → Expr Γ τ → L.EnvSimple Γ → L.Val τ
  deps : {Γ : L.CtxSimple} → {τ : L.Ty} → Expr Γ τ → List (Sigma fun τ => L.Var Γ τ)

/-- Backend-facing sampling interface: finite-support distributions and deps. -/
structure IDistKit (L : ExprLanguage) where
  DistExpr : L.CtxSimple → L.Ty → Type
  eval : {Γ : L.CtxSimple} → {τ : L.Ty} → DistExpr Γ τ → L.EnvSimple Γ → PMF (L.Val τ)
  deps : {Γ : L.CtxSimple} → {τ : L.Ty} → DistExpr Γ τ → List (Sigma fun τ => L.Var Γ τ)

end Vegas
