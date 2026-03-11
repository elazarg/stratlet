import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Backend language boundary

This file records the minimal semantic interface that the distilled Vegas
development should depend on.

Design:

- `Language` is the core PL interface.
- finiteness is not part of the language identity.
- backend compilation to finite game models can add `FiniteValuation`
  assumptions only where needed.

This boundary is a target for refactoring `distilled.Vegas`; it does not yet
replace the current hard-coded syntax and semantics.
-/

namespace Distilled

/-- A de Bruijn-style context for a backend expression language. -/
abbrev Ctx (Ty : Type) := List Ty

/-- Variables in a typed context. -/
inductive Var {Ty : Type} : Ctx Ty → Ty → Type where
  | vz : Var (τ :: Γ) τ
  | vs : Var Γ τ → Var (τ' :: Γ) τ

/-- Environments for a backend expression language. -/
def Env {Ty : Type} (Val : Ty → Type) : Ctx Ty → Type
  | [] => PUnit
  | τ :: Γ => Val τ × Env Val Γ

namespace Env

def get {Ty : Type} {Val : Ty → Type} :
    {Γ : Ctx Ty} → {τ : Ty} → Env Val Γ → @Var Ty Γ τ → Val τ
  | _ :: _, _, env, .vz => env.1
  | _ :: _, _, env, .vs x => get env.2 x

end Env

/-- Core PL interface for the Vegas layer. -/
structure Language where
  Ty : Type
  decEqTy : DecidableEq Ty
  Val : Ty → Type
  decEqVal : ∀ {τ : Ty}, DecidableEq (Val τ)
  bool : Ty

attribute [instance] Language.decEqTy Language.decEqVal

namespace Language

abbrev Ctx (L : Language) : Type := Distilled.Ctx L.Ty
abbrev Var (L : Language) (Γ : L.Ctx) (τ : L.Ty) : Type := @Distilled.Var L.Ty Γ τ
abbrev Env (L : Language) (Γ : L.Ctx) : Type := Distilled.Env L.Val Γ

end Language

/-- Variable identifiers for visibility-tagged Vegas contexts. -/
abbrev VarId : Type := Nat

/-- Visibility-aware binding types over an abstract language. -/
inductive VisBindTy (Player : Type) (L : Language) where
  | pub (τ : L.Ty)
  | hidden (owner : Player) (τ : L.Ty)

instance {Player : Type} [DecidableEq Player] {L : Language} :
    DecidableEq (VisBindTy Player L)
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

namespace VisBindTy

def base {Player : Type} {L : Language} : VisBindTy Player L → L.Ty
  | .pub τ => τ
  | .hidden _ τ => τ

end VisBindTy

/-- Visibility-tagged contexts indexed by variable identifiers. -/
abbrev VisCtx (Player : Type) (L : Language) : Type :=
  List (VarId × VisBindTy Player L)

/-- Typed membership in a visibility-tagged context. -/
inductive VisHasVar {Player : Type} {L : Language} :
    VisCtx Player L → VarId → VisBindTy Player L → Type where
  | here {Γ x τ} : VisHasVar ((x, τ) :: Γ) x τ
  | there {Γ x y τ τ'} : VisHasVar Γ x τ → VisHasVar ((y, τ') :: Γ) x τ

/-- Runtime environments for visibility-tagged contexts. -/
def VisEnv {Player : Type} (L : Language) : VisCtx Player L → Type :=
  fun Γ => ∀ x τ, VisHasVar (L := L) Γ x τ → L.Val τ.base

namespace VisEnv

def empty {Player : Type} (L : Language) : VisEnv (Player := Player) L [] := fun _ _ h => nomatch h

def cons {Player : Type} {L : Language} {Γ : VisCtx Player L} {x : VarId}
    {τ : VisBindTy Player L}
    (v : L.Val τ.base) (env : VisEnv (Player := Player) L Γ) :
    VisEnv (Player := Player) L ((x, τ) :: Γ) :=
  fun _ _ h =>
    match h with
    | .here => v
    | .there h' => env _ _ h'

def get {Player : Type} {L : Language} {Γ : VisCtx Player L} {x : VarId}
    {τ : VisBindTy Player L}
    (env : VisEnv (Player := Player) L Γ) (h : VisHasVar (L := L) Γ x τ) :
    L.Val τ.base :=
  env x τ h

@[simp] theorem cons_get_here {Player : Type} {L : Language} {Γ : VisCtx Player L}
    {x : VarId} {τ : VisBindTy Player L} {v : L.Val τ.base}
    {env : VisEnv (Player := Player) L Γ} :
    (VisEnv.cons v env).get (VisHasVar.here (Γ := Γ) (x := x) (τ := τ)) = v := rfl

@[simp] theorem cons_get_there {Player : Type} {L : Language} {Γ : VisCtx Player L}
    {x y : VarId} {τ σ : VisBindTy Player L}
    {v : L.Val τ.base} {env : VisEnv (Player := Player) L Γ}
    {h : VisHasVar (L := L) Γ y σ} :
    (VisEnv.cons (x := x) v env).get (VisHasVar.there h) = env.get h := rfl

end VisEnv

/-- Public observability predicate. -/
def canSee {Player : Type} [DecidableEq Player] {L : Language}
    (p : Player) : VisBindTy Player L → Bool
  | .pub _ => true
  | .hidden q _ => decide (p = q)

/-- Player-local visible subcontext. -/
def viewCtx {Player : Type} [DecidableEq Player] {L : Language}
    (p : Player) : VisCtx Player L → VisCtx Player L
  | [] => []
  | (x, τ) :: Γ =>
      if canSee p τ then (x, τ) :: viewCtx p Γ else viewCtx p Γ

namespace VisHasVar

def ofViewCtx {Player : Type} [DecidableEq Player] {L : Language} {p : Player}
    {Γ : VisCtx Player L} {x : VarId} {τ : VisBindTy Player L} :
    VisHasVar (L := L) (viewCtx p Γ) x τ → VisHasVar (L := L) Γ x τ := by
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

end VisHasVar

/-- Public-only fragment of a visibility context. -/
def pubCtx {Player : Type} {L : Language} : VisCtx Player L → VisCtx Player L
  | [] => []
  | (x, .pub τ) :: Γ => (x, .pub τ) :: pubCtx Γ
  | (_, .hidden _ _) :: Γ => pubCtx Γ

namespace VisHasVar

def ofPubCtx {Player : Type} {L : Language}
    {Γ : VisCtx Player L} {x : VarId} {τ : VisBindTy Player L} :
    VisHasVar (L := L) (pubCtx Γ) x τ → VisHasVar (L := L) Γ x τ := by
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

def ofPubToView {Player : Type} [DecidableEq Player] {L : Language} {p : Player}
    {Γ : VisCtx Player L} {x : VarId} {τ : VisBindTy Player L} :
    VisHasVar (L := L) (pubCtx Γ) x τ → VisHasVar (L := L) (viewCtx p Γ) x τ := by
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

end VisHasVar

/-- Flatten a visibility context to a public context with the same variables. -/
def flattenCtx {Player : Type} {L : Language} : VisCtx Player L → VisCtx Player L
  | [] => []
  | (x, τ) :: Γ => (x, .pub τ.base) :: flattenCtx Γ

@[simp] theorem flattenCtx_nil {Player : Type} {L : Language} :
    flattenCtx (Player := Player) (L := L) [] = [] := rfl

@[simp] theorem flattenCtx_cons {Player : Type} {L : Language}
    {x : VarId} {τ : VisBindTy Player L} {Γ : VisCtx Player L} :
    flattenCtx ((x, τ) :: Γ) = (x, .pub τ.base) :: flattenCtx Γ := rfl

theorem flattenCtx_map_fst {Player : Type} {L : Language} {Γ : VisCtx Player L} :
    (flattenCtx Γ).map Prod.fst = Γ.map Prod.fst := by
  induction Γ with
  | nil => rfl
  | cons hd tl ih => simp [flattenCtx, ih]

theorem flattenCtx_length {Player : Type} {L : Language} {Γ : VisCtx Player L} :
    (flattenCtx Γ).length = Γ.length := by
  have h := congrArg List.length (flattenCtx_map_fst (Γ := Γ))
  simp only [List.length_map] at h
  exact h

theorem flattenCtx_idempotent {Player : Type} {L : Language} {Γ : VisCtx Player L} :
    flattenCtx (flattenCtx Γ) = flattenCtx Γ := by
  induction Γ with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨x, τ⟩ := hd
    simp [flattenCtx, VisBindTy.base, ih]

/-- Erase variable ids and visibility, keeping only backend value types. -/
def eraseCtx {Player : Type} {L : Language} : VisCtx Player L → L.Ctx
  | [] => []
  | (_, τ) :: Γ => τ.base :: eraseCtx Γ

namespace VisHasVar

def toFlatten {Player : Type} {L : Language}
    {Γ : VisCtx Player L} {x : VarId} {τ : VisBindTy Player L} :
    VisHasVar (L := L) Γ x τ → VisHasVar (L := L) (flattenCtx Γ) x (.pub τ.base)
  | .here => .here
  | .there h => .there h.toFlatten

def unflatten {Player : Type} {L : Language} {Γ : VisCtx Player L} {x : VarId} {τ : L.Ty} :
    VisHasVar (L := L) (flattenCtx Γ) x (.pub τ) →
    (σ : VisBindTy Player L) × VisHasVar (L := L) Γ x σ × PLift (σ.base = τ) :=
  match Γ with
  | [] => fun h => nomatch h
  | (_, σ) :: _ => fun h =>
    match h with
    | .here => ⟨σ, .here, ⟨rfl⟩⟩
    | .there h' =>
      let ⟨σ', hv, ⟨hτ⟩⟩ := unflatten h'
      ⟨σ', .there hv, ⟨hτ⟩⟩

end VisHasVar

namespace VisEnv

def toView {Player : Type} [DecidableEq Player] {L : Language} (p : Player)
    {Γ : VisCtx Player L} (env : VisEnv (Player := Player) L Γ) :
    VisEnv (Player := Player) L (viewCtx p Γ) :=
  fun x τ h => env x τ h.ofViewCtx

def toPub {Player : Type} {L : Language} {Γ : VisCtx Player L}
    (env : VisEnv (Player := Player) L Γ) :
    VisEnv (Player := Player) L (pubCtx Γ) :=
  fun x τ h => env x τ h.ofPubCtx

def toFlat {Player : Type} {L : Language} {Γ : VisCtx Player L}
    (env : VisEnv (Player := Player) L Γ) :
    VisEnv (Player := Player) L (flattenCtx Γ) := by
  induction Γ with
  | nil => exact VisEnv.empty L
  | cons hd tl ih =>
    obtain ⟨_, σ⟩ := hd
    let v : L.Val σ.base := env.get .here
    exact VisEnv.cons (L := L) (τ := .pub σ.base) v
      (ih (fun a b c => env a b (.there c)))

def toFlatView {Player : Type} [DecidableEq Player] {L : Language} (p : Player)
    {Γ : VisCtx Player L} (env : VisEnv (Player := Player) L Γ) :
    VisEnv (Player := Player) L (flattenCtx (viewCtx p Γ)) :=
  VisEnv.toFlat (VisEnv.toView p env)

end VisEnv

/-- Extra assumptions needed only for finite-backend compilation. -/
structure FiniteValuation (L : Language) where
  fintypeVal : ∀ τ : L.Ty, Fintype (L.Val τ)

namespace FiniteValuation

instance instFintypeVal (L : Language) (LF : FiniteValuation L) (τ : L.Ty) :
    Fintype (L.Val τ) :=
  LF.fintypeVal τ

/-- The finite branching factor of values of type `τ`. -/
noncomputable def domainSize (L : Language) (LF : FiniteValuation L) (τ : L.Ty) : Nat :=
  let _ := instFintypeVal L LF τ
  Fintype.card (L.Val τ)

/-- A canonical encoding of values as `Fin domainSize`. -/
noncomputable def encodeFin (L : Language) (LF : FiniteValuation L) (τ : L.Ty) :
    L.Val τ ≃ Fin (LF.domainSize L τ) :=
  let _ := instFintypeVal L LF τ
  Fintype.equivFin (L.Val τ)

end FiniteValuation

/-- Backend-facing expression interface: evaluation and dependency extraction. -/
structure ExprKit (L : Language) where
  Expr : L.Ctx → L.Ty → Type
  eval : {Γ : L.Ctx} → {τ : L.Ty} → Expr Γ τ → L.Env Γ → L.Val τ
  deps : {Γ : L.Ctx} → {τ : L.Ty} → Expr Γ τ → List (Sigma fun τ => L.Var Γ τ)

/-- Backend-facing sampling interface: finite-support distributions and deps. -/
structure DistKit (L : Language) where
  DistExpr : L.Ctx → L.Ty → Type
  eval : {Γ : L.Ctx} → {τ : L.Ty} → DistExpr Γ τ → L.Env Γ → PMF (L.Val τ)
  deps : {Γ : L.Ctx} → {τ : L.Ty} → DistExpr Γ τ → List (Sigma fun τ => L.Var Γ τ)

/-- Backend-facing payoff interface. Utility outputs need not lie in a finite
value domain. -/
structure PayoffKit (L : Language) where
  Player : Type
  decEqPlayer : DecidableEq Player
  PayoffExpr : L.Ctx → Type
  eval : {Γ : L.Ctx} → PayoffExpr Γ → L.Env Γ → Player → Int
  deps : {Γ : L.Ctx} → PayoffExpr Γ → List (Sigma fun τ => L.Var Γ τ)

attribute [instance] PayoffKit.decEqPlayer

end Distilled
