import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Rat.Defs
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNRat.Order
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Basic

/-!
# Vegas: A Typed Game Calculus

Implements the distilled Vegas calculus with commit/reveal, visibility-tagged
contexts, SSA named variables, and denotational semantics.

## Key design decisions
- **Weight type**: `ℚ≥0` — computable, exact, non-negative, closed under `+`/`*`.
- **Distribution**: `FDist α := α →₀ ℚ≥0` — canonical Mathlib type with proper equality.
- **Outcome**: `Player →₀ Int` — `DecidableEq`, finite support, default 0.
- **Syntax**: All constructors use syntactic `Expr`/`DistExpr`, not opaque functions.
- **SSA**: Enforced by `WF` predicate requiring `Fresh x Γ` at each binding site.
- **Normalization**: Tracked by predicates, not baked into types.
-/

-- ============================================================================
-- § 1. Base types and identifiers
-- ============================================================================

abbrev VarId : Type := Nat
abbrev Player : Type := Nat

inductive BaseTy where
  | int : BaseTy
  | bool : BaseTy
deriving Repr, DecidableEq

abbrev Val : BaseTy → Type
  | .int => Int
  | .bool => Bool

instance : DecidableEq (Val b) := match b with
  | .int => inferInstanceAs (DecidableEq Int)
  | .bool => inferInstanceAs (DecidableEq Bool)

inductive BindTy where
  | pub (b : BaseTy)
  | hidden (owner : Player) (b : BaseTy)
deriving DecidableEq

def BindTy.base : BindTy → BaseTy
  | .pub b => b
  | .hidden _ b => b

abbrev Ctx : Type := List (VarId × BindTy)

-- ============================================================================
-- § 2. HasVar and Env
-- ============================================================================

inductive HasVar : Ctx → VarId → BindTy → Type where
  | here {Γ x τ} : HasVar ((x, τ) :: Γ) x τ
  | there {Γ x y τ τ'} (h : HasVar Γ x τ) : HasVar ((y, τ') :: Γ) x τ

def Env (Γ : Ctx) := ∀ x τ, HasVar Γ x τ → Val τ.base

namespace Env

def empty : Env [] := fun _ _ h => nomatch h

def cons {Γ : Ctx} {x : VarId} {τ : BindTy}
    (v : Val τ.base) (env : Env Γ) : Env ((x, τ) :: Γ) :=
  fun _ _ h =>
    match h with
    | .here => v
    | .there h' => env _ _ h'

def get {Γ : Ctx} {x : VarId} {τ : BindTy}
    (env : Env Γ) (h : HasVar Γ x τ) : Val τ.base :=
  env x τ h

@[simp] theorem cons_get_here {Γ : Ctx} {x : VarId} {τ : BindTy}
    {v : Val τ.base} {env : Env Γ} :
    (Env.cons v env).get (HasVar.here (Γ := Γ) (x := x) (τ := τ)) = v := rfl

@[simp] theorem cons_get_there {Γ : Ctx} {x y : VarId} {τ σ : BindTy}
    {v : Val τ.base} {env : Env Γ} {h : HasVar Γ y σ} :
    (Env.cons (x := x) v env).get (HasVar.there h) = env.get h := rfl

end Env

-- ============================================================================
-- § 3. Views and projections
-- ============================================================================

def canSee (p : Player) : BindTy → Bool
  | .pub _ => true
  | .hidden q _ => p == q

def viewCtx (p : Player) : Ctx → Ctx
  | [] => []
  | (x, τ) :: Γ =>
    if canSee p τ then (x, τ) :: viewCtx p Γ
    else viewCtx p Γ

def HasVar.ofViewCtx {p : Player} :
    HasVar (viewCtx p Γ) x τ → HasVar Γ x τ := by
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
    · intro h; exact .there (ih h)

def pubCtx : Ctx → Ctx
  | [] => []
  | (x, τ) :: Γ =>
    match τ with
    | .pub _ => (x, τ) :: pubCtx Γ
    | .hidden _ _ => pubCtx Γ

def HasVar.ofPubCtx : HasVar (pubCtx Γ) x τ → HasVar Γ x τ := by
  induction Γ with
  | nil => intro h; exact nomatch h
  | cons hd tl ih =>
    obtain ⟨y, σ⟩ := hd
    simp only [pubCtx]
    split
    · intro h
      match h with
      | .here => exact .here
      | .there h' => exact .there (ih h')
    · intro h; exact .there (ih h)

def HasVar.ofPubToView {p : Player} :
    HasVar (pubCtx Γ) x τ → HasVar (viewCtx p Γ) x τ := by
  induction Γ with
  | nil => intro h; exact nomatch h
  | cons hd tl ih =>
    obtain ⟨y, σ⟩ := hd
    intro h
    match σ with
    | .pub b =>
      simp only [pubCtx] at h
      simp only [viewCtx, canSee]
      match h with
      | .here => exact .here
      | .there h' => exact .there (ih h')
    | .hidden q b =>
      simp only [pubCtx] at h
      simp only [viewCtx]
      split
      · exact .there (ih h)
      · exact ih h

def Env.toView (p : Player) (env : Env Γ) : Env (viewCtx p Γ) :=
  fun x τ h => env x τ h.ofViewCtx

def Env.toPub (env : Env Γ) : Env (pubCtx Γ) :=
  fun x τ h => env x τ h.ofPubCtx

-- § 3a. flattenCtx

def flattenCtx : Ctx → Ctx
  | [] => []
  | (x, τ) :: Γ => (x, .pub τ.base) :: flattenCtx Γ

@[simp] theorem flattenCtx_nil : flattenCtx [] = [] := rfl
@[simp] theorem flattenCtx_cons {x : VarId} {τ : BindTy} {Γ : Ctx} :
    flattenCtx ((x, τ) :: Γ) = (x, .pub τ.base) :: flattenCtx Γ := rfl

theorem flattenCtx_map_fst :
    (flattenCtx Γ).map Prod.fst = Γ.map Prod.fst := by
  induction Γ with
  | nil => rfl
  | cons hd tl ih => simp [flattenCtx, ih]

theorem flattenCtx_length :
    (flattenCtx Γ).length = Γ.length := by
  have h := congrArg List.length (flattenCtx_map_fst (Γ := Γ))
  simp only [List.length_map] at h
  exact h

theorem flattenCtx_idempotent :
    flattenCtx (flattenCtx Γ) = flattenCtx Γ := by
  induction Γ with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨x, τ⟩ := hd
    simp [flattenCtx, BindTy.base, ih]

-- § 3b. HasVar embeddings for flattenCtx

def HasVar.toFlatten : HasVar Γ x τ → HasVar (flattenCtx Γ) x (.pub τ.base)
  | .here => .here
  | .there h => .there h.toFlatten

def HasVar.unflatten {Γ : Ctx} {x : VarId} {b : BaseTy} :
    HasVar (flattenCtx Γ) x (.pub b) →
    (τ : BindTy) × HasVar Γ x τ × PLift (τ.base = b) :=
  match Γ with
  | [] => fun h => nomatch h
  | (_, σ) :: _ => fun h =>
    match h with
    | .here => ⟨σ, .here, ⟨rfl⟩⟩
    | .there h' =>
      let ⟨τ, hv, ⟨hb⟩⟩ := unflatten h'
      ⟨τ, .there hv, ⟨hb⟩⟩

-- § 3c. Env projections for flattenCtx

def Env.toFlat {Γ : Ctx} (env : Env Γ) : Env (flattenCtx Γ) := by
  induction Γ with
  | nil => exact Env.empty
  | cons hd tl ih =>
    obtain ⟨_, σ⟩ := hd
    let v : Val σ.base := env.get .here
    exact Env.cons (τ := .pub σ.base) v
      (ih (fun a b c => env a b (.there c)))

def Env.toFlatView (p : Player) {Γ : Ctx} (env : Env Γ) :
    Env (flattenCtx (viewCtx p Γ)) :=
  (env.toView p).toFlat

-- ============================================================================
-- § 4. Expressions
-- ============================================================================

inductive Expr : Ctx → BaseTy → Type where
  | var (x : VarId) (h : HasVar Γ x (.pub b)) : Expr Γ b
  | constInt (i : Int) : Expr Γ .int
  | constBool (b : Bool) : Expr Γ .bool
  | addInt (l r : Expr Γ .int) : Expr Γ .int
  | eqInt (l r : Expr Γ .int) : Expr Γ .bool
  | eqBool (l r : Expr Γ .bool) : Expr Γ .bool
  | andBool (l r : Expr Γ .bool) : Expr Γ .bool
  | notBool (e : Expr Γ .bool) : Expr Γ .bool
  | ite (c : Expr Γ .bool) (t f : Expr Γ b) : Expr Γ b

def evalExpr : Expr Γ b → Env Γ → Val b
  | .var _ h, env => env.get h
  | .constInt i, _ => i
  | .constBool b, _ => b
  | .addInt l r, env => evalExpr l env + evalExpr r env
  | .eqInt l r, env => decide (evalExpr l env = evalExpr r env)
  | .eqBool l r, env => decide (evalExpr l env = evalExpr r env)
  | .andBool l r, env => evalExpr l env && evalExpr r env
  | .notBool e, env => !(evalExpr e env)
  | .ite c t f, env => if evalExpr c env then evalExpr t env else evalExpr f env

def Expr.weaken {Γ : Ctx} {b : BaseTy} {x : VarId} {τ : BindTy}
    (e : Expr Γ b) : Expr ((x, τ) :: Γ) b :=
  match e with
  | .var y h => .var y (.there h)
  | .constInt i => .constInt i
  | .constBool v => .constBool v
  | .addInt l r => .addInt l.weaken r.weaken
  | .eqInt l r => .eqInt l.weaken r.weaken
  | .eqBool l r => .eqBool l.weaken r.weaken
  | .andBool l r => .andBool l.weaken r.weaken
  | .notBool e => .notBool e.weaken
  | .ite c t f => .ite c.weaken t.weaken f.weaken

theorem evalExpr_weaken {Γ : Ctx} {b : BaseTy} {τ : BindTy} {x : VarId}
    (e : Expr Γ b) (v : Val τ.base) (env : Env Γ) :
    evalExpr e.weaken (Env.cons (x := x) v env) = evalExpr e env := by
  induction e with
  | var _ _ => rfl
  | constInt _ => rfl
  | constBool _ => rfl
  | addInt l r ihl ihr => simp [Expr.weaken, evalExpr, ihl, ihr]
  | eqInt l r ihl ihr => simp [Expr.weaken, evalExpr, ihl, ihr]
  | eqBool l r ihl ihr => simp [Expr.weaken, evalExpr, ihl, ihr]
  | andBool l r ihl ihr => simp [Expr.weaken, evalExpr, ihl, ihr]
  | notBool e ih => simp [Expr.weaken, evalExpr, ih]
  | ite c t f ihc iht ihf => simp [Expr.weaken, evalExpr, ihc, iht, ihf]

/-- Extract variable IDs referenced by an Expr. -/
def exprVars : Expr Γ b → List VarId
  | .var x _     => [x]
  | .constInt _  => []
  | .constBool _ => []
  | .addInt l r  => exprVars l ++ exprVars r
  | .eqInt l r   => exprVars l ++ exprVars r
  | .eqBool l r  => exprVars l ++ exprVars r
  | .andBool l r => exprVars l ++ exprVars r
  | .notBool e   => exprVars e
  | .ite c t f   => exprVars c ++ exprVars t ++ exprVars f

-- ============================================================================
-- § 5. FDist — Finsupp-based weighted distributions
-- ============================================================================

abbrev FDist (α : Type) [DecidableEq α] := α →₀ ℚ≥0

namespace FDist

variable {α : Type} {β : Type} [DecidableEq α] [DecidableEq β]

noncomputable def pure (x : α) : FDist α := Finsupp.single x 1
noncomputable def zero : FDist α := 0

noncomputable def bind (d : FDist α) (f : α → FDist β) : FDist β :=
  d.sum fun a w => (f a).mapRange (w * ·) (mul_zero w)

noncomputable def map (g : α → β) (d : FDist α) : FDist β :=
  d.sum (fun a w => Finsupp.single (g a) w)

noncomputable def totalWeight (d : FDist α) : ℚ≥0 := d.sum (fun _ w => w)

noncomputable def ofList (entries : List (α × ℚ≥0)) : FDist α :=
  entries.foldl (fun acc (a, w) => acc + Finsupp.single a w) 0

def Supported (d : FDist α) (P : α → Prop) : Prop := ∀ a ∈ d.support, P a

-- § 5a. FDist lemmas

@[simp] theorem totalWeight_pure (x : α) : (FDist.pure x).totalWeight = 1 := by
  simp [totalWeight, FDist.pure, Finsupp.sum_single_index]

@[simp] theorem support_pure (x : α) : (FDist.pure x).support = {x} :=
  Finsupp.support_single_ne_zero _ one_ne_zero

@[simp] theorem support_zero : (FDist.zero : FDist α).support = ∅ :=
  Finsupp.support_zero

@[simp] theorem Supported_pure {P : α → Prop} (x : α) :
    (FDist.pure x).Supported P ↔ P x := by
  simp [Supported, FDist.pure, Finsupp.support_single_ne_zero _ (one_ne_zero)]

theorem Supported_zero (P : α → Prop) : (FDist.zero : FDist α).Supported P := by
  simp [Supported, FDist.zero]

theorem pure_bind (x : α) (f : α → FDist β) : (FDist.pure x).bind f = f x := by
  simp only [FDist.pure, bind]
  rw [Finsupp.sum_single_index]
  · ext a; simp [Finsupp.mapRange_apply]
  · ext a; simp [Finsupp.mapRange_apply]

theorem bind_pure (d : FDist α) : d.bind FDist.pure = d := by
  simp only [bind, FDist.pure]
  simp_rw [Finsupp.mapRange_single, mul_one]
  exact d.sum_single

theorem bind_zero_left (f : α → FDist β) :
    (FDist.zero : FDist α).bind f = FDist.zero := by
  simp [bind, FDist.zero, Finsupp.sum_zero_index]

@[simp] theorem ofList_nil : (FDist.ofList (α := α) []) = FDist.zero := rfl

theorem ofList_cons (a : α) (w : ℚ≥0) (rest : List (α × ℚ≥0)) :
    FDist.ofList ((a, w) :: rest) = Finsupp.single a w + FDist.ofList rest := by
  simp only [ofList, List.foldl_cons, zero_add]
  suffices ∀ (init : FDist α) (l : List (α × ℚ≥0)),
      l.foldl (fun acc (p : α × ℚ≥0) => acc + Finsupp.single p.1 p.2) init =
      init + l.foldl (fun acc (p : α × ℚ≥0) => acc + Finsupp.single p.1 p.2) 0 by
    exact this _ _
  intro init l
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, zero_add]
    rw [ih, ih (Finsupp.single hd.1 hd.2), add_assoc]

/-- Pointwise evaluation of `bind`. -/
theorem bind_apply (d : FDist α) (f : α → FDist β) (b : β) :
    (d.bind f) b = d.support.sum (fun a => d a * (f a) b) := by
  simp only [bind, Finsupp.sum, Finsupp.finset_sum_apply, Finsupp.mapRange_apply]

/-- Support characterization for `bind`: `b` is in the support of `d.bind f`
    iff there exists some `a` in `d`'s support with `b` in `(f a)`'s support. -/
theorem mem_support_bind {d : FDist α} {f : α → FDist β} {b : β} :
    b ∈ (d.bind f).support ↔ ∃ a ∈ d.support, b ∈ (f a).support := by
  rw [Finsupp.mem_support_iff, bind_apply]
  constructor
  · intro h
    by_contra hall
    push_neg at hall
    apply h
    apply Finset.sum_eq_zero
    intro a ha
    have hfab : (f a) b = 0 := by
      by_contra hne
      exact hall a ha (Finsupp.mem_support_iff.mpr hne)
    rw [hfab, mul_zero]
  · rintro ⟨a, ha, hb⟩
    intro heq
    have hsplit := Finset.add_sum_erase d.support
      (fun a => d a * (f a) b) ha
    rw [heq] at hsplit
    -- hsplit : d a * (f a) b + rest = 0
    -- In ℚ≥0, le_self_add gives: d a * (f a) b ≤ d a * (f a) b + rest
    have hle : d a * (f a) b ≤ 0 := hsplit ▸ le_self_add
    -- 0 ≤ d a * (f a) b from le_self_add with a := 0
    have hge : 0 ≤ d a * (f a) b := zero_add (d a * (f a) b) ▸ le_self_add
    exact mul_ne_zero (Finsupp.mem_support_iff.mp ha)
      (Finsupp.mem_support_iff.mp hb) (le_antisymm hle hge)

@[simp] theorem mem_support_pure {a b : α} :
    b ∈ (FDist.pure a).support ↔ b = a := by
  rw [support_pure, Finset.mem_singleton]

theorem totalWeight_bind (d : FDist α) (f : α → FDist β) :
    (d.bind f).totalWeight = d.support.sum (fun a => d a * (f a).totalWeight) := by
  unfold totalWeight bind
  rw [Finsupp.sum_sum_index (fun _ => rfl) (fun _ _ _ => rfl)]
  have hmr : ∀ (a : α) (w : ℚ≥0),
      (Finsupp.mapRange (w * ·) (mul_zero w) (f a)).sum (fun _ x => x) =
      (f a).sum (fun _ b => w * b) :=
    fun _ _ => Finsupp.sum_mapRange_index (fun _ => rfl)
  simp_rw [hmr]
  simp only [Finsupp.sum, Finset.mul_sum]

theorem totalWeight_bind_of_normalized {d : FDist α} {f : α → FDist β}
    (hd : d.totalWeight = 1) (hf : ∀ a ∈ d.support, (f a).totalWeight = 1) :
    (d.bind f).totalWeight = 1 := by
  rw [totalWeight_bind]
  have : d.support.sum (fun a => d a * (f a).totalWeight) = d.support.sum (fun a => d a) := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [hf a ha, mul_one]
  rw [this]
  exact hd

/-- Pointwise evaluation of `map`. -/
theorem map_apply (g : α → β) (d : FDist α) (b : β) :
    (d.map g) b = d.support.sum (fun a => if g a = b then d a else 0) := by
  simp only [map, Finsupp.sum, Finsupp.finset_sum_apply, Finsupp.single_apply]

theorem map_apply_injective (g : α → β) (d : FDist α) (a : α)
    (hinj : Function.Injective g) :
    (d.map g) (g a) = d a := by
  rw [map_apply]
  simp only [hinj.eq_iff]
  rw [Finset.sum_ite_eq' d.support a (fun x => d x)]
  split
  · rfl
  · next h => simp [Finsupp.mem_support_iff] at h; exact h.symm

theorem map_apply_of_forall_ne (g : α → β) (d : FDist α) (b : β)
    (h : ∀ a ∈ d.support, g a ≠ b) :
    (d.map g) b = 0 := by
  rw [map_apply]
  apply Finset.sum_eq_zero
  intro a ha
  simp [h a ha]

theorem map_pure (g : α → β) (a : α) :
    (FDist.pure a).map g = FDist.pure (g a) := by
  simp only [FDist.pure, map]
  rw [Finsupp.sum_single_index (Finsupp.single_zero _)]

theorem map_map {γ : Type} [DecidableEq γ] (f : α → β) (g : β → γ) (d : FDist α) :
    (d.map f).map g = d.map (g ∘ f) := by
  simp only [map]
  rw [Finsupp.sum_sum_index (fun _ => Finsupp.single_zero _)
    (fun _ _ _ => Finsupp.single_add _ _ _)]
  have hz : ∀ b : β, (fun x : ℚ≥0 => Finsupp.single (g b) x) 0 = 0 :=
    fun b => Finsupp.single_zero _
  simp_rw [show ∀ b w, (Finsupp.single (f b) w).sum (fun x => Finsupp.single (g x)) =
    Finsupp.single (g (f b)) w from fun b w => Finsupp.sum_single_index (hz (f b))]
  rfl

theorem bind_map (d : FDist α) (f : α → FDist β) {γ : Type} [DecidableEq γ]
    (g : β → γ) :
    (d.bind f).map g = d.bind (fun a => (f a).map g) := by
  simp only [bind, map]
  rw [Finsupp.sum_sum_index (fun _ => Finsupp.single_zero _)
    (fun _ _ _ => Finsupp.single_add _ _ _)]
  congr 1; ext a w
  rw [Finsupp.sum_mapRange_index (fun _ => Finsupp.single_zero _)]
  -- LHS: (f a).sum fun b u => single (g b) (w * u)
  -- RHS: ((f a).sum fun b u => single (g b) u).mapRange (w * ·) ...
  simp only [Finsupp.sum, Finsupp.mapRange_apply, Finsupp.finset_sum_apply,
    Finsupp.single_apply]
  congr 1; rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro b _
  split <;> simp [mul_zero]

end FDist

-- ============================================================================
-- § 6. Outcomes and DistExpr
-- ============================================================================

abbrev Outcome := Player →₀ Int

inductive DistExpr (Γ : Ctx) (b : BaseTy) : Type where
  | weighted (entries : List (Val b × ℚ≥0)) : DistExpr Γ b
  | ite (c : Expr Γ .bool) (t f : DistExpr Γ b) : DistExpr Γ b

noncomputable def evalDistExpr : DistExpr Γ b → Env Γ → FDist (Val b)
  | .weighted entries, _ => FDist.ofList entries
  | .ite c t f, env =>
    if evalExpr c env then evalDistExpr t env else evalDistExpr f env

@[simp] theorem evalDistExpr_weighted {Γ : Ctx} {b : BaseTy}
    (entries : List (Val b × ℚ≥0)) (env : Env Γ) :
    evalDistExpr (.weighted entries) env = FDist.ofList entries := rfl

theorem evalDistExpr_ite_true {Γ : Ctx} {b : BaseTy}
    {c : Expr Γ .bool} {t f : DistExpr Γ b} {env : Env Γ}
    (hc : evalExpr c env = true) :
    evalDistExpr (.ite c t f) env = evalDistExpr t env := by
  simp [evalDistExpr, hc]

theorem evalDistExpr_ite_false {Γ : Ctx} {b : BaseTy}
    {c : Expr Γ .bool} {t f : DistExpr Γ b} {env : Env Γ}
    (hc : evalExpr c env = false) :
    evalDistExpr (.ite c t f) env = evalDistExpr f env := by
  simp [evalDistExpr, hc]

def DistExpr.point (v : Val b) : DistExpr Γ b := .weighted [(v, 1)]

def DistExpr.uniform (vs : List (Val b)) : DistExpr Γ b :=
  let w : ℚ≥0 := 1 / (vs.length : ℚ≥0)
  .weighted (vs.map fun v => (v, w))

/-- Extract variable IDs referenced by a DistExpr. -/
def distExprVars : DistExpr Γ b → List VarId
  | .weighted _ => []
  | .ite c t f => exprVars c ++ distExprVars t ++ distExprVars f

-- ============================================================================
-- § 7. Sampling modes and contexts
-- ============================================================================

inductive SampleMode : BindTy → Type where
  | NaturePub {b} : SampleMode (.pub b)
  | NaturePriv {p b} : SampleMode (.hidden p b)
  | PlayerPriv {p b} : SampleMode (.hidden p b)

abbrev distCtx (τ : BindTy) (m : SampleMode τ) (Γ : Ctx) : Ctx :=
  match τ, m with
  | .pub _, .NaturePub => pubCtx Γ
  | .hidden _ _, .NaturePriv => pubCtx Γ
  | .hidden p _, .PlayerPriv => flattenCtx (viewCtx p Γ)

def Env.projectDist {Γ : Ctx} (τ : BindTy) (m : SampleMode τ)
    (env : Env Γ) : Env (distCtx τ m Γ) :=
  match τ, m with
  | .pub _, .NaturePub => env.toPub
  | .hidden _ _, .NaturePriv => env.toPub
  | .hidden p _, .PlayerPriv => env.toFlatView p

-- ============================================================================
-- § 8. PayoffMap, Prog, Profile
-- ============================================================================

structure PayoffMap (Γ : Ctx) where
  entries : List (Player × Expr Γ .int)
  nodup : (entries.map Prod.fst).Nodup

noncomputable def evalPayoffMap (u : PayoffMap Γ) (env : Env Γ) : Outcome :=
  u.entries.foldl (fun acc (p, e) => acc + Finsupp.single p (evalExpr e env)) 0

def evalR {Γ : Ctx} {b : BaseTy} {who : Player} {x : VarId}
    (R : Expr ((x, .pub b) :: flattenCtx (viewCtx who Γ)) .bool)
    (a : Val b) (view : Env (viewCtx who Γ)) : Bool :=
  evalExpr R (Env.cons (x := x) a view.toFlat)

inductive Prog : Ctx → Type where
  | ret (u : PayoffMap Γ) : Prog Γ
  | letExpr (x : VarId) {b : BaseTy} (e : Expr Γ b)
      (k : Prog ((x, .pub b) :: Γ)) : Prog Γ
  | sample (x : VarId) (τ : BindTy) (m : SampleMode τ)
      (D : DistExpr (distCtx τ m Γ) τ.base)
      (k : Prog ((x, τ) :: Γ)) : Prog Γ
  | commit (x : VarId) (who : Player) {b : BaseTy}
      (acts : List (Val b))
      (R : Expr ((x, .pub b) :: flattenCtx (viewCtx who Γ)) .bool)
      (k : Prog ((x, .hidden who b) :: Γ)) : Prog Γ
  | reveal (y : VarId) (who : Player) (x : VarId) {b : BaseTy}
      (hx : HasVar Γ x (.hidden who b))
      (k : Prog ((y, .pub b) :: Γ)) : Prog Γ

abbrev CommitKernel (who : Player) (Γ : Ctx) (b : BaseTy) : Type :=
  Env (viewCtx who Γ) → FDist (Val b)

structure Profile where
  commit : {Γ : Ctx} → {b : BaseTy} → (who : Player) →
    (x : VarId) → (acts : List (Val b)) →
    (R : Expr ((x, .pub b) :: flattenCtx (viewCtx who Γ)) .bool) →
    CommitKernel who Γ b

-- ============================================================================
-- § 9. Denotational semantics
-- ============================================================================

noncomputable def outcomeDist (σ : Profile) : Prog Γ → Env Γ → FDist Outcome
  | .ret u, env =>
    FDist.pure (evalPayoffMap u env)
  | .letExpr x e k, env =>
    outcomeDist σ k (Env.cons (x := x) (evalExpr e env) env)
  | .sample x τ m D k, env =>
    FDist.bind (evalDistExpr D (env.projectDist τ m)) (fun v =>
      outcomeDist σ k (Env.cons (x := x) v env))
  | .commit x who acts R k, env =>
    FDist.bind (σ.commit who x acts R (env.toView who)) (fun v =>
      outcomeDist σ k (Env.cons (x := x) v env))
  | .reveal y _who _x (b := b) hx k, env =>
    let v : Val b := env.get hx
    outcomeDist σ k (Env.cons (x := y) (τ := .pub b) v env)

-- § 9a. outcomeDist simp lemmas

-- outcomeDist equation lemmas: auto-generated by Lean's equation compiler.
-- Access via `simp [outcomeDist]` or `unfold outcomeDist`.

-- ============================================================================
-- § 10. Partial profiles
-- ============================================================================

structure PProfile where
  commit? : {Γ : Ctx} → {b : BaseTy} → (who : Player) →
    (x : VarId) → (acts : List (Val b)) →
    (R : Expr ((x, .pub b) :: flattenCtx (viewCtx who Γ)) .bool) →
    Option (CommitKernel who Γ b)

def PProfile.toProfile (π : PProfile) (fallback : Profile) : Profile where
  commit := fun {Γ} {b} who x acts R view =>
    match π.commit? (Γ := Γ) (b := b) who x acts R with
    | some k => k view
    | none => fallback.commit who x acts R view

-- ============================================================================
-- § 11. SSA enforcement
-- ============================================================================

def Fresh (x : VarId) (Γ : Ctx) : Prop := x ∉ Γ.map Prod.fst
def WFCtx (Γ : Ctx) : Prop := (Γ.map Prod.fst).Nodup

instance {x : VarId} {Γ : Ctx} : Decidable (Fresh x Γ) :=
  inferInstanceAs (Decidable (x ∉ _))

def WF : Prog Γ → Prop
  | .ret _ => True
  | .letExpr x _ k => Fresh x Γ ∧ WF k
  | .sample x _ _ _ k => Fresh x Γ ∧ WF k
  | .commit x _ _ _ k => Fresh x Γ ∧ WF k
  | .reveal y _ _ _ k => Fresh y Γ ∧ WF k

-- § 11a. Context lemmas

@[simp] theorem WFCtx_nil : WFCtx [] := List.nodup_nil

theorem WFCtx.cons {x : VarId} {τ : BindTy} {Γ : Ctx}
    (hfresh : Fresh x Γ) (hwf : WFCtx Γ) :
    WFCtx ((x, τ) :: Γ) := by
  change (((x, τ) :: Γ).map Prod.fst).Nodup
  exact List.Nodup.cons hfresh hwf

theorem WFCtx.tail {x : VarId} {τ : BindTy} {Γ : Ctx} :
    WFCtx ((x, τ) :: Γ) → WFCtx Γ := by
  intro h; exact (List.nodup_cons.mp h).2

theorem WFCtx.fresh_head {x : VarId} {τ : BindTy} {Γ : Ctx} :
    WFCtx ((x, τ) :: Γ) → Fresh x Γ := by
  intro h; exact (List.nodup_cons.mp h).1

theorem HasVar.mem_map_fst {Γ : Ctx} {x : VarId} {τ : BindTy} :
    HasVar Γ x τ → x ∈ Γ.map Prod.fst := by
  intro h; induction h with
  | here => simp
  | there _ ih => exact List.mem_cons_of_mem _ ih

theorem HasVar.unique {Γ : Ctx} {x : VarId} {τ₁ τ₂ : BindTy}
    (hwf : WFCtx Γ) (h1 : HasVar Γ x τ₁) (h2 : HasVar Γ x τ₂) :
    τ₁ = τ₂ := by
  induction h1 with
  | here =>
    match h2 with
    | .here => rfl
    | .there h2' => exact absurd h2'.mem_map_fst hwf.fresh_head
  | there h1' ih =>
    match h2 with
    | .here => exact absurd h1'.mem_map_fst hwf.fresh_head
    | .there h2' => exact ih hwf.tail h2'

-- § 11b. Fresh lemmas for subcontexts

theorem viewCtx_map_fst_sub {x : VarId} {p : Player} {Γ : Ctx} :
    x ∈ (viewCtx p Γ).map Prod.fst → x ∈ Γ.map Prod.fst := by
  induction Γ with
  | nil => simp [viewCtx]
  | cons hd tl ih =>
    obtain ⟨y, τ⟩ := hd
    simp only [viewCtx]
    split
    · simp only [List.map, List.mem_cons]
      intro h; rcases h with rfl | h
      · exact Or.inl rfl
      · exact Or.inr (ih h)
    · intro h; exact List.mem_cons_of_mem _ (ih h)

theorem Fresh_viewCtx {x : VarId} {p : Player} {Γ : Ctx}
    (hfresh : Fresh x Γ) : Fresh x (viewCtx p Γ) :=
  fun hmem => hfresh (viewCtx_map_fst_sub hmem)

theorem Fresh_flattenCtx {x : VarId} {Γ : Ctx}
    (hfresh : Fresh x Γ) : Fresh x (flattenCtx Γ) := by
  unfold Fresh at *; rwa [flattenCtx_map_fst]

theorem WFCtx_flattenCtx {Γ : Ctx}
    (hwf : WFCtx Γ) : WFCtx (flattenCtx Γ) := by
  unfold WFCtx at *; rwa [flattenCtx_map_fst]

-- ============================================================================
-- § 12. Legality and admissibility
-- ============================================================================

def Legal : Prog Γ → Prop
  | .ret _ => True
  | .letExpr _ _ k => Legal k
  | .sample _ _ _ _ k => Legal k
  | .commit _ who acts R k =>
    (∀ view : Env (viewCtx who Γ), ∃ a ∈ acts, evalR R a view = true) ∧ Legal k
  | .reveal _ _ _ _ k => Legal k

def AdmissibleProfile (σ : Profile) : Prog Γ → Prop
  | .ret _ => True
  | .letExpr _ _ k => AdmissibleProfile σ k
  | .sample _ _ _ _ k => AdmissibleProfile σ k
  | .commit x who acts R k =>
    (∀ view, (σ.commit who x acts R view).Supported
      (fun a => a ∈ acts ∧ evalR R a view = true)) ∧
    AdmissibleProfile σ k
  | .reveal _ _ _ _ k => AdmissibleProfile σ k

theorem List.filter_ne_nil_of_exists {l : List α} {p : α → Bool}
    (h : ∃ a ∈ l, p a = true) : l.filter p ≠ [] := by
  obtain ⟨a, ha_mem, ha_p⟩ := h
  exact List.ne_nil_of_mem (List.mem_filter.mpr ⟨ha_mem, ha_p⟩)

-- ============================================================================
-- § 13. Normalization predicates
-- ============================================================================

def DistExpr.Normalized (D : DistExpr Γ b) : Prop :=
  ∀ env : Env Γ, (evalDistExpr D env).totalWeight = 1

def NormalizedDists : Prog Γ → Prop
  | .ret _ => True
  | .letExpr _ _ k => NormalizedDists k
  | .sample _ _ _ D k => DistExpr.Normalized D ∧ NormalizedDists k
  | .commit _ _ _ _ k => NormalizedDists k
  | .reveal _ _ _ _ k => NormalizedDists k

def Profile.NormalizedOn (σ : Profile) : Prog Γ → Prop
  | .ret _ => True
  | .letExpr _ _ k => σ.NormalizedOn k
  | .sample _ _ _ _ k => σ.NormalizedOn k
  | .commit x who acts R k =>
    (∀ view, (σ.commit who x acts R view).totalWeight = 1) ∧ σ.NormalizedOn k
  | .reveal _ _ _ _ k => σ.NormalizedOn k

theorem DistExpr.Normalized_ite {Γ : Ctx} {b : BaseTy}
    {c : Expr Γ .bool} {t f : DistExpr Γ b}
    (ht : t.Normalized) (hf : f.Normalized) :
    (DistExpr.ite c t f).Normalized := by
  intro env
  simp only [evalDistExpr]
  split <;> first | exact ht env | exact hf env

theorem outcomeDist_totalWeight_eq_one {Γ : Ctx} {σ : Profile}
    {p : Prog Γ} {env : Env Γ}
    (hd : NormalizedDists p) (hσ : σ.NormalizedOn p) :
    (outcomeDist σ p env).totalWeight = 1 := by
  induction p with
  | ret u => simp [outcomeDist, FDist.totalWeight_pure]
  | letExpr x e k ih => exact ih hd hσ
  | sample x τ m D k ih =>
    simp only [outcomeDist]
    exact FDist.totalWeight_bind_of_normalized (hd.1 _) (fun _ _ => ih hd.2 hσ)
  | commit x who acts R k ih =>
    simp only [outcomeDist]
    exact FDist.totalWeight_bind_of_normalized (hσ.1 _) (fun _ _ => ih hd hσ.2)
  | reveal y who x hx k ih => exact ih hd hσ

-- ============================================================================
-- § 14. Examples
-- ============================================================================

namespace Examples

def va : VarId := 0
def vb : VarId := 1
def va' : VarId := 2
def vb' : VarId := 3

def Γ0 : Ctx := []
def Γ1 : Ctx := [(va, .hidden 0 .bool)]
def Γ2 : Ctx := [(vb, .hidden 1 .bool), (va, .hidden 0 .bool)]
def Γ3 : Ctx := [(va', .pub .bool), (vb, .hidden 1 .bool), (va, .hidden 0 .bool)]
def Γ4 : Ctx :=
  [(vb', .pub .bool), (va', .pub .bool),
   (vb, .hidden 1 .bool), (va, .hidden 0 .bool)]

def hva_in_Γ2 : HasVar Γ2 va (.hidden 0 .bool) := .there .here
def hvb_in_Γ3 : HasVar Γ3 vb (.hidden 1 .bool) := .there .here
def hva'_in_Γ4 : HasVar Γ4 va' (.pub .bool) := .there .here
def hvb'_in_Γ4 : HasVar Γ4 vb' (.pub .bool) := .here

def mpPayoff : PayoffMap Γ4 :=
  ⟨[ (0, .ite
        (.eqBool (.var va' hva'_in_Γ4) (.var vb' hvb'_in_Γ4))
        (.constInt 1) (.constInt (-1))),
     (1, .ite
        (.eqBool (.var va' hva'_in_Γ4) (.var vb' hvb'_in_Γ4))
        (.constInt (-1)) (.constInt 1))
   ], by decide⟩

def matchingPennies : Prog Γ0 :=
  .commit va 0 (b := .bool) [true, false] (.constBool true)
    (.commit vb 1 (b := .bool) [true, false] (.constBool true)
      (.reveal va' 0 va hva_in_Γ2
        (.reveal vb' 1 vb hvb_in_Γ3
          (.ret mpPayoff))))

noncomputable def mpProfile : Profile where
  commit := fun {_Γ} {b} _who x _acts _R _view =>
    match x with
    | 0 =>
      match b with
      | .bool => FDist.pure true
      | .int => FDist.zero
    | 1 =>
      match b with
      | .bool => FDist.pure false
      | .int => FDist.zero
    | _ => FDist.zero

def conditionedGame : Prog Γ0 :=
  .commit va 0 (b := .bool) [true, false] (.constBool true)
    (.reveal va' 0 va .here
      (.commit vb 1 (b := .bool) [true, false]
        (.var va' (.there .here))
        (.ret ⟨[(0, .constInt 1), (1, .constInt 0)], by decide⟩)))

end Examples
