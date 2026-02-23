import Mathlib.Data.List.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.NNRat.Defs

/-!
# Vegas: A Typed Game Calculus

Implements the distilled Vegas calculus with commit/reveal, visibility-tagged
contexts, SSA named variables, and denotational semantics.
See `distilled/DESIGN.md` for the full specification.
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

inductive BindTy where
  | pub (b : BaseTy)
  | hidden (owner : Player) (b : BaseTy)
deriving DecidableEq

def BindTy.base : BindTy → BaseTy
  | .pub b => b
  | .hidden _ b => b

abbrev Ctx : Type := List (VarId × BindTy)

-- ============================================================================
-- § 2. HasVar and Env (function-based)
-- ============================================================================

/-- Proof that variable `x` has type `τ` in context `Γ`. -/
inductive HasVar : Ctx → VarId → BindTy → Type where
  | here {Γ x τ} : HasVar ((x, τ) :: Γ) x τ
  | there {Γ x y τ τ'} (h : HasVar Γ x τ) : HasVar ((y, τ') :: Γ) x τ

/-- An environment assigns a value to each variable in context. -/
def Env (Γ : Ctx) := ∀ x τ, HasVar Γ x τ → Val τ.base

namespace Env

def empty : Env [] := fun _ _ h => nomatch h

def cons (v : Val τ.base) (env : Env Γ) : Env ((x, τ) :: Γ) :=
  fun y σ h =>
    match h with
    | .here => v
    | .there h' => env y σ h'

def get (env : Env Γ) (h : HasVar Γ x τ) : Val τ.base :=
  env x τ h

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

/-- Embedding: a variable in the player's view is a variable in the full context. -/
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
    · intro h
      exact .there (ih h)

def Env.toView (p : Player) (env : Env Γ) : Env (viewCtx p Γ) :=
  fun x τ h => env x τ h.ofViewCtx

-- ============================================================================
-- § 4. Expressions (pub-only variable access; to be defined over obligation,
--      a capture lambda would transform BindTy.hidden to BindTy.pub, turning
--      negative polarity into positive.)
-- ============================================================================

/-- Expressions can only reference public variables. -/
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

-- ============================================================================
-- § 5. Weighted distributions
-- ============================================================================

structure WDist (α : Type) where
  weights : List (α × ℚ≥0)
deriving Inhabited

namespace WDist

def pure (x : α) : WDist α := ⟨[(x, 1)]⟩
def zero : WDist α := ⟨[]⟩

def bind (d : WDist α) (f : α → WDist β) : WDist β :=
  ⟨d.weights.flatMap (fun (a, w) => (f a).weights.map (fun (b, w') => (b, w * w')))⟩

def map (f : α → β) (d : WDist α) : WDist β :=
  ⟨d.weights.map (fun (a, w) => (f a, w))⟩

def scale (w : ℚ≥0) (d : WDist α) : WDist α :=
  ⟨d.weights.map (fun (a, w') => (a, w * w'))⟩

def append (d₁ d₂ : WDist α) : WDist α :=
  ⟨d₁.weights ++ d₂.weights⟩

end WDist

-- ============================================================================
-- § 6. Kernels and action sets
-- ============================================================================

abbrev CommitKernel (who : Player) (Γ : Ctx) (b : BaseTy) : Type :=
  Env (viewCtx who Γ) → WDist (Val b)

abbrev ActSet (who : Player) (Γ : Ctx) (b : BaseTy) : Type :=
  Env (viewCtx who Γ) → List (Val b)

-- ============================================================================
-- § 7. Payoff maps and program type (6 constructors)
-- ============================================================================

structure PayoffMap (Γ : Ctx) where
  entries : List (Player × Expr Γ .int)

def evalPayoffMap (u : PayoffMap Γ) (env : Env Γ) (who : Player) : Int :=
  match u.entries.find? (fun (p, _) => p == who) with
  | some (_, e) => evalExpr e env
  | none => 0

inductive Prog : Ctx → Type where
  | ret (u : PayoffMap Γ) : Prog Γ
  | letExpr (x : VarId) {b : BaseTy} (e : Expr Γ b)
      (k : Prog ((x, .pub b) :: Γ)) : Prog Γ
  | commit (x : VarId) (who : Player) {b : BaseTy}
      (A : ActSet who Γ b)
      (k : Prog ((x, .hidden who b) :: Γ)) : Prog Γ
  | reveal (y : VarId) (who : Player) (x : VarId) {b : BaseTy}
      (hx : HasVar Γ x (.hidden who b))
      (k : Prog ((y, .pub b) :: Γ)) : Prog Γ
  | assert (who : Player) (c : Expr Γ .bool)
      (k : Prog Γ) : Prog Γ
  | observe (c : Expr Γ .bool)
      (k : Prog Γ) : Prog Γ

-- ============================================================================
-- § 8. Profile and PProfile
-- ============================================================================

structure Profile where
  commit : {Γ : Ctx} → {b : BaseTy} → (who : Player) →
    (x : VarId) → ActSet who Γ b → CommitKernel who Γ b

-- ============================================================================
-- § 9. Denotational semantics
-- ============================================================================

def outcomeDist (σ : Profile) : Prog Γ → Env Γ → WDist (Player → Int)
  | .ret u, env =>
    WDist.pure (fun who => evalPayoffMap u env who)
  | .letExpr x e k, env =>
    outcomeDist σ k (Env.cons (x := x) (evalExpr e env) env)
  | .commit x who A k, env =>
    WDist.bind (σ.commit who x A (env.toView who)) (fun v =>
      outcomeDist σ k (Env.cons (x := x) v env))
  | .reveal y _who _x (b := b) hx k, env =>
    let v : Val b := env.get hx
    outcomeDist σ k (Env.cons (x := y) v env)
  | .assert _who c k, env =>
    if evalExpr c env then outcomeDist σ k env else WDist.zero
  | .observe c k, env =>
    if evalExpr c env then outcomeDist σ k env else WDist.zero

-- ============================================================================
-- § 10. Partial profiles
-- ============================================================================

structure PProfile where
  commit? : {Γ : Ctx} → {b : BaseTy} → (who : Player) →
    (x : VarId) → ActSet who Γ b →
    Option (CommitKernel who Γ b)

def PProfile.Complete (π : PProfile) : Prop :=
  ∀ {Γ : Ctx} {b : BaseTy} (who : Player) (x : VarId) (A : ActSet who Γ b),
    (π.commit? who x A).isSome

def PProfile.commitOfComplete (π : PProfile) (hπ : π.Complete)
    {Γ : Ctx} {b : BaseTy} (who : Player) (x : VarId)
    (A : ActSet who Γ b) : CommitKernel who Γ b :=
  (π.commit? who x A).get (hπ who x A)

-- ============================================================================
-- § 11. Examples
-- ============================================================================

namespace Examples

-- Named variable IDs for readability
def va : VarId := 0   -- P0's commit
def vb : VarId := 1   -- P1's commit
def va' : VarId := 2  -- P0's reveal
def vb' : VarId := 3  -- P1's reveal

-- Contexts at each program point
def Γ0 : Ctx := []
def Γ1 : Ctx := [(va, .hidden 0 .bool)]
def Γ2 : Ctx := [(vb, .hidden 1 .bool), (va, .hidden 0 .bool)]
def Γ3 : Ctx := [(va', .pub .bool), (vb, .hidden 1 .bool), (va, .hidden 0 .bool)]
def Γ4 : Ctx :=
  [(vb', .pub .bool), (va', .pub .bool),
   (vb, .hidden 1 .bool), (va, .hidden 0 .bool)]

-- Action sets: {true, false} regardless of view
def boolActs (who : Player) : ActSet who Γ .bool := fun _ => [true, false]

-- HasVar proofs
def hva_in_Γ2 : HasVar Γ2 va (.hidden 0 .bool) :=
  .there .here

def hvb_in_Γ3 : HasVar Γ3 vb (.hidden 1 .bool) :=
  .there .here

def hva'_in_Γ4 : HasVar Γ4 va' (.pub .bool) :=
  .there .here

def hvb'_in_Γ4 : HasVar Γ4 vb' (.pub .bool) :=
  .here

/-- Matching pennies:
  P0 commits a ∈ {T,F}, P1 commits b ∈ {T,F},
  both reveal, payoff = ±1 based on match. -/
def matchingPennies : Prog Γ0 :=
  .commit va 0 (boolActs 0)
    (.commit vb 1 (boolActs 1)
      (.reveal va' 0 va hva_in_Γ2
        (.reveal vb' 1 vb hvb_in_Γ3
          (.ret ⟨[
            (0, .ite
              (.eqBool (.var va' hva'_in_Γ4) (.var vb' hvb'_in_Γ4))
              (.constInt 1) (.constInt (-1))),
            (1, .ite
              (.eqBool (.var va' hva'_in_Γ4) (.var vb' hvb'_in_Γ4))
              (.constInt (-1)) (.constInt 1))
          ]⟩))))

/-- Profile: pick from action set by variable id. -/
def mpProfile : Profile where
  commit := fun {_Γ} {_b} _who x A obs =>
    match x with
    | 0 => -- P0 plays first action (true)
      match A obs with
      | a :: _ => WDist.pure a
      | [] => WDist.zero
    | 1 => -- P1 plays second action (false)
      match A obs with
      | _ :: a :: _ => WDist.pure a
      | a :: _ => WDist.pure a
      | [] => WDist.zero
    | _ =>
      match A obs with
      | a :: _ => WDist.pure a
      | [] => WDist.zero

end Examples
