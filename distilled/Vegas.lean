import Mathlib.Data.List.Basic
import Mathlib.Data.Rat.Defs

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
abbrev ChannelId : Type := Nat
abbrev Player : Type := Nat

inductive BaseTy where
  | int : BaseTy
  | bool : BaseTy
deriving Repr, DecidableEq

abbrev Val : BaseTy → Type
  | .int => Int
  | .bool => Bool

inductive Vis where
  | pub : Vis
  | priv : Player → Vis
deriving Repr, DecidableEq

structure Ty where
  base : BaseTy
  vis : Vis
deriving Repr, DecidableEq

abbrev Ctx : Type := List (VarId × Ty)

-- ============================================================================
-- § 2. HasVar and Env (function-based)
-- ============================================================================

/-- Proof that variable `x` has type `τ` in context `Γ`. -/
inductive HasVar : Ctx → VarId → Ty → Type where
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

def canSee (p : Player) : Vis → Bool
  | .pub => true
  | .priv q => p == q

def viewCtx (p : Player) : Ctx → Ctx
  | [] => []
  | (x, τ) :: Γ =>
    if canSee p τ.vis then (x, τ) :: viewCtx p Γ
    else viewCtx p Γ

def pubCtx : Ctx → Ctx
  | [] => []
  | (x, τ) :: Γ =>
    match τ.vis with
    | .pub => (x, τ) :: pubCtx Γ
    | .priv _ => pubCtx Γ

/-- Embedding: a variable in the player's view is a variable in the full context. -/
def HasVar.ofViewCtx {p : Player} :
    HasVar (viewCtx p Γ) x τ → HasVar Γ x τ := by
  induction Γ with
  | nil => intro h; exact nomatch h
  | cons hd tl ih =>
    obtain ⟨y, σ⟩ := hd
    simp [viewCtx]
    split
    · intro h
      match h with
      | .here => exact .here
      | .there h' => exact .there (ih h')
    · intro h; exact .there (ih h)

/-- Embedding: a variable in the public view is a variable in the full context. -/
def HasVar.ofPubCtx : HasVar (pubCtx Γ) x τ → HasVar Γ x τ := by
  induction Γ with
  | nil => intro h; exact nomatch h
  | cons hd tl ih =>
    obtain ⟨y, σ⟩ := hd
    simp [pubCtx]
    split
    · intro h
      match h with
      | .here => exact .here
      | .there h' => exact .there (ih h')
    · intro h; exact .there (ih h)

def Env.toView (p : Player) (env : Env Γ) : Env (viewCtx p Γ) :=
  fun x τ h => env x τ h.ofViewCtx

def Env.toPub (env : Env Γ) : Env (pubCtx Γ) :=
  fun x τ h => env x τ h.ofPubCtx

-- ============================================================================
-- § 4. Expressions (pub-only variable access)
-- ============================================================================

/-- Expressions can only reference public variables. -/
inductive Expr : Ctx → BaseTy → Type where
  | var (x : VarId) (h : HasVar Γ x ⟨b, .pub⟩) : Expr Γ b
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
  weights : List (α × Rat)
deriving Inhabited

namespace WDist

def pure (x : α) : WDist α := ⟨[(x, 1)]⟩
def zero : WDist α := ⟨[]⟩

def bind (d : WDist α) (f : α → WDist β) : WDist β :=
  ⟨d.weights.flatMap (fun (a, w) => (f a).weights.map (fun (b, w') => (b, w * w')))⟩

def map (f : α → β) (d : WDist α) : WDist β :=
  ⟨d.weights.map (fun (a, w) => (f a, w))⟩

def scale (w : Rat) (d : WDist α) : WDist α :=
  ⟨d.weights.map (fun (a, w') => (a, w * w'))⟩

def append (d₁ d₂ : WDist α) : WDist α :=
  ⟨d₁.weights ++ d₂.weights⟩

end WDist

-- ============================================================================
-- § 6. Samplers, kernels, action sets, asserts
-- ============================================================================

inductive Sampler where
  | Nature : Sampler
  | Player : Player → Sampler

def samplerCtx (s : Sampler) (Γ : Ctx) : Ctx :=
  match s with
  | .Nature => pubCtx Γ
  | .Player p => viewCtx p Γ

def SampleKernel (s : Sampler) (Γ : Ctx) (b : BaseTy) : Type :=
  Env (samplerCtx s Γ) → WDist (Val b)

def ActSet (who : Player) (Γ : Ctx) (b : BaseTy) : Type :=
  Env (viewCtx who Γ) → List (Val b)

def Assert (who : Player) (Γ : Ctx) : Type :=
  Env (viewCtx who Γ) → Bool

def Env.projectSampler (s : Sampler) (env : Env Γ) : Env (samplerCtx s Γ) :=
  match s with
  | .Nature => env.toPub
  | .Player p => env.toView p

-- ============================================================================
-- § 7. Program type (8 constructors)
-- ============================================================================

inductive Prog : Ctx → BaseTy → Type where
  | ret (e : Expr Γ b) : Prog Γ b
  | letExpr (x : VarId) (e : Expr Γ b') (k : Prog ((x, ⟨b', .pub⟩) :: Γ) b) : Prog Γ b
  | sample (x : VarId) (id : ChannelId) (vis : Vis) (s : Sampler)
      (K : SampleKernel s Γ b') (k : Prog ((x, ⟨b', vis⟩) :: Γ) b) : Prog Γ b
  | commit (x : VarId) (id : ChannelId) (who : Player) (A : ActSet who Γ b')
      (k : Prog ((x, ⟨b', .priv who⟩) :: Γ) b) : Prog Γ b
  | reveal (y : VarId) (who : Player) (x : VarId) {b' : BaseTy}
      (hx : HasVar Γ x ⟨b', .priv who⟩)
      (k : Prog ((y, ⟨b', .pub⟩) :: Γ) b) : Prog Γ b
  | assert (who : Player) (P : Assert who Γ) (k : Prog Γ b) : Prog Γ b
  | observe (c : Expr Γ .bool) (k : Prog Γ b) : Prog Γ b
  | withdraw (payoff : Player → Expr Γ .int) : Prog Γ .int

-- ============================================================================
-- § 8. Profile and PProfile
-- ============================================================================

structure Profile where
  commit : {Γ : Ctx} → {b : BaseTy} → (who : Player) → ChannelId →
    ActSet who Γ b → Env (viewCtx who Γ) → WDist (Val b)

structure PProfile where
  commit? : {Γ : Ctx} → {b : BaseTy} → (who : Player) → ChannelId →
    ActSet who Γ b → Option (Env (viewCtx who Γ) → WDist (Val b))

def PProfile.Complete (π : PProfile) : Prop :=
  ∀ {Γ : Ctx} {b : BaseTy} (who : Player) (id : ChannelId) (A : ActSet who Γ b),
    (π.commit? who id A).isSome

def PProfile.commitOfComplete (π : PProfile) (hπ : π.Complete)
    {Γ : Ctx} {b : BaseTy} (who : Player) (id : ChannelId)
    (A : ActSet who Γ b) : Env (viewCtx who Γ) → WDist (Val b) :=
  (π.commit? who id A).get (hπ who id A)

-- ============================================================================
-- § 9. Denotational semantics
-- ============================================================================

def eval (σ : Profile) (who : Player) : Prog Γ b → Env Γ → WDist (Val b)
  | .ret e, env => WDist.pure (evalExpr e env)
  | .letExpr x e k, env =>
    eval σ who k (Env.cons (x := x) (evalExpr e env) env)
  | .sample x _id _vis s K k, env =>
    WDist.bind (K (env.projectSampler s)) (fun v =>
      eval σ who k (Env.cons (x := x) v env))
  | .commit x id p A k, env =>
    WDist.bind (σ.commit p id A (env.toView p)) (fun v =>
      eval σ who k (Env.cons (x := x) v env))
  | .reveal y _who' _x (b' := b') hx k, env =>
    let v : Val b' := env.get hx
    eval σ who k (Env.cons (x := y) v env)
  | .assert p P k, env =>
    if P (env.toView p) then eval σ who k env else WDist.zero
  | .observe c k, env =>
    if evalExpr c env then eval σ who k env else WDist.zero
  | .withdraw payoff, env =>
    WDist.pure (evalExpr (payoff who) env)

-- ============================================================================
-- § 10. Expected utility
-- ============================================================================

def EU (p : Prog Γ .int) (σ : Profile) (env : Env Γ) (who : Player) : Rat :=
  let d := eval σ who p env
  d.weights.foldl (fun acc (v, w) => acc + w * ↑v) 0

-- ============================================================================
-- § 11. Profile application
-- ============================================================================

def applyPProfile (π : PProfile) : Prog Γ b → Prog Γ b
  | .ret e => .ret e
  | .letExpr x e k => .letExpr x e (applyPProfile π k)
  | .sample x id vis s K k => .sample x id vis s K (applyPProfile π k)
  | .commit x id who A k =>
    match π.commit? who id A with
    | some Kdec => .sample x id (.priv who) (.Player who) Kdec (applyPProfile π k)
    | none => .commit x id who A (applyPProfile π k)
  | .reveal y who' x hx k => .reveal y who' x hx (applyPProfile π k)
  | .assert who' P k => .assert who' P (applyPProfile π k)
  | .observe c k => .observe c (applyPProfile π k)
  | .withdraw payoff => .withdraw payoff

-- ============================================================================
-- § 12. Deviation and Nash equilibrium
-- ============================================================================

structure Deviator (who : Player) where
  commit : {Γ : Ctx} → {b : BaseTy} → ChannelId →
    ActSet who Γ b → Env (viewCtx who Γ) → WDist (Val b)

def Profile.deviate (σ : Profile) {who : Player} (δ : Deviator who) : Profile where
  commit := fun {_Γ} {_b} p id A obs =>
    if h : p = who then
      δ.commit id (h ▸ A) (h ▸ obs)
    else
      σ.commit p id A obs

def IsNash (p : Prog Γ .int) (σ : Profile) (env : Env Γ) : Prop :=
  ∀ (who : Player) (δ : Deviator who),
    EU p σ env who ≥ EU p (σ.deviate δ) env who

-- ============================================================================
-- § 13. Examples
-- ============================================================================

namespace Examples

-- Named variable IDs for readability
def va : VarId := 0   -- P0's commit
def vb : VarId := 1   -- P1's commit
def va' : VarId := 2  -- P0's reveal
def vb' : VarId := 3  -- P1's reveal

-- Contexts at each program point
def Γ0 : Ctx := []
def Γ1 : Ctx := [(va, ⟨.bool, .priv 0⟩)]
def Γ2 : Ctx := [(vb, ⟨.bool, .priv 1⟩), (va, ⟨.bool, .priv 0⟩)]
def Γ3 : Ctx := [(va', ⟨.bool, .pub⟩), (vb, ⟨.bool, .priv 1⟩), (va, ⟨.bool, .priv 0⟩)]
def Γ4 : Ctx :=
  [(vb', ⟨.bool, .pub⟩), (va', ⟨.bool, .pub⟩),
   (vb, ⟨.bool, .priv 1⟩), (va, ⟨.bool, .priv 0⟩)]

-- Action sets: {true, false} regardless of view
def boolActs (who : Player) : ActSet who Γ .bool := fun _ => [true, false]

-- HasVar proofs
def hva_in_Γ2 : HasVar Γ2 va ⟨.bool, .priv 0⟩ :=
  .there .here

def hvb_in_Γ3 : HasVar Γ3 vb ⟨.bool, .priv 1⟩ :=
  .there .here

def hva'_in_Γ4 : HasVar Γ4 va' ⟨.bool, .pub⟩ :=
  .there .here

def hvb'_in_Γ4 : HasVar Γ4 vb' ⟨.bool, .pub⟩ :=
  .here

/-- Matching pennies:
  P0 commits a ∈ {T,F}, P1 commits b ∈ {T,F},
  both reveal, payoff = ±1 based on match. -/
def matchingPennies : Prog Γ0 .int :=
  .commit va 0 0 (boolActs 0)
    (.commit vb 1 1 (boolActs 1)
      (.reveal va' 0 va hva_in_Γ2
        (.reveal vb' 1 vb hvb_in_Γ3
          (.withdraw (fun who =>
            .ite
              (.eqBool (.var va' hva'_in_Γ4)
                       (.var vb' hvb'_in_Γ4))
              (if who = 0 then .constInt 1
               else .constInt (-1))
              (if who = 0 then .constInt (-1)
               else .constInt 1))))))

/-- Profile: pick from action set by channel id. -/
def mpProfile : Profile where
  commit := fun {_Γ} {_b} _who id A obs =>
    match id with
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

-- Expected utility computations
def mpEU_p0 : Rat :=
  EU matchingPennies mpProfile Env.empty 0
def mpEU_p1 : Rat :=
  EU matchingPennies mpProfile Env.empty 1

end Examples
