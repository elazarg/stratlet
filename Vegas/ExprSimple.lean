import Vegas.Core

/-!
# Concrete Vegas expression layer

This file fixes the concrete value types used by the current Vegas protocol
and defines the concrete expression and distribution syntax over plain
(non-visibility) contexts.
-/

namespace Vegas

abbrev Player : Type := Nat

inductive BaseTy where
  | int : BaseTy
  | bool : BaseTy
deriving Repr, DecidableEq

abbrev Val : BaseTy → Type
  | .int => Int
  | .bool => Bool

instance : DecidableEq (Val b) := by
  cases b <;> infer_instance

/-- Plain (non-visibility) context over `BaseTy`. -/
abbrev CtxSimple : Type := Vegas.Ctx BaseTy

/-- Plain `Env` over concrete value types. -/
abbrev PlainEnv (Γ : CtxSimple) : Type := Vegas.Env Val Γ

inductive Expr : CtxSimple → BaseTy → Type where
  | var (x : VarId) (h : HasVar Γ x b) : Expr Γ b
  | constInt (i : Int) : Expr Γ .int
  | constBool (b : Bool) : Expr Γ .bool
  | addInt (l r : Expr Γ .int) : Expr Γ .int
  | eqInt (l r : Expr Γ .int) : Expr Γ .bool
  | eqBool (l r : Expr Γ .bool) : Expr Γ .bool
  | andBool (l r : Expr Γ .bool) : Expr Γ .bool
  | notBool (e : Expr Γ .bool) : Expr Γ .bool
  | ite (c : Expr Γ .bool) (t f : Expr Γ b) : Expr Γ b

def evalExpr : Expr Γ b → PlainEnv Γ → Val b
  | .var _ h, env => env.get h
  | .constInt i, _ => i
  | .constBool b, _ => b
  | .addInt l r, env => evalExpr l env + evalExpr r env
  | .eqInt l r, env => decide (evalExpr l env = evalExpr r env)
  | .eqBool l r, env => decide (evalExpr l env = evalExpr r env)
  | .andBool l r, env => evalExpr l env && evalExpr r env
  | .notBool e, env => !(evalExpr e env)
  | .ite c t f, env => if evalExpr c env then evalExpr t env else evalExpr f env

/-- Expression dependency set. -/
def exprDeps : Expr Γ b → Finset VarId
  | .var x _ => {x}
  | .constInt _ => ∅
  | .constBool _ => ∅
  | .addInt l r => exprDeps l ∪ exprDeps r
  | .eqInt l r => exprDeps l ∪ exprDeps r
  | .eqBool l r => exprDeps l ∪ exprDeps r
  | .andBool l r => exprDeps l ∪ exprDeps r
  | .notBool e => exprDeps e
  | .ite c t f => exprDeps c ∪ exprDeps t ∪ exprDeps f

theorem expr_deps_sound {Γ : CtxSimple} {b : BaseTy}
    (e : Expr Γ b) (ρ₁ ρ₂ : PlainEnv Γ)
    (ha : AgreesOn ρ₁ ρ₂ (exprDeps e)) :
    evalExpr e ρ₁ = evalExpr e ρ₂ := by
  induction e with
  | var x h =>
    exact ha x _ h (Finset.mem_singleton.mpr rfl)
  | constInt _ => rfl
  | constBool _ => rfl
  | addInt l r ihl ihr =>
    simp only [evalExpr]
    rw [ihl (ha.mono Finset.subset_union_left),
        ihr (ha.mono Finset.subset_union_right)]
  | eqInt l r ihl ihr =>
    simp only [evalExpr]
    rw [ihl (ha.mono Finset.subset_union_left),
        ihr (ha.mono Finset.subset_union_right)]
  | eqBool l r ihl ihr =>
    simp only [evalExpr]
    rw [ihl (ha.mono Finset.subset_union_left),
        ihr (ha.mono Finset.subset_union_right)]
  | andBool l r ihl ihr =>
    simp only [evalExpr]
    rw [ihl (ha.mono Finset.subset_union_left),
        ihr (ha.mono Finset.subset_union_right)]
  | notBool e ih =>
    simp only [evalExpr]
    rw [ih ha]
  | ite c t f ihc iht ihf =>
    simp only [evalExpr]
    rw [ihc (ha.mono (Finset.subset_union_left.trans Finset.subset_union_left))]
    split
    · exact iht (ha.mono (Finset.subset_union_right.trans Finset.subset_union_left))
    · exact ihf (ha.mono Finset.subset_union_right)

inductive DistExpr (Γ : CtxSimple) (b : BaseTy) : Type where
  | weighted (entries : List (Val b × ℚ≥0)) : DistExpr Γ b
  | ite (c : Expr Γ .bool) (t f : DistExpr Γ b) : DistExpr Γ b

noncomputable def evalDistExpr : DistExpr Γ b → PlainEnv Γ → FDist (Val b)
  | .weighted entries, _ => FDist.ofList entries
  | .ite c t f, env =>
      if evalExpr c env then evalDistExpr t env else evalDistExpr f env

/-- Distribution expression dependency set. -/
def distExprDeps : DistExpr Γ b → Finset VarId
  | .weighted _ => ∅
  | .ite c t f => exprDeps c ∪ distExprDeps t ∪ distExprDeps f

theorem dist_deps_sound {Γ : CtxSimple} {b : BaseTy}
    (d : DistExpr Γ b) (ρ₁ ρ₂ : PlainEnv Γ)
    (ha : AgreesOn ρ₁ ρ₂ (distExprDeps d)) :
    evalDistExpr d ρ₁ = evalDistExpr d ρ₂ := by
  induction d with
  | weighted _ => rfl
  | ite c t f iht ihf =>
    simp only [evalDistExpr]
    rw [expr_deps_sound c ρ₁ ρ₂
      (ha.mono (Finset.subset_union_left.trans Finset.subset_union_left))]
    split
    · exact iht (ha.mono (Finset.subset_union_right.trans Finset.subset_union_left))
    · exact ihf (ha.mono Finset.subset_union_right)

def Expr.weakenAfterHead
    {Γ : CtxSimple} {x y : VarId} {τ σ b : BaseTy}
    (e : Expr ((x, τ) :: Γ) b) : Expr ((x, τ) :: (y, σ) :: Γ) b :=
  match e with
  | .var _ .here => .var x .here
  | .var z (.there h') => .var z (.there (.there h'))
  | .constInt i => .constInt i
  | .constBool v => .constBool v
  | .addInt l r => .addInt l.weakenAfterHead r.weakenAfterHead
  | .eqInt l r => .eqInt l.weakenAfterHead r.weakenAfterHead
  | .eqBool l r => .eqBool l.weakenAfterHead r.weakenAfterHead
  | .andBool l r => .andBool l.weakenAfterHead r.weakenAfterHead
  | .notBool e => .notBool e.weakenAfterHead
  | .ite c t f => .ite c.weakenAfterHead t.weakenAfterHead f.weakenAfterHead

theorem evalExpr_weakenAfterHead
    {Γ : CtxSimple} {x y : VarId} {τ σ b : BaseTy}
    (e : Expr ((x, τ) :: Γ) b)
    (vx : Val τ) (vy : Val σ) (env : PlainEnv Γ) :
    evalExpr e.weakenAfterHead (Env.cons (x := x) vx (Env.cons (x := y) vy env)) =
      evalExpr e (Env.cons (x := x) vx env) := by
  induction e with
  | var z h =>
      cases h <;> simp [Expr.weakenAfterHead, evalExpr]
  | constInt i =>
      simp [Expr.weakenAfterHead, evalExpr]
  | constBool v =>
      simp [Expr.weakenAfterHead, evalExpr]
  | addInt l r ihl ihr =>
      simp [Expr.weakenAfterHead, evalExpr, ihl, ihr]
  | eqInt l r ihl ihr =>
      simp [Expr.weakenAfterHead, evalExpr, ihl, ihr]
  | eqBool l r ihl ihr =>
      simp [Expr.weakenAfterHead, evalExpr, ihl, ihr]
  | andBool l r ihl ihr =>
      simp [Expr.weakenAfterHead, evalExpr, ihl, ihr]
  | notBool e ih =>
      simp [Expr.weakenAfterHead, evalExpr, ih]
  | ite c t f ihc iht ihf =>
      simp [Expr.weakenAfterHead, evalExpr, ihc, iht, ihf]

/-- The current concrete language, viewed as an instance of `IExpr`. -/
noncomputable def simpleExpr : Vegas.IExpr where
  Ty := BaseTy
  decEqTy := inferInstance
  Val := Val
  decEqVal := by intro τ; cases τ <;> infer_instance
  bool := .bool
  toBool := id
  int := .int
  toInt := id
  Expr := Expr
  eval := @evalExpr
  exprDeps := @exprDeps
  extendAfterHead := by
    intro Γ x y τ σ b e
    refine ⟨e.weakenAfterHead, ?_⟩
    intro vx vy env
    exact evalExpr_weakenAfterHead e vx vy env
  DistExpr := DistExpr
  evalDist := @evalDistExpr
  distDeps := @distExprDeps
  expr_deps_sound := @expr_deps_sound
  dist_deps_sound := @dist_deps_sound

abbrev BindTySimple : Type := Vegas.BindTy Player simpleExpr
abbrev VCtxSimple : Type := Vegas.VCtx Player simpleExpr
abbrev VHasVarSimple : VCtxSimple → VarId → BindTySimple → Type :=
  Vegas.VHasVar
abbrev VEnvSimple (Γ : VCtxSimple) : Type :=
  Vegas.VEnv (Player := Player) simpleExpr Γ

namespace BindTySimple

abbrev base : BindTySimple → BaseTy := Vegas.BindTy.base

end BindTySimple

namespace VHasVarSimple

abbrev here {Γ : VCtxSimple} {x : VarId} {τ : BindTySimple} :
    VHasVarSimple ((x, τ) :: Γ) x τ :=
  Vegas.VHasVar.here

abbrev there {Γ : VCtxSimple} {x y : VarId} {τ τ' : BindTySimple}
    (h : VHasVarSimple Γ x τ) : VHasVarSimple ((y, τ') :: Γ) x τ :=
  Vegas.VHasVar.there h

end VHasVarSimple

namespace VEnvSimple

abbrev empty : VEnvSimple [] :=
  Vegas.VEnv.empty (Player := Player) simpleExpr

abbrev cons {Γ : VCtxSimple} {x : VarId} {τ : BindTySimple}
    (v : Val τ.base) (env : VEnvSimple Γ) : VEnvSimple ((x, τ) :: Γ) :=
  Vegas.VEnv.cons v env

abbrev get {Γ : VCtxSimple} {x : VarId} {τ : BindTySimple}
    (env : VEnvSimple Γ) (h : VHasVarSimple Γ x τ) : Val τ.base :=
  Vegas.VEnv.get env h

@[simp] theorem cons_get_here {Γ : VCtxSimple} {x : VarId} {τ : BindTySimple}
    {v : Val τ.base} {env : VEnvSimple Γ} :
    (VEnvSimple.cons v env).get
      (VHasVarSimple.here (Γ := Γ) (x := x) (τ := τ)) = v := by
  exact Vegas.VEnv.cons_get_here

@[simp] theorem cons_get_there {Γ : VCtxSimple} {x y : VarId}
    {τ σ : BindTySimple}
    {v : Val τ.base} {env : VEnvSimple Γ}
    {h : VHasVarSimple Γ y σ} :
    (VEnvSimple.cons (x := x) v env).get (VHasVarSimple.there h) =
      env.get h := by
  exact Vegas.VEnv.cons_get_there

abbrev toView (p : Player) {Γ : VCtxSimple} (env : VEnvSimple Γ) :
    VEnvSimple (Vegas.viewVCtx p Γ) :=
  Vegas.VEnv.toView p env

abbrev toPub {Γ : VCtxSimple} (env : VEnvSimple Γ) :
    VEnvSimple (Vegas.pubVCtx Γ) :=
  Vegas.VEnv.toPub env

noncomputable abbrev toFlat {Γ : VCtxSimple} (env : VEnvSimple Γ) :
    VEnvSimple (Vegas.flattenVCtx Γ) :=
  Vegas.VEnv.toFlat env

noncomputable abbrev toFlatView (p : Player) {Γ : VCtxSimple}
    (env : VEnvSimple Γ) :
    VEnvSimple (Vegas.flattenVCtx (Vegas.viewVCtx p Γ)) :=
  Vegas.VEnv.toFlatView p env

end VEnvSimple

namespace VHasVarSimple

abbrev ofViewVCtx {p : Player} {Γ : VCtxSimple} {x : VarId}
    {τ : BindTySimple} :
    VHasVarSimple (Vegas.viewVCtx p Γ) x τ → VHasVarSimple Γ x τ :=
  Vegas.VHasVar.ofViewVCtx (p := p)

abbrev ofPubVCtx {Γ : VCtxSimple} {x : VarId} {τ : BindTySimple} :
    VHasVarSimple (Vegas.pubVCtx Γ) x τ → VHasVarSimple Γ x τ :=
  Vegas.VHasVar.ofPubVCtx

abbrev ofPubToView {p : Player} {Γ : VCtxSimple} {x : VarId}
    {τ : BindTySimple} :
    VHasVarSimple (Vegas.pubVCtx Γ) x τ →
      VHasVarSimple (Vegas.viewVCtx p Γ) x τ :=
  Vegas.VHasVar.ofPubToView (p := p)

abbrev toFlatten {Γ : VCtxSimple} {x : VarId} {τ : BindTySimple} :
    VHasVarSimple Γ x τ →
      VHasVarSimple (Vegas.flattenVCtx Γ) x (.pub τ.base) :=
  Vegas.VHasVar.toFlatten

abbrev unflatten {Γ : VCtxSimple} {x : VarId} {b : BaseTy} :
    VHasVarSimple (Vegas.flattenVCtx Γ) x (.pub b) →
      (τ : BindTySimple) × VHasVarSimple Γ x τ × PLift (τ.base = b) :=
  Vegas.VHasVar.unflatten

end VHasVarSimple

def Expr.weaken {Γ : CtxSimple} {b : BaseTy} {x : VarId} {τ : BaseTy}
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

theorem evalExpr_weaken {Γ : CtxSimple} {b τ : BaseTy} {x : VarId}
    (e : Expr Γ b) (v : Val τ) (env : PlainEnv Γ) :
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

/-- Extract variable IDs referenced by an expression (as a list). -/
def exprVars : Expr Γ b → List VarId
  | .var x _ => [x]
  | .constInt _ => []
  | .constBool _ => []
  | .addInt l r => exprVars l ++ exprVars r
  | .eqInt l r => exprVars l ++ exprVars r
  | .eqBool l r => exprVars l ++ exprVars r
  | .andBool l r => exprVars l ++ exprVars r
  | .notBool e => exprVars e
  | .ite c t f => exprVars c ++ exprVars t ++ exprVars f

/-- Extract variable IDs referenced by a distribution expression (as a list). -/
def distExprVars : DistExpr Γ b → List VarId
  | .weighted _ => []
  | .ite c t f => exprVars c ++ distExprVars t ++ distExprVars f

@[simp] theorem evalDistExpr_weighted {Γ : CtxSimple} {b : BaseTy}
    (entries : List (Val b × ℚ≥0)) (env : PlainEnv Γ) :
    evalDistExpr (.weighted entries) env = FDist.ofList entries := rfl

theorem evalDistExpr_ite_true {Γ : CtxSimple} {b : BaseTy}
    {c : Expr Γ .bool} {t f : DistExpr Γ b} {env : PlainEnv Γ}
    (hc : evalExpr c env = true) :
    evalDistExpr (.ite c t f) env = evalDistExpr t env := by
  simp [evalDistExpr, hc]

theorem evalDistExpr_ite_false {Γ : CtxSimple} {b : BaseTy}
    {c : Expr Γ .bool} {t f : DistExpr Γ b} {env : PlainEnv Γ}
    (hc : evalExpr c env = false) :
    evalDistExpr (.ite c t f) env = evalDistExpr f env := by
  simp [evalDistExpr, hc]

def DistExpr.point (v : Val b) : DistExpr Γ b := .weighted [(v, 1)]

def DistExpr.uniform (vs : List (Val b)) : DistExpr Γ b :=
  let w : ℚ≥0 := 1 / (vs.length : ℚ≥0)
  .weighted (vs.map fun v => (v, w))

end Vegas
