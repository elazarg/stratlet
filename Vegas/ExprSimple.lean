import Vegas.Core

/-!
# Concrete Vegas expression layer

This file fixes the concrete value types used by the current Vegas protocol
and defines the concrete expression syntax over visibility-aware contexts.
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

/-- The current concrete value layer, viewed as an instance of `ExprLanguage`. -/
def simpleExpr : Vegas.ExprLanguage where
  Ty := BaseTy
  decEqTy := inferInstance
  Val := Val
  decEqVal := by
    intro τ
    cases τ <;> infer_instance
  bool := .bool
  toBool := id
  int := .int
  toInt := id

abbrev BindTySimple : Type := Vegas.BindTy Player simpleExpr
abbrev CtxSimple : Type := Vegas.Ctx Player simpleExpr
abbrev HasVarSimple : CtxSimple → VarId → BindTySimple → Type :=
  Vegas.HasVar
abbrev EnvSimple (Γ : CtxSimple) : Type := Vegas.Env (Player := Player) simpleExpr Γ

namespace BindTySimple

abbrev base : BindTySimple → BaseTy := Vegas.BindTy.base

end BindTySimple

namespace HasVarSimple

abbrev here {Γ : CtxSimple} {x : VarId} {τ : BindTySimple} : HasVarSimple ((x, τ) :: Γ) x τ :=
  Vegas.HasVar.here

abbrev there {Γ : CtxSimple} {x y : VarId} {τ τ' : BindTySimple}
    (h : HasVarSimple Γ x τ) : HasVarSimple ((y, τ') :: Γ) x τ :=
  Vegas.HasVar.there h

end HasVarSimple

namespace EnvSimple

abbrev empty : EnvSimple [] := Vegas.Env.empty (Player := Player) simpleExpr

abbrev cons {Γ : CtxSimple} {x : VarId} {τ : BindTySimple}
    (v : Val τ.base) (env : EnvSimple Γ) : EnvSimple ((x, τ) :: Γ) :=
  Vegas.Env.cons v env

abbrev get {Γ : CtxSimple} {x : VarId} {τ : BindTySimple}
    (env : EnvSimple Γ) (h : HasVarSimple Γ x τ) : Val τ.base :=
  Vegas.Env.get env h

@[simp] theorem cons_get_here {Γ : CtxSimple} {x : VarId} {τ : BindTySimple}
    {v : Val τ.base} {env : EnvSimple Γ} :
    (EnvSimple.cons v env).get (HasVarSimple.here (Γ := Γ) (x := x) (τ := τ)) = v := by
  exact Vegas.Env.cons_get_here

@[simp] theorem cons_get_there {Γ : CtxSimple} {x y : VarId} {τ σ : BindTySimple}
    {v : Val τ.base} {env : EnvSimple Γ} {h : HasVarSimple Γ y σ} :
    (EnvSimple.cons (x := x) v env).get (HasVarSimple.there h) = env.get h := by
  exact Vegas.Env.cons_get_there

abbrev toView (p : Player) (env : EnvSimple Γ) :
    EnvSimple (Vegas.viewCtx p Γ) :=
  Vegas.Env.toView p env

abbrev toPub (env : EnvSimple Γ) :
    EnvSimple (Vegas.pubCtx Γ) :=
  Vegas.Env.toPub env

abbrev toFlat {Γ : CtxSimple} (env : EnvSimple Γ) :
    EnvSimple (Vegas.flattenCtx Γ) :=
  Vegas.Env.toFlat env

abbrev toFlatView (p : Player) {Γ : CtxSimple} (env : EnvSimple Γ) :
    EnvSimple (Vegas.flattenCtx
      (Vegas.viewCtx p Γ)) :=
  Vegas.Env.toFlatView p env

end EnvSimple

namespace HasVarSimple

abbrev ofViewCtx {p : Player} :
    HasVarSimple (Vegas.viewCtx p Γ) x τ → HasVarSimple Γ x τ :=
  Vegas.HasVar.ofViewCtx (p := p)

abbrev ofPubCtx :
    HasVarSimple (Vegas.pubCtx Γ) x τ → HasVarSimple Γ x τ :=
  Vegas.HasVar.ofPubCtx

abbrev ofPubToView {p : Player} :
    HasVarSimple (Vegas.pubCtx Γ) x τ →
      HasVarSimple (Vegas.viewCtx p Γ) x τ :=
  Vegas.HasVar.ofPubToView (p := p)

abbrev toFlatten :
    HasVarSimple Γ x τ →
      HasVarSimple (Vegas.flattenCtx Γ) x (.pub τ.base) :=
  Vegas.HasVar.toFlatten

abbrev unflatten {Γ : CtxSimple} {x : VarId} {b : BaseTy} :
    HasVarSimple (Vegas.flattenCtx Γ) x (.pub b) →
      (τ : BindTySimple) × HasVarSimple Γ x τ × PLift (τ.base = b) :=
  Vegas.HasVar.unflatten

end HasVarSimple

inductive Expr : CtxSimple → BaseTy → Type where
  | var (x : VarId) (h : HasVarSimple Γ x (.pub b)) : Expr Γ b
  | constInt (i : Int) : Expr Γ .int
  | constBool (b : Bool) : Expr Γ .bool
  | addInt (l r : Expr Γ .int) : Expr Γ .int
  | eqInt (l r : Expr Γ .int) : Expr Γ .bool
  | eqBool (l r : Expr Γ .bool) : Expr Γ .bool
  | andBool (l r : Expr Γ .bool) : Expr Γ .bool
  | notBool (e : Expr Γ .bool) : Expr Γ .bool
  | ite (c : Expr Γ .bool) (t f : Expr Γ b) : Expr Γ b

def evalExpr : Expr Γ b → EnvSimple Γ → Val b
  | .var _ h, env => env.get h
  | .constInt i, _ => i
  | .constBool b, _ => b
  | .addInt l r, env => evalExpr l env + evalExpr r env
  | .eqInt l r, env => decide (evalExpr l env = evalExpr r env)
  | .eqBool l r, env => decide (evalExpr l env = evalExpr r env)
  | .andBool l r, env => evalExpr l env && evalExpr r env
  | .notBool e, env => !(evalExpr e env)
  | .ite c t f, env => if evalExpr c env then evalExpr t env else evalExpr f env

def Expr.weaken {Γ : CtxSimple} {b : BaseTy} {x : VarId} {τ : BindTySimple}
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

theorem evalExpr_weaken {Γ : CtxSimple} {b : BaseTy} {τ : BindTySimple} {x : VarId}
    (e : Expr Γ b) (v : Val τ.base) (env : EnvSimple Γ) :
    evalExpr e.weaken (EnvSimple.cons (x := x) v env) = evalExpr e env := by
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

/-- Extract variable IDs referenced by an expression. -/
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

/-- The current Vegas expression syntax as an instance of the generic
visibility-aware expression interface. -/
instance exprKit : Vegas.ExprKit Player simpleExpr where
  Expr := Expr
  eval := @evalExpr
  deps := @exprVars

end Vegas
