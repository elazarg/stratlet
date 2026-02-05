import Vegas.Env

/-- The interface required to instantiate the Vegas calculus. -/
structure Language where
  /-- The universe of types (e.g., int, bool, tensor, etc.) -/
  Ty : Type
  /-- Decidable equality for types is needed for context manipulation -/
  decEqTy : DecidableEq Ty

  /-- The interpretation of types into runtime values -/
  Val : Ty → Type
  /-- We need decidable equality on values for discrete probability support -/
  decEqVal {τ : Ty} : DecidableEq (Val τ)

  /-- The abstract boolean type, required for `observe` conditions -/
  bool : Ty
  /-- Isomorphism between the runtime boolean value and Lean's Bool -/
  toBool : Val bool → Bool
  fromBool : Bool → Val bool

  /-- The Expression syntax, indexed by Context and Return Type -/
  Expr : Env.Ctx → Ty → Type

  /-- The Evaluation function -/
  eval {Γ} {τ : Ty} : Expr Γ τ → Env.Env Val Γ → Val τ

attribute [instance] Language.decEqTy Language.decEqVal

namespace Language

abbrev Ctx (L : Language) : Type := Env.Ctx (Ty := L.Ty)
abbrev Env (L : Language) (Γ : L.Ctx) : Type := Env.Env (Val := L.Val) Γ

end Language


/-- What ProgCore-lemmas need from expressions beyond `Language`. -/
structure ExprLaws (L : Language) where
  weaken :
    {Γ : Env.Ctx (Ty := L.Ty)} → {τ τ' : L.Ty} →
      L.Expr Γ τ → L.Expr (τ' :: Γ) τ

  eval_weaken :
    ∀ {Γ : Env.Ctx (Ty := L.Ty)} {τ τ'} (e : L.Expr Γ τ)
      (env : Env.Env (Val := L.Val) Γ) (v : L.Val τ'),
      L.eval (weaken (Γ := Γ) (τ := τ) (τ' := τ') e) (v, env) = L.eval e env

  constBool :
    {Γ : Env.Ctx (Ty := L.Ty)} → Bool → L.Expr Γ L.bool

  andBool :
    {Γ : Env.Ctx (Ty := L.Ty)} →
      L.Expr Γ L.bool → L.Expr Γ L.bool → L.Expr Γ L.bool

  toBool_eval_constBool :
    ∀ {Γ : Env.Ctx (Ty := L.Ty)} (b : Bool) (env : Env.Env (Val := L.Val) Γ),
      L.toBool (L.eval (constBool (Γ := Γ) b) env) = b

  toBool_eval_andBool :
    ∀ {Γ : Env.Ctx (Ty := L.Ty)} (c₁ c₂ : L.Expr Γ L.bool)
      (env : Env.Env (Val := L.Val) Γ),
      L.toBool (L.eval (andBool (Γ := Γ) c₁ c₂) env)
        =
      (L.toBool (L.eval c₁ env) && L.toBool (L.eval c₂ env))

  /-- variable expressions -/
  var : {Γ : Env.Ctx} → Env.Var Γ τ → L.Expr Γ τ

  /-- evaluation of variable expressions -/
  eval_var :
    ∀ {Γ τ} (x : Env.Var Γ τ) (env : Env.Env L.Val Γ),
      L.eval (var x) env = env.get x

namespace ExprLaws

abbrev vz (EL : ExprLaws L) {Γ : Env.Ctx (Ty := L.Ty)} {τ : L.Ty} :
    L.Expr (τ :: Γ) τ :=
  EL.var Env.Var.vz

@[simp] theorem eval_vz (EL : ExprLaws L) {Γ} {τ} (v : L.Val τ) (env : Env.Env (Val := L.Val) Γ) :
    L.eval (EL.vz (L := L) (Γ := Γ) (τ := τ)) (v, env) = v := by
  simpa [ExprLaws.vz] using (EL.eval_var (L := L) (x := (Env.Var.vz : Env.Var (τ :: Γ) τ)) (env := (v, env)))

end ExprLaws
