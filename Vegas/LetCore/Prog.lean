import Vegas.LetCore.Env
import Vegas.LetCore.Language

namespace Prog

section Core

variable {L : Language}

attribute [instance] Language.decEqTy Language.decEqVal

/-- Commands that bind a result. -/
abbrev CmdB := L.Ctx → L.Ty → Type

/-- Commands that do not bind a result. -/
abbrev CmdS := L.Ctx → Type

/-- Observation statements: `observe cond` (rejects the current path if false). -/
inductive CmdStmtObs : CmdS where
  | observe {Γ : L.Ctx} (cond : L.Expr Γ L.bool) : CmdStmtObs Γ

/--
Minimal effect-carrier interface for interpreting `Prog` into `M`.
-/
structure Eff (M : Type u → Type v) where
  pure : {α : Type u} → α → M α
  bind : {α β : Type u} → M α → (α → M β) → M β
  fail : {α : Type u} → M α

namespace Eff
def guard {M} (E : Eff M) (b : Bool) : M Unit :=
  if b then E.pure () else E.fail
end Eff

/-- Core program syntax, parameterized by bind-commands `CB` and stmt-commands `CS`. -/
inductive Prog (CB : CmdB) (CS : CmdS) : L.Ctx → L.Ty → Type where
  | ret {Γ τ} (e : L.Expr Γ τ) : Prog CB CS Γ τ
  | letDet {Γ τ τ'} (e : L.Expr Γ τ') (k : Prog CB CS (τ' :: Γ) τ) : Prog CB CS Γ τ
  | doBind {Γ τ τ'} (c : CB Γ τ') (k : Prog CB CS (τ' :: Γ) τ) : Prog CB CS Γ τ
  | doStmt {Γ τ} (s : CS Γ) (k : Prog CB CS Γ τ) : Prog CB CS Γ τ

/-- Deterministic fragment has no bind-commands. -/
abbrev CmdBindD : CmdB (L := L) := fun _ _ => Empty

/-! Deterministic statements: just `observe`.

`observe cond` is a guard: it checks `cond` and, if false, triggers the effect’s `fail`
(i.e. aborts/rejects the current execution according to the chosen `Eff M`). If `cond` is true it
behaves like `skip` and continues. Thus `observe` is "assume" in the *trace-restriction* sense
(keep only executions satisfying `cond`), with the exact meaning of rejection determined by `fail`.

This is not the same as Vegas' surface `where` / blockchain `require`: a failing `require` can have
externally visible consequences (e.g. revert/gas/penalties). If those consequences are modeled as an
explicit outcome, `require` is *not* trace-deletion; only under an abstraction that ignores them may
`where` be compiled/idealized as `observe` (e.g. under a declared fair-play / refinement assumption).
-/
inductive CmdStmtD : CmdS where
  | observe {Γ : L.Ctx} (cond : L.Expr Γ (L.bool)) : CmdStmtD Γ

abbrev DProg := Prog (L := L) (CB := CmdBindD) (CS := CmdStmtD)

namespace DProg
def ret {Γ τ} (e : L.Expr Γ τ) : DProg Γ τ := Prog.ret e
def letDet {Γ τ τ'} (e : L.Expr Γ τ') (k : DProg (τ' :: Γ) τ) : DProg Γ τ :=
  Prog.letDet e k
def observe {Γ τ} (cond : L.Expr Γ (L.bool)) (k : DProg Γ τ) : DProg Γ τ :=
  Prog.doStmt (CmdStmtD.observe cond) k
end DProg

/-- Generic evaluator given handlers for bind-commands and stmt-commands. -/
def evalProg_gen
    {M : Type → Type} (E : Eff M)
    {CB : CmdB} {CS : CmdS}
    (handleBind : {Γ : L.Ctx} → {τ : L.Ty} → CB Γ τ → L.Env Γ → M (L.Val τ))
    (handleStmt : {Γ : L.Ctx} → CS Γ → L.Env Γ → M Unit)
    {Γ τ} : Prog  CB CS Γ τ → L.Env Γ → M (L.Val τ)
  | .ret e, env =>
      E.pure (L.eval e env)
  | .letDet e k, env =>
      evalProg_gen E handleBind handleStmt k (L.eval e env, env)
  | .doBind c k, env =>
      E.bind (handleBind c env) (fun v => evalProg_gen E handleBind handleStmt k (v, env))
  | .doStmt s k, env =>
      E.bind (handleStmt s env) (fun _ => evalProg_gen E handleBind handleStmt k env)

/-- A semantics packages the effect structure + handlers. -/
structure LangSem (CB : CmdB) (CS : CmdS (L := L)) (M : Type → Type) where
  E : Eff M
  handleBind : {Γ : L.Ctx} → {τ : L.Ty} → CB Γ τ → L.Env Γ → M (L.Val τ)
  handleStmt : {Γ : L.Ctx } → CS Γ → L.Env Γ → M Unit

def evalWith {CB CS M} (S : LangSem  CB CS M) {Γ τ} :
    Prog  CB CS Γ τ → L.Env Γ → M (L.Val τ) :=
  evalProg_gen  (CB := CB) (CS := CS) S.E S.handleBind S.handleStmt

-- Convenient simp-lemmas
@[simp] theorem evalWith_ret {CB CS M} (S : LangSem  CB CS M)
    {Γ τ} (e : L.Expr Γ τ) (env : L.Env Γ) :
    evalWith  S (.ret e) env = S.E.pure (L.eval e env) := rfl

@[simp] theorem evalWith_letDet {CB CS M} (S : LangSem CB CS M)
    {Γ τ τ'} (e : L.Expr Γ τ') (k : Prog  CB CS (τ' :: Γ) τ) (env : L.Env Γ) :
    evalWith  S (.letDet e k) env = evalWith  S k (L.eval e env, env) := rfl

@[simp] theorem evalWith_doBind {CB CS M} (S : LangSem (L := L) CB CS M)
    {Γ τ τ'} (c : CB Γ τ') (k : Prog  CB CS (τ' :: Γ) τ) (env : L.Env Γ) :
    evalWith  S (.doBind c k) env =
      S.E.bind (S.handleBind c env) (fun v => evalWith  S k (v, env)) := rfl

@[simp] theorem evalWith_doStmt {CB CS M} (S : LangSem (L := L) CB CS M)
    {Γ τ} (s : CS Γ) (k : Prog  CB CS Γ τ) (env : L.Env Γ) :
    evalWith  S (.doStmt s k) env =
      S.E.bind (S.handleStmt s env) (fun _ => evalWith  S k env) := rfl

/-- Option effect carrier. -/
def EffOption : Eff Option where
  pure := fun x => some x
  bind := fun mx f => mx.bind f
  fail := none

/-- Deterministic semantics into Option: observe fails when condition is false. -/
def DetOptionSem : LangSem (L := L) (CmdBindD) (CmdStmtD) Option where
  E := EffOption
  handleBind := fun c => nomatch c
  handleStmt
    | .observe cond, env =>
        Eff.guard EffOption (L.toBool (L.eval cond env))

def evalProgOption {Γ τ} : DProg Γ τ → L.Env Γ → Option (L.Val τ) :=
  evalWith  (DetOptionSem )

def handleObserveOption {Γ} (cond : L.Expr Γ (L.bool)) (env : L.Env Γ) : Option Unit :=
  Eff.guard EffOption (L.toBool (L.eval cond env))

end Core

end Prog
