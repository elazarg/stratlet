import Vegas.Env
import Vegas.Expr

namespace ProgCore

/-- Commands that bind a result. -/
abbrev CmdB := Ctx → Ty → Type

/-- Commands that do not bind a result. -/
abbrev CmdS := Ctx → Type

inductive CmdStmtObs : CmdS where
  | observe {Γ} (cond : Expr Γ .bool) : CmdStmtObs Γ
deriving Repr

/--
`Eff M` is the minimal "effect carrier" interface needed to interpret `Prog` into some semantic
domain `M`.

Why this exists (instead of using `Monad` / `Alternative` typeclasses):

* `evalProg_gen` only needs three operations: `pure` (return), `bind` (sequence), and `fail`
  (hard rejection for `observe`). No other structure is required to define evaluation.
* Many intended semantic domains are awkward to express as lawful Lean typeclasses under
  definitional equality (e.g. list-based weighted distributions, game/optimization evaluators),
  and we do not want the core calculus to depend on typeclass inference or monad laws.
* Keeping the interface explicit makes the "algebraic effects" separation clear:
  `Prog` is syntax; a `LangSem` provides handlers into a chosen `M`; `Eff` supplies just enough
  structure on `M` to compose handler results.

In short: `Eff` avoids committing the core calculus to a particular library hierarchy or set of
laws, while remaining expressive enough to plug in `Option`, weighted distributions, expectimax,
equilibrium solvers, etc.
-/
structure Eff (M : Type u → Type v) where
  pure : {α : Type u} → α → M α
  bind : {α β : Type u} → M α → (α → M β) → M β
  fail : {α : Type u} → M α

namespace Eff
def guard {M} (E : Eff M) (b : Bool) : M Unit :=
  if b then E.pure () else E.fail
end Eff

inductive Prog (CB : CmdB) (CS : CmdS) : Ctx → Ty → Type where
  | ret {Γ τ} (e : Expr Γ τ) : Prog CB CS Γ τ
  | letDet {Γ τ τ'} (e : Expr Γ τ') (k : Prog CB CS (τ' :: Γ) τ) : Prog CB CS Γ τ
  | doBind {Γ τ τ'} (c : CB Γ τ') (k : Prog CB CS (τ' :: Γ) τ) : Prog CB CS Γ τ
  | doStmt {Γ τ} (s : CS Γ) (k : Prog CB CS Γ τ) : Prog CB CS Γ τ

abbrev CmdBindD : CmdB := fun _ _ => Empty

inductive CmdStmtD : CmdS where
  | observe {Γ} (cond : Expr Γ .bool) : CmdStmtD Γ
deriving Repr

abbrev DProg := Prog CmdBindD CmdStmtD

namespace DProg

def ret {Γ τ} (e : Expr Γ τ) : DProg Γ τ := Prog.ret e

def letDet {Γ τ τ'} (e : Expr Γ τ') (k : DProg (τ' :: Γ) τ) : DProg Γ τ := Prog.letDet e k

def observe {Γ τ} (cond : Expr Γ .bool) (k : DProg Γ τ) : DProg Γ τ :=
  Prog.doStmt (CmdStmtD.observe cond) k

end DProg

def evalProg_gen
    {M : Type → Type} (E : Eff M)
    {CB : CmdB} {CS : CmdS}
    (handleBind : {Γ : Ctx} → {τ : Ty} → CB Γ τ → Env Γ → M (Val τ))
    (handleStmt : {Γ : Ctx} → CS Γ → Env Γ → M Unit)
    {Γ τ} : Prog CB CS Γ τ → Env Γ → M (Val τ)
  | .ret e, env =>
      E.pure (evalExpr e env)
  | .letDet e k, env =>
      evalProg_gen E handleBind handleStmt k (evalExpr e env, env)
  | .doBind c k, env =>
      E.bind (handleBind c env) (fun v => evalProg_gen E handleBind handleStmt k (v, env))
  | .doStmt s k, env =>
      E.bind (handleStmt s env) (fun _ => evalProg_gen E handleBind handleStmt k env)

structure LangSem (CB : CmdB) (CS : CmdS) (M : Type → Type) where
  E : Eff M
  handleBind : {Γ : Ctx} → {τ : Ty} → CB Γ τ → Env Γ → M (Val τ)
  handleStmt : {Γ : Ctx} → CS Γ → Env Γ → M Unit

def evalWith {CB CS M} (S : LangSem CB CS M) {Γ τ} :
    Prog CB CS Γ τ → Env Γ → M (Val τ) :=
  evalProg_gen (CB := CB) (CS := CS) S.E S.handleBind S.handleStmt

@[simp] theorem evalWith_ret{CB CS M}  (S : LangSem CB CS M) (e : Expr Γ τ) (env : Env Γ) :
    evalWith S (.ret e) env = S.E.pure (evalExpr e env) := rfl

@[simp] theorem  evalWith_letDet{CB CS M}  (S : LangSem CB CS M) (e : Expr Γ τ')
    (k : Prog CB CS (τ' :: Γ) τ) (env : Env Γ) :
    evalWith S (.letDet e k) env = evalWith S k (evalExpr e env, env) := rfl

@[simp] theorem  evalWith_doBind{CB CS M}  (S : LangSem CB CS M) (c : CB Γ τ')
    (k : Prog CB CS (τ' :: Γ) τ) (env : Env Γ) :
    evalWith S (.doBind c k) env =
      S.E.bind (S.handleBind c env) (fun v => evalWith S k (v, env)) := rfl

@[simp] theorem  evalWith_doStmt{CB CS M}  (S : LangSem CB CS M) (s : CS Γ)
    (k : Prog CB CS Γ τ) (env : Env Γ) :
    evalWith S (.doStmt s k) env =
      S.E.bind (S.handleStmt s env) (fun _ => evalWith S k env) := rfl

def EffOption : Eff Option where
  pure := fun x => some x
  bind := fun mx f => mx.bind f
  fail := none

def DetOptionSem : LangSem CmdBindD CmdStmtD Option where
  E := EffOption
  handleBind := fun c => nomatch c
  handleStmt
    | .observe cond, env =>
        if evalExpr cond env then EffOption.pure () else EffOption.fail

def evalProgOption {Γ τ} : DProg Γ τ → Env Γ → Option (Val τ) :=
  evalWith DetOptionSem

end ProgCore
