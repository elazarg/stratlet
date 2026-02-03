import Mathlib.Data.Rat.Init
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic

import Vegas.WDist
import Vegas.ProgCore
import Vegas.Env
import Vegas.Expr
import Vegas.ProbLet

namespace PartialInfoLet

/-! ## Partial information via explicit views (no changes to ProgCore/ProbLet) -/

abbrev Player := Nat

/--
A `View Γ` is an explicit environment slice:
- a visible context `Δ`
- a projection `Env Γ → Env Δ`

No players or visibility tags appear in the core calculus; views are command payloads.

View is the only mechanism for epistemic restriction;
we do not model belief, only information availability.
-/
structure View (Γ : Ctx) where
  Δ : Ctx
  proj : Env Γ → Env Δ

/-- Action sets offered at a choice point; parameterized by the visible env `Env v.Δ`. -/
abbrev Act {Γ : Ctx} (v : View Γ) (τ : Ty) := Env v.Δ → List (Val τ)

/-! ## 1) Strategic bind-commands: choose / commit / reveal

In the current formulation, commit can only commit to values already in v.Δ;
hence it does not express secrecy. It only expresses a protocol step / constraint check.
A secrecy-capable commit will require committing to data in Γ not necessarily in v.Δ,
and/or an explicit commitment store / randomness.

Placeholder: commit/reveal currently do not hide; they only enforce a deterministic relation
within visible state. A secrecy-capable version will require
(a) committing to values not in view,
(b) randomness/salts, and likely
(c) an explicit commitment store or token/value linkage not computable from public info alone.
 -/
inductive CmdBindS : ProgCore.CmdB where
  | choose {Γ τ}  (who : Player) (v : View Γ) (A : Act v τ) : CmdBindS Γ τ
  | commit {Γ τ}  (who : Player) (v : View Γ) (x : Var v.Δ τ) : CmdBindS Γ .int
  | reveal {Γ τ}  (who : Player) (v : View Γ) (c : Var v.Δ .int) (x : Var v.Δ τ) : CmdBindS Γ τ

abbrev CmdStmtS := ProgCore.CmdStmtObs
abbrev SProg := ProgCore.Prog CmdBindS CmdStmtS

namespace SProg
def ret {Γ τ} (e : Expr Γ τ) : SProg Γ τ := ProgCore.Prog.ret e

def letDet {Γ τ τ'} (e : Expr Γ τ') (k : SProg (τ' :: Γ) τ) : SProg Γ τ :=
  ProgCore.Prog.letDet e k

def doStmt {Γ τ} (s : CmdStmtS Γ) (k : SProg Γ τ) : SProg Γ τ :=
  ProgCore.Prog.doStmt s k

def doBind {Γ τ τ'} (c : CmdBindS Γ τ') (k : SProg (τ' :: Γ) τ) : SProg Γ τ :=
  ProgCore.Prog.doBind c k

def observe {Γ τ} (cond : Expr Γ .bool) (k : SProg Γ τ) : SProg Γ τ :=
  .doStmt (.observe cond) k
end SProg

/-! ## 2) Profile: strategies only for `choose` -/

/--
A profile supplies behavior only for `choose`.

`commit` / `reveal` are protocol-level steps with deterministic semantics here.
(You can later refine commit schemes without touching ProgCore/ProbLet.)

A profile is a family of kernels indexed by (who, view, actionset);
this is behavioral (history-dependent) by construction because Env v.Δ can contain history.
-/
structure Profile where
  choose :
    {Γ : Ctx} → {τ : Ty} →
    (who : Player) → (v : View Γ) → (A : Act v τ) →
    -- strategy sees exactly the projected environment:
    Env v.Δ → WDist (Val τ)

/-! ## 3) Deterministic commitment check (placeholder commitment scheme)

We need *some* relation between token and revealed value to make `reveal` meaningful.
This is a minimal, purely-functional “tag”:
- for Int: token = x + who
- for Bool: token = (if b then 1 else 0) + who

This is NOT cryptographic; it’s a structural placeholder enabling the protocol shape
(commit returns token; reveal checks it).
-/

-- 1. Map your Ty enum to actual Lean Types
def Ty.interp : Ty → Type
  | .int  => Int
  | .bool => Bool

-- Helper for the bool conversion
def boolToInt : Bool → Int
  | true  => 1
  | false => 0

-- 2. Define the function using dependent types
def commitTag (who : Player) {τ : Ty} (x : Val τ) : Int :=
  match τ with
  | .int  => x + (who : Int)
  | .bool => (if x then 1 else 0) + (who : Int)

/-! ## 4) Denotational semantics for strategic programs (WDist) -/

def EffWDist : ProgCore.Eff WDist := ProbLet.EffWDist

def StratSem (σ : Profile) : ProgCore.LangSem CmdBindS CmdStmtS WDist where
  E := EffWDist
  handleBind
    | .choose who v A, env =>
        σ.choose who v A (v.proj env)
    | .commit who v x, env =>
        let obs : Env v.Δ := v.proj env
        let xv  : Val _ := Env.get obs x
        WDist.pure (commitTag who xv)
    | .reveal (τ := τ) who v c x, env =>
        let obs : Env v.Δ := v.proj env
        let cv  : Int := Env.get obs c
        let xv  : Val τ := Env.get obs x
        if cv == commitTag who xv then
          WDist.pure xv
        else
          WDist.zero
  handleStmt
    | .observe cond, env =>
        if evalExpr cond env then WDist.pure () else WDist.zero

def evalS {Γ τ} (σ : Profile) : SProg Γ τ → Env Γ → WDist (Val τ) :=
  ProgCore.evalWith (StratSem σ)

/-! ## 5) Compilation to ProbLet by fixing a profile -/

/--
Compile a strategic program to a probabilistic program:

- `choose who v A` becomes `sample (σ.choose who v A ∘ v.proj)`
- `commit` / `reveal` become deterministic kernels (Dirac/empty) implemented as `sample` too

This keeps ProbLet completely unchanged and preserves the same commutation proof style
as FullInfoLet.

Compilation uses sample for both strategic and protocol binds;
this is intentional (one bind-command interface), but later we may want to separate
‘nature randomness’ from ‘strategic randomness’ to control correlation assumptions.
-/
def toProb (σ : Profile) : SProg Γ τ → ProbLet.PProg Γ τ
  | .ret e        => .ret e
  | .letDet e k   => .letDet e (toProb σ k)
  | .doStmt s k   => .doStmt s (toProb σ k)
  | .doBind c k   =>
      match c with
      | .choose who v A =>
          let K : ProbLet.Kernel Γ _ := fun env => σ.choose who v A (v.proj env)
          .doBind (.sample K) (toProb σ k)
      | .commit who v x =>
          let K : ProbLet.Kernel Γ .int := fun env =>
            let obs : Env v.Δ := v.proj env
            let xv : Val _ := Env.get obs x
            WDist.pure (commitTag who xv)
          .doBind (.sample K) (toProb σ k)
      | .reveal (τ := τ') who v c x =>
          let K : ProbLet.Kernel Γ τ' := fun env =>
            let obs : Env v.Δ := v.proj env
            let cv  : Int := Env.get obs c
            let xv  : Val τ' := Env.get obs x
            if cv == commitTag who xv then WDist.pure xv else WDist.zero
          .doBind (.sample K) (toProb σ k)

/-- Commutation theorem: evalS under σ coincides with ProbLet eval of the compilation. -/
theorem evalS_eq_evalP_toProb {Γ τ} (σ : Profile) (p : SProg Γ τ) (env : Env Γ) :
    evalS σ p env = ProbLet.evalP (toProb σ p) env := by
  simp only [evalS, StratSem, EffWDist, ProbLet.evalP, ProbLet.ProbSem]
  induction p with
  | ret e =>
      simp [toProb]
  | letDet e k ih =>
      simp [toProb]
      simp_all only [beq_iff_eq]
  | doStmt s k ih =>
      simp [toProb, ProgCore.evalWith_doStmt]
      simp_all only [beq_iff_eq]
      rfl
  | doBind c k ih =>
      cases c with
      | choose who v A =>
          simp [toProb, ProgCore.evalWith_doBind]
          simp_all only [beq_iff_eq]
      | commit who v x =>
          simp [toProb, ProgCore.evalWith_doBind]
          simp_all only [beq_iff_eq]
      | reveal who v c x =>
          simp [toProb, ProgCore.evalWith_doBind]
          simp_all only [beq_iff_eq]

/-! ## 6) Behavioral interpreter (optional but useful) -/

inductive Beh : Ty → Type where
  | ret  {τ} (v : Val τ) : Beh τ
  | fail {τ} : Beh τ
  | choose {τ τ'} (who : Player)
      (actions : List (Val τ'))
      (dist    : Profile → WDist (Val τ'))
      (k       : Val τ' → Beh τ)
      : Beh τ
  | commit {τ} (who : Player)
      (tok : Int)
      (k   : Int → Beh τ)
      : Beh τ
  | reveal {τ τ'} (who : Player)
      (ok  : Bool)
      (v   : Val τ')
      (k   : Val τ' → Beh τ)
      : Beh τ

def behEval {Γ τ} : SProg Γ τ → Env Γ → Beh τ
  | .ret e, env =>
      Beh.ret (evalExpr e env)
  | .letDet e k, env =>
      behEval k (evalExpr e env, env)
  | .doStmt (.observe cond) k, env =>
      if evalExpr cond env then behEval k env else Beh.fail
  | .doBind (.choose who v A) k, env =>
      let obs := v.proj env
      let acts := A obs
      let distThunk : Profile → WDist (Val _) := fun σ => σ.choose who v A obs
      Beh.choose who acts distThunk (fun a => behEval k (a, env))
  | .doBind (.commit (τ := τ') who v x) k, env =>
      let obs : Env v.Δ := v.proj env
      let xv : Val τ' := Env.get obs x
      let tok := commitTag who xv
      Beh.commit who tok (fun t => behEval k (t, env))
  | .doBind (.reveal (τ := τ') who v c x) k, env =>
      let obs : Env v.Δ := v.proj env
      let cv : Int := Env.get obs c
      let xv : Val τ' := Env.get obs x
      let ok : Bool := (cv == commitTag who xv)
      if ok then
        Beh.reveal who true xv (fun r => behEval k (r, env))
      else
        Beh.reveal who false xv (fun _ => Beh.fail)

def runBeh {τ} (σ : Profile) : Beh τ → WDist (Val τ)
  | .ret v => WDist.pure v
  | .fail => []
  | .choose _ _ d k => WDist.bind (d σ) (fun a => runBeh σ (k a))
  | .commit _ tok k => runBeh σ (k tok)
  | .reveal _ ok v k =>
      if ok then runBeh σ (k v) else []

@[simp] lemma EffWDist_pure {α} (x : α) :
    EffWDist.pure x = (WDist.pure x : WDist α) := rfl

@[simp] lemma EffWDist_fail {α} :
    (EffWDist.fail : WDist α) = (WDist.zero : WDist α) := rfl

@[simp] lemma EffWDist_bind {α β} (xs : WDist α) (f : α → WDist β) :
    EffWDist.bind xs f = WDist.bind xs f := rfl


@[simp] lemma StratSem_handleStmt_observe (σ : Profile)
    (cond : Expr Γ .bool) (env : Env Γ) :
    (StratSem σ).handleStmt (ProgCore.CmdStmtObs.observe (Γ := Γ) cond) env
      =
    (if evalExpr cond env then WDist.pure () else WDist.zero) := rfl

@[simp] lemma StratSem_handleBind_choose (σ : Profile)
    (who : Player) (v : View Γ) (A : Act v τ) (env : Env Γ) :
    (StratSem σ).handleBind (CmdBindS.choose (Γ := Γ) (τ := τ) who v A) env
      =
    σ.choose who v A (v.proj env) := rfl

@[simp] lemma StratSem_handleBind_commit (σ : Profile)
    (who : Player) (v : View Γ) (x : Var v.Δ τ) (env : Env Γ) :
    (StratSem σ).handleBind (CmdBindS.commit (Γ := Γ) (τ := τ) who v x) env
      =
    WDist.pure (commitTag who ((v.proj env).get x)) := rfl

@[simp] lemma StratSem_handleBind_reveal (σ : Profile)
    (who : Player) (v : View Γ) (c : Var v.Δ .int) (x : Var v.Δ τ) (env : Env Γ) :
    (StratSem σ).handleBind (CmdBindS.reveal (Γ := Γ) (τ := τ) who v c x) env
      =
    (if (v.proj env).get c == commitTag who ((v.proj env).get x)
     then WDist.pure ((v.proj env).get x)
     else WDist.zero) := rfl

theorem runBeh_behEval_eq_evalS {Γ τ} (σ : Profile) (p : SProg Γ τ) (env : Env Γ) :
    runBeh σ (behEval p env) = evalS σ p env := by
  induction p with
  | ret e => rfl
  | letDet e k ih => simpa [behEval, evalS] using ih (evalExpr e env, env)
  | doStmt s k ih =>
      cases s with
      | observe cond =>
          -- reduce both sides to an if on the same condition
          by_cases h : evalExpr cond env
          · -- cond true: both continue
            simp only [behEval, evalS,
                       ProgCore.evalWith_doStmt, StratSem_handleStmt_observe, h, reduceIte]
            rw [ih]
            change ProgCore.evalWith (StratSem σ) k env =
              WDist.bind (WDist.pure ()) (fun _ => ProgCore.evalWith (StratSem σ) k env)
            simp [WDist.bind_pure]
          · -- cond false: both reject (mass 0)
            simp [behEval, runBeh, evalS, h, StratSem, EffWDist]
            simp_all only [Bool.not_eq_true]
            rfl
  | doBind c k ih =>
      cases c with
      | choose who v A =>
          -- LHS = bind (σ.choose ...) (fun a => runBeh σ (behEval k (a, env)))
          -- RHS = bind (σ.choose ...) (fun a => evalS σ k (a, env))
          simp only [behEval]
          -- `simp` leaves an equality of binds; prove pointwise with funext + IH
          refine congrArg (fun f => WDist.bind (σ.choose who v A (v.proj env)) f) ?_
          funext a
          -- IH expects env : Env (_ :: Γ), i.e. (a, env)
          simpa using ih (a, env)
      | commit who v x =>
          -- `commit` is deterministic: both sides just extend env with the token then continue
          -- simp uses WDist.bind_pure to drop the bind on RHS
          simp only [behEval, runBeh]
          set tok : Int := commitTag who ((v.proj env).get x)
          rw [ih (tok, env)]
          change ProgCore.evalWith (StratSem σ) k (tok, env) =
            WDist.bind (WDist.pure tok) (fun a => ProgCore.evalWith (StratSem σ) k (a, env))
          simp
      | reveal who v c x =>
          -- split on the reveal check (same boolean on both sides)
          by_cases h :
              (Env.get (v.proj env) c) == commitTag who (Env.get (v.proj env) x)
          · -- success: both extend env with revealed value and continue
            simp only [behEval, h, reduceIte, runBeh, evalS]
            set xv : Val _ := (v.proj env).get x
            rw [ih (xv, env)]
            have hxv : (v.proj env).get x = xv := rfl
            simp only [ProgCore.evalWith_doBind, StratSem_handleBind_reveal, hxv, h]
            change ProgCore.evalWith (StratSem σ) k (xv, env) =
              WDist.bind (WDist.pure xv) (fun a => ProgCore.evalWith (StratSem σ) k (a, env))
            simp
          · -- failure: both return []
            simp [behEval, evalS, h]
            rfl


theorem runBeh_behEval_eq_evalP_toProb (σ : Profile) (p : SProg Γ τ) (env : Env Γ) :
    runBeh σ (behEval p env) = ProbLet.evalP (toProb σ p) env := by
  simpa [runBeh_behEval_eq_evalS] using (evalS_eq_evalP_toProb (Γ := Γ) (τ := τ) σ p env)

/-! ## 7) Tiny example -/

namespace Examples

def Γ0 : Ctx := []

def idView (Γ : Ctx) : View Γ where
  Δ := Γ
  proj := fun env => env

def uniformProfile : Profile where
  choose := by
    intro Γ τ who v A obs
    let xs := A obs
    match xs.length with
    | 0 => exact []
    | n =>
        let w : W := (1 : W) / (n : W)
        exact xs.map (fun a => (a, w))

def A24 : Act (v := idView Γ0) .int := fun _ => [2, 3, 4]

def Γ1 : Ctx := Ty.int :: Γ0          -- after choose
def Γ2 : Ctx := Ty.int :: Γ1          -- after commit (token :: x :: Γ0)

-- variables in Γ1
def xVar : Var Γ1 .int := Var.vz

-- variables in Γ2
def cVar : Var Γ2 .int := Var.vz
def xVar2 : Var Γ2 .int := Var.vs Var.vz

def pEx : SProg Γ0 .bool :=
  SProg.doBind (.choose 0 (idView Γ0) A24)
    (SProg.doBind (.commit 0 (idView Γ1) xVar)
      (SProg.doBind (.reveal 0 (idView Γ2) cVar xVar2)
        -- after reveal, the revealed value is bound at Var.vz
        (SProg.ret (Expr.eqInt (Expr.var Var.vz) (Expr.constInt 3)))))

end Examples


end PartialInfoLet
