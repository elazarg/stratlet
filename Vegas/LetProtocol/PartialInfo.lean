import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic

import Vegas.LetProb.WDist
import Vegas.LetCore.Prog
import Vegas.LetCore.Env
import Vegas.LetCore.Concrete
import Vegas.LetProb.Prob
import Vegas.Defs

namespace PartialInfo

open Defs

/-! ## Partial information via explicit views (no changes to ProgCore/ProbLet) -/

/-- The partial-info calculus is specialized to BasicLang (concrete int/bool types),
since the commit/reveal mechanism relies on concrete Ty constructors. -/
abbrev L : Language := BasicLang

/--
A `View Γ` is an explicit environment slice:
- a visible context `Δ`
- a projection `L.Env Γ → L.Env Δ`

No players or visibility tags appear in the core calculus; views are command payloads.

View is the only mechanism for epistemic restriction;
we do not model belief, only information availability.
-/
structure View (Γ : L.Ctx) where
  Δ : L.Ctx
  proj : L.Env Γ → L.Env Δ

/-- Action sets offered at a choice point; parameterized by the visible env `L.Env v.Δ`. -/
abbrev Act {Γ : L.Ctx} (v : View Γ) (τ : L.Ty) := L.Env v.Δ → List (Val τ)

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
inductive CmdBindS : Prog.CmdB where
  | choose {Γ τ}  (who : Player) (v : View Γ) (A : Act v τ) : CmdBindS Γ τ
  | commit {Γ τ}  (who : Player) (v : View Γ) (x : Env.Var v.Δ τ) : CmdBindS Γ .int
  | reveal {Γ τ}  (who : Player) (v : View Γ)
      (c : Env.Var v.Δ .int) (x : Env.Var v.Δ τ) : CmdBindS Γ τ

abbrev CmdStmtS := Prog.CmdStmtObs (L := L)
abbrev SProg := Prog.Prog CmdBindS CmdStmtS

namespace SProg
def ret {Γ τ} (e : L.Expr Γ τ) : SProg Γ τ := Prog.Prog.ret e

def letDet {Γ τ τ'} (e : L.Expr Γ τ') (k : SProg (τ' :: Γ) τ) : SProg Γ τ :=
  Prog.Prog.letDet e k

def doStmt {Γ τ} (s : CmdStmtS Γ) (k : SProg Γ τ) : SProg Γ τ :=
  Prog.Prog.doStmt s k

def doBind {Γ τ τ'} (c : CmdBindS Γ τ') (k : SProg (τ' :: Γ) τ) : SProg Γ τ :=
  Prog.Prog.doBind c k

def observe {Γ τ} (cond : L.Expr Γ .bool) (k : SProg Γ τ) : SProg Γ τ :=
  .doStmt (.observe cond) k
end SProg

/-! ## 2) Profile: strategies only for `choose` -/

/--
A profile supplies behavior only for `choose`.

`commit` / `reveal` are protocol-level steps with deterministic semantics here.
(You can later refine commit schemes without touching ProgCore/Prob.)

A profile is a family of kernels indexed by (who, view, actionset);
this is behavioral (history-dependent) by construction because L.Env v.Δ can contain history.
-/
structure Profile where
  choose :
    {Γ : L.Ctx} → {τ : L.Ty} →
    (who : Player) → (v : View Γ) → (A : Act v τ) →
    -- strategy sees exactly the projected environment:
    L.Env v.Δ → WDist (Val τ)

/-! ## 3) Deterministic commitment check (placeholder commitment scheme)

We need *some* relation between token and revealed value to make `reveal` meaningful.
This is a minimal, purely-functional "tag":
- for Int: token = x + who
- for Bool: token = (if b then 1 else 0) + who

This is NOT cryptographic; it's a structural placeholder enabling the protocol shape
(commit returns token; reveal checks it).
-/

-- Define the function using dependent types
def commitTag (who : Player) {τ : L.Ty} (x : Val τ) : Int :=
  match τ with
  | .int  => x + (who : Int)
  | .bool => (if x then 1 else 0) + (who : Int)

/-! ## Denotational semantics for strategic programs (WDist) -/

abbrev EffWDist : Prog.Eff WDist := Prob.EffWDist

@[simp] lemma EffWDist_pure {α} (x : α) :
    EffWDist.pure x = (WDist.pure x : WDist α) := rfl

@[simp] lemma EffWDist_fail {α} :
    (EffWDist.fail : WDist α) = (WDist.zero : WDist α) := rfl

@[simp] lemma EffWDist_bind {α β} (xs : WDist α) (f : α → WDist β) :
    EffWDist.bind xs f = WDist.bind xs f := rfl

variable (σ : Profile)

def StratSem : Prog.LangSem CmdBindS CmdStmtS WDist where
  E := EffWDist
  handleBind
    | .choose who v A, env =>
        σ.choose who v A (v.proj env)
    | .commit who v x, env =>
        let obs : L.Env v.Δ := v.proj env
        let xv  : Val _ := obs.get x
        WDist.pure (commitTag who xv)
    | .reveal (τ := τ) who v c x, env =>
        let obs : L.Env v.Δ := v.proj env
        let cv  : Int := obs.get c
        let xv  : Val τ := obs.get x
        if cv == commitTag who xv then
          WDist.pure xv
        else
          WDist.zero
  handleStmt
    | .observe cond, env =>
        if L.toBool (L.eval cond env) then .pure () else .zero

def evalS {Γ τ} : SProg Γ τ → L.Env Γ → WDist (Val τ) :=
  Prog.evalWith (StratSem σ)

/-! ## 5) Compilation to ProbLet by fixing a profile -/

/--
Compile a strategic program to a probabilistic program:

- `choose who v A` becomes `sample (σ.choose who v A ∘ v.proj)`
- `commit` / `reveal` become deterministic kernels (Dirac/empty) implemented as `sample` too

This keeps ProbLet completely unchanged and preserves the same commutation proof style
as FullInfo.

Compilation uses sample for both strategic and protocol binds;
this is intentional (one bind-command interface), but later we may want to separate
‘nature randomness’ from ‘strategic randomness’ to control correlation assumptions.
-/
def toProb (σ : Profile) : SProg Γ τ → Prob.PProg Γ τ
  | .ret e        => .ret e
  | .letDet e k   => .letDet e (toProb σ k)
  | .doStmt s k   => .doStmt s (toProb σ k)
  | .doBind c k   =>
      match c with
      | .choose who v A =>
          let K : Prob.Kernel Γ _ := fun env => σ.choose who v A (v.proj env)
          .doBind (.sample K) (toProb σ k)
      | .commit who v x =>
          let K : Prob.Kernel Γ .int := fun env =>
            let obs : L.Env v.Δ := v.proj env
            let xv : Val _ := obs.get x
            WDist.pure (commitTag who xv)
          .doBind (.sample K) (toProb σ k)
      | .reveal (τ := τ') who v c x =>
          let K : Prob.Kernel Γ τ' := fun env =>
            let obs : L.Env v.Δ := v.proj env
            let cv  : Int := obs.get c
            let xv  : Val τ' := obs.get x
            if cv == commitTag who xv then WDist.pure xv else WDist.zero
          .doBind (.sample K) (toProb σ k)

/-- Commutation theorem: evalS under σ coincides with ProbLet eval of the compilation. -/
theorem evalS_eq_evalP_toProb {Γ τ} (p : SProg Γ τ) (env : L.Env Γ) :
    evalS σ p env = Prob.evalP (toProb σ p) env := by
  simp only [evalS, StratSem, EffWDist, Prob.evalP, Prob.ProbSem]
  induction p with
  | ret e =>
      simp [toProb]
  | letDet e k ih =>
      simp [toProb]
      simp_all only [beq_iff_eq]
  | doStmt s k ih =>
      cases s with
      | observe cond =>
          simp only [toProb, Prog.evalWith_doStmt]
          congr 1
          funext _
          exact ih _
  | doBind c k ih =>
      cases c with
      | choose who v A =>
          simp [toProb, Prog.evalWith_doBind]
          simp_all only [beq_iff_eq]
      | commit who v x =>
          simp [toProb, Prog.evalWith_doBind]
          simp_all only [beq_iff_eq]
      | reveal who v c x =>
          simp [toProb, Prog.evalWith_doBind]
          simp_all only [beq_iff_eq]

/-! ## 6) Behavioral interpreter (optional but useful) -/

inductive Beh : L.Ty → Type where
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

def behEval {Γ τ} : SProg Γ τ → L.Env Γ → Beh τ
  | .ret e, env =>
      Beh.ret (L.eval e env)
  | .letDet e k, env =>
      behEval k (L.eval e env, env)
  | .doStmt (.observe cond) k, env =>
      if L.toBool (L.eval cond env) then behEval k env else Beh.fail
  | .doBind (.choose who v A) k, env =>
      let obs := v.proj env
      let acts := A obs
      let distThunk : Profile → WDist (Val _) := fun σ => σ.choose who v A obs
      Beh.choose who acts distThunk (fun a => behEval k (a, env))
  | .doBind (.commit (τ := τ') who v x) k, env =>
      let obs : L.Env v.Δ := v.proj env
      let xv : Val τ' := obs.get x
      let tok := commitTag who xv
      Beh.commit who tok (fun t => behEval k (t, env))
  | .doBind (.reveal (τ := τ') who v c x) k, env =>
      let obs : L.Env v.Δ := v.proj env
      let cv : Int := obs.get c
      let xv : Val τ' := obs.get x
      let ok : Bool := (cv == commitTag who xv)
      if ok then
        Beh.reveal who true xv (fun r => behEval k (r, env))
      else
        Beh.reveal who false xv (fun _ => Beh.fail)

def runBeh (σ : Profile) {τ} : Beh τ → WDist (Val τ)
  | .ret v => WDist.pure v
  | .fail => .zero
  | .choose _ _ d k => WDist.bind (d σ) (fun a => runBeh σ (k a))
  | .commit _ tok k => runBeh σ (k tok)
  | .reveal _ ok v k =>
      if ok then runBeh σ (k v) else .zero

@[simp] lemma StratSem_handleStmt_observe
    (cond : L.Expr Γ .bool) (env : L.Env Γ) :
    (StratSem σ).handleStmt (Prog.CmdStmtObs.observe (Γ := Γ) cond) env
      =
    (if L.toBool (L.eval cond env) then WDist.pure () else WDist.zero) := rfl

@[simp] lemma StratSem_handleBind_choose
    (who : Player) (v : View Γ) (A : Act v τ) (env : L.Env Γ) :
    (StratSem σ).handleBind (CmdBindS.choose (Γ := Γ) (τ := τ) who v A) env
      =
    σ.choose who v A (v.proj env) := rfl

@[simp] lemma StratSem_handleBind_commit
    (who : Player) (v : View Γ) (x : Env.Var v.Δ τ) (env : L.Env Γ) :
    (StratSem σ).handleBind (CmdBindS.commit (Γ := Γ) (τ := τ) who v x) env
      =
    WDist.pure (commitTag who ((v.proj env).get x)) := rfl

@[simp] lemma StratSem_handleBind_reveal
    (who : Player) (v : View Γ) (c : Env.Var v.Δ .int) (x : Env.Var v.Δ τ) (env : L.Env Γ) :
    (StratSem σ).handleBind (CmdBindS.reveal (Γ := Γ) (τ := τ) who v c x) env
      =
    (if (v.proj env).get c == commitTag who ((v.proj env).get x)
     then WDist.pure ((v.proj env).get x)
     else WDist.zero) := rfl

@[simp] lemma StratSem_E_bind {α β}
    (xs : WDist α) (f : α → WDist β) :
    (StratSem σ).E.bind xs f = WDist.bind xs f := rfl

theorem runBeh_behEval_eq_evalS {Γ τ} (p : SProg Γ τ) (env : L.Env Γ) :
    runBeh σ (behEval p env) = evalS σ p env := by
  induction p with
  | ret e => rfl
  | letDet e k ih => simpa [behEval, evalS] using ih (L.eval e env, env)
  | doStmt s k ih =>
      cases s with
      | observe cond =>
          -- reduce both sides to an if on the same condition
          by_cases h : L.toBool (L.eval cond env)
          · -- cond true: both continue
            simp only [behEval, evalS,
                       Prog.evalWith_doStmt, StratSem_handleStmt_observe, h, reduceIte]
            rw [ih]
            change Prog.evalWith (StratSem σ) k env =
              WDist.bind (WDist.pure ()) (fun _ => Prog.evalWith (StratSem σ) k env)
            simp [WDist.bind_pure]
          · -- cond false: both reject (mass 0)
            simp [behEval, runBeh, evalS, h, StratSem, EffWDist]
  | doBind c k ih =>
      cases c with
      | choose who v A =>
          simp only [evalS, Prog.evalWith_doBind, StratSem_handleBind_choose, StratSem_E_bind]
          refine congrArg (fun f => WDist.bind (σ.choose who v A (v.proj env)) f) ?_
          funext a
          simpa [evalS] using ih (a, env)
      | commit who v x =>
          -- `commit` is deterministic: both sides just extend env with the token then continue
          -- simp uses WDist.bind_pure to drop the bind on RHS
          simp only [behEval, runBeh]
          set tok : Int := commitTag who ((v.proj env).get x)
          rw [ih (tok, env)]
          change Prog.evalWith (StratSem σ) k (tok, env) =
            WDist.bind (WDist.pure tok) (fun a => Prog.evalWith (StratSem σ) k (a, env))
          simp
      | reveal who v c x =>
          -- split on the reveal check (same boolean on both sides)
          by_cases h :
              ((v.proj env).get c) == commitTag who ((v.proj env).get x)
          · -- success: both extend env with revealed value and continue
            simp only [behEval, h, reduceIte, runBeh, evalS]
            set xv : Val _ := (v.proj env).get x
            rw [ih (xv, env)]
            have hxv : (v.proj env).get x = xv := rfl
            simp only [Prog.evalWith_doBind, StratSem_handleBind_reveal, hxv, h]
            change Prog.evalWith (StratSem σ) k (xv, env) =
              WDist.bind (WDist.pure xv) (fun a => Prog.evalWith (StratSem σ) k (a, env))
            simp
          · -- failure: both return []
            simp [behEval, evalS, h]
            rfl


theorem runBeh_behEval_eq_evalP_toProb (p : SProg Γ τ) (env : L.Env Γ) :
    runBeh σ (behEval p env) = Prob.evalP (toProb σ p) env := by
  simpa [runBeh_behEval_eq_evalS] using (evalS_eq_evalP_toProb (Γ := Γ) (τ := τ) σ p env)

/-- Identity view sees everything: projection is identity. -/
def idView (Γ : L.Ctx) : View Γ where
  Δ := Γ
  proj := fun env => env

end PartialInfo

/-!
## What we might want to add (future extensions / characterization)

This file defines a minimal core: syntax (`CmdBindS` + `Prog.Prog`) and one denotational
semantics (`evalS`) parameterized by a `Profile`, plus compilation to `Prob`.

Typical next additions (kept out on purpose):

### A) Well-formedness / admissibility predicates
* `WFView` / `WFAct`: basic sanity of views and action sets
(e.g. actions finite, nonempty when required).
* `WFProfile` (legality): for every choice point,
the support of `σ.choose ... obs` is contained in `A obs`.
* (Optional) normalization: require `mass = 1`
(mixed strategies) or allow subprobability (rejection/quit).

### B) Extensional equality and quotienting
`WDist` is intensional (lists); many laws are intended up to reordering/combining equal outcomes.
We may introduce an extensional equivalence (e.g. as a finite measure) and work modulo that.

### C) Commit/reveal with real secrecy
Current `commit`/`reveal` are a deterministic placeholder (no hiding).
A secrecy-capable version likely needs:
* committing to data not necessarily in the view (data in Γ outside v.Δ),
* explicit randomness/salts (or an oracle),
* an explicit commitment store / token discipline,
* and a soundness statement: a revealed value verifies against the stored commitment.

### D) Strategy classes and correlation assumptions
The type of `Profile.choose` permits history-dependent randomization via `L.Env v.Δ`.
If we want to enforce assumptions like "no common randomization"
or "independent private randomness",
we should define restricted strategy/profile classes
(or additional structure) rather than changing the core.

### E) Game-theoretic solution concepts / properties
Once admissibility is pinned down, we can define and study properties such as:
* best-response, (subgame-perfect) equilibrium notions relative to views,
* refinement conditions (e.g. perfect recall-like constraints on views),
* and semantic preservation theorems for compilation targets.

### F) Small-step / interactive operational semantics
The `Beh` interpreter gives an interaction-friendly big-step view.
A small-step semantics (or trace semantics) may be useful
for execution models and compilation proofs.
-/
