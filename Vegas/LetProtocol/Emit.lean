/-
Vegas/LetProtocol/Emit.lean

Effect extension layer: adds `emit` (event emission) to ProtoProg.

This is a thin layer on top of Proto. The key idea:
- `CmdStmtEv Ev` extends statement commands with `emit`
- `EProtoProg Ev` = Prog over CmdBindProto × CmdStmtEv
- Semantics into `WDist (Val τ × Trace Ev)` via a writer-style traced effect
- `liftProto` embeds plain ProtoProg into EProtoProg (no events)
- `applyProfileE` mirrors `applyProfile` for EProtoProg

Design: `emit (f : Env Γ → Ev)` is environment-dependent (subsumes static emit).
Traces are chronological (earliest event first).
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic

import Vegas.Defs
import Vegas.LetCore.Prog
import Vegas.LetProb.Prob
import Vegas.LetProb.WDist
import Vegas.LetProtocol.Proto

namespace Emit

open Defs Prog Proto

variable {L : Language}

-- ============================================================
-- 1) Trace type
-- ============================================================

/-- A trace is a chronological list of events. -/
abbrev Trace (Ev : Type) := List Ev

-- ============================================================
-- 2) Statement commands with emit
-- ============================================================

/-- Statement commands for the event-emitting protocol layer.
- `observe`: hard conditioning (same as Proto)
- `emit f`: emit an event computed from the current environment
-/
inductive CmdStmtEv (Ev : Type) : Prog.CmdS (L := L) where
  | observe {Γ : L.Ctx} (cond : L.Expr Γ L.bool) : CmdStmtEv Ev Γ
  | emit {Γ : L.Ctx} (f : L.Env Γ → Ev) : CmdStmtEv Ev Γ

/-- Event-emitting protocol programs. -/
abbrev EProtoProg (Ev : Type) : L.Ctx → L.Ty → Type :=
  Prog.Prog CmdBindProto (CmdStmtEv Ev)

-- ============================================================
-- 3) Smart constructors
-- ============================================================

namespace EProtoProg

/-- Smart constructor: return. -/
def ret {Ev : Type} {Γ : L.Ctx} {τ : L.Ty} (e : L.Expr Γ τ) : EProtoProg Ev Γ τ :=
  Prog.Prog.ret e

/-- Smart constructor: deterministic let-binding. -/
def letDet {Ev : Type} {Γ : L.Ctx} {τ τ' : L.Ty} (e : L.Expr Γ τ')
    (k : EProtoProg Ev (τ' :: Γ) τ) : EProtoProg Ev Γ τ :=
  Prog.Prog.letDet e k

/-- Smart constructor: hard observation / conditioning. -/
def observe {Ev : Type} {Γ : L.Ctx} {τ : L.Ty} (cond : L.Expr Γ L.bool)
    (k : EProtoProg Ev Γ τ) : EProtoProg Ev Γ τ :=
  .doStmt (.observe cond) k

/-- Smart constructor: emit an event. -/
def emit {Ev : Type} {Γ : L.Ctx} {τ : L.Ty} (f : L.Env Γ → Ev)
    (k : EProtoProg Ev Γ τ) : EProtoProg Ev Γ τ :=
  .doStmt (.emit f) k

/-- Smart constructor: chance sample yield. -/
def sample {Ev : Type} {Γ : L.Ctx} {τ τ' : L.Ty}
    (id : YieldId) (v : View Γ) (K : ObsKernel v τ')
    (k : EProtoProg Ev (τ' :: Γ) τ) : EProtoProg Ev Γ τ :=
  .doBind (.sample id v K) k

/-- Smart constructor: player decision yield. -/
def choose {Ev : Type} {Γ : L.Ctx} {τ τ' : L.Ty}
    (id : YieldId) (who : Player) (v : View Γ) (A : Act v τ')
    (k : EProtoProg Ev (τ' :: Γ) τ) : EProtoProg Ev Γ τ :=
  .doBind (.choose id who v A) k

end EProtoProg

-- ============================================================
-- 4) Traced effect monad (writer over WDist)
-- ============================================================

/-- The traced WDist type: pairs values with event traces. -/
abbrev TracedWDist (Ev : Type) (α : Type) := WDist (α × Trace Ev)

/-- Effect interface for the traced monad.
- pure: value with empty trace
- bind: sequence computations, concatenating traces
- fail: zero distribution
-/
def TracedEff (Ev : Type) : Prog.Eff (TracedWDist Ev) where
  pure x := WDist.pure (x, [])
  bind m f := WDist.bind m (fun (v, tr1) =>
    WDist.map (fun (v', tr2) => (v', tr1 ++ tr2)) (f v))
  fail := WDist.zero

-- ============================================================
-- 5) Semantics: EProtoSem
-- ============================================================

/--
Interpreter for `EProtoProg` under a fixed profile.

- `sample` uses the kernel, paired with empty trace
- `choose` delegates to the profile, paired with empty trace
- `observe` is hard rejection (zero mass) or success with empty trace
- `emit f` succeeds with singleton trace `[f env]`
-/
def EProtoSem (Ev : Type) (σ : Profile (L := L)) :
    Prog.LangSem (L := L) CmdBindProto (CmdStmtEv Ev) (TracedWDist Ev) where
  E := TracedEff Ev
  handleBind
    | .sample _id v K, env => WDist.map (fun x => (x, [])) (K (v.proj env))
    | .choose _id who v A, env => WDist.map (fun x => (x, [])) (σ.choose who _id v A (v.proj env))
  handleStmt
    | .observe cond, env =>
        if L.toBool (L.eval cond env) then WDist.pure ((), []) else WDist.zero
    | .emit f, env => WDist.pure ((), [f env])

/-- Evaluate an `EProtoProg` under profile `σ`. -/
def evalEProto {Ev : Type} {Γ : L.Ctx} {τ : L.Ty} (σ : Profile (L := L)) :
    EProtoProg Ev Γ τ → L.Env Γ → TracedWDist Ev (L.Val τ) :=
  Prog.evalWith (EProtoSem Ev σ)

-- ============================================================
-- 6) Lifting from ProtoProg to EProtoProg
-- ============================================================

/-- Lift a plain `ProtoProg` into `EProtoProg` (no events emitted).
Maps `CmdStmtProto.observe` to `CmdStmtEv.observe`. -/
def liftProto {Ev : Type} {Γ : L.Ctx} {τ : L.Ty} :
    ProtoProg (L := L) Γ τ → EProtoProg (L := L) Ev Γ τ
  | .ret e => .ret e
  | .letDet e k => .letDet e (liftProto k)
  | .doStmt s k =>
      match s with
      | .observe cond => .doStmt (.observe cond) (liftProto k)
  | .doBind c k => .doBind c (liftProto k)

-- ============================================================
-- 7) Strategy application for EProtoProg
-- ============================================================

/-- Apply a partial profile to an `EProtoProg`: resolve `choose` sites
where the profile provides a strategy (identical to `applyProfile` but
for `EProtoProg`). Both `observe` and `emit` pass through unchanged. -/
def applyProfileE (π : PProfile (L := L)) {Ev : Type} {Γ : L.Ctx} {τ : L.Ty} :
    EProtoProg Ev Γ τ → EProtoProg Ev Γ τ
  | .ret e => .ret e
  | .letDet e k => .letDet e (applyProfileE π k)
  | .doStmt s k => .doStmt s (applyProfileE π k)
  | .doBind c k =>
      match c with
      | .sample id v K =>
          .doBind (.sample id v K) (applyProfileE π k)
      | .choose id who v A =>
          match π.choose? who id v A with
          | some Kdec =>
              .doBind (.sample id v Kdec) (applyProfileE π k)
          | none =>
              .doBind (.choose id who v A) (applyProfileE π k)

/-- Predicate: EProtoProg has no remaining decision yields. -/
def NoChooseE {Ev : Type} {Γ : L.Ctx} {τ : L.Ty} : EProtoProg (L := L) Ev Γ τ → Prop
  | .ret _ => True
  | .letDet _ k => NoChooseE k
  | .doStmt _ k => NoChooseE k
  | .doBind c k =>
      match c with
      | .sample _ _ _ => NoChooseE k
      | .choose _ _ _ _ => False

-- ============================================================
-- 8) WF / legality for EProtoProg
-- ============================================================

/-- Program-relative well-formedness for EProtoProg (mirrors Proto.WFOnProg). -/
def WFOnProgE {Ev : Type} (Reach : ReachSpec (L := L)) (σ : Profile (L := L)) :
    {Γ : L.Ctx} → {τ : L.Ty} → EProtoProg Ev Γ τ → Prop
  | _Γ, _τ, .ret _ => True
  | _Γ, _τ, .letDet _ k => WFOnProgE Reach σ k
  | _Γ, _τ, .doStmt _ k => WFOnProgE Reach σ k
  | Γ, _τ, .doBind c k =>
      (match c with
       | .sample _id _v _K => True
       | .choose id who v A =>
           ∀ env : L.Env Γ, Reach env → LegalAt σ who id v A (v.proj env))
      ∧ WFOnProgE Reach σ k

end Emit
