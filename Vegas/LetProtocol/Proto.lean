/-
Vegas/Proto.lean

ProtoLet = "protocol-with-yields" core (milestone layer).

What this layer commits to (and what it *doesn't*):
- Stable yield IDs carried explicitly in syntax.
- Explicit `View` at each yield site; resolvers can only depend on `Env v.Δ`.
- Separate chance vs decision yields in syntax.
- Semantics into `WDist` via `Prog.evalWith` (no new evaluator).
- "Strategy application" pass: discharge decision yields where a (partial) profile is provided.
- Compilation `ProtoProg → ProbLet` is only defined for programs with *no remaining* decision yields.
- Legality/WF predicates, discrete EU, Nash restricted to WF deviations.
- No parent-sets / ObsSpec, no perfect recall enforcement, no Reachσ, no MeasureTheory EU,
  no commutativity quotient, no commit/reveal (all postponed).

Modeling assumptions (non-obvious):
1) Yield IDs are provided by the encoder and must be preserved by rewriting/compilation.
2) Perfect recall is an encoder responsibility: later `View`s must include what should be remembered.
3) Conditioning is hard rejection (`observe` filters mass; no normalization).
4) Semantics does not enforce legality; WF is used only for equilibrium reasoning.
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic

import Vegas.Defs
import Vegas.LetCore.Prog
import Vegas.LetProb.Prob
import Vegas.LetProb.WDist

namespace Proto

open Defs
open Prog

variable {L : Language}

-- ============================================================
-- 1) Stable yield identifiers
-- ============================================================

/-- Stable identifier for a yield site (encoder responsibility). -/
abbrev YieldId : Type := Nat

-- ============================================================
-- 2) Views: observable slice at a yield site
-- ============================================================

/--
A `View Γ` describes what is observable at a yield site.

- `Δ` is the visible context
- `proj` extracts the visible environment

Note: this is just an env projection (no explicit transcript/store).
If you later add transcript/common knowledge, `View` likely becomes a projection on a richer state.
-/
structure View (Γ : L.Ctx) where
  Δ : L.Ctx
  proj : L.Env Γ → L.Env Δ

/-- Action set offered at a decision yield: depends only on the visible env. -/
abbrev Act {Γ : L.Ctx} (v : View Γ) (τ : L.Ty) : Type :=
  L.Env v.Δ → List (L.Val τ)

/-- Chance kernel at a sample yield: depends only on the visible env. -/
abbrev ObsKernel {Γ : L.Ctx} (v : View Γ) (τ : L.Ty) : Type :=
  L.Env v.Δ → WDist (L.Val τ)

-- ============================================================
-- 3) ProtoProg syntax: chance vs decision yields + observe
-- ============================================================

/--
Bind-commands for protocol-with-yields.

- `sample`: chance node with a kernel over the visible env
- `choose`: decision node with a legal action set over the visible env

Both carry a `YieldId` intended to be the *semantic identity* of the node.
-/
inductive CmdBindProto : Prog.CmdB where
  | sample {Γ : L.Ctx} {τ : L.Ty}
      (id : YieldId) (v : View Γ) (K : ObsKernel v τ) :
      CmdBindProto Γ τ
  | choose {Γ : L.Ctx} {τ : L.Ty}
      (id : YieldId) (who : Player) (v : View Γ) (A : Act v τ) :
      CmdBindProto Γ τ

/-- Statements: reuse unnormalized `observe` from `Prog`. -/
abbrev CmdStmtProto : Prog.CmdS (L := L) := Prog.CmdStmtObs

/-- Protocol programs are `Prog.Prog` instantiated with `CmdBindProto` + `observe`. -/
abbrev ProtoProg : L.Ctx → L.Ty → Type :=
  Prog.Prog CmdBindProto CmdStmtProto

namespace ProtoProg

/-- Smart constructor: return. -/
def ret {Γ : L.Ctx} {τ : L.Ty} (e : L.Expr Γ τ) : ProtoProg Γ τ :=
  Prog.Prog.ret e

/-- Smart constructor: deterministic let-binding. -/
def letDet {Γ : L.Ctx} {τ τ' : L.Ty} (e : L.Expr Γ τ')
    (k : ProtoProg (τ' :: Γ) τ) : ProtoProg Γ τ :=
  Prog.Prog.letDet e k

/-- Smart constructor: hard observation / conditioning (unnormalized). -/
def observe {Γ : L.Ctx} {τ : L.Ty} (cond : L.Expr Γ L.bool)
    (k : ProtoProg Γ τ) : ProtoProg Γ τ :=
  .doStmt (.observe cond) k

/-- Smart constructor: chance sample yield. -/
def sample {Γ : L.Ctx} {τ τ' : L.Ty}
    (id : YieldId) (v : View Γ) (K : ObsKernel v τ')
    (k : ProtoProg (τ' :: Γ) τ) : ProtoProg Γ τ :=
  .doBind (.sample id v K) k

/-- Smart constructor: player decision yield. -/
def choose {Γ : L.Ctx} {τ τ' : L.Ty}
    (id : YieldId) (who : Player) (v : View Γ) (A : Act v τ')
    (k : ProtoProg (τ' :: Γ) τ) : ProtoProg Γ τ :=
  .doBind (.choose id who v A) k

end ProtoProg

-- ============================================================
-- 4) Strategy profile (decision resolver)
-- ============================================================

/--
Decision resolver / strategy profile (milestone shape).

Strategy may depend on:
- player `who`
- stable yield id `id`
- the site’s `View` and offered action set `A`
- the visible env `Env v.Δ`

This avoids infosets/perfect-recall machinery while keeping deviations well-scoped by `id`.
-/
structure Profile where
  choose :
    {Γ : L.Ctx} → {τ : L.Ty} →
      (who : Player) → (id : YieldId) → (v : View Γ) → (A : Act v τ) →
      (L.Env v.Δ → WDist (L.Val τ))

-- ============================================================
-- 5) Semantics into WDist (fixing a profile)
-- ============================================================

/-- `WDist` effect interface (reuse ProbLet’s). -/
abbrev EffWDist : Prog.Eff WDist := Prob.EffWDist

/--
Interpreter for `ProtoProg` under a fixed profile.

- `sample` uses the kernel payload (`K`) applied to the projected env.
- `choose` delegates to the profile and passes only the projected env.
- `observe` is hard rejection (zero mass).
-/
def ProtoSem (σ : Profile (L := L)) :
    Prog.LangSem (L := L) CmdBindProto CmdStmtProto WDist where
  E := EffWDist
  handleBind
    | .sample _id v K, env      => K (v.proj env)
    | .choose _id who v A, env  => σ.choose who _id v A (v.proj env)
  handleStmt
    | .observe cond, env =>
        if L.toBool (L.eval cond env) then WDist.pure () else WDist.zero

@[simp] lemma ProtoSem_handleBind_sample
    (σ : Profile)
    {Γ : L.Ctx} {τ : L.Ty}
    (id : YieldId) (v : View Γ) (K : ObsKernel v τ)
    (env : L.Env Γ) :
    (ProtoSem σ).handleBind (.sample id v K) env = K (v.proj env) := rfl

@[simp] lemma ProtoSem_handleBind_choose
    (σ : Profile)
    {Γ : L.Ctx} {τ : L.Ty}
    (id : YieldId) (who : Player) (v : View Γ) (A : Act v τ)
    (env : L.Env Γ) :
    (ProtoSem σ).handleBind (.choose id who v A) env =
      σ.choose who id v A (v.proj env) := rfl

@[simp] lemma ProtoSem_handleStmt_observe
    (σ : Profile)
    {Γ : L.Ctx}
    (cond : L.Expr Γ L.bool)
    (env : L.Env Γ) :
    (ProtoSem σ).handleStmt (.observe cond) env =
      (if L.toBool (L.eval cond env) then WDist.pure () else WDist.zero) := rfl

/-- Evaluate a `ProtoProg` under profile `σ`. -/
def evalProto {Γ : L.Ctx} {τ : L.Ty} (σ : Profile (L := L)) :
    ProtoProg Γ τ → L.Env Γ → WDist (L.Val τ) :=
  Prog.evalWith (ProtoSem σ)

-- ============================================================
-- 6) Strategy application + compilation to ProbLet
-- ============================================================

/--
A *partial* profile: may or may not resolve a given decision site.

Modeling assumption:
- Partiality represents "strategy not chosen/committed yet" (or intentionally left symbolic),
  NOT runtime failure. If you want runtime failure, return `WDist.zero` instead of `none`.
-/
structure PProfile (L := L) where
  choose? :
    {Γ : L.Ctx} → {τ : L.Ty} →
      (who : Player) → (id : YieldId) → (v : View Γ) → (A : Act v τ) →
      Option (L.Env v.Δ → WDist (L.Val τ))

/-- Embed a total `Profile` as a partial one. -/
def Profile.toPartial (σ : Profile (L := L)) : PProfile (L := L) where
  choose? := fun who id v A => some (σ.choose who id v A)

/--
Apply a partial profile: resolve any `choose` site where `choose?` returns `some kernel`.

This is a syntax-to-syntax pass producing another `ProtoProg`.
It does NOT "finish compilation"; it just discharges decision yields when a strategy is provided.
-/
def applyProfile (π : PProfile (L := L)) {Γ : L.Ctx} {τ : L.Ty} :
    ProtoProg Γ τ → ProtoProg Γ τ
  | .ret e        => .ret e
  | .letDet e k   => .letDet e (applyProfile π k)
  | .doStmt s k   => .doStmt s (applyProfile π k)
  | .doBind c k   =>
      match c with
      | .sample id v K =>
          .doBind (.sample id v K) (applyProfile π k)
      | .choose id who v A =>
          match π.choose? who id v A with
          | some Kdec =>
              -- resolved decision becomes a chance-sample with the decided kernel
              .doBind (.sample id v Kdec) (applyProfile π k)
          | none =>
              -- unresolved decision remains a decision yield
              .doBind (.choose id who v A) (applyProfile π k)

/-- Predicate: program has no remaining decision yields (`choose`). -/
def NoChoose {Γ : L.Ctx} {τ : L.Ty} : ProtoProg Γ τ → Prop
  | .ret _        => True
  | .letDet _ k   => NoChoose k
  | .doStmt _ k   => NoChoose k
  | .doBind c k   =>
      match c with
      | .sample _ _ _    => NoChoose k
      | .choose _ _ _ _  => False

/--
Compile a `ProtoProg` with **no remaining** `choose` into `Prob`.

This is the "real compilation" step: it is only defined under a `NoChoose` proof.
-/
def toProbNoChoose {Γ : L.Ctx} {τ : L.Ty} :
    (p : ProtoProg Γ τ) → NoChoose p → Prob.PProg Γ τ
  | .ret e, _ =>
      .ret e
  | .letDet e k, h =>
      .letDet e (toProbNoChoose k h)
  | .doStmt s k, h =>
      .doStmt s (toProbNoChoose k h)
  | .doBind c k, h =>
      match c with
      | .sample _id v K =>
          let Kfull : Prob.Kernel Γ _ := fun env => K (v.proj env)
          .doBind (.sample Kfull) (toProbNoChoose k h)
      | .choose _id _who _v _A =>
          -- impossible under `NoChoose`
          False.elim h

/-- Optional compilation: returns `none` if any `choose` remains. -/
def toProb? {Γ : L.Ctx} {τ : L.Ty} :
    ProtoProg Γ τ → Option (Prob.PProg Γ τ)
  | .ret e        => some (.ret e)
  | .letDet e k   => Option.map (.letDet e) (toProb? k)
  | .doStmt s k   => Option.map (.doStmt s) (toProb? k)
  | .doBind c k   =>
      match c with
      | .sample _id v K =>
          let Kfull : Prob.Kernel Γ _ := fun env => K (v.proj env)
          Option.map (.doBind (.sample Kfull)) (toProb? k)
      | .choose _id _who _v _A =>
          none

/--
Convenience name: "strategy application" (not final compilation).

Workflow:
  p₀ : ProtoProg Γ τ
  π  : PProfile (L := L)

  p₁ := toProb π p₀              -- resolves some/all decision yields
  if h : NoChoose p₁ then
     q := toProbNoChoose p₁ h    -- now a genuine ProbLet program
-/
abbrev discharge (π : PProfile (L := L)) {Γ τ} :
    ProtoProg (L := L) Γ τ → ProtoProg Γ τ :=
  applyProfile π

-- ============================================================
-- 7) Encoder-facing sanity: yield id collection + uniqueness
-- ============================================================

/-- Collect all yield ids (both chance and decision) appearing in a program. -/
def yieldIds {Γ : L.Ctx} {τ : L.Ty} : ProtoProg Γ τ → List YieldId
  | .ret _        => []
  | .letDet _ k   => yieldIds k
  | .doStmt _ k   => yieldIds k
  | .doBind c k   =>
      match c with
      | .sample id _ _    => id :: yieldIds k
      | .choose id _ _ _  => id :: yieldIds k

/-- Collect decision yield ids (`choose`) appearing in a program. -/
def chooseIds {Γ : L.Ctx} {τ : L.Ty} : ProtoProg Γ τ → List YieldId
  | .ret _        => []
  | .letDet _ k   => chooseIds k
  | .doStmt _ k   => chooseIds k
  | .doBind c k   =>
      match c with
      | .sample _ _ _      => chooseIds k
      | .choose id _ _ _   => id :: chooseIds k

/-- Encoder well-formedness: all yield ids are unique. -/
def NoDupYieldIds {Γ : L.Ctx} {τ : L.Ty} (p : ProtoProg Γ τ) : Prop :=
  (yieldIds p).Nodup

-- ============================================================
-- 8) Legality / WF (program-relative, reachable-env parameter threaded)
-- ============================================================

/--
Generic "support is within predicate" for finite-support `WDist`.

We ignore outcomes with weight `0` (representations may contain zero-weight junk).
-/
def SupportedOn {α : Type _} (d : WDist α) (S : α → Prop) : Prop :=
  ∀ {a : α} {w : NNReal}, (a, w) ∈ d.weights → w ≠ 0 → S a

/-- Legality at a specific decision yield instance. -/
def LegalAt
    {Γ : L.Ctx} {τ : L.Ty}
    (σ : Profile (L := L))
    (who : Player) (id : YieldId)
    (v : View Γ) (A : Act v τ)
    (obs : L.Env v.Δ) : Prop :=
  SupportedOn (σ.choose who id v A obs) (fun a => a ∈ A obs)

/--
Reachability predicate, threaded parametrically but (for the milestone)
usually instantiated as `True`.

Polymorphic in Γ so the same `Reach` works under context extension.
-/
abbrev ReachSpec : Type :=
  {Γ : L.Ctx} → L.Env Γ → Prop

/-- Milestone default: everything is reachable. -/
def ReachAll : ReachSpec (L := L) := fun {_Γ} _env => True

/--
Program-relative well-formedness: only checks `choose` nodes that actually appear in `p`.

At each `choose id who v A` site in context Γ, require:
  ∀ env : Env Γ, Reach env → LegalAt σ who id v A (v.proj env)
-/
def WFOnProg (Reach : ReachSpec (L := L)) (σ : Profile (L := L)) :
    {Γ : L.Ctx} → {τ : L.Ty} → ProtoProg Γ τ → Prop
  | _Γ, _τ, .ret _        => True
  | _Γ, _τ, .letDet _ k   => WFOnProg Reach σ k
  | _Γ, _τ, .doStmt _ k   => WFOnProg Reach σ k
  | Γ,  _τ, .doBind c k   =>
      (match c with
       | .sample _id _v _K =>
           True
       | .choose id who v A =>
           ∀ env : L.Env Γ, Reach env → LegalAt σ who id v A (v.proj env))
      ∧ WFOnProg Reach σ k

-- ============================================================
-- 9) Deviations (global per-player patches)
-- ============================================================

/--
A deviator for a fixed player `who` supplies replacement behavior for *all* of that player’s
decision yields (still view-restricted by types).

Note: if the encoder reuses yield ids, deviations may patch multiple sites at once.
Use `NoDupYieldIds` as an encoder-side side condition when this matters.
-/
structure Deviator (who : Player) where
  choose :
    {Γ : L.Ctx} → {τ : L.Ty} →
      (id : YieldId) → (v : View Γ) → (A : Act v τ) →
      (L.Env v.Δ → WDist (L.Val τ))

/-- Apply a deviator to a profile: only the specified player’s decisions change. -/
def Profile.applyDev (σ : Profile (L := L)) {who : Player} (δ : Deviator (L := L) who) :
    Profile (L := L) where
  choose := by
    intro Γ τ who' id v A obs
    by_cases h : who' = who
    · subst h
      exact δ.choose id v A obs
    · exact σ.choose who' id v A obs

-- ============================================================
-- 10) EU and Nash (discrete, finite-support; no MeasureTheory)
-- ============================================================

/-- Utility of terminal values.
Milestone choice: `Real` for easy interaction with NNReal weights. -/
abbrev Utility (τ : L.Ty) : Type := L.Val τ → Player → Real

/--
Expected utility of a `WDist` outcome for one player (finite sum over weights).

Note: unnormalized semantics (e.g. after `observe`) is intentional at this milestone.
-/
noncomputable def EU_dist {τ : L.Ty} (d : WDist (L.Val τ)) (u : Utility τ) (who : Player) :
    Real :=
  d.weights.foldr
    (fun (vw : L.Val τ × NNReal) acc => acc + ((vw.2 : Real) * (u vw.1 who)))
    0

/-- Raw EU: treat rejected runs as 0 payoff (since they contribute no mass). -/
noncomputable def EU_raw {τ : L.Ty} (d : WDist (L.Val τ))
    (u : Utility τ) (who : Player) : Real :=
  d.weights.foldr
    (fun (vw : L.Val τ × NNReal) acc => acc + ((vw.2 : Real) * (u vw.1 who)))
    0

/-- Conditional EU: normalize by total mass; undefined mass=0 mapped to 0 by convention. -/
noncomputable def EU_cond {τ : L.Ty} (d : WDist (L.Val τ))
    (u : Utility τ) (who : Player) : Real :=
  if d.mass = 0 then 0 else
    (EU_raw d u who) / (d.mass : Real)

def IsProb {α} (d : WDist α) : Prop := d.mass = 1

def WFChanceOnProg (Reach : ReachSpec (L := L)) :
    {Γ : L.Ctx} → {τ : L.Ty} → ProtoProg Γ τ → Prop
  | _, _, .ret _        => True
  | _, _, .letDet _ k   => WFChanceOnProg Reach k
  | _, _, .doStmt _ k   => WFChanceOnProg Reach k
  | Γ, _, .doBind c k   =>
      match c with
      | .sample _id v K =>
          (∀ env : L.Env Γ, Reach env → IsProb (K (v.proj env))) ∧ WFChanceOnProg Reach k
      | .choose _ _ _ _ =>
          WFChanceOnProg Reach k

/--
A game is just a protocol program plus a utility function on its final value.
(Thin wrapper: no new calculus.)
-/
structure Game (Γ : L.Ctx) where
  τ : L.Ty
  p : ProtoProg Γ τ
  u : Utility τ

/-- Outcome distribution of a game under a profile. -/
def OutcomeDist {Γ : L.Ctx} (G : Game Γ) (σ : Profile (L := L)) (env : L.Env Γ) :
    WDist (L.Val G.τ) :=
  evalProto σ G.p env

/-- Expected utility of a game under a profile. -/
noncomputable def EU {Γ : L.Ctx} (G : Game Γ) (σ : Profile (L := L)) (env : L.Env Γ)
    (who : Player) : Real :=
  EU_dist (OutcomeDist G σ env) G.u who

/--
Nash equilibrium restricted to WF deviations (WF is a side-condition).

Milestone version:
- deviations are *global per player* (patch all of the deviator’s decision sites)
- both σ and deviated profiles must satisfy `WFOnProg Reach _ G.p`
-/
def IsNash_WF {Γ : L.Ctx}
    (Reach : ReachSpec (L := L))
    (G : Game Γ)
    (σ : Profile (L := L))
    (env : L.Env Γ) : Prop :=
  WFOnProg Reach σ G.p ∧
  ∀ (who : Player) (δ : Deviator who),
    WFOnProg Reach (Profile.applyDev σ δ) G.p →
      EU G σ env who ≥ EU G (Profile.applyDev σ δ) env who

/-- Milestone default Nash: all environments reachable. -/
def IsNash {Γ : L.Ctx} (G : Game Γ) (σ : Profile (L := L)) (env : L.Env Γ) : Prop :=
  IsNash_WF (ReachAll) G σ env

end Proto
