import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic

import Vegas.LetProb.WDist
import Vegas.LetCore.Env
import Vegas.Defs
import Vegas.LetProtocol.Dag
import Vegas.LetProb.Prob
import Vegas.LetProb.ProbLemmas

/-!
# GameProg: game-theoretic layer on top of DagLet

This file does **not** change the operational / probabilistic semantics.
It adds the missing "game" structure:

- utilities on outcomes,
- expected utility (EU) induced by `evalD`,
- profile well-formedness predicates (e.g. legality/support),
- unilateral deviations,
- a Nash-style "no profitable deviation" notion.

Important design choice:
`Dag` returns values of some object-language type `τ : L.Ty`.
So utilities are provided *externally* as `L.Val τ → Player → Real`.
(If you later add a dedicated payoff type in `L.Ty`, you can specialize.)
-/

namespace Game

open Prog Defs Dag
open scoped BigOperators

variable {L : Language}
variable {W : Type} [WeightModel W]

section Support

abbrev VCtx {L} {Γ : L.Ctx} (v : Dag.View (L := L) Γ) := v.Δ
abbrev VEnv {L} {Γ : L.Ctx} (v : Dag.View (L := L) Γ) := L.Env v.Δ

/-- `d` is supported on the action set `A envv` (where `envv` lives in the view context). -/
def SupportedOn
    {L : Language} {W : Type} [WeightModel W] {Γ : L.Ctx} {τ : L.Ty}
    (v : Dag.View (L := L) Γ)
    (A : Dag.Act (L := L) v τ)
    (envv : L.Env v.Δ)
    (d : WDist W (L.Val τ)) : Prop :=
  ∀ vw ∈ d.weights, vw.1 ∈ A envv

/-- Global-env version: check support against `A (v.proj env)`. -/
def SupportedOnGlobal
    {L : Language} {W : Type} [WeightModel W] {Γ : L.Ctx} {τ : L.Ty}
    (v : Dag.View (L := L) Γ)
    (A : Dag.Act (L := L) v τ)
    (env : L.Env Γ)
    (d : WDist W (L.Val τ)) : Prop :=
  ∀ vw ∈ d.weights, vw.1 ∈ A (v.proj env)

/-- A minimal well-formedness predicate for profiles: every chosen kernel
is supported on the offered action set.
-/
def WFProfileLocal {L : Language} {W : Type} [WeightModel W] {Γ : L.Ctx}
    (σ : Dag.Profile (L := L) (W := W)) : Prop :=
  ∀ {τ : L.Ty} (who : Player) (v : Dag.View (L := L) Γ) (A : Dag.Act (L := L) v τ)
    (envv : L.Env v.Δ),
    SupportedOn (L := L) v A envv (σ.choose who v A envv)

/-- Global-env well-formedness: for every global `env : Env Γ`,
the chosen distribution at the projected env is supported on the offered actions
at that same projected env. -/
def WFProfileGlobal
    {L : Language} {W : Type} [WeightModel W] {Γ : L.Ctx}
    (σ : Dag.Profile (L := L) (W := W)) : Prop :=
  ∀ {τ : L.Ty} (who : Player) (v : Dag.View (L := L) Γ)
    (A : Dag.Act (L := L) v τ)
    (env : L.Env Γ),
    SupportedOnGlobal (L := L) v A env (σ.choose who v A (v.proj env))

/-- Global-env well-formedness restricted to reachable global environments. -/
def WFProfileGlobalOn
    {L : Language} {W : Type} [WeightModel W] {Γ : L.Ctx}
    (Reach : L.Env Γ → Prop)
    (σ : Dag.Profile (L := L) (W := W)) : Prop :=
  ∀ {τ : L.Ty} (who : Player) (v : Dag.View (L := L) Γ)
    (A : Dag.Act (L := L) v τ)
    (env : L.Env Γ),
    Reach env →
    SupportedOnGlobal (L := L) v A env (σ.choose who v A (v.proj env))

theorem WFProfileLocal.implies_global
    {L : Language} {W : Type} [WeightModel W] {Γ : L.Ctx}
    {σ : Dag.Profile (L := L) (W := W)} :
    WFProfileLocal (Γ := Γ) σ → WFProfileGlobal (Γ := Γ) σ := by
  intro h τ who v A env
  exact h who v A (v.proj env)

end Support

section EU

/-- Expected utility of player `who`, given:
- a distribution over outcomes `d : WDist W α`,
- a utility function `u : α → Player → Real`.

This is the finite-support sum: `∑ w * u(x)` (weights are `W`). -/
noncomputable def EU_ofWDist {α : Type _}
    (d : WDist W α) (u : α → Player → Real) (who : Player) : Real :=
  d.weights.foldr
    (fun (xw : α × W) acc => acc + (WeightModel.toReal xw.2) * u xw.1 who)
    0

/-- Expected utility induced by evaluating a `DagProg`. -/
noncomputable def EU
    {Γ : L.Ctx} {τ : L.Ty}
    (σ : Dag.Profile (L := L) (W := W))
    (p : Dag.DagProg (L := L) (W := W) Γ τ)
    (env : L.Env Γ)
    (u : L.Val τ → Player → Real)
    (who : Player) : Real :=
  EU_ofWDist (Dag.evalD σ p env) u who

end EU

section Deviations

/-- Override a profile on a single player, leaving other players unchanged. -/
noncomputable def Profile.overrideAt
    {Γ : L.Ctx} (σ : Profile (L := L) (W := W)) (who : Player)
    (choose' :
      {τ : L.Ty} →
        Player → (v : View (L := L) Γ) → Act (L := L) v τ →
          (L.Env v.Δ → WDist W (L.Val τ))) :
    Profile (L := L) (W := W) :=
by
  classical
  refine ⟨?choose⟩
  intro Γ' τ p v A envv
  classical
  by_cases hΓ : Γ' = Γ
  · subst hΓ
    by_cases hp : p = who
    · subst hp
      exact choose' p v A envv
    · exact σ.choose p v A envv
  · -- for other contexts, leave profile unchanged
    exact σ.choose p v A envv

noncomputable def Deviate
    {Γ : L.Ctx} (σ : Profile (L := L) (W := W)) (who : Player)
    (choose' :
      {τ : L.Ty} →
        Player → (v : View (L := L) Γ) → Act (L := L) v τ →
          (L.Env v.Δ → WDist W (L.Val τ))) :
    Profile (L := L) (W := W) :=
  Profile.overrideAt σ who choose'

end Deviations

section Equilibrium

/-- `σ` is a Nash-style equilibrium for program `p` at environment `env`
w.r.t. utility `u` if no player can improve their expected utility by a unilateral deviation.

This is intentionally *very general*: deviations range over all `choose'`.
If you want to restrict deviations (e.g. to legal / supported ones), add those
premises inside the quantifier. -/
def IsNash
    {Γ : L.Ctx} {τ : L.Ty}
    (σ : Dag.Profile (L := L) (W := W))
    (p : Dag.DagProg (L := L) (W := W) Γ τ)
    (env : L.Env Γ)
    (u : L.Val τ → Player → Real) : Prop :=
  ∀ who : Player,
    ∀ choose' :
      ({τ' : L.Ty} →
        Player →
        (v : Dag.View (L := L) Γ) →
        Dag.Act (L := L) v τ' →
        (L.Env v.Δ → WDist W (L.Val τ'))),
      EU σ p env u who ≥
        EU (Deviate (Γ := Γ) σ who choose') p env u who

/-- A legality-restricted equilibrium: only deviations that remain `WFProfile` count. -/
def IsNash_WF
    {Γ : L.Ctx} {τ : L.Ty}
    (σ : Dag.Profile (L := L) (W := W))
    (p : Dag.DagProg (L := L) (W := W) Γ τ)
    (env : L.Env Γ)
    (u : L.Val τ → Player → Real) : Prop :=
  WFProfileLocal (Γ := Γ) σ ∧
  ∀ who : Player,
    ∀ choose' :
      ({τ' : L.Ty} →
        Player →
        (v : Dag.View (L := L) Γ) →
        Dag.Act (L := L) v τ' →
        (L.Env v.Δ → WDist W (L.Val τ'))),
      WFProfileLocal (Γ := Γ) (Deviate (Γ := Γ) σ who choose')
      → EU σ  p env u who ≥ EU (Deviate (Γ := Γ) σ who choose') p env u who

end Equilibrium

/-!
## Bridge to ProbLet

You already proved `evalD = Prob.evalP ∘ toProb`. As a consequence,
any EU computed from `evalD` can be pushed to ProbLet if you need to reuse
measure-theory infrastructure there. We keep the lemma here as a convenience.
-/
section ProbBridge

@[simp] theorem evalD_eq_evalP_toProb
    (σ : Dag.Profile (L := L) (W := W)) {Γ : L.Ctx} {τ : L.Ty}
    (p : Dag.DagProg (L := L) (W := W) Γ τ) (env : L.Env Γ) :
    Dag.evalD σ p env
      =
    Prob.evalP (Dag.toProb σ p) env :=
  Dag.evalD_eq_evalP_toProb σ p env

end ProbBridge

end Game
