/-
Vegas/LetGames/Assume.lean

Game events with inline payoff assumptions.

Each `emit` site carries a `GameEvent` (event name + payoff function).
EU is computed by summing payoffs from the trace — no separate utility needed.

This reuses Emit.lean/EmitLemmas.lean unchanged: `GameEvent` is just the `Ev`
type parameter.
-/

import Mathlib.Data.Real.Basic

import Vegas.Defs
import Vegas.LetGames.ProtoGame
import Vegas.LetProtocol.Emit
import Vegas.LetProtocol.EmitLemmas

namespace Assume

open Defs Prog Proto Emit

variable {L : Language}
variable {W : Type} [WeightModel W]

-- ============================================================
-- 1) GameEvent: event with inline payoff
-- ============================================================

/-- A game event: carries both a descriptive name and a payoff function.
The payoff is syntactic metadata that travels in the trace alongside the event. -/
structure GameEvent where
  name : String
  payoff : Player → Real

-- ============================================================
-- 2) GameProg / GameDist abbreviations
-- ============================================================

/-- Game programs: EProtoProg parameterized by GameEvent. -/
abbrev GameProg (L : Language) (W : Type) [WeightModel W] (Γ : L.Ctx) (τ : L.Ty) :=
  EProtoProg (L := L) (W := W) GameEvent Γ τ

/-- Game distributions: traced WDist over GameEvent. -/
abbrev GameDist (L : Language) (W : Type) [WeightModel W] (τ : L.Ty) :=
  TracedWDist (W := W) GameEvent (L.Val τ)

-- ============================================================
-- 3) Smart constructor: emit with name + payoff
-- ============================================================

/-- Emit a game event with environment-dependent name and payoff. -/
def GameProg.emit {Γ : L.Ctx} {τ : L.Ty}
    (name : L.Env Γ → String)
    (payoff : L.Env Γ → Player → Real)
    (k : GameProg L W Γ τ) : GameProg L W Γ τ :=
  EProtoProg.emit (fun env => ⟨name env, payoff env⟩) k

-- ============================================================
-- 4) Trace payoff and EU
-- ============================================================

/-- Sum of payoffs in a trace for a given player. -/
def tracePayoff (tr : Trace GameEvent) (who : Player) : Real :=
  tr.foldr (fun ev acc => acc + ev.payoff who) 0

/-- Expected utility from a traced game distribution. -/
noncomputable def EU_game {τ : L.Ty}
    (d : GameDist L W τ) (who : Player) : Real :=
  d.weights.foldr
    (fun (xw : (L.Val τ × Trace GameEvent) × W) acc =>
      acc + WeightModel.toReal xw.2 * tracePayoff xw.1.2 who)
    0

/-- Expected utility of a game program under a profile. -/
noncomputable def EU {Γ : L.Ctx} {τ : L.Ty}
    (p : GameProg L W Γ τ)
    (σ : Profile (L := L) (W := W)) (env : L.Env Γ) (who : Player) : Real :=
  EU_game (evalEProto σ p env) who

-- ============================================================
-- 5) Nash equilibrium
-- ============================================================

/-- Nash equilibrium restricted to WF deviations.
Both σ and deviated profiles must satisfy `WFOnProgE`. -/
def IsNash_WF {Γ : L.Ctx} {τ : L.Ty}
    (Reach : ReachSpec (L := L))
    (p : GameProg L W Γ τ)
    (σ : Profile (L := L) (W := W))
    (env : L.Env Γ) : Prop :=
  WFOnProgE Reach σ p ∧
  ∀ (who : Player) (δ : Deviator (L := L) (W := W) who),
    WFOnProgE Reach (Profile.applyDev σ δ) p →
      EU p σ env who ≥ EU p (Profile.applyDev σ δ) env who

/-- Default Nash: all environments reachable. -/
def IsNash {Γ : L.Ctx} {τ : L.Ty}
    (p : GameProg L W Γ τ)
    (σ : Profile (L := L) (W := W))
    (env : L.Env Γ) : Prop :=
  IsNash_WF ReachAll p σ env

-- ============================================================
-- 6) Simp lemma for GameProg.emit
-- ============================================================

@[simp] lemma evalEProto_gameEmit {Γ : L.Ctx} {τ : L.Ty}
    (σ : Profile (L := L) (W := W))
    (name : L.Env Γ → String)
    (payoff : L.Env Γ → Player → Real)
    (k : GameProg L W Γ τ) (env : L.Env Γ) :
    evalEProto σ (GameProg.emit name payoff k) env =
      WDist.map (fun (v, tr) => (v, ⟨name env, payoff env⟩ :: tr))
        (evalEProto σ k env) :=
  by simp [GameProg.emit]

end Assume
