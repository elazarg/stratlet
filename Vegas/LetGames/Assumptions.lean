/-
Vegas/LetGames/Assumptions.lean

Game-theoretic layer on top of the event-emitting protocol (EProtoProg).

This file defines:
- `TracedUtility`: utility that depends on both final value and trace
- `Assumptions`: game assumptions bundle (players, utility, convention)
- `GameE`: game = EProtoProg + assumptions
- `EU_traced`: expected utility over traced distributions
- `EU`: expected utility of a game under a profile
- `IsNash`: Nash equilibrium for traced games
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic

import Vegas.Defs
import Vegas.LetCore.Prog
import Vegas.LetProb.WDist
import Vegas.LetGames.ProtoGame
import Vegas.LetProtocol.Emit

namespace Assumptions

open Defs Prog Proto Emit

variable {L : Language}

-- ============================================================
-- 1) Traced utility
-- ============================================================

/-- Utility function that depends on both the terminal value and the event trace.
This generalizes Proto.Utility (which ignores traces). -/
abbrev TracedUtility (Ev : Type) (τ : L.Ty) : Type :=
  L.Val τ → Trace Ev → Player → Real

-- ============================================================
-- 2) Assumptions bundle
-- ============================================================

/-- Game assumptions: players, utility, and an optional convention (predicate on traces).
The convention defaults to `True` (no restriction). -/
structure GameAssumptions (Ev : Type) (τ : L.Ty) where
  players : List Player
  utility : TracedUtility Ev τ
  convention : Trace Ev → Prop := fun _ => True

-- ============================================================
-- 3) GameE: event-emitting game
-- ============================================================

/-- A game with events: an EProtoProg plus assumptions. -/
structure GameE (Ev : Type) (Γ : L.Ctx) where
  τ : L.Ty
  protocol : EProtoProg (L := L) Ev Γ τ
  assumptions : GameAssumptions (L := L) Ev τ

-- ============================================================
-- 4) Expected utility
-- ============================================================

/-- Expected utility of a traced distribution for one player.
Finite-support sum: `Σ w * u(v, tr, who)` over all (value, trace, weight) triples. -/
noncomputable def EU_traced {Ev : Type} {τ : L.Ty}
    (d : TracedWDist Ev (L.Val τ))
    (u : TracedUtility (L := L) Ev τ)
    (who : Player) : Real :=
  d.weights.foldr
    (fun (xw : (L.Val τ × Trace Ev) × NNReal) acc =>
      acc + (xw.2 : Real) * u xw.1.1 xw.1.2 who)
    0

/-- Expected utility of a game under a profile at a given environment. -/
noncomputable def EU {Ev : Type} {Γ : L.Ctx}
    (G : GameE (L := L) Ev Γ) (σ : Profile (L := L)) (env : L.Env Γ)
    (who : Player) : Real :=
  EU_traced (evalEProto σ G.protocol env) G.assumptions.utility who

-- ============================================================
-- 5) Deviations and Nash equilibrium
-- ============================================================

/-- Nash equilibrium for event-emitting games, restricted to WF deviations.
Both σ and deviated profiles must satisfy `WFOnProgE`. -/
def IsNash_WF {Ev : Type} {Γ : L.Ctx}
    (Reach : ReachSpec (L := L))
    (G : GameE (L := L) Ev Γ)
    (σ : Profile (L := L))
    (env : L.Env Γ) : Prop :=
  WFOnProgE Reach σ G.protocol ∧
  ∀ (who : Player) (δ : Deviator (L := L) who),
    WFOnProgE Reach (Profile.applyDev σ δ) G.protocol →
      EU G σ env who ≥ EU G (Profile.applyDev σ δ) env who

/-- Milestone default Nash: all environments reachable. -/
def IsNash {Ev : Type} {Γ : L.Ctx}
    (G : GameE (L := L) Ev Γ)
    (σ : Profile (L := L))
    (env : L.Env Γ) : Prop :=
  IsNash_WF ReachAll G σ env

-- ============================================================
-- 6) Bridge: lifting plain Proto games to GameE
-- ============================================================

/-- Convert a plain Proto.Utility to a TracedUtility (ignoring traces). -/
def liftUtility {Ev : Type} {τ : L.Ty} (u : Proto.Utility (L := L) τ) :
    TracedUtility (L := L) Ev τ :=
  fun v _tr who => u v who

/-- Lift a Proto.Game to a GameE (using liftProto for the protocol, liftUtility for utility). -/
def liftGame {Ev : Type} {Γ : L.Ctx} (G : Proto.Game (L := L) Γ) :
    GameE (L := L) Ev Γ where
  τ := G.τ
  protocol := liftProto G.p
  assumptions := {
    players := []  -- Proto.Game doesn't track players
    utility := liftUtility G.u
  }

end Assumptions
