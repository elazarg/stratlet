/-
Vegas/LetGames/ProtoGame.lean

Game-theoretic definitions extracted from Proto.lean:
- Deviations (Deviator, Profile.applyDev)
- Expected utility (EU_dist, EU_raw, EU_cond, Utility)
- Game structure (Game, OutcomeDist, EU)
- Nash equilibrium (IsNash_WF, IsNash)

These are game-layer concepts; protocol mechanics stay in Proto.lean.
-/

import Vegas.LetProtocol.Proto

namespace Proto

open Defs Prog

variable {L : Language}
variable {W : Type} [WeightModel W]

-- ============================================================
-- 1) Deviations (global per-player patches)
-- ============================================================

/--
A deviator for a fixed player `who` supplies replacement behavior for *all* of that player's
decision yields (still view-restricted by types).

Note: if the encoder reuses yield ids, deviations may patch multiple sites at once.
Use `NoDupYieldIds` as an encoder-side side condition when this matters.
-/
structure Deviator (who : Player) where
  choose :
    {Γ : L.Ctx} → {τ : L.Ty} →
      (id : YieldId) → (v : View Γ) → (A : Act v τ) →
      (L.Env v.Δ → WDist W (L.Val τ))

/-- Apply a deviator to a profile: only the specified player's decisions change. -/
def Profile.applyDev (σ : Profile (L := L) (W := W)) {who : Player}
    (δ : Deviator (L := L) (W := W) who) :
    Profile (L := L) (W := W) where
  choose := by
    intro Γ τ who' id v A obs
    by_cases h : who' = who
    · subst h
      exact δ.choose id v A obs
    · exact σ.choose who' id v A obs

-- ============================================================
-- 2) EU and Nash (discrete, finite-support; no MeasureTheory)
-- ============================================================

/-- Utility of terminal values.
Milestone choice: `Real` for easy interaction with NNReal weights. -/
abbrev Utility (τ : L.Ty) : Type := L.Val τ → Player → Real

/--
Expected utility of a `WDist` outcome for one player (finite sum over weights).

Note: unnormalized semantics (e.g. after `observe`) is intentional at this milestone.
-/
noncomputable def EU_dist {τ : L.Ty} (d : WDist W (L.Val τ)) (u : Utility τ) (who : Player) :
    Real :=
  d.weights.foldr
    (fun (vw : L.Val τ × W) acc => acc + (WeightModel.toReal vw.2 * (u vw.1 who)))
    0

/-- Raw EU: treat rejected runs as 0 payoff (since they contribute no mass). -/
noncomputable def EU_raw {τ : L.Ty} (d : WDist W (L.Val τ))
    (u : Utility τ) (who : Player) : Real :=
  d.weights.foldr
    (fun (vw : L.Val τ × W) acc => acc + (WeightModel.toReal vw.2 * (u vw.1 who)))
    0

open Classical in
/-- Conditional EU: normalize by total mass; undefined mass=0 mapped to 0 by convention. -/
noncomputable def EU_cond {τ : L.Ty} (d : WDist W (L.Val τ))
    (u : Utility τ) (who : Player) : Real :=
  if d.mass = 0 then 0 else
    (EU_raw d u who) / WeightModel.toReal d.mass

/--
A game is just a protocol program plus a utility function on its final value.
(Thin wrapper: no new calculus.)
-/
structure Game (Γ : L.Ctx) where
  τ : L.Ty
  p : ProtoProg (W := W) Γ τ
  u : Utility τ

/-- Outcome distribution of a game under a profile. -/
def OutcomeDist {Γ : L.Ctx} (G : Game (W := W) Γ) (σ : Profile (L := L) (W := W))
    (env : L.Env Γ) : WDist W (L.Val G.τ) :=
  evalProto σ G.p env

/-- Expected utility of a game under a profile. -/
noncomputable def EU {Γ : L.Ctx} (G : Game (W := W) Γ) (σ : Profile (L := L) (W := W))
    (env : L.Env Γ) (who : Player) : Real :=
  EU_dist (OutcomeDist G σ env) G.u who

/--
Nash equilibrium restricted to WF deviations (WF is a side-condition).

Milestone version:
- deviations are *global per player* (patch all of the deviator's decision sites)
- both σ and deviated profiles must satisfy `WFOnProg Reach _ G.p`
-/
def IsNash_WF {Γ : L.Ctx}
    (Reach : ReachSpec (L := L))
    (G : Game (W := W) Γ)
    (σ : Profile (L := L) (W := W))
    (env : L.Env Γ) : Prop :=
  WFOnProg Reach σ G.p ∧
  ∀ (who : Player) (δ : Deviator (W := W) who),
    WFOnProg Reach (Profile.applyDev σ δ) G.p →
      EU G σ env who ≥ EU G (Profile.applyDev σ δ) env who

/-- Milestone default Nash: all environments reachable. -/
def IsNash {Γ : L.Ctx} (G : Game (W := W) Γ) (σ : Profile (L := L) (W := W))
    (env : L.Env Γ) : Prop :=
  IsNash_WF (ReachAll) G σ env

end Proto
