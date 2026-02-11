import Vegas.LetGames.ProtoGame
import Vegas.LetProtocol.ProtoLemmas
import Vegas.LetProb.ConditionalEU

/-!
# Proto Conditional EU Integration

Connects the generic `WDist.EV` / `WDist.EV_cond` with Proto's
`EU_dist` / `EU_cond`, and defines `IsNash_Cond` (Nash via conditional EU).
-/

namespace Proto

open Defs Prog WDist

variable {L : Language}

/-! ## EU as EV -/

/-- `EU_dist` is `WDist.EV` applied to the utility-for-player function. -/
theorem EU_dist_eq_EV {τ : L.Ty}
    (d : WDist (L.Val τ)) (u : Utility τ) (who : Player) :
    EU_dist d u who = d.EV (fun v => u v who) := by
  simp only [EU_dist, WDist.EV]

/-- `EU_raw` equals `WDist.EV` (same as EU_dist). -/
theorem EU_raw_eq_EV {τ : L.Ty}
    (d : WDist (L.Val τ)) (u : Utility τ) (who : Player) :
    EU_raw d u who = d.EV (fun v => u v who) := by
  simp only [EU_raw, WDist.EV]

/-- `EU_cond` equals `WDist.EV_cond` applied to utility-for-player. -/
theorem EU_cond_eq_EV_cond {τ : L.Ty}
    (d : WDist (L.Val τ)) (u : Utility τ) (who : Player) :
    EU_cond d u who = d.EV_cond (fun v => u v who) := by
  simp only [EU_cond, EU_raw, WDist.EV_cond, WDist.EV]

/-! ## Conditional Nash equilibrium -/

/-- Expected utility using conditional EU (normalized by mass). -/
noncomputable def EU_Cond {Γ : L.Ctx} (G : Game Γ) (σ : Profile (L := L))
    (env : L.Env Γ) (who : Player) : Real :=
  EU_cond (OutcomeDist G σ env) G.u who

/-- Nash equilibrium defined via conditional EU.
    Under WF chance conditions (all sample distributions are proper probabilities),
    this is equivalent to the standard `IsNash_WF`. -/
def IsNash_Cond {Γ : L.Ctx}
    (Reach : ReachSpec (L := L))
    (G : Game Γ)
    (σ : Profile (L := L))
    (env : L.Env Γ) : Prop :=
  WFOnProg Reach σ G.p ∧
  ∀ (who : Player) (δ : Deviator who),
    WFOnProg Reach (Profile.applyDev σ δ) G.p →
      EU_Cond G σ env who ≥ EU_Cond G (Profile.applyDev σ δ) env who

/-! ## Equivalence under WF chance conditions -/

/-- When mass = 1 (IsProb), EU_dist = EU_cond (no normalization needed). -/
theorem EU_cond_eq_EU_dist_of_isProb {τ : L.Ty}
    (d : WDist (L.Val τ)) (u : Utility τ) (who : Player)
    (hp : IsProb d) :
    EU_cond d u who = EU_dist d u who := by
  rw [EU_cond_eq_EV_cond, EU_dist_eq_EV]
  exact WDist.EV_cond_of_mass_one hp

/-- When the outcome distribution has mass 1, conditional and raw EU agree. -/
theorem EU_Cond_eq_EU_of_isProb {Γ : L.Ctx}
    (G : Game Γ) (σ : Profile (L := L)) (env : L.Env Γ) (who : Player)
    (hp : IsProb (OutcomeDist G σ env)) :
    EU_Cond G σ env who = EU G σ env who := by
  simp only [EU_Cond, EU]
  exact EU_cond_eq_EU_dist_of_isProb _ _ _ hp

-- TODO: prove IsNash_WF ↔ IsNash_Cond under WFChanceOnProg
-- This requires showing that WFChanceOnProg implies IsProb on the outcome distribution,
-- which in turn depends on mass_bind_const / mass preservation through evalProto.
-- Leaving as sorry for now; depends on ProtoGameLemmas progress.

end Proto
