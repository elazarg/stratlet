import Vegas.LetProtocol.ProtoLemmas

/-!
# Proto Game-Theory Lemmas

Basic game-theoretic lemmas for `EU_dist`, `EU`, and deviation identity.
-/

namespace Proto

open Defs Prog
variable {L : Language}

-- ============================================================
-- EU_dist lemmas
-- ============================================================

/-- EU of a point distribution is `1 * u v who`. -/
theorem EU_dist_pure {τ : L.Ty}
    (v : L.Val τ) (u : Utility τ) (who : Player) :
    EU_dist (WDist.pure v) u who = 1 * u v who := by
  simp [EU_dist, WDist.pure]

/-- EU of the zero distribution is 0. -/
theorem EU_dist_zero {τ : L.Ty}
    (u : Utility τ) (who : Player) :
    EU_dist (WDist.zero : WDist (L.Val τ)) u who = 0 := by
  simp [EU_dist, WDist.zero]

/-- If a protocol has no decision yields, EU is profile-independent. -/
theorem EU_profile_indep_NoChoose {Γ : L.Ctx}
    (G : Game Γ) (hNC : NoChoose G.p)
    (σ₁ σ₂ : Profile) (env : L.Env Γ) (who : Player) :
    EU G σ₁ env who = EU G σ₂ env who := by
  simp only [EU, OutcomeDist]
  rw [ProtoProg.evalProto_profile_indep G.p hNC σ₁ σ₂ env]

/-- Deviating with a player's own strategy is an identity. -/
theorem Deviator_id (σ : Profile (L := L)) (who : Player) :
    Profile.applyDev σ
      (Deviator.mk (L := L) (who := who)
        (fun id v A obs => σ.choose who id v A obs)) = σ := by
  cases σ with
  | mk choose =>
      simp only [Profile.applyDev]
      congr 1
      funext Γ τ who' id v A obs
      split
      · next h => subst h; rfl
      · rfl

end Proto
