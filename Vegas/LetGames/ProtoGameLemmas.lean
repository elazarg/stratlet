import Vegas.LetGames.ProtoGame
import Vegas.LetProtocol.ProtoLemmas
import Vegas.LetProtocol.ProtoEquiv

/-!
# Proto Game-Theory Lemmas

Basic game-theoretic lemmas for `EU_dist`, `EU`, and deviation identity.
Also includes EU preservation templates (moved from ProtoEquiv.lean).
-/

namespace Proto

open Defs Prog
variable {L : Language}
variable {W : Type} [WeightModel W]

-- ============================================================
-- EU_dist lemmas
-- ============================================================

/-- EU of a point distribution is `1 * u v who`. -/
theorem EU_dist_pure {τ : L.Ty}
    (v : L.Val τ) (u : Utility τ) (who : Player) :
    EU_dist (WDist.pure (W := W) v) u who = 1 * u v who := by
  simp [EU_dist, WDist.pure, WeightModel.toReal_one]

/-- EU of the zero distribution is 0. -/
theorem EU_dist_zero {τ : L.Ty}
    (u : Utility τ) (who : Player) :
    EU_dist (WDist.zero : WDist W (L.Val τ)) u who = 0 := by
  simp [EU_dist, WDist.zero]

/-- If a protocol has no decision yields, EU is profile-independent. -/
theorem EU_profile_indep_NoChoose {Γ : L.Ctx}
    (G : Game (W := W) Γ) (hNC : NoChoose G.p)
    (σ₁ σ₂ : Profile (L := L) (W := W)) (env : L.Env Γ) (who : Player) :
    EU G σ₁ env who = EU G σ₂ env who := by
  simp only [EU, OutcomeDist]
  rw [ProtoProg.evalProto_profile_indep G.p hNC σ₁ σ₂ env]

omit [WeightModel W] in
/-- Deviating with a player's own strategy is an identity. -/
theorem Deviator_id (σ : Profile (L := L) (W := W)) (who : Player) :
    Profile.applyDev σ
      (Deviator.mk (L := L) (W := W) (who := who)
        (fun id v A obs => σ.choose who id v A obs)) = σ := by
  cases σ with
  | mk choose =>
      simp only [Profile.applyDev]
      congr 1
      funext Γ τ who' id v A obs
      split
      · next h => subst h; rfl
      · rfl

-- ============================================================
-- EU preservation templates (moved from ProtoEquiv.lean)
-- ============================================================

/-- A program transformation that preserves denotations preserves EU. -/
theorem EU_preserved_of_sem_eq
    {Γ : L.Ctx} (G : Game (W := W) Γ)
    {p' : ProtoProg (W := W) Γ G.τ}
    (hEq : sem G.p = sem p')
    (σ : Profile (L := L) (W := W)) (env : L.Env Γ) (who : Player) :
    EU G σ env who =
      EU_dist (evalProto σ p' env) G.u who := by
  unfold EU OutcomeDist
  rw [show evalProto σ G.p env = evalProto σ p' env
      from congr_fun (congr_fun hEq σ) env]

/-- A transformation preserving yield structure and denotations
    produces a program with the same EU as the original game. -/
theorem EU_preserved_of_pass
    {Γ : L.Ctx} (G : Game (W := W) Γ)
    (f : {Γ' : L.Ctx} → {τ' : L.Ty} →
         ProtoProg (L := L) (W := W) Γ' τ' → ProtoProg (W := W) Γ' τ')
    (_hStruct : PreservesYieldStructure f)
    (hEq : sem G.p = sem (f G.p))
    (σ : Profile (L := L) (W := W)) (env : L.Env Γ) (who : Player) :
    EU G σ env who =
      EU_dist (evalProto σ (f G.p) env) G.u who :=
  EU_preserved_of_sem_eq G hEq σ env who

/-- Specialization: if `f` preserves denotations and NoChoose,
    then the compiled ProbLet program has the same EU. -/
theorem EU_preserved_of_noChoose_pass
    {Γ : L.Ctx} (G : Game (W := W) Γ)
    (f : {Γ' : L.Ctx} → {τ' : L.Ty} →
         ProtoProg (L := L) (W := W) Γ' τ' → ProtoProg (W := W) Γ' τ')
    (hStruct : PreservesYieldStructure f)
    (hEq : sem G.p = sem (f G.p))
    (hNC : NoChoose G.p)
    (σ : Profile (L := L) (W := W)) (env : L.Env Γ) (who : Player) :
    EU G σ env who =
      EU_dist (evalProto σ (f G.p) env) G.u who := by
  have _hNC' := hStruct.preserves_noChoose G.p hNC
  exact EU_preserved_of_pass G f hStruct hEq σ env who

end Proto
