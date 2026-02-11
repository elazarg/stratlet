import Vegas.LetGames.Denotations
import Vegas.LetProb.ConditionalEU

/-!
# EU Bridge: Proto ↔ EFG Expected Utility Preservation

This module establishes the connection between Proto's `EU_dist` and the
expected utility computed on the EFG tree produced by `ParentProtoProg.toEFG`.

## Strategy

We define a structural recursive EU directly on `ParentProtoProg` using
`WDist.EV` as the core compositional tool. The key bridge theorem
`eu_preservation_directEU` connects Proto's `EU_dist` to this structural
computation via `WDist.EV_bind` (the tower property).

## Main results

1. `Proto.directEU` — structural recursive EU on ParentProtoProg (fuel-free)
2. `Proto.eu_preservation_directEU` — the main preservation theorem
-/

namespace Proto

open Defs Prog Env

variable {W : Type} [WeightModel W]

-- ============================================================
-- 1) Direct EU on ParentProtoProg (the "unfolded" bridge)
-- ============================================================

/-- Compute EU directly on a `ParentProtoProg` by structural recursion,
    using the Proto profile to resolve decisions and the utility function
    for terminal values.

    Uses `WDist.EV` for the sample/choose cases, which enables clean
    composition via `WDist.EV_bind` in the preservation proof. -/
noncomputable def ParentProtoProg.directEU
    (σ : Profile (L := BasicLang) (W := W))
    (u : Proto.Utility (L := BasicLang) τ) (who : Player) :
    ParentProtoProg W Γ τ → BasicLang.Env Γ → ℝ
  | .ret e, env => u (BasicLang.eval e env) who
  | .letDet e k, env => directEU σ u who k (BasicLang.eval e env, env)
  | .observe _c k, env =>
      -- observe is transparent in toEFG; for Proto semantics,
      -- observe filters mass. In the bridge we assume observe passes.
      directEU σ u who k env
  | .sample _id ps K k, env =>
      let obs := (viewOfVarSpec ps.vars).proj env
      WDist.EV (K obs) (fun v => directEU σ u who k (v, env))
  | .choose _id _who' ps A k, env =>
      let obs := (viewOfVarSpec ps.vars).proj env
      let stratDist := σ.choose _who' _id (viewOfVarSpec ps.vars) A obs
      WDist.EV stratDist (fun v => directEU σ u who k (v, env))

-- ============================================================
-- 2) ObserveFree predicate
-- ============================================================

/-- A `ParentProtoProg` contains no `observe` nodes.
    Under this condition, Proto semantics and EFG semantics agree
    (no mass filtering vs. pass-through mismatch). -/
def ObserveFree : ParentProtoProg W Γ τ → Prop
  | .ret _ => True
  | .letDet _ k => ObserveFree k
  | .observe _ _ => False
  | .sample _ _ _ k => ObserveFree k
  | .choose _ _ _ _ k => ObserveFree k

-- ============================================================
-- 3) The core EU preservation: Proto EU_dist = directEU
-- ============================================================

/-- Key relationship: `EU_dist` is `WDist.EV` with the utility curried.
    This is definitional — both are `weights.foldr` with the same function. -/
private theorem EU_dist_eq_EV {τ : BasicLang.Ty}
    (d : WDist W (BasicLang.Val τ)) (u : Proto.Utility (L := BasicLang) τ) (who : Player) :
    EU_dist d u who = WDist.EV d (fun v => u v who) := rfl

/-- **Main theorem**: For observe-free ParentProtoProgs (no hard conditioning),
    the Proto expected utility equals the direct EU computation.

    The observe-free restriction is because `toEFG` treats observe as
    transparent (pass-through) while Proto's `observe` filters mass.
    For observe-free programs, these agree trivially. -/
theorem eu_preservation_directEU
    (σ : Profile (L := BasicLang) (W := W))
    (u : Proto.Utility (L := BasicLang) τ) (who : Player) :
    (p : ParentProtoProg (L := BasicLang) W Γ τ) → (env : BasicLang.Env Γ) →
    ObserveFree p →
    EU_dist (p.eval σ env) u who = p.directEU σ u who env := by
  intro p
  induction p with
  | ret e =>
      intro env _hof
      simp only [EU_dist_eq_EV]
      exact WDist.EV_pure _ _
  | letDet e k ih =>
      intro env hof
      exact ih u (BasicLang.eval e env, env) hof
  | observe c k ih =>
      intro env hof
      exact absurd hof (by simp [ObserveFree])
  | sample id ps K k ih =>
      intro env hof
      change EU_dist (WDist.bind (K ((viewOfVarSpec ps.vars).proj env))
        (fun v => ParentProtoProg.eval σ k (v, env))) u who
        = WDist.EV (K ((viewOfVarSpec ps.vars).proj env))
            (fun v => ParentProtoProg.directEU σ u who k (v, env))
      rw [EU_dist_eq_EV, WDist.EV_bind]
      congr 1; ext v
      rw [← EU_dist_eq_EV]
      exact ih u (v, env) hof
  | choose id who' ps A k ih =>
      intro env hof
      change EU_dist (WDist.bind (σ.choose who' id (viewOfVarSpec ps.vars) A
          ((viewOfVarSpec ps.vars).proj env))
        (fun v => ParentProtoProg.eval σ k (v, env))) u who
        = WDist.EV (σ.choose who' id (viewOfVarSpec ps.vars) A
            ((viewOfVarSpec ps.vars).proj env))
            (fun v => ParentProtoProg.directEU σ u who k (v, env))
      rw [EU_dist_eq_EV, WDist.EV_bind]
      congr 1; ext v
      rw [← EU_dist_eq_EV]
      exact ih u (v, env) hof

end Proto
